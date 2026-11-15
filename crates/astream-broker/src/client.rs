//! A blocking client for the broker: connect, publish (awaiting the ack), and
//! subscribe (blocking on each delivery). The blocking calls are what make tests
//! deterministic — a publish round-trips before the next step, and a subscriber's
//! `recv` returns exactly when the next delivery arrives, with no reliance on sleeps
//! or wall-clock.
//!
//! One publisher's API does not wait for its broker's answers, for a caller whose loop
//! has other work: the pipelined writes (`Client::send_publish`, `send_retire`,
//! `send_commit`) return once written, and `Client::try_recv_publish_ack` reads an ack
//! only if the broker has answered already, keeping a frame that has only partly
//! arrived for the next read. The writes are still blocking writes: the broker stops
//! reading a connection once about 1,024 of its acks are unresolved (its per-connection
//! bound, `PIPELINE_DEPTH`: acks not yet written back, because their batch is still
//! being flushed or because the client is not reading what was written), and once the
//! socket's buffers fill the next write parks until the broker writes acks again. A
//! caller that keeps what it owes under `Client::MAX_PIPELINE_WINDOW`, trying as it
//! writes, never meets that bound: no more of its acks can be unresolved than it owes.

use crate::logid::{Lineage, LogIdentity};
use crate::proto::{
    append_commit_frame, append_frame, append_fresh_publish_frame, append_publish_frame,
    append_relay_frame, append_retire_frame, decode_delivery_origin, decode_response_with_bt,
    encode_request, foreign_protocol, fresh_publish_frame_len, read_frame, Request, Response,
    WireStats, CAP_EXPIRED_PREFIX, ERR_BAD_FILTER, ERR_BAD_SUBJECT, ERR_FRESH_FENCED,
    ERR_FRESH_HELD, ERR_ORIGIN_REFUSED, ERR_ORIGIN_UNKNOWN, ERR_PROTOCOL, ERR_RATE_LIMITED,
    ERR_RECORD_REFUSED, ERR_REFUSED, ERR_RETIRE_REFUSED, ERR_SUBJECT_BOUND, ERR_UNAUTHORIZED,
    LOG_POISONED_PREFIX, PROTO_VERSION, RATE_LIMITED_PREFIX, RETAINED_FROM_PREFIX,
    RETIRE_CHARGED_PREFIX, RETIRE_CUT_PREFIX, RETIRE_LOG_PREFIX, RETIRE_WILL_PREFIX,
};
use crate::proto::{Gap, NonceExt, ServedInfo};
use astream_wire::frame::decode_frame_header_bytes;
use astream_wire::{crc32_ieee, FrameError, HEADER_SIZE};
use std::io::{self, Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
#[cfg(unix)]
use std::os::unix::net::UnixStream;
#[cfg(unix)]
use std::path::Path;
use std::sync::Arc;
use std::time::{Duration, Instant};

/// A decoded reply, its broker timestamp and its optional delivery origin.
type StampedResponse = (Response, Option<u64>, Option<(u64, u64)>);

#[cfg(clean_islands)]
#[path = "client_island.rs"]
mod client_island;
#[cfg(not(clean_islands))]
pub use crate::twins::client_walk_page_advance;
#[cfg(clean_islands)]
pub use client_island::client_walk_page_advance;

contract_fn! {
    /// Verified check that a `Last` walk page count lies within the liveness limit
    /// (`pages <= max_pages`), linked via `clean-kernel-defeq` to `client_walk_within_limit_isl`.
    #[must_use]
    pub fn client_walk_within_limit(pages: usize, max_pages: usize) -> bool
    clauses [ensures result == (pages <= max_pages)]
    {
        pages <= max_pages
    }
}

/// One record as a client sees it: `(offset, subject, body)` — what a `Delivery`
/// carries.
pub type Record = (u64, String, Vec<u8>);

/// One record with its monotone broker-stamped wall time (`bt=`, unix ms;
/// `REQUIREMENTS` R3): `(offset, subject, body, bt_ms)`. `bt_ms` is `None` for records
/// written before R3 or read from a broker that predates [`Request::BrokerTimes`].
pub type StampedRecord = (u64, String, Vec<u8>, Option<u64>);

/// The answer to a bounded, NON-TERMINAL read ([`Client::last`], [`Client::fetch`]):
/// the page of records, then the `(next, head)` its closing `Mark` carried. Also the
/// shape of [`Client::last_all`]'s whole-face answer, whose mark is its FIRST page's.
pub type Page = (Vec<Record>, (u64, u64));

/// [`Page`] with each record's broker-stamped wall time (`bt=`, unix ms;
/// `REQUIREMENTS` R3): `(records, (next, head))`.
pub type StampedPage = (Vec<StampedRecord>, (u64, u64));

/// A producer's DISTINCT-SUBJECT BUDGET as one broker log counts it: the answer to
/// [`Client::subject_budget`].
///
/// `subjects` is how many entries of the last-value index are charged to the
/// producer (a subject is charged to the producer whose record first put it in the
/// index — updating someone else's subject costs nothing), `reserved` how many more
/// its registered wills hold for subjects they have not landed yet, and `max` the
/// budget both count against
/// ([`MAX_SUBJECTS_PER_PRODUCER`](crate::store::MAX_SUBJECTS_PER_PRODUCER)). A publish
/// that would add a subject past it is refused with
/// [`ERR_SUBJECT_BOUND`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SubjectBudget {
    /// Index entries charged to the producer.
    pub subjects: u64,
    /// Subjects the producer's registered, unlanded wills hold in reserve.
    pub reserved: u64,
    /// The budget `subjects + reserved` counts against.
    pub max: u64,
}

impl SubjectBudget {
    /// How many NEW subjects the producer may still introduce: `max - subjects -
    /// reserved`, saturating at 0. A snapshot — another connection publishing as the
    /// same producer spends from it at once.
    pub const fn remaining(&self) -> u64 {
        self.max
            .saturating_sub(self.subjects)
            .saturating_sub(self.reserved)
    }
}

/// The most `Last` requests one [`Client::last_walk`] may make before the walk is
/// called a FAILURE rather than an answer.
///
/// A liveness bound, not a size one. Every page moves the resume cursor strictly
/// forward (it is the last subject the broker VISITED, after the one it was sent), so
/// against a conforming broker a walk ends; one that has not ended in this many
/// requests has met something pathological — a peer whose cursor never runs out, an
/// index grown faster than it is walked — and the honest answer to a caller that must
/// not read absence as evidence is an error, not a short list. At the broker's
/// `LAST_PAGE_MAX` rows a page the ceiling is 4096 × 4096 = 16 777 216 rows; pages the
/// index-scan bound cuts short reach it sooner.
pub const LAST_WALK_PAGES_MAX: usize = 4096;

/// What a [`Client::last_walk`] callback answers after each row.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Walk {
    /// Deliver the next row, paging on as the answer needs.
    Continue,
    /// That row was the last one wanted: the walk returns at once — the rest of the
    /// page already read is dropped and no further page is asked for — reporting the
    /// row's subject as the cursor that continues it (or no cursor at all, when that
    /// row was the last of an answer the broker said was complete).
    Stop,
}

/// Credit-windowed pipelined flow-control state machine, backed directly by the
/// Clean-origin transition functions [`crate::proto::credit_horizon_monotone`],
/// [`crate::proto::replica_ack_monotone`], [`crate::proto::committed_watermark`], and
/// the `#[ensures]`-verified guard [`crate::proto::can_send_in_window`] from
/// `Astream.Broker.TlaCreditFlowWindow`.
///
/// Maintains the machine-checked invariant `CreditWindowInv`:
/// `acked_seq <= next_send && next_send <= credit_horizon`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CreditWindow {
    acked_seq: u64,
    next_send: u64,
    credit_horizon: u64,
}

impl CreditWindow {
    /// Construct a fresh credit window starting at `(0, 0, initial_credit)` (`Init` in
    /// `Astream.Broker.TlaCreditFlowWindow`).
    #[must_use]
    pub const fn new(initial_credit: u64) -> Self {
        Self {
            acked_seq: 0,
            next_send: 0,
            credit_horizon: initial_credit,
        }
    }

    /// Monotone cumulative sequence acknowledged so far.
    #[must_use]
    pub const fn acked_seq(&self) -> u64 {
        self.acked_seq
    }

    /// Next sequence index to be sent.
    #[must_use]
    pub const fn next_send(&self) -> u64 {
        self.next_send
    }

    /// Current credit horizon (`next_send <= credit_horizon`).
    #[must_use]
    pub const fn credit_horizon(&self) -> u64 {
        self.credit_horizon
    }

    /// Number of unacknowledged frames currently in flight (`next_send - acked_seq`).
    #[must_use]
    pub const fn in_flight(&self) -> u64 {
        self.next_send.saturating_sub(self.acked_seq)
    }

    /// Whether a send is permitted under the current credit horizon
    /// (`can_send_in_window(self.credit_horizon, self.next_send)`).
    #[must_use]
    pub const fn can_send(&self) -> bool {
        crate::proto::can_send_in_window(self.credit_horizon, self.next_send)
    }

    /// Attempt to consume one unit of send credit (`SendBatch` in
    /// `Astream.Broker.TlaCreditFlowWindow`) via the 4-parameter
    /// [`crate::proto::windowed_send_advance`] kernel, hand-written Rust that calls the
    /// Clean-Origin (`I5`) functions its doc names. Returns `true` and advances
    /// `next_send` by 1 if `self.can_send()` holds, or `false` if the credit window is full.
    pub const fn try_send(&mut self) -> bool {
        if !self.can_send() {
            return false;
        }
        let cand = self.next_send.saturating_add(1);
        let next = crate::proto::windowed_send_advance(
            self.next_send,
            self.acked_seq,
            self.credit_horizon,
            cand,
        );
        if next > self.next_send {
            self.next_send = next;
            true
        } else {
            false
        }
    }

    /// Advance `next_send` toward `cand_seq` clamped by `credit_horizon` via the
    /// 4-parameter [`crate::proto::windowed_send_advance`] kernel, hand-written Rust that
    /// calls the Clean-Origin (`I5`) functions its doc names.
    pub const fn advance_send_to(&mut self, cand_seq: u64) -> u64 {
        self.next_send = crate::proto::windowed_send_advance(
            self.next_send,
            self.acked_seq,
            self.credit_horizon,
            cand_seq,
        );
        self.next_send
    }

    /// Record a cumulative acknowledgment up to `ack` (`AckStep` in
    /// `Astream.Broker.TlaCreditFlowWindow`), clamped to `self.next_send` via
    /// [`crate::proto::committed_watermark`] and advanced monotonically via
    /// [`crate::proto::replica_ack_monotone`].
    pub const fn record_ack(&mut self, ack: u64) -> u64 {
        let bounded = crate::proto::committed_watermark(self.next_send, ack);
        self.acked_seq = crate::proto::replica_ack_monotone(self.acked_seq, bounded);
        self.acked_seq
    }

    /// Advance the credit horizon monotonically (`GrantCreditStep` in
    /// `Astream.Broker.TlaCreditFlowWindow`) via Clean-origin
    /// [`crate::proto::credit_horizon_monotone`].
    pub const fn grant_credit(&mut self, new_horizon: u64) -> u64 {
        self.credit_horizon =
            crate::proto::credit_horizon_monotone(self.credit_horizon, new_horizon);
        self.credit_horizon
    }

    /// Grant sliding-window credit so the horizon covers `acked_seq + window`.
    pub const fn grant_window(&mut self, window: u64) -> u64 {
        self.grant_credit(self.acked_seq.saturating_add(window))
    }
}

const ATTACH_WINDOW: usize = 16;
const MAX_PIPELINE_WINDOW: usize = 512;

/// Maximum total framed bytes accepted by one [`Client::send_fresh_pipelined`] call.
pub const MAX_FRESH_PIPELINE_BYTES: usize = 16 * 1024 * 1024;

/// A connection to a broker over a byte stream. Three transports:
///
/// - [`connect`](Client::connect) — a Unix socket, same machine, unsealed (the
///   kernel scopes who can reach the socket path).
/// - [`connect_tcp`](Client::connect_tcp) — PLAINTEXT TCP, multi-machine on a
///   trusted network only: no confidentiality, no peer authentication.
/// - `connect_tcp_sealed` (behind the `aead` feature) — TCP inside an
///   XChaCha20-Poly1305 sealed record layer under a pre-shared key: confidential
///   and authenticated across an untrusted network. `connect_tcp_handshake`
///   (`handshake`) and `connect_tcp_identity` (`identity`) put a forward-secret key
///   agreement in front of the same record layer.
///
/// `S` is the byte stream; any `Read + Write` works (see
/// [`from_stream`](Client::from_stream)), and the Frame protocol is identical on
/// every transport. A caller that picks the transport at RUNTIME uses the free
/// function [`connect`] instead: one [`AnyClient`] for every wire, plus the
/// [`Closer`] that ends it and bounds its I/O.
///
/// A request/reply client keeps itself IN STEP with its replies. A request that fails
/// part-way through its exchange — a write error, a read that timed out or hit EOF, a
/// reply that does not decode or is not the one the request is owed, a page longer
/// than it asked for — leaves the stream at an unknown point (a late reply may still
/// arrive), so the client latches: every later request on it fails at once with
/// `ErrorKind::BrokenPipe`, writing nothing, rather than reading the reply owed to
/// the request before it. Reconnect. A broker REFUSAL is a whole reply and leaves the
/// client in step ([`BrokerRefusal`]). A broker in ANOTHER protocol is neither: its
/// reply is a [`ProtocolMismatch`], and it latches the client like any other failure.
///
/// The client also keeps itself in step with the acks it OWES ITSELF. A pipelined
/// write ([`send_publish`](Client::send_publish), [`send_retire`](Client::send_retire),
/// [`send_commit`](Client::send_commit)) leaves its ack on the stream for a later
/// [`recv_publish_ack`](Client::recv_publish_ack) (or a
/// [`try_recv_publish_ack`](Client::try_recv_publish_ack), which does not wait for it),
/// and the broker answers a connection's requests in the order it read them, so the
/// next frame belongs to the oldest owed publish, not to whatever request is sent
/// after it. A request that reads its own reply — a blocking publish, a commit, a
/// fetch, a `Hello`, a subscribe: every verb but the pipelined ones — would take that
/// ack as its answer: a commit would return the publish's offset, a fetch would fail
/// on a reply of the wrong kind, and a REFUSED publish's `Error` would come back as
/// the later request's own refusal. So the client counts the acks owed
/// ([`owed_acks`](Client::owed_acks)) and, while any are, refuses every such request
/// with [`AcksOwed`], writing nothing and reading nothing: the connection stays in
/// step, and the request goes through once `recv_publish_ack` has read them all.
/// The three verbs that CONSUME the client — [`subscribe`](Client::subscribe),
/// [`subscribe_group`](Client::subscribe_group) and
/// [`fork_subscribe`](Client::fork_subscribe) — are refused the same way, with nothing
/// sent, but the client was moved into the call, so the refusal drops it: the
/// connection closes with the owed acks unread, and a will registered on it fires. A
/// caller that pipelines reads [`owed_acks`](Client::owed_acks) down to zero before it
/// subscribes.
#[cfg(unix)]
pub struct Client<S = UnixStream> {
    stream: S,
    /// Why this connection is out of step with its replies, once it is.
    lost: Option<String>,
    /// The log identity this connection's latest `Hello` answer carried.
    identity: Option<LogIdentity>,
    /// The extension block beside it (the served tier, the lineage).
    ext: NonceExt,
    /// When this client last wrote a request (or was made): what
    /// [`keepalive_if_idle`](Client::keepalive_if_idle) measures idleness from.
    sent_at: Instant,
    /// The broker answered a `Keepalive` as a verb it does not know.
    keepalive_unknown: bool,
    /// The durable head the newest `Mark` this connection read carried
    /// ([`seen_durable`](Client::seen_durable)).
    durable: Option<u64>,
    /// The oldest offset the newest page's `Mark` carried
    /// ([`seen_oldest`](Client::seen_oldest)).
    oldest: Option<u64>,
    /// Whether this connection asked for gap notices, and the broker took the ask
    /// ([`gap_notices`](Client::gap_notices)); `None`: not asked.
    told: Option<bool>,
    /// Whether this connection asked for broker-stamped wall times (`bt=`, R3) and the
    /// broker took the ask ([`broker_times`](Client::broker_times)); `None`: not asked.
    broker_times: Option<bool>,
    /// Whether this connection asked for each delivery's origin and the broker took the ask
    /// ([`origin_stamps`](Client::origin_stamps)).
    origins: bool,
    /// The origin of each record the newest page delivered, in order
    /// ([`page_origins`](Client::page_origins)).
    page_origins: Vec<Option<(u64, u64)>>,
    /// The gap notices the pages [`fetch`](Client::fetch) read carried since
    /// [`take_gaps`](Client::take_gaps) last took them, each with its fetch's filter, in the
    /// order read.
    gaps: Vec<(String, Gap)>,
    /// Pipelined publishes written whose acks have not been read
    /// ([`owed_acks`](Client::owed_acks)).
    owed: u64,
    /// What a [`try_recv_publish_ack`](Client::try_recv_publish_ack) read off the
    /// stream that no reply has used yet: the part of a frame that had arrived when the
    /// stream had no more to give, and whatever arrived with it. Empty until a try
    /// leaves something, and every reply is read through it while it is not
    /// ([`read_response`](Client::read_response)), so no byte read is dropped.
    rx: RecvBuf,
    /// How a try reads without waiting ([`Nowait`]).
    nowait: Nowait<S>,
    /// The negative control of the owed-ack guard: a client that does not refuse a
    /// request while acks are owed, as every client did before it. Only this module's
    /// own unit tests set it.
    #[cfg(test)]
    unguarded: bool,
    /// The negative controls of the try's two guarantees ([`TryMutant`]). Only this
    /// module's own unit tests set it.
    #[cfg(test)]
    try_mutant: TryMutant,
}

/// A connection to a broker over a byte stream. Windows twin: std has no
/// Unix-domain sockets there, so TCP (`connect_tcp`) is the default (and only)
/// transport.
#[cfg(not(unix))]
pub struct Client<S = TcpStream> {
    stream: S,
    /// Why this connection is out of step with its replies, once it is.
    lost: Option<String>,
    /// The log identity this connection's latest `Hello` answer carried.
    identity: Option<LogIdentity>,
    /// The extension block beside it (the served tier, the lineage).
    ext: NonceExt,
    /// When this client last wrote a request (or was made): what
    /// [`keepalive_if_idle`](Client::keepalive_if_idle) measures idleness from.
    sent_at: Instant,
    /// The broker answered a `Keepalive` as a verb it does not know.
    keepalive_unknown: bool,
    /// The durable head the newest `Mark` this connection read carried
    /// ([`seen_durable`](Client::seen_durable)).
    durable: Option<u64>,
    /// The oldest offset the newest page's `Mark` carried
    /// ([`seen_oldest`](Client::seen_oldest)).
    oldest: Option<u64>,
    /// Whether this connection asked for gap notices, and the broker took the ask
    /// ([`gap_notices`](Client::gap_notices)); `None`: not asked.
    told: Option<bool>,
    /// Whether this connection asked for broker-stamped wall times (`bt=`, R3) and the
    /// broker took the ask ([`broker_times`](Client::broker_times)); `None`: not asked.
    broker_times: Option<bool>,
    /// Whether this connection asked for each delivery's origin and the broker took the ask
    /// ([`origin_stamps`](Client::origin_stamps)).
    origins: bool,
    /// The origin of each record the newest page delivered, in order
    /// ([`page_origins`](Client::page_origins)).
    page_origins: Vec<Option<(u64, u64)>>,
    /// The gap notices the pages [`fetch`](Client::fetch) read carried since
    /// [`take_gaps`](Client::take_gaps) last took them, each with its fetch's filter, in the
    /// order read.
    gaps: Vec<(String, Gap)>,
    /// Pipelined publishes written whose acks have not been read
    /// ([`owed_acks`](Client::owed_acks)).
    owed: u64,
    /// What a try read that no reply has used yet (see the Unix definition).
    rx: RecvBuf,
    /// How a try reads without waiting ([`Nowait`]).
    nowait: Nowait<S>,
    /// The negative control of the owed-ack guard (see the Unix definition).
    #[cfg(test)]
    unguarded: bool,
    /// The negative controls of the try's two guarantees (see the Unix definition).
    #[cfg(test)]
    try_mutant: TryMutant,
}

/// How a client puts the socket under its stream into the mode a
/// [`try_recv_publish_ack`](Client::try_recv_publish_ack) reads in — NON-BLOCKING, so a
/// read with nothing to give answers at once — and back out of it. Every other verb
/// reads and writes the stream blocking, as every constructor here leaves it.
enum Nowait<S> {
    /// A stream handed to [`Client::from_stream`]: the client cannot reach a socket
    /// under it, so a try reads as the stream reads, and a read that answers
    /// `WouldBlock` or `TimedOut` is "not yet".
    AsIs,
    /// The stream IS the socket, or wraps it and lends it out: [`Client::connect`], the
    /// TCP constructors, and the sealed ones (through the record layer's `get_ref`).
    /// Here and under [`Socket`](Nowait::Socket) only `WouldBlock` is "not yet"
    /// ([`not_yet`](Nowait::not_yet)).
    Stream(fn(&S, bool) -> io::Result<()>),
    /// The stream was erased behind [`AnyStream`] by [`connect`]: the duplicate of its
    /// socket the [`Closer`] holds, shared. Blocking or not is a property of the socket
    /// (the open file description a duplicate shares), not of one descriptor, so what
    /// is set through it is what the stream's own reads see — as the closer's timeouts
    /// are.
    Socket(Arc<Socket>),
}

impl<S> Nowait<S> {
    /// Whether the error a try's read stopped on is "not yet" — the stream had nothing
    /// more to give — rather than a failure. `WouldBlock` always is: a non-blocking
    /// socket's, or (Unix) a read timeout's. `TimedOut` is only where a read TIMEOUT
    /// can have fired, a stream read as it is ([`AsIs`](Nowait::AsIs); Windows reports
    /// a read timeout so). A read on a socket the client put in non-blocking mode
    /// ITSELF has no timeout to fire, so `TimedOut` there is the connection's own
    /// `ETIMEDOUT` (`WSAETIMEDOUT`): retransmission or keepalive gave up on the peer.
    /// Taken for "not yet", it would leave the client owing acks a dead connection will
    /// never bring, and cost the caller the cause, which the read just consumed (the
    /// next one reads a plain close); as a failure it latches the client with it.
    fn not_yet(&self, e: &io::Error) -> bool {
        match self {
            Nowait::AsIs => is_not_yet(e),
            Nowait::Stream(_) | Nowait::Socket(_) => e.kind() == io::ErrorKind::WouldBlock,
        }
    }
}

/// Which of a try's two guarantees a unit test switches off, to show it is what its
/// test rests on: [`Torn`](TryMutant::Torn) reads with `proto::read_frame`, which drops
/// the bytes of a frame it had only part of when the read stopped (what a try built on
/// the blocking read would do); [`KeepsNowait`](TryMutant::KeepsNowait) leaves the
/// socket non-blocking after the try, so the next blocking read cannot wait.
#[cfg(test)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
enum TryMutant {
    #[default]
    Off,
    Torn,
    KeepsNowait,
}

#[cfg(unix)]
impl Client<UnixStream> {
    /// Connect to the broker's Unix socket at `socket_path` (same machine,
    /// unsealed — reachability is scoped by the socket path's permissions).
    pub fn connect(socket_path: impl AsRef<Path>) -> io::Result<Client<UnixStream>> {
        let stream = UnixStream::connect(socket_path)?;
        kept_from_children(&stream)?;
        Ok(Client::from_stream(stream).nowait_by(UnixStream::set_nonblocking))
    }
}

impl Client<TcpStream> {
    /// Connect to the broker over PLAINTEXT TCP: multi-machine, but for a trusted
    /// network only — the bytes are neither encrypted nor authenticated. For an
    /// untrusted network use `connect_tcp_sealed` (the `aead` feature), which
    /// carries the same protocol inside an authenticated-encryption record layer.
    pub fn connect_tcp(addr: impl ToSocketAddrs) -> io::Result<Client<TcpStream>> {
        Ok(Client::from_stream(dial_tcp(addr, None)?).nowait_by(TcpStream::set_nonblocking))
    }

    /// [`connect_tcp`](Self::connect_tcp) with a bound on the CONNECT: each address
    /// `addr` resolves to is tried in turn with `TcpStream::connect_timeout`, so a
    /// black-holed address fails `TimedOut` after `timeout` instead of after the OS's
    /// SYN-retry schedule (minutes). The bound is per address, so the worst case is
    /// `timeout` × addresses; the error is the LAST address's. Name resolution itself
    /// is not bounded (std's resolver has no timeout) — an IP-literal `addr` makes
    /// this a hard bound. The stream comes back blocking: this bounds the connect,
    /// not the requests (see [`Closer`] for those).
    ///
    /// # Errors
    /// Every address failed (the last one's error), `addr` resolved to nothing
    /// (`InvalidInput`), or a zero `timeout` (`InvalidInput`, std's own refusal).
    pub fn connect_tcp_timeout(
        addr: impl ToSocketAddrs,
        timeout: Duration,
    ) -> io::Result<Client<TcpStream>> {
        Ok(Client::from_stream(dial_tcp(addr, Some(timeout))?)
            .nowait_by(TcpStream::set_nonblocking))
    }
}

/// Dial TCP with `TCP_NODELAY` — every request is one small frame that waits for its
/// answer, so Nagle only adds latency. `None` is `TcpStream::connect` exactly (each
/// resolved address under the OS's own connect timeout); `Some(t)` tries each
/// resolved address with `TcpStream::connect_timeout(addr, t)` and answers the first
/// that connects, else the last error.
fn dial_tcp(addr: impl ToSocketAddrs, timeout: Option<Duration>) -> io::Result<TcpStream> {
    let stream = match timeout {
        None => TcpStream::connect(addr)?,
        Some(t) => {
            let mut last = None;
            let mut connected = None;
            for a in addr.to_socket_addrs()? {
                match TcpStream::connect_timeout(&a, t) {
                    Ok(s) => {
                        connected = Some(s);
                        break;
                    }
                    Err(e) => last = Some(e),
                }
            }
            match (connected, last) {
                (Some(s), _) => s,
                (None, Some(e)) => return Err(e),
                (None, None) => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "could not resolve to any addresses",
                    ))
                }
            }
        }
    };
    stream.set_nodelay(true)?;
    kept_from_children(&stream)?;
    Ok(stream)
}

/// Request close-on-fork for every socket the broker creates, accepts or duplicates.
/// Kernels that ignore the request retain the existing close-on-exec behavior;
/// this best-effort request does not establish pre-exec descriptor isolation there.
///
/// # Errors
/// The `fcntl(2)` errno of reading or setting the descriptor's flags.
#[cfg(unix)]
pub(crate) fn kept_from_children(socket: &impl std::os::fd::AsFd) -> io::Result<()> {
    astream_sys::close_on_fork(socket.as_fd()).map(|_| ())
}

/// Off Unix there is no `fork`, so no child is ever given a copy (see the Unix twin).
#[cfg(not(unix))]
pub(crate) fn kept_from_children<S>(_socket: &S) -> io::Result<()> {
    Ok(())
}

/// How long the broker may take to complete the SEALED handshake when the caller gave
/// no connect timeout; lifted after it.
#[cfg(feature = "aead")]
const SEALED_HANDSHAKE_TIMEOUT: Duration = Duration::from_secs(5);

/// Run the client half of the sealed handshake over an already-dialed socket, each
/// read bounded by `deadline` so an unresponsive peer cannot hang the connect; the
/// socket is blocking again afterwards.
#[cfg(feature = "aead")]
fn seal_tcp(
    stream: TcpStream,
    key: [u8; astream_aead::KEY_LEN],
    deadline: Duration,
) -> io::Result<astream_aead::SealedStream<TcpStream>> {
    stream.set_read_timeout(Some(deadline))?;
    let stream = astream_aead::SealedStream::handshake_client(stream, key)?;
    stream.get_ref().set_read_timeout(None)?;
    Ok(stream)
}

/// How long the Rung-7 key agreement may take when the caller gave no connect
/// timeout; lifted after it.
#[cfg(feature = "handshake")]
const KEY_AGREEMENT_TIMEOUT: Duration = Duration::from_secs(10);

/// Run the client half of the Rung-7 forward-secret handshake over an already-dialed
/// socket. Its reads AND writes are bounded by `deadline`, so a broken or hostile
/// server cannot hang the client on the key-agreement I/O; reset to blocking after.
#[cfg(feature = "handshake")]
fn agree_tcp(
    stream: TcpStream,
    psk: &[u8; astream_aead::KEY_LEN],
    deadline: Duration,
) -> io::Result<astream_aead::SealedStream<TcpStream>> {
    stream.set_read_timeout(Some(deadline))?;
    stream.set_write_timeout(Some(deadline))?;
    let sealed = astream_aead::client_handshake(stream, psk)?;
    sealed.get_ref().set_read_timeout(None)?;
    sealed.get_ref().set_write_timeout(None)?;
    Ok(sealed)
}

/// Put the TCP socket under a sealed stream into, or out of, non-blocking mode — for
/// a [`Client::try_recv_publish_ack`]. The record layer keeps a record that has only
/// partly arrived across a read that answers `WouldBlock`, and the plaintext of one it
/// has opened and not yet handed out, so a try over it loses nothing either.
#[cfg(feature = "aead")]
fn sealed_nonblocking(s: &astream_aead::SealedStream<TcpStream>, on: bool) -> io::Result<()> {
    s.get_ref().set_nonblocking(on)
}

#[cfg(feature = "aead")]
impl Client<astream_aead::SealedStream<TcpStream>> {
    /// Connect to a broker served by [`serve_tcp_sealed`](crate::Broker::serve_tcp_sealed)
    /// over an XChaCha20-Poly1305-sealed transport under the pre-shared `key`. Runs
    /// the sealed handshake before returning — a fresh hello from each side, bound
    /// with the direction and the record sequence into every record's AAD, and a
    /// key-confirming record each way — so a broker that lacks the key is refused
    /// HERE (the connect fails; nothing but an empty confirm was sent under the
    /// key), and a record recorded from any other connection or direction cannot
    /// be replayed into this one. The Frame protocol is unchanged; it just rides
    /// inside an encrypted, ordered record layer. The handshake has a deadline, so
    /// an unresponsive peer cannot hang the connect.
    pub fn connect_tcp_sealed(
        addr: impl ToSocketAddrs,
        key: [u8; astream_aead::KEY_LEN],
    ) -> io::Result<Client<astream_aead::SealedStream<TcpStream>>> {
        let stream = seal_tcp(dial_tcp(addr, None)?, key, SEALED_HANDSHAKE_TIMEOUT)?;
        Ok(Client::from_stream(stream).nowait_by(sealed_nonblocking))
    }
}

#[cfg(feature = "handshake")]
impl Client<astream_aead::SealedStream<TcpStream>> {
    /// Connect to a broker served by [`serve_tcp_handshake`](crate::Broker::serve_tcp_handshake),
    /// running the Rung-7 forward-secret handshake (ephemeral X25519 authenticated
    /// by the pre-shared `psk`) before the Frame protocol. Each connection derives a
    /// fresh session key, so a later `psk` compromise cannot decrypt this session's
    /// recorded traffic. A wrong `psk`, or a peer not speaking the handshake, fails
    /// the connect.
    pub fn connect_tcp_handshake(
        addr: impl ToSocketAddrs,
        psk: [u8; astream_aead::KEY_LEN],
    ) -> io::Result<Client<astream_aead::SealedStream<TcpStream>>> {
        let sealed = agree_tcp(dial_tcp(addr, None)?, &psk, KEY_AGREEMENT_TIMEOUT)?;
        Ok(Client::from_stream(sealed).nowait_by(sealed_nonblocking))
    }
}

#[cfg(feature = "handshake")]
impl Client<astream_aead::RoamStream> {
    /// Connect to a broker served by [`serve_udp_roaming`](crate::Broker::serve_udp_roaming)
    /// over forward-secret AEAD-over-UDP (`AROM` v1) under `psk`, returning both the
    /// connected [`Client`] and its [`RoamHandle`](astream_aead::RoamHandle) migration
    /// controller.
    ///
    /// Calling [`RoamHandle::migrate`](astream_aead::RoamHandle::migrate) or
    /// [`RoamHandle::migrate_socket`](astream_aead::RoamHandle::migrate_socket) switches
    /// the underlying [`std::net::UdpSocket`] (local IP/port) with RFC 9000 §8.2
    /// `PATH_CHALLENGE` / `PATH_RESPONSE` validation while preserving live
    /// [`Subscription`]s, pipelined publishes, attached capabilities, and registered
    /// Last Wills with zero gap and zero reconnect.
    pub fn connect_udp_roaming(
        addr: impl ToSocketAddrs,
        psk: [u8; astream_aead::KEY_LEN],
    ) -> io::Result<(Client<astream_aead::RoamStream>, astream_aead::RoamHandle)> {
        let (roam_stream, roam_handle) = astream_aead::client_roam_connect(addr, &psk)?;
        let client =
            Client::from_stream(roam_stream).nowait_by(astream_aead::RoamStream::set_nonblocking);
        Ok((client, roam_handle))
    }
}

#[cfg(feature = "identity")]
impl Client<astream_aead::SealedStream<TcpStream>> {
    /// Connect to a broker served by [`serve_tcp_identity`](crate::Broker::serve_tcp_identity)
    /// with **static public-key identity, no shared secret** (Rung 8). Runs a
    /// mutual signed-DH (SIGMA/Ed25519) handshake: the broker must present exactly
    /// `expected_server` (its pinned host key), and we prove our own `identity`
    /// (which the broker must have allow-listed). The session key comes from the
    /// ephemeral DH alone (forward-secret under identity-key compromise). A wrong
    /// host key, an unauthorized identity, or a bad signature fails the connect.
    pub fn connect_tcp_identity(
        addr: impl ToSocketAddrs,
        identity: astream_aead::IdentityKeypair,
        expected_server: [u8; astream_aead::ID_PUB_LEN],
    ) -> io::Result<Client<astream_aead::SealedStream<TcpStream>>> {
        let stream = TcpStream::connect(addr)?;
        stream.set_nodelay(true)?;
        let hs_timeout = std::time::Duration::from_secs(10);
        stream.set_read_timeout(Some(hs_timeout))?;
        stream.set_write_timeout(Some(hs_timeout))?;
        let sealed = astream_aead::client_identity_handshake(stream, &identity, &expected_server)?;
        sealed.get_ref().set_read_timeout(None)?;
        sealed.get_ref().set_write_timeout(None)?;
        Ok(Client::from_stream(sealed).nowait_by(sealed_nonblocking))
    }

    /// Connect to a broker served by [`serve_tcp_certified`](crate::Broker::serve_tcp_certified)
    /// using an external-authority `ACRT` certificate and an [`IdentitySigner`](astream_aead::IdentitySigner)
    /// (in-memory [`IdentityKeypair`](astream_aead::IdentityKeypair) or out-of-process
    /// [`SshAgentSigner`](astream_aead::SshAgentSigner) over `SSH_AUTH_SOCK`, Rung 9).
    ///
    /// Verifies the server's `CertRole::Host` certificate against `server_trust` (and
    /// `expected_host_principal` when `Some`) before transmitting `client_cert`, and keys
    /// the resulting [`SealedStream`](astream_aead::SealedStream) solely from ephemeral X25519.
    pub fn connect_tcp_certified(
        addr: impl ToSocketAddrs,
        client_signer: astream_aead::IdentitySigner,
        client_cert: astream_aead::IdentityCertificate,
        server_trust: &astream_aead::CertTrustStore,
        expected_host_principal: Option<&str>,
    ) -> io::Result<Client<astream_aead::SealedStream<TcpStream>>> {
        let (client, _) = Self::connect_tcp_certified_verified(
            addr,
            client_signer,
            client_cert,
            server_trust,
            expected_host_principal,
        )?;
        Ok(client)
    }

    /// Like [`Self::connect_tcp_certified`], returning both the connected [`Client`] and the
    /// verified broker host certificate metadata ([`VerifiedPeerCert`](astream_aead::VerifiedPeerCert)).
    pub fn connect_tcp_certified_verified(
        addr: impl ToSocketAddrs,
        client_signer: astream_aead::IdentitySigner,
        client_cert: astream_aead::IdentityCertificate,
        server_trust: &astream_aead::CertTrustStore,
        expected_host_principal: Option<&str>,
    ) -> io::Result<(
        Client<astream_aead::SealedStream<TcpStream>>,
        astream_aead::VerifiedPeerCert,
    )> {
        let now_ms = match std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH) {
            Ok(d) => u64::try_from(d.as_millis()).unwrap_or(u64::MAX),
            Err(_) => 0,
        };
        let stream = dial_tcp(addr, None)?;
        let hs_timeout = KEY_AGREEMENT_TIMEOUT;
        stream.set_read_timeout(Some(hs_timeout))?;
        stream.set_write_timeout(Some(hs_timeout))?;
        let (sealed, verified_host) = astream_aead::client_cert_handshake(
            stream,
            &client_signer,
            &client_cert,
            server_trust,
            expected_host_principal,
            now_ms,
        )?;
        sealed.get_ref().set_read_timeout(None)?;
        sealed.get_ref().set_write_timeout(None)?;
        Ok((
            Client::from_stream(sealed).nowait_by(sealed_nonblocking),
            verified_host,
        ))
    }
}

impl<S: Read + Write> Client<S> {
    /// Wrap an already-connected byte stream (any `Read + Write`, e.g. a boxed
    /// `dyn` stream chosen at runtime) as a client. The caller has already done
    /// whatever transport setup (nodelay, sealing) the stream needs; this is the
    /// inverse of [`into_stream`](Self::into_stream).
    pub fn from_stream(stream: S) -> Client<S> {
        Client {
            stream,
            lost: None,
            identity: None,
            ext: NonceExt::default(),
            sent_at: Instant::now(),
            keepalive_unknown: false,
            durable: None,
            oldest: None,
            told: None,
            broker_times: None,
            origins: false,
            page_origins: Vec::new(),
            gaps: Vec::new(),
            owed: 0,
            rx: RecvBuf::default(),
            nowait: Nowait::AsIs,
            #[cfg(test)]
            unguarded: false,
            #[cfg(test)]
            try_mutant: TryMutant::Off,
        }
    }

    /// This client, told how to put its stream's socket into and out of non-blocking
    /// mode for a [`try_recv_publish_ack`](Self::try_recv_publish_ack): what every
    /// constructor that knows its socket says, and [`from_stream`](Self::from_stream)
    /// cannot ([`Nowait`]).
    fn nowait_by(mut self, set: fn(&S, bool) -> io::Result<()>) -> Client<S> {
        self.nowait = Nowait::Stream(set);
        self
    }

    /// Give the underlying byte stream back (e.g. to box it behind a `dyn` trait so
    /// one code path serves every transport). The connection stays open. A client
    /// that was out of step hands back a stream that still is. Read the acks the client
    /// owes itself ([`owed_acks`](Self::owed_acks)) before giving the stream up, for
    /// nothing is left to count them, and they may not even be on the stream any more:
    /// - a client that never tried hands back a stream they will still arrive on,
    ///   first;
    /// - but whatever the client has READ AHEAD goes with it and is dropped. A
    ///   [`try_recv_publish_ack`](Self::try_recv_publish_ack) reads all the stream has
    ///   to give, whole acks it has not returned yet as well as part of the next, and a
    ///   reply read after a try reads through what it left. So the stream handed back
    ///   can start mid-frame, or past acks that are owed and were already read off it.
    pub fn into_stream(self) -> S {
        self.stream
    }

    /// How many pipelined acks this connection owes itself: publishes, retires and
    /// commits written by [`send_publish`](Self::send_publish),
    /// [`send_retire`](Self::send_retire) and [`send_commit`](Self::send_commit) whose
    /// acks [`recv_publish_ack`](Self::recv_publish_ack) (or
    /// [`try_recv_publish_ack`](Self::try_recv_publish_ack)) has not read yet. While it
    /// is above zero every request that reads its own reply is refused with
    /// [`AcksOwed`] (see [`Client`]).
    ///
    /// A latched client owes NOTHING, so this is zero once any failure has put the
    /// client out of step: a pipelined write that failed is not counted, and a read
    /// that fails part-way through the acks (a close, a timeout, a reply that does not
    /// decode or is not an ack) zeroes what was left, because nothing is read on the
    /// connection again and no ack still on the way can be paid. What those publishes
    /// did is then unknown; re-sending them under the same producer id dedups the ones
    /// that landed. So a loop that reads acks while this is above zero ends, on the
    /// failure, rather than spinning on `BrokenPipe`.
    pub const fn owed_acks(&self) -> u64 {
        self.owed
    }

    /// Ask the broker for this connection's NONCE — the value an [`attach`](Self::attach)
    /// proof is computed over. Answered by a guarded and an unguarded broker alike, so
    /// one client works against either. The log identity the answer carries is kept
    /// ([`seen_log_identity`](Self::seen_log_identity)).
    ///
    /// The broker answers a `Hello` after the connection's pending acks, so while
    /// pipelined acks are owed ([`owed_acks`](Self::owed_acks)) it is refused with
    /// [`AcksOwed`] and nothing is sent — and so are [`hello_identity`](Self::hello_identity),
    /// [`log_identity`](Self::log_identity), the attaches, and every other request that
    /// reads its own reply ([`Client`]).
    pub fn hello(&mut self) -> io::Result<[u8; 32]> {
        let (nonce, _) = self.hello_identity()?;
        Ok(nonce)
    }

    /// [`hello`](Self::hello), returning beside the nonce the [`LogIdentity`] of the
    /// log the broker serves — `None` from a broker that predates log identity. Kept,
    /// like `hello`'s, as [`seen_log_identity`](Self::seen_log_identity).
    pub fn hello_identity(&mut self) -> io::Result<([u8; 32], Option<LogIdentity>)> {
        self.send(&Request::Hello)?;
        match self.read_response()? {
            Response::Nonce { nonce, log, ext } => match nonce.as_slice().try_into() {
                Ok(nonce) => {
                    self.identity = log;
                    self.ext = ext;
                    Ok((nonce, log))
                }
                Err(_) => Err(self.lose(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("broker nonce is {} bytes, expected 32", nonce.len()),
                ))),
            },
            other => Err(self.reply_error(other)),
        }
    }

    /// The [`LogIdentity`] of the log the broker serves NOW: one `Hello` round trip.
    /// `Ok(None)` is a broker that predates log identity, which says nothing either
    /// way.
    ///
    /// Check it before using any offset persisted from an EARLIER connection — a
    /// delivered-up-to watermark, a cursor, an offset already answered. If it is not
    /// the identity that offset was read under (a different `id` OR `generation`),
    /// the offset names nothing in this log: drop it and start over from this log, as
    /// a first run would (the [`LogIdentity`] docs say how). The broker's own consumer
    /// groups need no such check: their cursors live inside the log.
    ///
    /// It IS a `Hello`: the connection's nonce is replaced, so an attach proof
    /// computed over an earlier one no longer verifies ([`attach`](Self::attach) and
    /// [`attach_all`](Self::attach_all) fetch their own).
    pub fn log_identity(&mut self) -> io::Result<Option<LogIdentity>> {
        let (_, log) = self.hello_identity()?;
        Ok(log)
    }

    /// The [`LogIdentity`] this connection's latest `Hello` answer carried — the one
    /// [`attach`](Self::attach) and [`attach_all`](Self::attach_all) send — so a client
    /// that attached learns it with no further round trip. `None` before any `Hello`
    /// on this connection, or from a broker that predates log identity
    /// ([`log_identity`](Self::log_identity) asks). A connection to a REPLICA can see
    /// it change, when the replica adopts its leader's: ask again for the current one.
    pub const fn seen_log_identity(&self) -> Option<LogIdentity> {
        self.identity
    }

    /// The [`Lineage`] the latest `Hello` answer carried beside the identity: where the
    /// log's generations agree, so offsets kept under an earlier generation resume at
    /// [`LogIdentity::continues`] instead of being forgotten. `None` before any
    /// `Hello`, or from a broker that predates lineage (which says nothing either way:
    /// forget, as before).
    pub const fn log_lineage(&self) -> Option<&Lineage> {
        self.ext.lineage.as_ref()
    }

    /// The tier the broker serves, as the latest `Hello` answer told it
    /// ([`ServedInfo`]) — read from the broker itself, so a status line never infers it
    /// from how the broker was started. `None` before any `Hello`, or from a broker that
    /// predates the extension block.
    pub const fn served_durability(&self) -> Option<ServedInfo> {
        self.ext.durability
    }

    /// Whether the latest `Hello` answer announced support for the conditional
    /// [`Request::Retire`] verb (`DESIGN-aterm-fabric` §5.2).
    /// `false` before any `Hello`, or against an older broker that predates the verb.
    pub const fn supports_retire(&self) -> bool {
        self.ext.supports_retire()
    }

    /// Whether the latest `Hello` answer announced [`Request::GapNotices`]: a tail on this
    /// broker can be told what retention gave up below it ([`gap_notices`](Self::gap_notices)).
    /// `false` before any `Hello`, or against an older broker that predates the verb.
    pub const fn supports_gap_notices(&self) -> bool {
        self.ext.supports_gap_notices()
    }

    /// Whether the latest `Hello` answer announced TOLD FETCHES
    /// ([`REQUEST_TOLD_FETCH`](crate::proto::REQUEST_TOLD_FETCH)): on this broker a fetch on
    /// a connection that asked for gap notices reads what retention still holds below its
    /// filter's oldest ([`fetch_told`](Self::fetch_told)), so its `retained-from=` there says
    /// the filter holds none of it. `false` before any `Hello`, or against a broker that
    /// predates it: one that tells tails only refuses such a fetch with the rest, whatever
    /// it still holds below the oldest.
    pub const fn supports_told_fetch(&self) -> bool {
        self.ext.supports_told_fetch()
    }

    /// Whether the latest `Hello` answer announced [`Request::BrokerTimes`]
    /// (`REQUIREMENTS` R3): this broker stamps `bt=<unix ms>` at append and appends a
    /// 9-byte `[BT_TAG, bt_ms BE]` trailer to `Delivery` frames on connections that ask
    /// ([`broker_times`](Self::broker_times)).
    pub const fn supports_broker_times(&self) -> bool {
        self.ext.supports_broker_times()
    }

    /// Whether the latest `Hello` answer announced [`Request::Stats`]
    /// (`REQUIREMENTS` R5): this broker serves operational fleet statistics over the wire
    /// ([`stats`](Self::stats)).
    pub const fn supports_stats(&self) -> bool {
        self.ext.supports_stats()
    }

    /// Whether the latest `Hello` answer announced that this broker GAP-FENCES each
    /// producer's writes on a connection that asks ([`fence_gaps`](Self::fence_gaps),
    /// [`REQUEST_GAP_FENCES`](crate::REQUEST_GAP_FENCES)): once one is refused, every later
    /// one of that producer sent on this connection above the refused sequence is refused
    /// `gap-fenced=<seq>` in send order, until a write at or under it commits, the connection
    /// closes, or [`clear_gap_fences`](Self::clear_gap_fences) lifts them. So a producer that
    /// asked may keep several writes in flight whose order must hold on the log: a refused
    /// one lets nothing sent after it land. `false` before any `Hello`, against a broker
    /// opened without `OpenOptions::sticky_batch_refusal` (where a refused batch is rolled
    /// back and the next write lands), and against one that predates it.
    pub const fn supports_gap_fences(&self) -> bool {
        self.ext.supports_gap_fences()
    }

    /// Whether the latest `Hello` answer announced [`Request::Settle`]
    /// ([`REQUEST_SETTLE`](crate::REQUEST_SETTLE)): a full flush issued after the broker read
    /// the request, never skipped ([`send_settle`](Self::send_settle)). `false` before any
    /// `Hello`, or against a broker that predates it.
    pub const fn supports_settle(&self) -> bool {
        self.ext.supports_settle()
    }

    /// Whether the latest `Hello` offered [`Request::FreshPublish`] and its mandatory fence.
    /// False before `Hello` and against a broker that predates the request.
    pub const fn supports_fresh_publish(&self) -> bool {
        self.ext.supports_fresh_publish()
    }

    /// The device the broker's log file is on and whether its full flush drains it, as the
    /// latest `Hello` answer told it ([`LogDevice`](crate::LogDevice)). `None` before any
    /// `Hello`, from a broker that predates the entry, or from one that could not read its
    /// file's device: a writer then settles its own writes by a flush of its own.
    pub const fn log_device(&self) -> Option<crate::LogDevice> {
        self.ext.device
    }

    /// The log's health as the latest `Hello` answer told it
    /// ([`HelloHealth`](crate::HelloHealth)): whether it is POISONED — it refuses every
    /// write until it is reopened — and why, and the flushes it has issued since it
    /// opened. Read from the broker itself, so a status line never calls a broker whose
    /// log takes no write `connected`. `None` before any `Hello`, or from a broker that
    /// predates the entry. A fresh `Hello` ([`log_identity`](Self::log_identity)) asks
    /// again.
    pub const fn broker_health(&self) -> Option<&crate::proto::HelloHealth> {
        self.ext.health.as_ref()
    }

    /// The broker's DURABLE head as the newest `Mark` this connection read told it —
    /// every record below it is on stable media by a full flush. `None` before any
    /// `Mark` (an `Attach`'s, a `Fetch`'s or a `Last` page's), or from a broker that
    /// predates the field. To ask about an offset now, a `Fetch` head query (`max = 0`)
    /// answers with a fresh `Mark`.
    pub const fn seen_durable(&self) -> Option<u64> {
        self.durable
    }

    /// The OLDEST offset of the newest `Fetch`'s filter, as its `Mark` told it
    /// (`REQUIREMENTS` R4): the offset at and above which the filter is complete, every
    /// record of it retention still wants readable and none given up. The log's base, or
    /// for what a hold rule keeps records of, the greatest floor of the subjects it
    /// matches: so not the lowest record a read of it can reach, since of a filter whose
    /// subjects have different floors some can still hold records below it
    /// ([`fetch_told`](Self::fetch_told) reads them). `None` before any page, after a
    /// `Last` page (whose `Mark` carries none), or from a broker that predates it.
    pub const fn seen_oldest(&self) -> Option<u64> {
        self.oldest
    }

    /// THE `HEAD`-STYLE QUERY that answers `oldest=` (`REQUIREMENTS` R4): a head query
    /// (`Fetch` with `max = 0`, never refused) on `filter`, and the oldest offset its
    /// `Mark` says the filter is complete from ([`seen_oldest`](Self::seen_oldest)),
    /// beside the visible head. `None` for the oldest from a broker that predates it.
    /// Refused with [`AcksOwed`], sending nothing, while pipelined acks are owed, as every
    /// `fetch` is.
    pub fn oldest(&mut self, filter: &str) -> io::Result<(Option<u64>, u64)> {
        let (_, (_, head)) = self.fetch(0, filter, 0)?;
        Ok((self.oldest, head))
    }

    /// The RETENTION RULES the broker retains its log by, as the latest `Hello` answer
    /// advertised them. `None` before any `Hello`, from a broker that retains by none,
    /// or from one that predates them.
    #[cfg(feature = "retention")]
    #[must_use]
    pub fn retention_rules(&self) -> Option<crate::Retention> {
        self.ext.retention_rules()
    }

    /// Keep what a `Mark` said about durability (an older broker's says nothing, which
    /// leaves the last word standing).
    const fn saw_durable(&mut self, durable: Option<u64>) {
        if durable.is_some() {
            self.durable = durable;
        }
    }

    /// Add a grant to this connection's keyring by presenting a PROOF the caller has
    /// already computed over the nonce from [`hello`](Self::hello) — the primitive
    /// under [`attach`](Self::attach), for a caller that holds its tag somewhere this
    /// process cannot reach it (an agent, a signer). Blocks for the acknowledgement
    /// and returns its `(next, head)`; a refused attach is an error HERE, not a
    /// surprise at the next request.
    pub fn attach_with_proof(&mut self, grant: &str, proof: &[u8]) -> io::Result<(u64, u64)> {
        self.send(&Request::Attach {
            grant: grant.to_string(),
            proof: proof.to_vec(),
        })?;
        self.read_mark()
    }

    /// Add the capability `grant`/`tag` to this connection's keyring: `Hello` for the
    /// connection's nonce, then `Attach` carrying `HMAC-SHA256(tag, nonce ‖ grant)` —
    /// a PROOF OF POSSESSION, so the tag never crosses the wire and a captured attach
    /// cannot be replayed onto another connection. Blocks for the acknowledgement and
    /// returns its `(next, head)`. [`attach_all`](Self::attach_all) with one grant.
    ///
    /// `Attach` APPENDS: several narrow grants on one connection are the intended
    /// shape (read one subtree, commit under another, publish as a bound principal in
    /// a third), and each request is authorized existentially over the ring. A
    /// repeated grant string replaces rather than growing it. A connection that holds
    /// several grants attaches them with [`attach_all`](Self::attach_all), which pays
    /// one `Hello` for the lot.
    ///
    /// # Errors
    /// The socket errors, or the broker refuses the attach (a proof that does not
    /// verify, a producer-id collision in the binding table, or a full keyring).
    pub fn attach(&mut self, grant: &str, tag: &[u8]) -> io::Result<(u64, u64)> {
        match self.attach_all([(grant, tag)])? {
            Some(mark) => Ok(mark),
            None => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "no attach was acknowledged",
            )),
        }
    }

    /// Add every capability in `ring` — `(grant, tag)` pairs, in order — to this
    /// connection's keyring in TWO round trips however many there are: ONE `Hello`
    /// (the broker keeps a connection's nonce until the next `Hello`, and verifies any
    /// number of `Attach`es against it), then every `Attach` pipelined, at most
    /// [`ATTACH_WINDOW`](Self::ATTACH_WINDOW) in flight, each acknowledged in order.
    /// Returns the LAST acknowledgement's `(next, head)`; `None` for an empty ring,
    /// which sends nothing at all (an unguarded setup with no capability files).
    ///
    /// A REFUSED grant stops the sending: the attaches already in flight are still
    /// answered and read — so the connection stays in step for the next request —
    /// and the FIRST refusal is returned ([`BrokerRefusal`] inside, in ring order).
    /// Each grant is decided on its own: on an `Err` the connection holds the grants
    /// ahead of the refused one, and perhaps some that were in flight behind it, so a
    /// caller that needs the whole ring drops the connection.
    ///
    /// # Errors
    /// A tag that is not 32 bytes (`InvalidInput`, before anything is sent); the
    /// socket; or the broker's first refusal.
    #[cfg(feature = "cap")]
    pub fn attach_all<'a>(
        &mut self,
        ring: impl IntoIterator<Item = (&'a str, &'a [u8])>,
    ) -> io::Result<Option<(u64, u64)>> {
        let mut parsed_ring = Vec::new();
        for (grant, tag) in ring {
            let Ok(tag_arr): Result<[u8; 32], _> = tag.try_into() else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("capability tag is {} bytes, expected 32", tag.len()),
                ));
            };
            parsed_ring.push((grant, tag_arr));
        }
        let ring = parsed_ring;
        if ring.is_empty() {
            return Ok(None);
        }
        let nonce = self.hello()?;
        let mut mark = None;
        let mut sent = 0usize;
        let mut received = 0usize;
        let mut failure: Option<io::Error> = None;
        loop {
            while failure.is_none()
                && sent < ring.len()
                && sent.saturating_sub(received) < ATTACH_WINDOW
            {
                let (grant, tag) = &ring[sent];
                let proof = astream_cap::attach_proof(tag, &nonce, grant);
                match self.send(&Request::Attach {
                    grant: grant.to_string(),
                    proof: proof.to_vec(),
                }) {
                    Ok(()) => sent = sent.saturating_add(1),
                    Err(e) => failure = Some(e),
                }
            }
            if received == sent {
                break;
            }
            received = received.saturating_add(1);
            match self.read_mark() {
                Ok(m) => mark = Some(m),
                Err(e) if broker_refusal(&e).is_some() => {
                    failure.get_or_insert(e);
                }
                // A transport failure: the client is out of step now, and says so.
                Err(e) => return Err(failure.unwrap_or(e)),
            }
        }
        match failure {
            Some(e) => Err(e),
            None => Ok(mark),
        }
    }

    /// Without the `cap` feature there is no way to compute an attach PROOF: the tag
    /// stays on the client and the wire carries `HMAC-SHA256(tag, nonce ‖ grant)`
    /// instead, which needs the same vetted MAC a guarded broker uses. Build with
    /// `cap` (or compute the proof yourself and call
    /// [`attach_with_proof`](Self::attach_with_proof)). An EMPTY ring needs no proof:
    /// it is `Ok(None)`, as with `cap`, and sends nothing.
    #[cfg(not(feature = "cap"))]
    pub fn attach_all<'a>(
        &mut self,
        ring: impl IntoIterator<Item = (&'a str, &'a [u8])>,
    ) -> io::Result<Option<(u64, u64)>> {
        if ring.into_iter().next().is_none() {
            return Ok(None);
        }
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "presenting a capability needs the `cap` feature: an Attach carries a proof of \
             possession (HMAC-SHA256 over the broker's per-connection nonce), never the tag, \
             so the client must be able to compute that MAC",
        ))
    }

    /// The most `Attach`es [`attach_all`](Self::attach_all) keeps in flight before
    /// reading an acknowledgement — a keyring's worth (`MAX_KEYRING`, past which the
    /// broker refuses anyway), so a ring of any length cannot fill both directions'
    /// socket buffers and wedge the connection.
    pub const ATTACH_WINDOW: usize = ATTACH_WINDOW;

    /// Publish `body` to `subject`, deduped by `(producer_id, producer_seq)`. Blocks
    /// for the ack; returns `(offset, deduped)` — `deduped` true means a re-send
    /// returning the original offset.
    ///
    /// Refused with [`AcksOwed`], sending nothing, while pipelined acks are owed
    /// ([`owed_acks`](Self::owed_acks)): the ack it read would be theirs.
    pub fn publish(
        &mut self,
        producer_id: u64,
        producer_seq: u64,
        subject: &str,
        body: &[u8],
    ) -> io::Result<(u64, bool)> {
        self.owes_nothing()?;
        self.send_publish(producer_id, producer_seq, subject, body)?;
        self.recv_publish_ack()
    }

    /// Durably retire an exact [`astream_wire::Subject`] from the broker's last-value
    /// index (`Last`) and decrement its charged producer's distinct-subject count
    /// (`MAX_SUBJECTS_PER_PRODUCER`), sending a [`crate::store::RETIRE_SUBJECT`]
    /// (`/a/retire`) request over the wire (`DESIGN-aterm-fabric` §5.2).
    ///
    /// Returns `(offset, already_absent)`: `already_absent` is `false` when `subject`
    /// was in `Last` and a `/a/retire` record was appended at `offset`, or `true` when
    /// `subject` was already absent (idempotent no-op). Refuses on a replica or a
    /// retention-cut log (`base > 0`), when `subject` is not an exact `Subject`
    /// (including wildcards), when `subject` is charged in `Last` to a producer other
    /// than `producer_id`, while a will that can still append targets `subject`, or if
    /// the connection's capability keyring does not grant read-write publish authority
    /// on `subject` for `producer_id`. Refused with [`AcksOwed`], sending nothing, while
    /// pipelined acks are owed.
    pub fn retire_subject(&mut self, producer_id: u64, subject: &str) -> io::Result<(u64, bool)> {
        self.owes_nothing()?;
        self.send_publish(
            producer_id,
            0,
            crate::store::RETIRE_SUBJECT,
            subject.as_bytes(),
        )?;
        self.recv_publish_ack()
    }

    /// Conditional subject retirement (`DESIGN-aterm-fabric` §5.2): remove `subject` from
    /// the broker's last-value index (`Last`) and credit `producer_id`'s distinct-subject
    /// budget by one if and only if `subject`'s current entry in `Last` is at `offset` on
    /// `log`.
    ///
    /// Returns `(offset, deduped)`:
    /// - `(r, false)` when `subject` was in `Last` at `offset` on `log` and a marked
    ///   `/a/retire` record was appended at `r`.
    /// - `(o_or_head, true)` when `subject` was already absent from `Last` (with
    ///   `offset < head`) or its entry in `Last` was already superseded by a newer record
    ///   at `o > offset` (moot: nothing appended).
    /// - `Err` on refusal (`BrokerRefusal::is_retire_charged`, `is_retire_will`,
    ///   `is_retire_log`, `is_retire_cut`, reserved `/a/...`, malformed subject, replica,
    ///   or unauthorized), or [`AcksOwed`], sending nothing, while pipelined acks are
    ///   owed.
    pub fn retire(
        &mut self,
        producer_id: u64,
        subject: &str,
        offset: u64,
        log: LogIdentity,
    ) -> io::Result<(u64, bool)> {
        self.owes_nothing()?;
        self.send_retire(producer_id, subject, offset, log)?;
        self.recv_publish_ack()
    }

    /// PIPELINED conditional retire (send side): write a [`Request::Retire`] without
    /// waiting for its ack. Pair with [`recv_publish_ack`](Self::recv_publish_ack) in
    /// request order; until then its ack is owed ([`owed_acks`](Self::owed_acks)).
    pub fn send_retire(
        &mut self,
        producer_id: u64,
        subject: &str,
        offset: u64,
        log: LogIdentity,
    ) -> io::Result<()> {
        self.in_step()?;
        let mut out = Vec::new();
        append_retire_frame(&mut out, producer_id, subject, offset, log)?;
        self.write_owed(&out)
    }

    /// PIPELINED publish (send side): write a publish WITHOUT waiting for its ack, so a
    /// single connection can keep many in flight (they coalesce into one group-commit
    /// fsync at the broker). Pair each `send_publish` with a later
    /// [`recv_publish_ack`](Self::recv_publish_ack) in the SAME order — the broker
    /// streams acks back in request order. Interleave sends and receives within a
    /// bounded window to avoid filling the socket buffers.
    ///
    /// Each one WRITTEN adds an owed ack ([`owed_acks`](Self::owed_acks)), and until
    /// `recv_publish_ack` has read them all, every request that reads its own reply is
    /// refused with [`AcksOwed`]. A publish refused before a byte is written (a frame
    /// over the cap) owes nothing and leaves the client in step; a write that failed
    /// latches it out of step.
    pub fn send_publish(
        &mut self,
        producer_id: u64,
        producer_seq: u64,
        subject: &str,
        body: &[u8],
    ) -> io::Result<()> {
        self.in_step()?;
        let mut out = Vec::new();
        append_publish_frame(&mut out, producer_id, producer_seq, subject, body)?;
        self.write_owed(&out)
    }

    /// PIPELINED commit (send side): write consumer `group`'s commit to `upto` WITHOUT
    /// waiting for its ack, so a caller that publishes and commits on one connection
    /// keeps its commits in the same pipeline as its publishes, and a loop that has
    /// other work does not park on the commit's flush. Pair it with a later
    /// [`recv_publish_ack`](Self::recv_publish_ack) or
    /// [`try_recv_publish_ack`](Self::try_recv_publish_ack) in send order, exactly as a
    /// [`send_publish`](Self::send_publish).
    ///
    /// The broker answers a commit as it answers a publish — through the same in-order
    /// ack stream, with a `PublishAck` whose offset is the commit record's and whose
    /// dedup flag is false (`broker.rs` `emit_op`) — so its ack is OWED like a
    /// publish's ([`owed_acks`](Self::owed_acks)), and until it is read every request
    /// that reads its own reply is refused with [`AcksOwed`]. A refused commit (a group
    /// the connection's grants do not cover, a log that takes nothing) is the broker's
    /// [`BrokerRefusal`] where its ack would be, and pays it. The commit is staged in
    /// the order the broker read it, behind the publishes written before it on this
    /// connection, and its ack, like each publish's, answers for the group-commit batch
    /// it landed in. A publish ahead of it whose batch the broker rolled back (an
    /// append or a flush that failed: the whole batch is refused) takes the commit with
    /// it when the two shared that batch, as writes sent back to back usually do, and
    /// does not when the commit reached a later batch, which can land. So the publish's
    /// refusal says nothing about the commit behind it; the commit's own ack does.
    ///
    /// A commit refused before a byte is written (a frame over the cap) owes nothing
    /// and leaves the client in step; a write that failed latches it out of step. The
    /// blocking [`commit`](Self::commit) is this, refused first while acks are owed,
    /// and then its own ack read at once.
    pub fn send_commit(&mut self, group: &str, upto: u64) -> io::Result<()> {
        self.in_step()?;
        let mut out = Vec::new();
        append_commit_frame(&mut out, group, upto)?;
        self.write_owed(&out)
    }

    /// PIPELINED BURST (send side): write every publish and commit in `burst` in ONE
    /// write, in order, without waiting for an ack — what [`send_publish`](Self::send_publish)
    /// and [`send_commit`](Self::send_commit) do one write each. Each op owes its own
    /// ack ([`owed_acks`](Self::owed_acks) rises by `burst.len()`), read with
    /// [`recv_publish_ack`](Self::recv_publish_ack) or
    /// [`try_recv_publish_ack`](Self::try_recv_publish_ack) in burst order, exactly as
    /// if they had been sent one by one; a refused op is its [`BrokerRefusal`] where its
    /// ack would be, and pays it.
    ///
    /// ONE BATCH, NOT ONE PER OP. The broker's connection reader hands the writer the
    /// writes it finds already received whole, behind each other, as one unit, so a burst
    /// the reader takes in one read lands in one group-commit batch: one flush (on
    /// Ordered, one barrier) for all of it, where ops written one at a time can each
    /// meet the writer idle and pay their own (`broker.pipelining`). A burst the reader
    /// does not take whole in one read (larger than the connection's receive step or the
    /// socket's buffer, or cut short by the network) is handed over in parts, so its
    /// ops share batches as the parts allow. The batch is a cost, never a contract: what
    /// each op did is its own ack's to say. A publish and a commit in one batch that the
    /// broker rolls back are both refused, as [`send_commit`](Self::send_commit) says of
    /// writes sent back to back.
    ///
    /// All or nothing on THIS side: every frame is built before a byte is written, so a
    /// burst with an op over the frame cap is refused whole, owes nothing and leaves
    /// the client in step; a write that failed latches the client out of step, owing
    /// nothing. Owing nothing is not landing nothing: a write cut short (a peer that
    /// closed, a timeout part way) may have delivered every frame ahead of the cut that the
    /// broker received whole, and the broker may have published or committed each of them,
    /// though no ack of theirs is read here. Only the frame the cut fell in, and those after
    /// it, are sure not to have landed, so a caller that sends the burst's publishes again
    /// sends them under the same producer ids, and the ones that landed dedup (each answered
    /// `deduped`). An empty burst writes nothing. While the burst's acks are owed every
    /// request that reads its own reply is refused with [`AcksOwed`], as after any
    /// pipelined send; keep [`owed_acks`](Self::owed_acks) under
    /// [`MAX_PIPELINE_WINDOW`](Self::MAX_PIPELINE_WINDOW).
    pub fn send_pipelined(&mut self, burst: &[Pipelined<'_>]) -> io::Result<()> {
        self.in_step()?;
        let mut out = Vec::new();
        for op in burst {
            match *op {
                Pipelined::Publish {
                    producer_id,
                    producer_seq,
                    subject,
                    body,
                } => append_publish_frame(&mut out, producer_id, producer_seq, subject, body)?,
                Pipelined::Relay {
                    producer_id,
                    producer_seq,
                    subject,
                    body,
                } => append_relay_frame(&mut out, producer_id, producer_seq, subject, body)?,
                Pipelined::Commit { group, upto } => append_commit_frame(&mut out, group, upto)?,
            }
        }
        if burst.is_empty() {
            return Ok(());
        }
        self.write_owed_n(&out, burst.len())
    }

    /// Send fresh publishes in order, without waiting for their FIFO acknowledgements.
    /// Read each answer with [`recv_publish_ack`](Self::recv_publish_ack). A held key is an
    /// [`ERR_FRESH_HELD`] refusal even when its subject and body match. A staging refusal makes
    /// later fresh publishes [`ERR_FRESH_FENCED`] before they stage. A late commit, flush or quorum
    /// error fences subsequent staging; other requests already staged in that batch retain their
    /// own outcomes. Reconnect before sending fresh publishes after a broker refusal. Ordinary
    /// publishes retain their existing behavior.
    ///
    /// The latest `Hello` must offer [`supports_fresh_publish`](Self::supports_fresh_publish),
    /// including for an empty call. At most [`MAX_PIPELINE_WINDOW`](Self::MAX_PIPELINE_WINDOW)
    /// acknowledgements may be outstanding after the send, and this call may contain at most
    /// [`MAX_FRESH_PIPELINE_BYTES`] framed bytes. All bounds and framing are checked before any
    /// bytes are written; a refusal leaves the client in step and its owed count unchanged.
    ///
    /// A transport error may follow complete frames already received by the broker. It leaves
    /// their outcomes unknown and latches the client out of step. It does not imply success or
    /// failure of those publishes; a caller chooses recovery according to its own replay contract.
    pub fn send_fresh_pipelined(&mut self, burst: &[FreshPublish<'_>]) -> io::Result<()> {
        self.in_step()?;
        if !self.supports_fresh_publish() {
            return Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "broker did not offer fresh publishes",
            ));
        }
        if burst.len() > Self::MAX_PIPELINE_WINDOW
            || self
                .owed
                .checked_add(burst.len() as u64)
                .is_none_or(|owed| owed > Self::MAX_PIPELINE_WINDOW as u64)
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "fresh publish batch exceeds the outstanding acknowledgement window",
            ));
        }
        let mut bytes = 0usize;
        for op in burst {
            let len = fresh_publish_frame_len(op.subject.len(), op.body.len())?;
            bytes = bytes
                .checked_add(len)
                .filter(|&n| n <= MAX_FRESH_PIPELINE_BYTES)
                .ok_or_else(|| {
                    io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "fresh publish batch exceeds byte cap",
                    )
                })?;
        }
        if burst.is_empty() {
            return Ok(());
        }
        let mut out = Vec::new();
        out.try_reserve_exact(bytes).map_err(|_| {
            io::Error::new(
                io::ErrorKind::OutOfMemory,
                "fresh publish buffer allocation failed",
            )
        })?;
        for op in burst {
            append_fresh_publish_frame(
                &mut out,
                op.producer_id,
                op.producer_seq,
                op.subject,
                op.body,
            )?;
        }
        self.write_owed_n(&out, burst.len())
    }

    /// Write one pipelined request whose ack the caller reads later, and count that ack
    /// as owed — only once the whole frame is written: a failed write latches the
    /// client, and nothing it is owed is read again.
    fn write_owed(&mut self, frame: &[u8]) -> io::Result<()> {
        self.write_owed_n(frame, 1)
    }

    /// [`write_owed`](Self::write_owed) for `frames` requests written as one buffer:
    /// all `frames` acks are owed once the whole buffer is written, none if it is not.
    fn write_owed_n(&mut self, buf: &[u8], frames: usize) -> io::Result<()> {
        if let Err(e) = self.stream.write_all(buf) {
            return Err(self.lose(e));
        }
        self.sent_at = Instant::now();
        self.owed = self.owed.saturating_add(frames as u64);
        Ok(())
    }

    /// PIPELINED publish (receive side): read the next ack in order, returning
    /// `(offset, deduped)`, and count it paid. See [`send_publish`](Self::send_publish).
    ///
    /// A refused publish is the broker's [`BrokerRefusal`] here, and it pays its ack
    /// too: a refusal is a whole reply, so the client stays in step for the next one.
    ///
    /// # Errors
    /// The owed publish's refusal; a transport failure (which latches the client); or,
    /// when NO ack is owed ([`owed_acks`](Self::owed_acks) is zero), `InvalidInput`
    /// before anything is read — there is no ack on the way for it to read, so a read
    /// would park until the broker hung up, or take a reply that is nobody's.
    pub fn recv_publish_ack(&mut self) -> io::Result<(u64, bool)> {
        self.owes_an_ack("recv_publish_ack")?;
        let resp = self.read_response()?;
        self.pay(resp)
    }

    /// PIPELINED publish (receive side), WITHOUT WAITING: the next owed ack if the
    /// broker has answered it already, `Ok(None)` if not yet. For a publisher whose
    /// loop has other work — a bridge serving its own mailbox — which reads its acks as
    /// they arrive instead of parking on the broker's flush for each, as
    /// [`recv_publish_ack`](Self::recv_publish_ack) does. Acks come in send order
    /// either way, a commit's ([`send_commit`](Self::send_commit)) among them.
    ///
    /// FRAME-ATOMIC. An ack that has only partly arrived is KEPT, in the client, and
    /// the next read finishes it — a try, or a blocking `recv_publish_ack` or any other
    /// reply read — so no byte read is ever dropped: a `None` leaves the client in
    /// step, owing what it owed. A sealed record partly arrived is kept by the record
    /// layer the same way.
    ///
    /// HOW IT DOES NOT WAIT. A client that knows its socket — one from
    /// [`connect`] (an [`AnyClient`]) or from any of the typed constructors here — puts
    /// it in non-blocking mode for the length of the try and back after it, so a read
    /// with nothing to give answers at once, and every other verb keeps the blocking
    /// stream it had (the read and write timeouts set through a [`Closer`] are
    /// untouched). A client made [`from_stream`](Self::from_stream) cannot reach a
    /// socket under the stream it was handed: its try reads as that stream reads, and a
    /// read that answers `WouldBlock` or `TimedOut` is `None` — so over a stream that
    /// blocks, with no read timeout, it parks as `recv_publish_ack` does.
    ///
    /// It pays an owed ack exactly when it returns one, or the owed write's refusal (a
    /// [`BrokerRefusal`]: a whole reply, which leaves the client in step).
    ///
    /// What does not wait is the READ. The pipelined writes stay blocking writes, and
    /// the broker back-pressures a connection whose acks go unresolved (see the module
    /// documentation): keep [`owed_acks`](Self::owed_acks) under
    /// [`MAX_PIPELINE_WINDOW`](Self::MAX_PIPELINE_WINDOW) by trying as you write.
    ///
    /// # Errors
    /// As [`recv_publish_ack`](Self::recv_publish_ack)'s: the owed write's refusal; a
    /// transport failure, or the broker's close, which latch the client (and zero what
    /// it owes); and `InvalidInput`, before anything is read, when no ack is owed — no
    /// ack is on the way, and `None` would say one is. On a socket the client put in
    /// non-blocking mode itself a read that answers `TimedOut` is such a failure, not a
    /// `None`: no read timeout can fire there, so it is the connection's own
    /// (`ETIMEDOUT`, the peer gone). A failure to put the socket into non-blocking
    /// mode, or back out of it, latches the client too: its blocking reads could no
    /// longer be trusted to wait.
    pub fn try_recv_publish_ack(&mut self) -> io::Result<Option<(u64, bool)>> {
        self.owes_an_ack("try_recv_publish_ack")?;
        let Some(payload) = self.try_frame()? else {
            return Ok(None);
        };
        let resp = match decode_reply(&payload) {
            Ok(resp) => resp,
            Err(e) => return Err(self.lose(e)),
        };
        self.pay(resp).map(Some)
    }

    /// `Ok` when the client is in step and owes an ack for `verb` to read; else the
    /// latch's `BrokenPipe`, or `InvalidInput` with nothing read: there is no ack on
    /// the way, so a read would park until the broker hung up, or take a reply that is
    /// nobody's.
    fn owes_an_ack(&self, verb: &str) -> io::Result<()> {
        self.in_step()?;
        if self.owed == 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!(
                    "no pipelined ack is owed on this connection: {verb} reads the ack of an \
                     earlier send_publish, send_retire or send_commit"
                ),
            ));
        }
        Ok(())
    }

    /// Count one owed ack paid by the whole reply `resp`, and answer it: its
    /// `(offset, deduped)`, or the owed write's refusal.
    fn pay(&mut self, resp: Response) -> io::Result<(u64, bool)> {
        self.owed = self.owed.saturating_sub(1);
        match resp {
            Response::PublishAck { offset, deduped } => Ok((offset, deduped)),
            other => Err(self.reply_error(other)),
        }
    }

    /// The next whole reply frame if it can be had WITHOUT WAITING, `None` if not yet:
    /// one already in [`rx`](Client::rx) costs no I/O; otherwise the stream is read in
    /// non-blocking mode ([`Nowait`]) until it has no more to give, and whatever part of
    /// a frame arrived stays in `rx` for the next read. A close is `UnexpectedEof`, and
    /// every failure latches the client.
    fn try_frame(&mut self) -> io::Result<Option<Vec<u8>>> {
        let held = self.rx.buf.get(self.rx.start..self.rx.end).unwrap_or(&[]);
        if let Some(hdr) = held.first_chunk::<HEADER_SIZE>() {
            match decode_frame_header_bytes(hdr) {
                Ok((len, expected_crc)) => {
                    let consumed = HEADER_SIZE.saturating_add(len);
                    if let Some(payload_slice) = held.get(HEADER_SIZE..consumed) {
                        if crc32_ieee(payload_slice) != expected_crc {
                            self.rx.reset();
                            return Err(self.lose(io::Error::new(
                                io::ErrorKind::InvalidData,
                                "corrupt frame",
                            )));
                        }
                        let mut payload = Vec::new();
                        payload.extend_from_slice(payload_slice);
                        self.rx.start = self.rx.start.saturating_add(consumed);
                        if self.rx.start == self.rx.end {
                            self.rx.reset();
                        }
                        return Ok(Some(payload));
                    }
                }
                Err(e) => {
                    self.rx.reset();
                    let msg = match e {
                        FrameError::TooLarge => "frame exceeds cap",
                        _ => "corrupt frame",
                    };
                    return Err(self.lose(io::Error::new(io::ErrorKind::InvalidData, msg)));
                }
            }
        }
        if let Err(e) = self.set_nowait(true) {
            // A link with no non-blocking mode has lost nothing: the client stays framed, and the
            // blocking `recv_publish_ack` still reads the ack.
            if e.kind() == io::ErrorKind::Unsupported {
                return Err(e);
            }
            return Err(self.lose(e));
        }
        // Read through `rx`, which keeps the bytes of a frame the stream stopped
        // part-way through. (Its negative control reads with `proto::read_frame`,
        // which drops them.)
        let read = {
            #[cfg(test)]
            if self.try_mutant == TryMutant::Torn {
                read_frame(&mut self.stream)
            } else {
                self.rx.next_frame(&mut self.stream)
            }
            #[cfg(not(test))]
            {
                self.rx.next_frame(&mut self.stream)
            }
        };
        // Back to blocking BEFORE the read is judged, whatever it answered: a client
        // left non-blocking would fail its next blocking read at once.
        if let Err(e) = self.set_nowait(false) {
            return Err(self.lose(e));
        }
        match read {
            Ok(Some(payload)) => Ok(Some(payload)),
            Ok(None) => Err(self.lose(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "broker closed",
            ))),
            // The stream had no more to give: "not yet", the client in step.
            Err(e) if self.nowait.not_yet(&e) => Ok(None),
            Err(e) => Err(self.lose(e)),
        }
    }

    /// Put the socket under the stream into non-blocking mode (`on`), or back into
    /// blocking mode ([`Nowait`]); nothing for a stream the client cannot reach under.
    fn set_nowait(&self, on: bool) -> io::Result<()> {
        #[cfg(test)]
        if !on && self.try_mutant == TryMutant::KeepsNowait {
            return Ok(());
        }
        match &self.nowait {
            Nowait::AsIs => Ok(()),
            Nowait::Stream(set) => set(&self.stream, on),
            Nowait::Socket(socket) => socket.set_nonblocking(on),
        }
    }

    /// Read the `PublishAck` a blocking write request is answered with — a
    /// `ProcessAndProduce`'s, which the broker answers like a publish
    /// (`broker.rs` `emit_op`). Its own reply, read at once: never an owed ack.
    fn read_publish_ack(&mut self) -> io::Result<(u64, bool)> {
        match self.read_response()? {
            Response::PublishAck { offset, deduped } => Ok((offset, deduped)),
            other => Err(self.reply_error(other)),
        }
    }

    /// The largest in-flight window [`publish_pipelined`](Self::publish_pipelined) will
    /// use, regardless of the requested window. Kept well under the broker's
    /// `PIPELINE_DEPTH` so the interleaved send/recv loop can never wedge the connection
    /// (a window at/above the broker's bound + non-draining could deadlock until the
    /// broker's ack write-timeout).
    pub const MAX_PIPELINE_WINDOW: usize = 512;

    /// Convenience windowed pipeline: publish `bodies` under `producer_id` (seqs
    /// `1..=len`), keeping at most `window` acks outstanding, and return the acks in
    /// order. Far faster than calling [`publish`](Self::publish) in a loop because the
    /// in-flight publishes share group-commit fsyncs — one connection, many in flight.
    /// The effective window is clamped to `[1, MAX_PIPELINE_WINDOW]` so it cannot
    /// out-run the broker's bounded ack queue.
    ///
    /// The first publish that fails — refused by the broker, or unframeable here —
    /// stops the sending, and the error is returned only after the responses of the
    /// publishes already in flight have been read, so the connection stays in step
    /// for the next call. Those publishes may have landed; re-sending the same bodies
    /// under the same `producer_id` dedups them.
    ///
    /// It reads every ack it is owed before it returns, so it owes the caller none
    /// afterwards; and it is refused with [`AcksOwed`], sending nothing, while acks of
    /// the caller's own [`send_publish`](Self::send_publish)es are owed, whose acks it
    /// would read as its first ones.
    pub fn publish_pipelined(
        &mut self,
        producer_id: u64,
        subject: &str,
        bodies: &[&[u8]],
        window: usize,
    ) -> io::Result<Vec<(u64, bool)>> {
        self.owes_nothing()?;
        let window = window.clamp(1, MAX_PIPELINE_WINDOW);
        let mut credit = CreditWindow::new(window as u64);
        let mut acks = Vec::new();
        let mut tx = Vec::new();
        let mut failure: Option<io::Error> = None;
        loop {
            // Top the in-flight window back up using the TLA+-verified `CreditWindow`
            // (`Astream.Broker.TlaCreditFlowWindow`), coalescing all frames that fit
            // into one `write_all` syscall so the broker's reader drains a whole batch
            // into one group-commit fsync.
            credit.grant_window(window as u64);
            tx.clear();
            let mut staged = credit;
            let mut batch_count = 0usize;
            while failure.is_none() && staged.can_send() {
                let idx = staged.next_send() as usize;
                let Some(&body) = bodies.get(idx) else {
                    break;
                };
                match append_publish_frame(
                    &mut tx,
                    producer_id,
                    (idx as u64).saturating_add(1),
                    subject,
                    body,
                ) {
                    Ok(()) => {
                        let _ = staged.try_send();
                        batch_count = batch_count.saturating_add(1);
                    }
                    Err(e) => failure = Some(e),
                }
            }
            if batch_count > 0 {
                match self.stream.write_all(&tx) {
                    Ok(()) => {
                        self.sent_at = Instant::now();
                        credit = staged;
                    }
                    Err(e) => {
                        let e = self.lose(e);
                        return Err(failure.unwrap_or(e));
                    }
                }
            }
            if credit.in_flight() == 0 {
                break;
            }
            // Drain up to half the window (or all remaining if sending is done) before
            // the next coalesced batch refill so each refill is a true batch.
            let in_flight = credit.in_flight() as usize;
            let drain_target = if failure.is_some() || (credit.next_send() as usize) == bodies.len()
            {
                in_flight
            } else {
                (in_flight / 2).max(1)
            };
            for _ in 0..drain_target {
                let resp = match self.read_response() {
                    Ok(resp) => resp,
                    Err(e) => return Err(failure.unwrap_or(e)),
                };
                credit.record_ack(credit.acked_seq().saturating_add(1));
                match resp {
                    Response::PublishAck { offset, deduped } => acks.push((offset, deduped)),
                    other => {
                        let e = self.reply_error(other);
                        failure.get_or_insert(e);
                    }
                }
            }
        }
        match failure {
            Some(e) => Err(e),
            None => Ok(acks),
        }
    }

    /// REGISTER A LAST WILL on this connection: the record the broker appends on your
    /// behalf when the connection ends, for any reason — a clean close, a crash, a
    /// cable pull the broker eventually notices. Blocks for the acknowledgement and
    /// returns its `(next, head)`.
    ///
    /// One per connection: a second call replaces the first. The will fires as an
    /// ordinary publish under `(producer_id, producer_seq)`, so publishing that key
    /// yourself first makes it a no-op (an exactly-once goodbye), and it is FENCED —
    /// it appends nothing if a record with a higher `producer_seq` from the same
    /// producer has landed since.
    ///
    /// The fence reads sequences BELOW [`ACK_SEQ_BASE`] only: an ack's sequence is
    /// derived from an offset rather than an incarnation, so acking under this producer
    /// id does not suppress this will. For the same reason a `producer_seq` in the
    /// reserved half is REFUSED here — the fence could not protect a will that lives
    /// where it does not look.
    ///
    /// THE FENCE RESTS ON YOUR OBLIGATION, and the broker cannot check it: a will is a
    /// hidden record no read returns, and which incarnation a sequence belongs to is
    /// yours to count. Two things are owed.
    /// - A new incarnation's sequences sit ABOVE every sequence of any incarnation you
    ///   ever presented to a broker, whether you registered a will under it or
    ///   published under it.
    /// - The incarnation is FLUSHED to your stable storage before you register its
    ///   will. After a power loss only your disk can say the incarnation was used,
    ///   because a will that was registered before the first publish landed leaves
    ///   nothing a read returns.
    ///
    /// Reuse an incarnation and nothing fences it. Its two wills share one key, so
    /// whichever connection ends first fires its will and the other dedups away. When
    /// that is the old, half-open connection, its goodbye lands over the new
    /// incarnation's records while you are alive.
    ///
    /// [`will_seq`](crate::will_seq) is the layout that keeps the first half by
    /// construction: `producer_seq = will_seq(inc)`, the incarnation's ordinary
    /// publishes strictly between [`incarnation_base`](crate::incarnation_base)`(inc)`
    /// and it, `inc` at most [`INC_MAX`](crate::INC_MAX). The second half, and the
    /// counter that yields `inc`, stay yours.
    pub fn will(
        &mut self,
        producer_id: u64,
        producer_seq: u64,
        subject: &str,
        body: &[u8],
    ) -> io::Result<(u64, u64)> {
        self.send(&Request::Will {
            producer_id,
            producer_seq,
            subject: subject.to_string(),
            body: body.to_vec(),
        })?;
        self.read_mark()
    }

    /// Say this connection is alive: one [`Request::Keepalive`], answered with a
    /// `Mark` and appending nothing. Over TCP it also asks the broker to HOLD the
    /// connection to its keepalive deadline
    /// ([`KEEPALIVE_DEADLINE`](crate::broker::KEEPALIVE_DEADLINE), 60 s unless the
    /// broker set another) from now on: a connection that then goes that long with
    /// nothing read from it is ended exactly as a closed one is — its will fires, its
    /// slot is freed — which is how the broker notices a client that vanished without a
    /// FIN (a power loss, a NAT or Wi-Fi change, a cable pull) instead of waiting on it
    /// until the broker restarts. So a client that keeps alive once keeps alive for the
    /// connection's life: every
    /// [`KEEPALIVE_INTERVAL`](crate::broker::KEEPALIVE_INTERVAL) it has sent nothing
    /// else, which is [`keepalive_if_idle`](Self::keepalive_if_idle). Any request
    /// counts, so a busy connection never needs one. A Unix-socket connection is
    /// answered and never held: its peer cannot vanish without its kernel closing it.
    ///
    /// ARMING ON A KEEPALIVE IS THE VERSION CHECK, the twin of
    /// [`Subscription::recv_live`] arming on a `Mark`: a client that never sends one is
    /// never cut, so every client that predates the verb idles exactly as it always has.
    ///
    /// `Ok(true)`: the broker knows the verb. `Ok(false)`: it predates it — it answered
    /// `ERR_REFUSED` ("malformed request"), a whole reply, so this client is in step —
    /// and it will never cut this connection; `keepalive_if_idle` sends nothing more
    /// on it.
    ///
    /// PRECONDITION, as for [`fetch`](Self::fetch): no pipelined publish is un-acked on
    /// this connection. The client holds it: while acks are owed the keepalive is
    /// refused with [`AcksOwed`] and nothing is sent.
    ///
    /// # Errors
    /// The socket; on a guarded broker, `ERR_UNAUTHORIZED` while no capability is
    /// attached (a keepalive grants nothing, but its answer names the log's head);
    /// [`AcksOwed`].
    pub fn keepalive(&mut self) -> io::Result<bool> {
        self.send(&Request::Keepalive)?;
        match self.read_mark() {
            Ok(_) => Ok(true),
            Err(e) if is_refused_error(&e) => {
                self.keepalive_unknown = true;
                Ok(false)
            }
            Err(e) => Err(e),
        }
    }

    /// [`keepalive`](Self::keepalive) when this client has sent nothing for `interval`
    /// — pass [`KEEPALIVE_INTERVAL`](crate::broker::KEEPALIVE_INTERVAL) — and nothing at
    /// all otherwise, or once the broker has answered a keepalive as a verb it does not
    /// know. Call it from a loop that wakes at least that often: it reads the clock
    /// and, while the connection is busy, sends nothing. Returns whether a keepalive
    /// went out.
    ///
    /// Idleness runs from the last request WRITTEN (or the client's making), whatever
    /// it was; a blocking request's own wait for its answer is not idleness on the
    /// broker's side, which counts only the time it spends waiting to read.
    ///
    /// # Errors
    /// As [`keepalive`](Self::keepalive): a connection idle with acks still owed is
    /// refused [`AcksOwed`] — its caller wrote publishes and has not read their acks,
    /// and a keepalive would read one as its answer.
    pub fn keepalive_if_idle(&mut self, interval: Duration) -> io::Result<bool> {
        if self.keepalive_unknown || self.sent_at.elapsed() < interval {
            return Ok(false);
        }
        let _ = self.keepalive()?;
        Ok(true)
    }

    /// READ `producer_id`'s DISTINCT-SUBJECT BUDGET: one [`Request::Budget`], answered
    /// with what the broker's log counts against the producer and the budget it
    /// counts against ([`SubjectBudget`]). Appends nothing.
    ///
    /// It is the count a subject-bound refusal is decided by
    /// ([`BrokerRefusal::is_subject_bound`]), read after this connection's own pending
    /// acks, so a producer can keep headroom for the subjects it cannot do without
    /// from the broker's number rather than from a guess of its own.
    ///
    /// `Ok(None)`: the broker predates the verb — it answered `ERR_REFUSED` ("malformed
    /// request"), a whole reply, so this client is in step — and cannot say.
    ///
    /// PRECONDITION, as for [`fetch`](Self::fetch): no pipelined publish is un-acked on
    /// this connection. The client holds it: while acks are owed the request is
    /// refused with [`AcksOwed`] and nothing is sent.
    ///
    /// # Errors
    /// The socket; on a guarded broker, `ERR_UNAUTHORIZED` unless the ring holds a
    /// genuine, unexpired read-write grant that publishes as `producer_id` (bound to
    /// it, or unbound); [`AcksOwed`].
    pub fn subject_budget(&mut self, producer_id: u64) -> io::Result<Option<SubjectBudget>> {
        self.send(&Request::Budget { producer_id })?;
        match self.read_response()? {
            Response::Budget {
                subjects,
                reserved,
                max,
            } => Ok(Some(SubjectBudget {
                subjects,
                reserved,
                max,
            })),
            other => match self.reply_error(other) {
                e if is_refused_error(&e) => Ok(None),
                e => Err(e),
            },
        }
    }

    /// Ask for catch-up and idle marks on this connection's next subscription.
    /// `subscribe` and `subscribe_group` negotiate this before handing the socket
    /// over. A broker that does not know the verb returns `Ok(false)` and leaves
    /// the stream framed; the subscription retains that broker's behavior.
    /// This request arms no deadline and appends no record. A guarded broker
    /// requires an attached capability because the acknowledgement names the head.
    ///
    /// As for `fetch`, no pipelined publish may be awaiting its acknowledgement: while
    /// one is, the request is refused with [`AcksOwed`] and nothing is sent.
    pub fn idle_marks(&mut self) -> io::Result<bool> {
        self.send(&Request::IdleMarks)?;
        match self.read_mark() {
            Ok(_) => Ok(true),
            Err(e) if is_refused_error(&e) => Ok(false),
            Err(e) => Err(e),
        }
    }

    /// Ask for GAP NOTICES on this connection's next subscription
    /// (`REQUIREMENTS-fabric-operations` R4, addendum A9): before the tail delivers any
    /// record past ones retention gave up below it, it says which range it lost and, where
    /// the broker knows, how many records of the filter ([`Event::Gap`]). `subscribe` and
    /// `subscribe_group` negotiate this, after [`idle_marks`](Self::idle_marks), before
    /// handing the socket over. A broker that does not know the verb returns `Ok(false)`
    /// and leaves the stream framed; its tail says nothing of what it skipped, as before.
    /// Hello's request set says beforehand ([`NonceExt::supports_gap_notices`]). It arms
    /// no deadline and appends no record; on a guarded broker it needs an attached
    /// capability, as `idle_marks` does.
    ///
    /// It holds for this connection's FETCHES too: a fetch below its filter's oldest, while
    /// retention still holds records of the filter there, is answered with them, the
    /// notice ahead of the page, where it would have been refused `retained-from=`
    /// ([`fetch_told`](Self::fetch_told) asks for it and hands the notice back;
    /// [`fetch`](Self::fetch) keeps it for [`take_gaps`](Self::take_gaps)).
    ///
    /// As for `fetch`, no pipelined publish may be awaiting its acknowledgement: while
    /// one is, the request is refused with [`AcksOwed`] and nothing is sent.
    pub fn gap_notices(&mut self) -> io::Result<bool> {
        self.send(&Request::GapNotices)?;
        let took = match self.read_mark() {
            Ok(_) => true,
            Err(e) if is_refused_error(&e) => false,
            Err(e) => return Err(e),
        };
        self.told = Some(took);
        Ok(took)
    }

    /// Ask for monotone broker-stamped wall times (`bt=<unix ms>`, `REQUIREMENTS` R3) on
    /// this connection's deliveries (`Fetch`, `Last`, `Subscribe`, `SubscribeGroup`).
    /// Answered with a `Mark`; against an older broker that predates the verb (`ERR_REFUSED`),
    /// returns `Ok(false)` and leaves the stream framed.
    pub fn broker_times(&mut self) -> io::Result<bool> {
        self.send(&Request::BrokerTimes)?;
        let took = match self.read_mark() {
            Ok(_) => true,
            Err(e) if is_refused_error(&e) => false,
            Err(e) => return Err(e),
        };
        self.broker_times = Some(took);
        Ok(took)
    }

    /// Ask that this connection's deliveries carry each record's own `(producer_id, producer_seq)`
    /// ([`Request::OriginStamps`], read back with [`Subscription::last_origin`] on a tail and with
    /// [`page_origins`](Self::page_origins) on a page). `Ok(false)` from a broker that predates
    /// the verb, with the stream still framed.
    pub fn origin_stamps(&mut self) -> io::Result<bool> {
        self.send(&Request::OriginStamps)?;
        let took = match self.read_mark() {
            Ok(_) => true,
            Err(e) if is_refused_error(&e) => false,
            Err(e) => return Err(e),
        };
        self.origins = took;
        Ok(took)
    }

    /// The origin of each record the newest page this connection read delivered, in the order
    /// it delivered them: the record's own `(producer_id, producer_seq)`, the key it was
    /// published or relayed under, so a reader of a page learns where each record came from
    /// with no read of its own. Every bounded read refills it ([`fetch`](Self::fetch),
    /// [`fetch_told`](Self::fetch_told), [`last`](Self::last), [`last_page`](Self::last_page)
    /// and their stamped forms); a walk of several requests ([`last_walk`](Self::last_walk),
    /// [`last_all`](Self::last_all), [`last_all_stamped`](Self::last_all_stamped)) leaves only
    /// its last request's page, which its collected rows do not pair with. Filled only on a
    /// connection that asked with [`origin_stamps`](Self::origin_stamps) and was taken, one
    /// entry per record, `None` for a record the broker stamped no origin on; empty on any
    /// other connection. Each request this connection sends clears it first, so it is empty
    /// after a request that read no page or was refused as it was sent or by the broker. Read
    /// it after a page call returned `Ok`: a call refused before it sent anything (a failed
    /// negotiation) leaves what was there, and a connection lost partway through a page leaves
    /// the origins of what that page read before it failed.
    #[must_use]
    pub fn page_origins(&self) -> &[Option<(u64, u64)>] {
        &self.page_origins
    }

    /// Append a record that originated elsewhere, under its origin's `(producer_id, producer_seq)`
    /// ([`Request::Relay`]), returning `(offset, deduped)`. Refused with [`AcksOwed`], sending
    /// nothing, while pipelined acks are owed.
    pub fn relay(
        &mut self,
        producer_id: u64,
        producer_seq: u64,
        subject: &str,
        body: &[u8],
    ) -> io::Result<(u64, bool)> {
        self.owes_nothing()?;
        self.send_pipelined(&[Pipelined::Relay {
            producer_id,
            producer_seq,
            subject,
            body,
        }])?;
        self.recv_publish_ack()
    }

    /// Ask for a `Mark` each time this connection's tail catches up after delivering, and once as
    /// it first catches up ([`Request::BurstMarks`]): [`Event::Mark`] ends a burst. `Ok(false)`
    /// from a broker that predates the verb, with the stream still framed.
    pub fn burst_marks(&mut self) -> io::Result<bool> {
        self.send(&Request::BurstMarks)?;
        match self.read_mark() {
            Ok(_) => Ok(true),
            Err(e) if is_refused_error(&e) => Ok(false),
            Err(e) => Err(e),
        }
    }

    /// LIFT THIS CONNECTION'S GAP FENCES ([`Request::ClearGapFences`]): the broker answers
    /// once every write sent before it is answered, then drops every fence this
    /// connection's refused writes set ([`supports_gap_fences`](Self::supports_gap_fences)),
    /// so the next write is judged afresh. Send it only once the answer to every write
    /// sent before it has been READ, and each refused one is known: a write sent after it
    /// lands though one sent before it was refused. A broker that holds no fence answers
    /// the same, `Ok(true)`; one that predates the verb (`ERR_REFUSED`) returns `Ok(false)`
    /// and leaves the stream framed.
    ///
    /// As for `fetch`, no pipelined publish may be awaiting its acknowledgement: while one
    /// is, the request is refused with [`AcksOwed`] and nothing is sent.
    pub fn clear_gap_fences(&mut self) -> io::Result<bool> {
        self.send(&Request::ClearGapFences)?;
        match self.read_mark() {
            Ok(_) => Ok(true),
            Err(e) if is_refused_error(&e) => Ok(false),
            Err(e) => Err(e),
        }
    }

    /// ASK THE BROKER TO GAP-FENCE THIS CONNECTION'S WRITES ([`Request::FenceGaps`]) for
    /// the rest of its life: the broker answers once every write sent before it is
    /// answered (each judged unfenced), and from then a refused write fences every later
    /// one of its producer above its sequence, until a write at or under it commits,
    /// [`clear_gap_fences`](Self::clear_gap_fences) lifts it, or the connection closes.
    /// `Ok(true)`: the connection is fenced. `Ok(false)`: a broker opened without
    /// `OpenOptions::sticky_batch_refusal`, or one that predates the verb (`ERR_REFUSED`),
    /// keeps none; the stream stays framed and the connection unfenced, so a producer keeps
    /// one write in flight whose order must hold. Ask where
    /// [`supports_gap_fences`](Self::supports_gap_fences) says the broker keeps them.
    ///
    /// As for `fetch`, no pipelined publish may be awaiting its acknowledgement: while one
    /// is, the request is refused with [`AcksOwed`] and nothing is sent.
    pub fn fence_gaps(&mut self) -> io::Result<bool> {
        self.send(&Request::FenceGaps)?;
        match self.read_mark() {
            Ok(_) => Ok(true),
            Err(e) if is_refused_error(&e) => Ok(false),
            Err(e) => Err(e),
        }
    }

    /// PIPELINED SETTLE (send side, [`Request::Settle`]): ask the broker for a full flush of
    /// its log issued after it read this request, never skipped, WITHOUT waiting for the
    /// answer. Its ack is owed like a publish's and read in send order with
    /// [`recv_publish_ack`](Self::recv_publish_ack) or
    /// [`try_recv_publish_ack`](Self::try_recv_publish_ack): `(durable, false)`, where
    /// `durable` is the log's durable head after the flush, or the refusal every write of
    /// that batch got.
    ///
    /// What it is for: a writer whose own file is on the log's device
    /// ([`log_device`](Self::log_device), [`LogDevice::settles`](crate::LogDevice::settles)) orders its writes by a
    /// barrier (`astream_sys::barrier_sync`), then sends this, and holds what depends on
    /// those writes until it reads the answer. Sent before the barrier returned, the answer
    /// proves nothing about them: the flush may have run ahead of the barrier. A broker that
    /// does not announce it ([`supports_settle`](Self::supports_settle)) answers `Error 5`
    /// where the ack would be, which pays it.
    pub fn send_settle(&mut self) -> io::Result<()> {
        self.in_step()?;
        let mut out = Vec::new();
        crate::proto::append_frame(&mut out, &crate::proto::encode_request(&Request::Settle))?;
        self.write_owed(&out)
    }

    /// [`send_settle`](Self::send_settle), refused first with [`AcksOwed`] while acks are
    /// owed, and then its answer read at once: the log's durable head after a full flush
    /// the broker issued once it read the request.
    ///
    /// # Errors
    /// [`AcksOwed`]; the broker's refusal (a flush that failed, a poisoned log, a broker
    /// that predates the verb, a ring with no read-write grant); a transport failure.
    pub fn settle(&mut self) -> io::Result<u64> {
        self.owes_nothing()?;
        self.send_settle()?;
        let (durable, _) = self.recv_publish_ack()?;
        Ok(durable)
    }

    fn ensure_broker_times(&mut self) -> io::Result<bool> {
        match self.broker_times {
            Some(took) => Ok(took),
            None => self.broker_times(),
        }
    }

    /// The negotiation `subscribe` and `subscribe_group` make: idle marks, then gap
    /// notices. A broker that predates idle marks predates gap notices too, so it is not
    /// asked for them.
    fn ask_for_tail(&mut self) -> io::Result<()> {
        if self.idle_marks()? {
            self.gap_notices()?;
        }
        Ok(())
    }

    /// Query operational fleet statistics for `filter` (`REQUIREMENTS` R5).
    /// Requires a read grant covering `/f/<F>/>` (or root `/>`) on a guarded broker;
    /// never returns record bodies.
    pub fn stats(&mut self, filter: &str) -> io::Result<WireStats> {
        self.send(&Request::Stats {
            filter: filter.to_string(),
        })?;
        match self.read_response()? {
            Response::Stats(stats) => Ok(stats),
            other => Err(self.reply_error(other)),
        }
    }

    /// LAST-VALUE query: the most recent record of every subject matching `filter`
    /// whose subject sorts strictly after `after` (`""` for the first page), at most
    /// `max`, in ascending SUBJECT order. Returns the page and the `(next, head)` of
    /// the closing `Mark`.
    ///
    /// `next` pairs with THIS PAGE, and with no other: it is the head this page was
    /// read at, so a `subscribe` from it tails gap-free and dup-free from THIS
    /// snapshot. A PAGED reader must therefore tail from the FIRST page's `next` and
    /// fold newest-wins across the pages — later pages are read at later heads, and
    /// subscribing from the LAST page's `next` silently skips any record that
    /// superseded a value an earlier page already reported.
    ///
    /// The broker CLAMPS `max` and bounds its scan of the subject index, so a short
    /// page — an EMPTY one included — does not mean the answer ended, and this method
    /// has already thrown away the cursor that says whether it did. It is ONE page, and
    /// nothing that must see the whole face should read it as more. Walk instead:
    /// [`last_walk`](Self::last_walk) (streaming, row-bounded, stoppable) or
    /// [`last_all`](Self::last_all) (collected) follow the cursor to the end, keep the
    /// FIRST page's mark, and turn a walk that does not end into an error.
    /// [`last_page`](Self::last_page) is the one-request primitive under them.
    ///
    /// Non-terminal: the connection is fully usable afterwards (this is the one read
    /// verb that does NOT consume the client).
    ///
    /// PRECONDITION: no pipelined publish is un-acked on this connection. The broker
    /// answers a connection's requests in order, so an owed ack
    /// ([`owed_acks`](Self::owed_acks)) would arrive where the page should; the client
    /// holds the precondition itself, refusing the request with [`AcksOwed`] and sending
    /// nothing until [`recv_publish_ack`](Self::recv_publish_ack) has read them. The
    /// same holds for [`last_page`](Self::last_page), [`last_walk`](Self::last_walk) and
    /// [`last_all`](Self::last_all).
    pub fn last(&mut self, filter: &str, after: &str, max: u32) -> io::Result<Page> {
        let (page, mark, _) = self.last_page(filter, after, max)?;
        Ok((page, mark))
    }

    /// [`last`](Self::last) with the RESUME CURSOR: `(page, (next, head), resume)`.
    ///
    /// `resume` is the `after` for the next page; an EMPTY `resume` means the broker's
    /// scan reached the end of the filter's range and this was the last page. Page
    /// until it is empty — a page shorter than `max` is NOT the end, because the
    /// broker bounds how many index entries one request may visit (matched or not) as
    /// well as how many rows it may return. [`last_walk`](Self::last_walk) is that loop.
    pub fn last_page(
        &mut self,
        filter: &str,
        after: &str,
        max: u32,
    ) -> io::Result<(Vec<Record>, (u64, u64), String)> {
        self.send(&Request::Last {
            filter: filter.to_string(),
            after: after.to_string(),
            max,
        })?;
        let read = self.read_page_resumable(max, false)?;
        Ok((read.page, read.mark, read.resume))
    }

    /// [`last`](Self::last) with each record's monotone broker-stamped wall time
    /// (`bt=`, unix ms; `REQUIREMENTS` R3). Negotiates [`broker_times`](Self::broker_times)
    /// once on this connection before reading.
    pub fn last_stamped(&mut self, filter: &str, after: &str, max: u32) -> io::Result<StampedPage> {
        let (page, mark, _) = self.last_page_stamped(filter, after, max)?;
        Ok((page, mark))
    }

    /// [`last_page`](Self::last_page) with each record's monotone broker-stamped wall
    /// time (`bt=`, unix ms; `REQUIREMENTS` R3).
    pub fn last_page_stamped(
        &mut self,
        filter: &str,
        after: &str,
        max: u32,
    ) -> io::Result<(Vec<StampedRecord>, (u64, u64), String)> {
        self.ensure_broker_times()?;
        self.send(&Request::Last {
            filter: filter.to_string(),
            after: after.to_string(),
            max,
        })?;
        let read = self.read_page_resumable_stamped(max, false)?;
        Ok((read.page, read.mark, read.resume))
    }

    /// WALK A LAST-VALUE FACE: [`last_page`](Self::last_page) repeated on its resume
    /// cursor until the broker says the filter's range is exhausted, each row handed to
    /// `on_row` in ascending subject order. This is the one loop that knows how a
    /// `Last` answer ENDS, so a reader that must see every subject — a roster, a halt
    /// list, an escalation view — calls it rather than restating it.
    ///
    /// THE END IS AN EMPTY `resume`, AND NOTHING ELSE. The broker clamps each request
    /// to `LAST_PAGE_MAX` rows and cuts its index scan after `LAST_SCAN_MAX` entries
    /// VISITED, matched or not, so a page shorter than asked — an EMPTY one included —
    /// is not the end of the answer. The walk pages on the cursor, never on the row
    /// count and never on the last row's subject, which an empty page does not have.
    ///
    /// THE MARK IS THE FIRST PAGE'S. Each request pins its own, later head, so the
    /// answer is a UNION of per-page snapshots, not one snapshot. The `(next, head)`
    /// returned is the first request's — the lowest pin, and so the only offset a
    /// `subscribe(next, filter)` can splice on at with no gap: from a later page's
    /// `next`, a record that superseded a value an earlier page already delivered would
    /// never arrive. The reader pays for the splice: a row from page 2..n may carry an
    /// offset AT OR ABOVE the returned `head`, and the tail may supersede a delivered
    /// row, so a reader that tails folds newest-wins and dedups on offset. Rows never
    /// repeat within one walk; the cursor is a strictly increasing subject.
    ///
    /// AND THE ROWS ALONE ARE NOT THE WHOLE FACE. A subject whose newest record lands
    /// at or above a request's pinned head before that request reaches it is OMITTED
    /// from its page rather than answered stale (see [`Request::Last`]); the record
    /// that displaced it arrives on the tail from `next`. The whole face is the rows
    /// PLUS that tail.
    ///
    /// `after` starts the walk strictly after that subject (`""` for the whole face).
    /// `max` bounds the ROWS the whole walk delivers, not one page's, and each request
    /// asks the broker for exactly the rows still owed, so it never works for rows the
    /// caller will not take; `u32::MAX` is the whole face. `max = 0` is the head query:
    /// one request, no rows, the mark.
    ///
    /// `on_row` runs once its row's page has been read to the closing `Mark`, so the
    /// connection is at a frame boundary whenever it runs and stays usable however the
    /// walk ends — [`Walk::Stop`], the row bound, an `on_row` error. Memory is one page,
    /// not the face.
    ///
    /// Returns the first page's `(next, head)` and the CONTINUATION:
    ///
    /// - `None` — the walk delivered the whole answer: the broker's cursor came back
    ///   empty and every row it sent reached `on_row` (a `Stop` on the very last row
    ///   included).
    /// - `Some(after)` — the walk ended early, on [`Walk::Stop`] or on `max`. Pass it
    ///   back as `after` to continue; it is the subject of the last row delivered (or
    ///   this walk's own `after`, if it delivered none), and continuing from it may
    ///   find nothing more. It is an `Option` where `last_page` has an
    ///   empty-means-done `String` because a walk that stopped before its first row
    ///   must be able to say "continue from the start", and that cursor IS `""`.
    ///
    /// # Errors
    ///
    /// A broker or transport failure, including the broker refusing a request; the
    /// first error `on_row` returns, which ends the walk and is returned as is; or a
    /// walk that has not ended within [`LAST_WALK_PAGES_MAX`] requests — because a
    /// caller that cannot tell "no rows" from "I stopped looking" reports an empty
    /// fleet while a node is escalating. Rows delivered before an error WERE
    /// delivered; the error says the answer is incomplete, not that nothing was seen.
    pub fn last_walk(
        &mut self,
        filter: &str,
        after: &str,
        max: u32,
        mut on_row: impl FnMut(Record) -> io::Result<Walk>,
    ) -> io::Result<((u64, u64), Option<String>)> {
        let mut cursor = after.to_string();
        // The continuation if the walk ends early: the last subject DELIVERED, which
        // starts as the walk's own `after` so a walk that delivered nothing hands that
        // back. `clone_from` reuses the buffer, so tracking it costs no allocation per
        // row once it has grown to the longest subject.
        let mut last = cursor.clone();
        let mut remaining = max;
        // The FIRST request's mark; every later page's is dropped (see above).
        let mut first: Option<(u64, u64)> = None;
        for _ in 0..LAST_WALK_PAGES_MAX {
            let ask = remaining;
            let (page, page_mark, resume) = self.last_page(filter, &cursor, ask)?;
            let mark = *first.get_or_insert(page_mark);
            let rows = page.len();
            let mut taken = 0usize;
            let mut stopped = false;
            for row in page {
                if remaining == 0 {
                    // Unreachable against `last_page`, which refuses a page longer
                    // than it asked for; kept so `max` holds whatever reads the page.
                    break;
                }
                remaining -= 1;
                taken = taken.saturating_add(1);
                last.clone_from(&row.1);
                if on_row(row)? == Walk::Stop {
                    stopped = true;
                    break;
                }
            }
            // `ask > 0`: a head query's empty cursor means "no page", not "complete".
            if resume.is_empty() && taken == rows && ask > 0 {
                return Ok((mark, None));
            }
            if stopped || remaining == 0 {
                return Ok((mark, Some(last)));
            }
            cursor = resume;
        }
        Err(io::Error::other(format!(
            "the last-value walk of {filter} did not end within {LAST_WALK_PAGES_MAX} pages"
        )))
    }

    /// The WHOLE last-value face of `filter`, collected: [`last_walk`](Self::last_walk)
    /// from the first subject with no row bound. Returns every row, in ascending subject
    /// order, and the FIRST page's `(next, head)` — the gap-free splice point for a
    /// `subscribe(next, filter)` that goes on watching the face (fold newest-wins across
    /// the seam; `last_walk` says why).
    ///
    /// `Ok` only for an answer the broker said was complete; a walk past
    /// [`LAST_WALK_PAGES_MAX`] pages is an error, never a short list. Memory is the
    /// whole face; a reader that can act row by row walks instead.
    pub fn last_all(&mut self, filter: &str) -> io::Result<Page> {
        let mut rows = Vec::new();
        let mut cursor = String::new();
        let mut remaining = u32::MAX;
        let mut first: Option<(u64, u64)> = None;
        for _ in 0..LAST_WALK_PAGES_MAX {
            let ask = remaining;
            let (page, page_mark, resume) = self.last_page(filter, &cursor, ask)?;
            let mark = *first.get_or_insert(page_mark);
            let page_rows = page.len();
            let mut taken = 0usize;
            for row in page {
                if remaining == 0 {
                    break;
                }
                remaining -= 1;
                taken = taken.saturating_add(1);
                rows.push(row);
            }
            if resume.is_empty() && taken == page_rows && ask > 0 {
                return Ok((rows, mark));
            }
            if remaining == 0 {
                return Err(io::Error::other(format!(
                    "the last-value face of {filter} did not end within {} rows",
                    u32::MAX
                )));
            }
            cursor = resume;
        }
        Err(io::Error::other(format!(
            "the last-value walk of {filter} did not end within {LAST_WALK_PAGES_MAX} pages"
        )))
    }

    /// [`last_all`](Self::last_all) with each record's monotone broker-stamped wall time
    /// (`bt=`, unix ms; `REQUIREMENTS` R3).
    pub fn last_all_stamped(&mut self, filter: &str) -> io::Result<StampedPage> {
        let mut rows = Vec::new();
        let mut cursor = String::new();
        let mut remaining = u32::MAX;
        let mut first: Option<(u64, u64)> = None;
        for _ in 0..LAST_WALK_PAGES_MAX {
            let ask = remaining;
            let (page, page_mark, resume) = self.last_page_stamped(filter, &cursor, ask)?;
            let mark = *first.get_or_insert(page_mark);
            let page_rows = page.len();
            let mut taken = 0usize;
            for row in page {
                if remaining == 0 {
                    break;
                }
                remaining -= 1;
                taken = taken.saturating_add(1);
                rows.push(row);
            }
            if resume.is_empty() && taken == page_rows && ask > 0 {
                return Ok((rows, mark));
            }
            if remaining == 0 {
                return Err(io::Error::other(format!(
                    "the last-value face of {filter} did not end within {} rows",
                    u32::MAX
                )));
            }
            cursor = resume;
        }
        Err(io::Error::other(format!(
            "the last-value walk of {filter} did not end within {LAST_WALK_PAGES_MAX} pages"
        )))
    }

    /// BOUNDED READ: at most `max` records matching `filter` with offset >= `from`,
    /// scanning at most the broker's [`FETCH_SCAN_MAX`](crate::broker::FETCH_SCAN_MAX)
    /// records. Returns the page and the `(next, head)` of its closing `Mark`; `next`
    /// is the offset AFTER the last record the broker SCANNED, so paging with it
    /// advances even when a page matched nothing. `max = 0` is the head query.
    ///
    /// Non-terminal: unlike `subscribe` it never tails and does not consume the
    /// client — the connection is fully usable afterwards.
    ///
    /// PRECONDITION: no pipelined publish is un-acked on this connection. The broker
    /// flushes a connection's pending acks BEFORE the page, so an owed ack
    /// ([`owed_acks`](Self::owed_acks)) would arrive where the page should. The client
    /// holds the precondition itself: while an ack is owed the fetch is refused with
    /// [`AcksOwed`] — never an empty page — and nothing is sent, until
    /// [`recv_publish_ack`](Self::recv_publish_ack) has read them.
    ///
    /// BELOW THE OLDEST (`REQUIREMENTS` R4): a fetch below its filter's oldest is refused
    /// `retained-from=<oldest>` ([`BrokerRefusal::retained_from`]), unless this connection
    /// asked for gap notices ([`gap_notices`](Self::gap_notices)) and retention still holds
    /// records of the filter there: then the page reads them, and the notice that came
    /// ahead of it is kept, with the filter, for [`take_gaps`](Self::take_gaps), as a
    /// subscription's [`recv`](Subscription::recv) keeps the ones it skips.
    /// [`fetch_told`](Self::fetch_told) asks, and hands each page's notice back with it.
    pub fn fetch(&mut self, from: u64, filter: &str, max: u32) -> io::Result<Page> {
        let (page, gap) = self.fetch_page(from, filter, max)?;
        if let Some(g) = gap {
            self.gaps.push((filter.to_string(), g));
        }
        Ok(page)
    }

    /// [`fetch`](Self::fetch) for a reader TOLD what retention gave up
    /// (`REQUIREMENTS-fabric-operations` R4, addendum A9, as a tail is told): it asks for
    /// gap notices on this connection first, once ([`gap_notices`](Self::gap_notices)),
    /// and hands back the page with the notice that came ahead of it.
    ///
    /// A fetch below its filter's oldest — the offset at and above which the filter is
    /// complete ([`seen_oldest`](Self::seen_oldest)) — reads from `from` while retention
    /// still holds records of the filter there: the held records in offset order, then
    /// the retained ones, with `Some(gap)`, which says every record of the filter in
    /// `gap.from..gap.to` the page and the pages after it do not deliver was given up, and
    /// how many where the broker knows. That is how records of a filter whose subjects
    /// have different floors are read (two reader groups' mail, a hold class beside the
    /// prefix): the oldest is the greatest floor, and some subjects hold records below it.
    /// Where the filter holds none there, or the broker predates the notices (an older
    /// broker refuses the ask as an unknown request, and this reads as `fetch` does), the
    /// fetch is refused `retained-from=` as [`fetch`](Self::fetch) is.
    ///
    /// A BROKER THAT TELLS TAILS BUT NOT FETCHES (one built before told fetches) takes the
    /// ask and refuses such a fetch `retained-from=` with the rest, so there the refusal does
    /// not say the filter holds nothing below the oldest. Hello's request set says which a
    /// broker is ([`supports_told_fetch`](Self::supports_told_fetch), after a `Hello`): a
    /// reader that must not skip a held record, against one that does not announce it, reads
    /// filters whose subjects share one floor (one reader group's mail) instead.
    ///
    /// Each page's notice is its own read's, a continuation's too: a reader paging on from a
    /// `next` below `gap.to` is told the rest of the range again, with its own count, while
    /// the filter still holds records there, and is refused `retained-from=<oldest>` where it
    /// holds none there, however the page before it ended (its `max`, or the broker's scan
    /// bound). Such a reader follows the refusal: the records of the filter it skips below
    /// `gap.to` are ones the notice told it of, and an offset above `gap.to` says those of
    /// `gap.to..offset` were given up since (a tick between its pages). So the first page's
    /// notice is the whole range a paged read lost below `gap.to`. Refused with [`AcksOwed`],
    /// sending nothing, as `fetch` is.
    pub fn fetch_told(
        &mut self,
        from: u64,
        filter: &str,
        max: u32,
    ) -> io::Result<(Page, Option<Gap>)> {
        if self.told.is_none() {
            self.gap_notices()?;
        }
        self.fetch_page(from, filter, max)
    }

    /// [`fetch`](Self::fetch) with each record's monotone broker-stamped wall time
    /// (`bt=`, unix ms; `REQUIREMENTS` R3). Negotiates [`broker_times`](Self::broker_times)
    /// once on this connection before reading.
    pub fn fetch_stamped(&mut self, from: u64, filter: &str, max: u32) -> io::Result<StampedPage> {
        self.ensure_broker_times()?;
        let (page, gap) = self.fetch_page_stamped(from, filter, max)?;
        if let Some(g) = gap {
            self.gaps.push((filter.to_string(), g));
        }
        Ok(page)
    }

    /// [`fetch_told`](Self::fetch_told) with each record's monotone broker-stamped wall
    /// time (`bt=`, unix ms; `REQUIREMENTS` R3).
    pub fn fetch_told_stamped(
        &mut self,
        from: u64,
        filter: &str,
        max: u32,
    ) -> io::Result<(StampedPage, Option<Gap>)> {
        if self.told.is_none() {
            self.gap_notices()?;
        }
        self.ensure_broker_times()?;
        self.fetch_page_stamped(from, filter, max)
    }

    /// Every gap notice the pages [`fetch`](Self::fetch) read carried since the last call,
    /// each with the filter its fetch read, in the order read; empty when none came.
    /// [`fetch_told`](Self::fetch_told) hands each one back instead.
    ///
    /// Kept apart, never merged: a notice speaks of its own filter and its own read's range
    /// only (every record of THAT filter in `from..to` its read did not deliver was given
    /// up), so two filters' notices, or two fetches' ranges with offsets neither read between
    /// them, say nothing together that either does not say alone. The counts of two notices
    /// whose ranges overlap can name the same record (a paged read is told the rest of its
    /// range again on each page below it), so they are not to be summed. They are kept until
    /// taken: one per fetch that carried a notice.
    pub fn take_gaps(&mut self) -> Vec<(String, Gap)> {
        std::mem::take(&mut self.gaps)
    }

    /// One `Fetch` and its answer: the page, and the gap notice ahead of it.
    fn fetch_page(&mut self, from: u64, filter: &str, max: u32) -> io::Result<(Page, Option<Gap>)> {
        self.send(&Request::Fetch {
            from_offset: from,
            filter: filter.to_string(),
            max,
        })?;
        let read = self.read_page_resumable(max, true)?;
        Ok(((read.page, read.mark), read.gap))
    }

    fn fetch_page_stamped(
        &mut self,
        from: u64,
        filter: &str,
        max: u32,
    ) -> io::Result<(StampedPage, Option<Gap>)> {
        self.send(&Request::Fetch {
            from_offset: from,
            filter: filter.to_string(),
            max,
        })?;
        let read = self.read_page_resumable_stamped(max, true)?;
        Ok(((read.page, read.mark), read.gap))
    }

    /// Read `Delivery*` then the closing `Mark` of a bounded, non-terminal read,
    /// keeping the `Mark`'s subject cursor. Where `told` (a `Fetch`'s answer), one gap
    /// notice ahead of the first delivery is the page's own; anywhere else a notice is
    /// out of step.
    ///
    /// The page is buffered before it is returned, so it is bounded by the `max` the
    /// request asked for (the broker never sends more): a peer that keeps sending
    /// deliveries past it is a protocol violation, not a longer page.
    ///
    /// PRECONDITION: no pipelined publish is un-acked on this connection. The broker
    /// flushes pending acks BEFORE the page (they arrive first, in order), so a caller
    /// that owes itself acks must drain them first; [`send`](Self::send) refuses the
    /// request that would have read past them ([`AcksOwed`]).
    fn read_page_resumable(&mut self, max: u32, told: bool) -> io::Result<ReadPage> {
        let mut page = Vec::new();
        let mut gap = None;
        loop {
            let (resp, _, origin) = self.read_response_stamped()?;
            match resp {
                Response::Gap(g) if told && page.is_empty() && gap.is_none() => gap = Some(g),
                // The rest of that page is still on the stream, unread: out of step.
                Response::Delivery { .. } if page.len() >= max as usize => {
                    return Err(self.lose(io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!("broker sent more than the {max} records the page asked for"),
                    )))
                }
                Response::Delivery {
                    offset,
                    subject,
                    body,
                } => {
                    page.push((offset, subject, body));
                    self.note_page_origin(origin);
                }
                Response::Mark {
                    next,
                    head,
                    resume,
                    durable,
                    oldest,
                } => {
                    self.saw_durable(durable);
                    self.oldest = oldest;
                    return Ok(ReadPage {
                        page,
                        mark: (next, head),
                        resume,
                        gap,
                    });
                }
                other => return Err(self.reply_error(other)),
            }
        }
    }

    fn read_page_resumable_stamped(&mut self, max: u32, told: bool) -> io::Result<ReadStampedPage> {
        let mut page = Vec::new();
        let mut gap = None;
        loop {
            let (resp, bt_ms, origin) = self.read_response_stamped()?;
            match resp {
                Response::Gap(g) if told && page.is_empty() && gap.is_none() => gap = Some(g),
                Response::Delivery { .. } if page.len() >= max as usize => {
                    return Err(self.lose(io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!("broker sent more than the {max} records the page asked for"),
                    )))
                }
                Response::Delivery {
                    offset,
                    subject,
                    body,
                } => {
                    page.push((offset, subject, body, bt_ms));
                    self.note_page_origin(origin);
                }
                Response::Mark {
                    next,
                    head,
                    resume,
                    durable,
                    oldest,
                } => {
                    self.saw_durable(durable);
                    self.oldest = oldest;
                    return Ok(ReadStampedPage {
                        page,
                        mark: (next, head),
                        resume,
                        gap,
                    });
                }
                other => return Err(self.reply_error(other)),
            }
        }
    }

    /// Keep the origin of a record the page in hand delivered, on a connection that asked for
    /// origins ([`page_origins`](Self::page_origins)).
    fn note_page_origin(&mut self, origin: Option<(u64, u64)>) {
        if self.origins {
            self.page_origins.push(origin);
        }
    }

    /// Subscribe to every record matching `filter` from `from_offset`, then live.
    /// Consumes the client (the connection becomes a delivery stream). Negotiates
    /// [`idle_marks`](Self::idle_marks), then [`gap_notices`](Self::gap_notices), first,
    /// falling back to an older broker's existing tail behavior. The acknowledgement is
    /// consumed before any subscription event, so only a tail's own mark arms `recv_live`.
    ///
    /// Refused with [`AcksOwed`], sending nothing, while pipelined acks are owed: the
    /// broker flushes them ahead of the stream, where the subscription would read them
    /// as a reply of the wrong kind. The same holds for
    /// [`subscribe_group`](Self::subscribe_group) and
    /// [`fork_subscribe`](Self::fork_subscribe).
    ///
    /// Unlike every other refused request, this one ENDS the connection: the client
    /// was moved into the call, and the refusal drops it. The acks it owed go with it,
    /// unread — whether those publishes landed can no longer be read on this
    /// connection (re-sending them under the same producer id dedups the ones that
    /// did) — and a will registered on it fires, as for any closed connection. So a
    /// caller that pipelines reads its acks first, until
    /// [`owed_acks`](Self::owed_acks) is zero, and subscribes after.
    pub fn subscribe(mut self, from_offset: u64, filter: &str) -> io::Result<Subscription<S>> {
        self.ask_for_tail()?;
        self.into_subscription(&Request::Subscribe {
            from_offset,
            filter: filter.to_string(),
        })
    }

    /// [`subscribe`](Self::subscribe) negotiating monotone broker-stamped wall times
    /// (`bt=`, unix ms; `REQUIREMENTS` R3) on the tail ([`Subscription::recv_stamped`],
    /// [`Subscription::last_bt_ms`]).
    pub fn subscribe_stamped(
        mut self,
        from_offset: u64,
        filter: &str,
    ) -> io::Result<Subscription<S>> {
        self.ask_for_tail()?;
        self.ensure_broker_times()?;
        self.into_subscription(&Request::Subscribe {
            from_offset,
            filter: filter.to_string(),
        })
    }

    /// Durably advance consumer `group`'s committed offset to `upto` (a pure commit).
    /// Blocks for the ack; returns the commit record's offset.
    ///
    /// The broker answers a commit with a `PublishAck`, the same reply a publish gets,
    /// so an owed pipelined ack would pass for the commit's own: the commit would
    /// return the publish's offset, with no error, and the commit's ack would be left
    /// for the next read. While acks are owed it is refused with [`AcksOwed`] and
    /// nothing is sent. Not waiting for the ack is [`send_commit`](Self::send_commit).
    pub fn commit(&mut self, group: &str, upto: u64) -> io::Result<u64> {
        self.owes_nothing()?;
        self.send_commit(group, upto)?;
        let (offset, _) = self.recv_publish_ack()?;
        Ok(offset)
    }

    /// Commit consumer `group` so it resumes at `next`: a group commit is inclusive (the group
    /// resumes one past it), so this commits `next - 1`, and nothing for a `next` of 0, where the
    /// group starts anyway. The one place the exclusive offset a reader scans next becomes the
    /// inclusive commit, so no caller writes the `- 1` itself. A commit below the group's is a
    /// no-op ([`commit`](Self::commit)). Answers the commit record's offset, if it made one.
    pub fn commit_before(&mut self, group: &str, next: u64) -> io::Result<Option<u64>> {
        match next.checked_sub(1) {
            Some(through) => self.commit(group, through).map(Some),
            None => Ok(None),
        }
    }

    /// The read-process-write TRANSACTION: append `out_body` to `out_subject` AND
    /// commit `group` to `upto` atomically (one durable record), deduped by
    /// `(producer_id, producer_seq)`. Returns `(offset, deduped)`. Refused with
    /// [`AcksOwed`], sending nothing, while pipelined acks are owed (it is answered
    /// with a `PublishAck`, as [`commit`](Self::commit) is).
    #[allow(clippy::too_many_arguments)]
    pub fn process_and_produce(
        &mut self,
        producer_id: u64,
        producer_seq: u64,
        out_subject: &str,
        out_body: &[u8],
        group: &str,
        upto: u64,
    ) -> io::Result<(u64, bool)> {
        self.send(&Request::ProcessAndProduce {
            producer_id,
            producer_seq,
            out_subject: out_subject.to_string(),
            out_body: out_body.to_vec(),
            group: group.to_string(),
            upto,
        })?;
        self.read_publish_ack()
    }

    /// Subscribe as consumer `group`: the broker resumes delivery from the group's
    /// DURABLE committed offset (no client-tracked cursor), then tails live.
    /// Negotiates [`idle_marks`](Self::idle_marks) and
    /// [`gap_notices`](Self::gap_notices) as [`subscribe`](Self::subscribe) does; an
    /// older broker keeps its existing tail behavior.
    ///
    /// Refused with [`AcksOwed`] while pipelined acks are owed, and the refusal ends
    /// the connection, the acks unread, as [`subscribe`](Self::subscribe)'s does.
    pub fn subscribe_group(mut self, group: &str, filter: &str) -> io::Result<Subscription<S>> {
        self.ask_for_tail()?;
        self.into_subscription(&Request::SubscribeGroup {
            group: group.to_string(),
            filter: filter.to_string(),
        })
    }

    /// [`subscribe_group`](Self::subscribe_group) negotiating monotone broker-stamped wall
    /// times (`bt=`, unix ms; `REQUIREMENTS` R3) on the tail ([`Subscription::recv_stamped`],
    /// [`Subscription::last_bt_ms`]).
    pub fn subscribe_group_stamped(
        mut self,
        group: &str,
        filter: &str,
    ) -> io::Result<Subscription<S>> {
        self.ask_for_tail()?;
        self.ensure_broker_times()?;
        self.into_subscription(&Request::SubscribeGroup {
            group: group.to_string(),
            filter: filter.to_string(),
        })
    }

    /// COUNTERFACTUAL fork-delivery: stream the alternate timeline that results from
    /// forking the topic at `fork_at` and swapping that record for
    /// `(replacement_subject, replacement_body)`, filtered by `filter`. The live log
    /// is unchanged; the snapshot is delivered then the stream ends (`recv` → `None`).
    ///
    /// Refused with [`AcksOwed`] while pipelined acks are owed, and the refusal ends
    /// the connection, the acks unread, as [`subscribe`](Self::subscribe)'s does.
    pub fn fork_subscribe(
        self,
        fork_at: u64,
        replacement_subject: &str,
        replacement_body: &[u8],
        filter: &str,
    ) -> io::Result<Subscription<S>> {
        self.into_subscription(&Request::ForkSubscribe {
            fork_at,
            replacement_subject: replacement_subject.to_string(),
            replacement_body: replacement_body.to_vec(),
            filter: filter.to_string(),
        })
    }

    /// Write one request frame. A request that cannot be FRAMED (over the frame cap)
    /// is refused before a byte is written, so the client stays in step; a failed
    /// WRITE may have sent part of a frame, so it latches the client out of step.
    ///
    /// Every request this writes reads its OWN reply next (or hands the stream to a
    /// subscription, which reads every frame after it), so each is refused with
    /// [`AcksOwed`] while a pipelined ack is owed: the next frame is that ack's. The
    /// pipelined writes go through [`write_owed`](Self::write_owed) instead.
    fn send(&mut self, req: &Request) -> io::Result<()> {
        // A request's reply is the newest page, or no page: the last one's origins go first, so a
        // request refused here or by the broker leaves none in place.
        self.page_origins.clear();
        self.owes_nothing()?;
        let mut out = Vec::new();
        append_frame(&mut out, &encode_request(req))?;
        if let Err(e) = self.stream.write_all(&out) {
            return Err(self.lose(e));
        }
        self.sent_at = Instant::now();
        Ok(())
    }

    /// Read the one response a request is owed. A close is `UnexpectedEof`, a broker in
    /// another protocol a [`ProtocolMismatch`] and an undecodable payload
    /// `InvalidData`; a broker `Error` is returned AS a response, because a refusal
    /// leaves the stream in step and a transport failure does not — every failure here
    /// latches the client out of step.
    ///
    /// A frame a [`try_recv_publish_ack`](Self::try_recv_publish_ack) began is finished
    /// out of [`rx`](Client::rx), and so is any frame read with it; with nothing there
    /// the reply is read straight off the stream, as every reply was before the try.
    fn read_response(&mut self) -> io::Result<Response> {
        let (resp, _) = self.read_response_with_bt()?;
        Ok(resp)
    }

    fn read_response_with_bt(&mut self) -> io::Result<(Response, Option<u64>)> {
        let (resp, bt_ms, _) = self.read_response_stamped()?;
        Ok((resp, bt_ms))
    }

    /// [`read_response_with_bt`](Self::read_response_with_bt), and on a connection that asked
    /// for origins ([`origin_stamps`](Self::origin_stamps)) the one a `Delivery` carries.
    fn read_response_stamped(&mut self) -> io::Result<StampedResponse> {
        self.in_step()?;
        let frame = if self.rx.is_empty() {
            read_frame(&mut self.stream)
        } else {
            self.rx.next_frame(&mut self.stream)
        };
        let origins = self.origins;
        let read = match frame {
            Ok(Some(p)) => decode_reply_with_bt(&p).map(|(resp, bt_ms)| {
                let origin = (origins && matches!(resp, Response::Delivery { .. }))
                    .then(|| decode_delivery_origin(&p))
                    .flatten();
                (resp, bt_ms, origin)
            }),
            Ok(None) => Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "broker closed",
            )),
            Err(e) => Err(e),
        };
        match read {
            Ok(resp) => Ok(resp),
            Err(e) => Err(self.lose(e)),
        }
    }

    /// Read the `Mark` that acknowledges an `Attach` or a `Will`: its `(next, head)`.
    fn read_mark(&mut self) -> io::Result<(u64, u64)> {
        match self.read_response()? {
            Response::Mark {
                next,
                head,
                durable,
                ..
            } => {
                self.saw_durable(durable);
                Ok((next, head))
            }
            other => Err(self.reply_error(other)),
        }
    }

    /// The error a reply other than the one a request is owed becomes: the broker's
    /// refusal, which leaves the client in step — or any other reply, which is the
    /// signature of a LATE one (owed to an earlier request), and latches it out.
    fn reply_error(&mut self, resp: Response) -> io::Error {
        match resp {
            Response::Error { code, msg } => BrokerRefusal { code, msg }.into(),
            _ => self.lose(unexpected_response()),
        }
    }

    /// Latch this client out of step with its replies because of `e`, and hand `e`
    /// back. The first cause is the one kept.
    ///
    /// A latched client owes nothing: nothing is read on it again, so no ack it was
    /// owed can be paid, and the count ([`owed_acks`](Self::owed_acks)) goes to zero
    /// with the latch. A caller that reads acks while the count is above zero stops
    /// on the failure, rather than reading `BrokenPipe` for an ack that never comes.
    fn lose(&mut self, e: io::Error) -> io::Error {
        if self.lost.is_none() {
            self.lost = Some(e.to_string());
        }
        self.owed = 0;
        e
    }

    /// `Ok` when the next frame on the stream is the reply to the NEXT request: the
    /// client is in step ([`in_step`](Self::in_step), whose `BrokenPipe` comes first —
    /// a latched client owes nothing it can read) and owes no pipelined ack; else the
    /// [`AcksOwed`] that request is refused with. Asked before a byte of a request that
    /// reads its own reply is written, so a refusal leaves the client exactly as it was
    /// — unless the verb consumed the client ([`subscribe`](Self::subscribe) and its
    /// two siblings), whose refusal drops it and so ends the connection.
    fn owes_nothing(&self) -> io::Result<()> {
        self.in_step()?;
        #[cfg(test)]
        if self.unguarded {
            return Ok(());
        }
        match self.owed {
            0 => Ok(()),
            owed => Err(AcksOwed { owed }.into()),
        }
    }

    /// `Ok` while the client is in step with its replies; once it is not, the
    /// `BrokenPipe` every later request fails with. Not `ErrorKind::Other`, which is
    /// what a broker refusal is.
    fn in_step(&self) -> io::Result<()> {
        match &self.lost {
            None => Ok(()),
            Some(why) => Err(io::Error::new(
                io::ErrorKind::BrokenPipe,
                format!(
                    "this connection is out of step with its replies since a request on it \
                     failed ({why}): reconnect"
                ),
            )),
        }
    }

    /// Send a streaming request and hand the connection over to its delivery stream.
    ///
    /// Whatever a try read ahead goes with the stream, in order. Nothing is owed by
    /// then ([`owes_nothing`](Self::owes_nothing)), so the broker has sent nothing past
    /// the replies the client read, and it is empty; carried rather than dropped, so no
    /// byte off the stream is ever lost.
    fn into_subscription(mut self, req: &Request) -> io::Result<Subscription<S>> {
        self.send(req)?;
        Ok(Subscription {
            stream: self.stream,
            rx: self.rx,
            marked: false,
            durable: self.durable,
            gap: None,
            last_bt: None,
            last_origin: None,
        })
    }
}

fn unexpected_response() -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, "unexpected response")
}

/// A read that stopped because the stream had nothing more to give right now — a
/// non-blocking socket's `WouldBlock`, or a read timeout's (`WouldBlock` on Unix,
/// `TimedOut` on Windows) — rather than because the connection failed.
fn is_not_yet(e: &io::Error) -> bool {
    matches!(
        e.kind(),
        io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut
    )
}

/// A bounded read's answer ([`Client::read_page_resumable`]): its records, the closing
/// `Mark`'s `(next, head)` and subject cursor, and the gap notice ahead of a `Fetch`'s page.
struct ReadPage {
    page: Vec<Record>,
    mark: (u64, u64),
    resume: String,
    gap: Option<Gap>,
}

struct ReadStampedPage {
    page: Vec<StampedRecord>,
    mark: (u64, u64),
    resume: String,
    gap: Option<Gap>,
}

fn is_refused_error(e: &io::Error) -> bool {
    match broker_refusal(e) {
        Some(r) => r.code == ERR_REFUSED,
        None => false,
    }
}

/// A reply payload as the response it carries — or, from a broker that speaks another
/// protocol, the [`ProtocolMismatch`] it is. Asked FIRST, so a reply this build cannot
/// decode for that reason is never reported as a garbled one.
fn decode_reply(p: &[u8]) -> io::Result<Response> {
    let (resp, _) = decode_reply_with_bt(p)?;
    Ok(resp)
}

fn decode_reply_with_bt(p: &[u8]) -> io::Result<(Response, Option<u64>)> {
    if let Some(broker) = foreign_protocol(p) {
        return Err(ProtocolMismatch {
            broker,
            client: PROTO_VERSION,
        }
        .into());
    }
    match decode_response_with_bt(p) {
        Some(resp) => Ok(resp),
        None => Err(unexpected_response()),
    }
}

/// The broker and this client speak DIFFERENT astream protocols (`PROTO_VERSION`s), so
/// nothing either says can be decoded by the other: the broker's reply came stamped with
/// another version — what an older broker's "malformed request" is — or was its
/// [`ERR_PROTOCOL`] refusal, which names its version. The
/// broker closes the connection after it, and the client is out of step for good.
/// The remedy is the same astream release on both ends; no retry on this pair succeeds.
///
/// It reaches the caller inside an `io::Error` of kind `Unsupported` — the kind of a
/// transport this build cannot speak, and for the same reason: two builds that do not
/// match. Read it back with [`protocol_mismatch`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProtocolMismatch {
    /// The protocol the broker speaks.
    pub broker: u8,
    /// The protocol this client speaks (this build's `PROTO_VERSION`).
    pub client: u8,
}

impl std::fmt::Display for ProtocolMismatch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "protocol mismatch: broker speaks astream protocol {}, this client {} (run the \
             same astream release on both ends)",
            self.broker, self.client
        )
    }
}

impl std::error::Error for ProtocolMismatch {}

impl From<ProtocolMismatch> for io::Error {
    /// `ErrorKind::Unsupported`, the mismatch inside.
    fn from(m: ProtocolMismatch) -> io::Error {
        io::Error::new(io::ErrorKind::Unsupported, m)
    }
}

/// The protocol mismatch `e` carries, if it is one: `Some` exactly when a broker's reply
/// said it speaks another astream protocol (see [`ProtocolMismatch`]).
pub fn protocol_mismatch(e: &io::Error) -> Option<&ProtocolMismatch> {
    e.get_ref()?.downcast_ref()
}

/// A request the CLIENT refused, before writing a byte of it, because the connection
/// still owes itself `owed` pipelined acks ([`Client::owed_acks`]).
///
/// The broker answers a connection's requests in the order it read them, so after a
/// [`Client::send_publish`] (or a [`Client::send_retire`] or [`Client::send_commit`])
/// the next frame on the stream is that publish's ack, and a request that reads its
/// own reply would take it for its own: a commit or a blocking publish would return
/// the PUBLISH's offset with no error, a fetch or a `Last` would fail on a reply of
/// the wrong kind, and a refused publish's `Error` would come back as the later
/// request's refusal. Nothing on the wire can tell one ack from another, so the rule
/// is the client's to keep, and this is it kept: read the owed acks with
/// [`Client::recv_publish_ack`] (or [`Client::try_recv_publish_ack`]), then send.
///
/// The client is NOT out of step: nothing was written and nothing read, the owed acks
/// are still owed and still in order, and the request goes through once they are
/// read. There is no drain that reads them for the caller, because each ack carries
/// its own answer — the offset, whether it was a dup, or the publish's refusal — and
/// only the caller that sent the publish knows what to do with it.
///
/// Except for the three verbs that CONSUME the client: [`Client::subscribe`],
/// [`Client::subscribe_group`] and [`Client::fork_subscribe`] are refused the same way,
/// with nothing sent, but the client was moved into the call and the refusal drops
/// it. The connection closes with the owed acks unread (what those publishes did can
/// no longer be read on it), and a will registered on it fires. A caller that
/// pipelines reads [`Client::owed_acks`] down to zero before it subscribes.
///
/// It reaches the caller inside an `io::Error` of kind `ResourceBusy`, a kind no other
/// request/reply failure of this client uses (a refusal is `Other`, an out-of-step
/// client `BrokenPipe`). Read it back with [`acks_owed`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AcksOwed {
    /// The acks owed when the request was refused.
    pub owed: u64,
}

/// One write of a [`Client::send_pipelined`] burst, whose ack the caller reads later.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Pipelined<'a> {
    /// What [`Client::send_publish`] writes: `body` to `subject`, deduped by
    /// `(producer_id, producer_seq)`.
    Publish {
        /// The producer the record is deduped under.
        producer_id: u64,
        /// Its sequence within that producer.
        producer_seq: u64,
        /// Where it is published.
        subject: &'a str,
        /// What it carries.
        body: &'a [u8],
    },
    /// What [`Client::relay`] writes: a record that originated elsewhere, under its origin's key.
    Relay {
        /// The origin's producer id.
        producer_id: u64,
        /// The origin's sequence.
        producer_seq: u64,
        /// Where it was published.
        subject: &'a str,
        /// What it carries.
        body: &'a [u8],
    },
    /// What [`Client::send_commit`] writes: consumer `group`'s commit to `upto`.
    Commit {
        /// The consumer group.
        group: &'a str,
        /// The offset it is committed to.
        upto: u64,
    },
}

/// One borrowed record for [`Client::send_fresh_pipelined`]. A fresh publish requires its
/// producer key to be absent; it is not an idempotent retry of an ordinary publish.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FreshPublish<'a> {
    /// The producer the key belongs to.
    pub producer_id: u64,
    /// Its sequence within that producer.
    pub producer_seq: u64,
    /// Where the record is published.
    pub subject: &'a str,
    /// What it carries.
    pub body: &'a [u8],
}

impl std::fmt::Display for AcksOwed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} pipelined publish ack{} still owed on this connection: read {} with \
             recv_publish_ack before a request that reads its own reply (nothing was \
             sent; a subscribe refused this way consumed its client and closed the \
             connection with {} unread)",
            self.owed,
            if self.owed == 1 { " is" } else { "s are" },
            if self.owed == 1 { "it" } else { "them" },
            if self.owed == 1 { "it" } else { "them" },
        )
    }
}

impl std::error::Error for AcksOwed {}

impl From<AcksOwed> for io::Error {
    /// `ErrorKind::ResourceBusy`, the count inside.
    fn from(a: AcksOwed) -> io::Error {
        io::Error::new(io::ErrorKind::ResourceBusy, a)
    }
}

/// The owed-ack refusal `e` carries, if it is one: `Some` exactly when the client
/// refused a request because pipelined acks were still owed (see [`AcksOwed`]).
pub fn acks_owed(e: &io::Error) -> Option<&AcksOwed> {
    e.get_ref()?.downcast_ref()
}

/// The error a response other than the one a stream expects becomes: the broker's
/// own refusal ([`BrokerRefusal`]), or a protocol violation.
fn refused(resp: Response) -> io::Error {
    match resp {
        Response::Error { code, msg } => BrokerRefusal { code, msg }.into(),
        _ => unexpected_response(),
    }
}

/// A REFUSAL the broker sent — its `Response::Error` — as the client hands it back:
/// inside the `io::Error` a refused request returns, with `ErrorKind::Other`. Read it
/// back with [`broker_refusal`].
///
/// `code` is the refusal's class (the [`proto`](crate::proto) table of `ERR_*`
/// codes); `msg` is the broker's words, and is the error's `Display`, so a caller
/// that only prints or matches the message sees exactly what it always did.
///
/// A refusal is a whole reply: the client stays in step and the next request on the
/// connection is answered normally. Every `ErrorKind::Other` the request/reply verbs
/// return is one of these, except what a client decides for itself — the error a
/// [`Client::last_walk`] callback returns, a walk past [`LAST_WALK_PAGES_MAX`] pages,
/// [`Client::last_all`] past `u32::MAX` rows — which carries no refusal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BrokerRefusal {
    /// The `proto::ERR_*` class.
    pub code: u8,
    /// The broker's message.
    pub msg: String,
}

impl BrokerRefusal {
    /// Whether a fresh publish found its key already held ([`ERR_FRESH_HELD`]). This request
    /// appended nothing, even if the held body is equal; later fresh requests need a reconnect.
    pub const fn is_fresh_held(&self) -> bool {
        self.code == ERR_FRESH_HELD
    }

    /// Whether an earlier fresh failure fenced this request ([`ERR_FRESH_FENCED`]). This request
    /// appended nothing and did not establish another key collision. Reconnect before retrying.
    pub const fn is_fresh_fenced(&self) -> bool {
        self.code == ERR_FRESH_FENCED
    }

    /// Whether the SAME request, resent unchanged on the same connection, is refused
    /// again — a record that can never land, a read the grants never cover — so a
    /// caller retrying it would loop: [`ERR_BAD_SUBJECT`], [`ERR_BAD_FILTER`],
    /// [`ERR_RECORD_REFUSED`], [`ERR_UNAUTHORIZED`], [`ERR_PROTOCOL`] (which this
    /// client reads as a [`ProtocolMismatch`] when the refusal names the broker's
    /// version), [`ERR_ORIGIN_REFUSED`] (a relayed record that is not its origin's).
    ///
    /// `false` is NOT "will succeed": it is every other code, [`ERR_REFUSED`] above
    /// all — a write that failed to append or commit, a quorum not reached — then
    /// [`ERR_SUBJECT_BOUND`] (see [`is_subject_bound`](Self::is_subject_bound)),
    /// [`ERR_ORIGIN_UNKNOWN`] (see [`is_origin_unknown`](Self::is_origin_unknown)), fresh-key
    /// collisions or fences, which require the caller's reconnect/recovery decision, and every
    /// code this client does not know. A broker older than the permanent codes
    /// answered every refusal but 2, 3 and 6 with `ERR_REFUSED`, so against it this is
    /// `false` for a permanent refusal too: the fail-safe reading, under which a
    /// caller retries rather than drops.
    pub const fn is_permanent(&self) -> bool {
        matches!(
            self.code,
            ERR_BAD_SUBJECT
                | ERR_BAD_FILTER
                | ERR_RECORD_REFUSED
                | ERR_UNAUTHORIZED
                | ERR_PROTOCOL
                | ERR_ORIGIN_REFUSED
        )
    }

    /// Whether a relayed record's origin is one the broker does not take now
    /// ([`ERR_ORIGIN_UNKNOWN`]): it holds no key for it, or that key stands revoked.
    /// Nothing was appended.
    ///
    /// Not [`is_permanent`](Self::is_permanent): the identical request lands once the
    /// broker's embedder gives it the origin's key or lifts the revocation. Whether to
    /// wait for that is the CARRIER's question, because only it knows whether it still
    /// seats the origin: one that does holds the record, and one that does not drops it.
    ///
    /// `false` against a broker that predates the code, which sends
    /// [`ERR_ORIGIN_REFUSED`] for this refusal.
    pub const fn is_origin_unknown(&self) -> bool {
        self.code == ERR_ORIGIN_UNKNOWN
    }

    /// Whether the producer is at its DISTINCT-SUBJECT BUDGET and the request named a
    /// subject new to the index ([`ERR_SUBJECT_BOUND`]): nothing was appended.
    ///
    /// Not [`is_permanent`](Self::is_permanent): the identical request lands once
    /// another producer introduces the subject (an update spends nothing) or the
    /// producer's own count falls. Whether to wait for that is the PRODUCER's
    /// question, because only it knows who else writes the subject: a producer that
    /// alone writes it — its own lanes — can drop the record for good, and one that
    /// shares it can hold the record. [`Client::subject_budget`] reads the count.
    ///
    /// `false` against a broker that predates the code, which sends [`ERR_REFUSED`]
    /// for this refusal: the fail-safe reading, under which a caller retries.
    pub const fn is_subject_bound(&self) -> bool {
        self.code == ERR_SUBJECT_BOUND
    }

    /// Whether the refusal is an EXPIRED capability: [`ERR_UNAUTHORIZED`] whose
    /// message starts [`CAP_EXPIRED_PREFIX`]. The broker sends that refusal for a
    /// genuine grant whose `exp=` has passed, whether at the `Attach`, on a request
    /// every covering grant has lapsed for, or when a stream ends at its grants'
    /// deadline. Its remedy is to mint the same grant again with a later `exp=`.
    ///
    /// `false` is every other refusal, every other code-8 one included: a proof that
    /// does not verify (a forged or tampered grant, or one minted under another
    /// secret), a request no attached grant ever covered, a full keyring, a producer
    /// id bound elsewhere, and a connection that stayed unattached too long. Neither
    /// half alone is enough. The words under another code are not an expiry, and code
    /// 8 under other words is not one either.
    ///
    /// Against a broker that predates [`CAP_EXPIRED_PREFIX`], this is `true` for an
    /// expired attach and for a stream ended at its deadline. It is `false` for a
    /// lone request whose grants lapsed, which such a broker refused as "does not
    /// grant".
    pub fn is_expired(&self) -> bool {
        self.code == ERR_UNAUTHORIZED && self.msg.starts_with(CAP_EXPIRED_PREFIX)
    }

    /// Whether the refusal is a POISONED log's: [`ERR_REFUSED`] whose message starts
    /// [`LOG_POISONED_PREFIX`]. The broker sends it for every write — publish, commit,
    /// will, binding, flush — while its log refuses every mutation until it is reopened
    /// ([`Broker::poisoned`](crate::Broker::poisoned)): a full flush failed with acked or
    /// held records no full flush covers, or a rollback could not put the file back.
    ///
    /// NOT [`is_permanent`](Self::is_permanent): the same record lands once the log is
    /// reopened. What it says is that nothing resent on THIS connection lands — the cure
    /// is a new open, which only the broker's embedder makes (a supervised broker exits
    /// and is started again), and the client sees it as the connection ending. A
    /// producer that reports whether its broker is working should report this broker
    /// as not, and wait for the reconnect, not retry into it.
    ///
    /// `false` is every other refusal, every other code-5 one included: a write that
    /// failed and was rolled back (the next may land on the same connection), a quorum
    /// not reached, a broker stopping. Against a broker that predates
    /// [`LOG_POISONED_PREFIX`] this is `false` for every refusal: such a broker answered
    /// the first op of a batch on a poisoned log `append failed: log poisoned (…)` and
    /// every later one `batch aborted (prior append I/O error)` — the fail-safe reading,
    /// under which a producer retries.
    pub fn is_poisoned(&self) -> bool {
        self.code == ERR_REFUSED && self.msg.starts_with(LOG_POISONED_PREFIX)
    }

    /// Where a read RETENTION refused can start: the `<off>` of an [`ERR_RECORD_REFUSED`]
    /// whose message starts [`RETAINED_FROM_PREFIX`]`<off>` — a `Fetch` below the oldest
    /// offset of its filter (`REQUIREMENTS` R4), the offset at and above which the filter
    /// is complete: of its records below `<off>` retention gave some up, so not all are
    /// kept. A fetch from `<off>` reads on; one that asked for gap notices
    /// ([`Client::fetch_told`]) reads what is still held below it. `None` for every other
    /// refusal, and against a broker that predates it (which clamped such a fetch to its
    /// base).
    pub fn retained_from(&self) -> Option<u64> {
        if self.code != ERR_RECORD_REFUSED {
            return None;
        }
        let rest = self.msg.strip_prefix(RETAINED_FROM_PREFIX)?;
        let n = rest.bytes().take_while(u8::is_ascii_digit).count();
        rest.get(..n)?.parse().ok()
    }

    /// Whether the refusal is a conditional or state-guarded `Retire` refusal
    /// ([`ERR_RETIRE_REFUSED`]): charged to another producer, targeted by a live or
    /// durable will that can still append, or (for the §5.2 `Retire` verb) a mismatched
    /// `LogIdentity`.
    pub const fn is_retire_refused(&self) -> bool {
        self.code == ERR_RETIRE_REFUSED
    }

    /// Whether `Retire` was refused because the subject is charged to a different
    /// producer (`ERR_RETIRE_REFUSED` starting with [`RETIRE_CHARGED_PREFIX`]).
    pub fn is_retire_charged(&self) -> bool {
        self.code == ERR_RETIRE_REFUSED && self.msg.starts_with(RETIRE_CHARGED_PREFIX)
    }

    /// Whether `Retire` was refused because a live or durable will that can still
    /// append targets the subject (`ERR_RETIRE_REFUSED` starting with
    /// [`RETIRE_WILL_PREFIX`]).
    pub fn is_retire_will(&self) -> bool {
        self.code == ERR_RETIRE_REFUSED && self.msg.starts_with(RETIRE_WILL_PREFIX)
    }

    /// Whether `Retire` was refused because the request's `LogIdentity` did not match
    /// the broker's current log identity (`ERR_RETIRE_REFUSED` starting with
    /// [`RETIRE_LOG_PREFIX`]).
    pub fn is_retire_log(&self) -> bool {
        self.code == ERR_RETIRE_REFUSED && self.msg.starts_with(RETIRE_LOG_PREFIX)
    }

    /// Whether `Retire` was refused because retention has cut the log (`base > 0`,
    /// `ERR_RECORD_REFUSED` starting with [`RETIRE_CUT_PREFIX`]).
    pub fn is_retire_cut(&self) -> bool {
        self.code == ERR_RECORD_REFUSED && self.msg.starts_with(RETIRE_CUT_PREFIX)
    }

    /// Whether a publish or `ProcessAndProduce` was refused by the broker's per-principal /
    /// per-producer monotone token-bucket rate limiter ([`ERR_RATE_LIMITED`],
    /// `DESIGN-aterm-fabric` T9 & T17).
    ///
    /// NOT [`is_permanent`](Self::is_permanent): nothing was appended, and the identical
    /// request lands once the bucket refills (see [`retry_after_ms`](Self::retry_after_ms)).
    #[must_use]
    pub const fn is_rate_limited(&self) -> bool {
        self.code == ERR_RATE_LIMITED
    }

    /// Minimum wait in milliseconds (`>= 1`) advertised in an [`ERR_RATE_LIMITED`] refusal
    /// starting with [`RATE_LIMITED_PREFIX`]`<ms>`, or `None` for any other refusal.
    #[must_use]
    pub fn retry_after_ms(&self) -> Option<u64> {
        if self.code != ERR_RATE_LIMITED {
            return None;
        }
        let rest = self.msg.strip_prefix(RATE_LIMITED_PREFIX)?;
        let raw = rest.as_bytes();
        let mut n = 0usize;
        while let Some(&b) = raw.get(n) {
            if b.is_ascii_digit() {
                n = n.saturating_add(1);
            } else {
                break;
            }
        }
        if n == 0 {
            return None;
        }
        rest.get(..n)?.parse().ok()
    }
}

impl std::fmt::Display for BrokerRefusal {
    /// The broker's message, exactly.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.msg)
    }
}

impl std::error::Error for BrokerRefusal {}

impl From<BrokerRefusal> for io::Error {
    /// `ErrorKind::Other`, the refusal inside.
    fn from(r: BrokerRefusal) -> io::Error {
        io::Error::other(r)
    }
}

/// The broker refusal `e` carries, if it is one: `Some` exactly when a request was
/// answered with the broker's `Response::Error` (see [`BrokerRefusal`]). A transport
/// failure, a client-side bound and an out-of-step client are `None`.
pub fn broker_refusal(e: &io::Error) -> Option<&BrokerRefusal> {
    e.get_ref()?.downcast_ref()
}

/// How long [`take`] must have WAITED for a `Mark` to read it as the broker saying
/// "idle, now" rather than as one already queued on the socket. Under the broker's
/// liveness poll (200 ms), which is the closest two idle marks can come.
const IDLE_STOP_WAIT: Duration = Duration::from_millis(100);

/// Take at most `max` records from a group subscription WITHOUT committing anything.
///
/// Stops early on end-of-stream, or when a read TIMES OUT — so a caller that wants
/// "whatever has arrived within an idle window" sets that window with
/// [`Subscription::set_read_timeout`] first. That method exists on the three
/// transports whose socket is reachable — `Subscription<UnixStream>` (Unix builds),
/// `Subscription<TcpStream>` and (feature `aead`) the sealed
/// `Subscription<SealedStream<TcpStream>>`, which the `handshake` and `identity`
/// transports also produce. An erased [`AnySubscription`] sets it through the
/// [`Closer`] that [`connect`] returned with its client. On any OTHER stream type
/// there is no idle window: bound the socket yourself before subscribing (reach it
/// with [`Subscription::get_ref`]), or this parks in the read until the broker sends
/// something.
///
/// It also stops when the broker says the subscription is IDLE: a caught-up tail is
/// sent a `Mark` after every [`IDLE_MARK`](crate::broker::IDLE_MARK) with nothing to
/// deliver, and each one is a read that returned, so without this stop a window
/// longer than the broker's interval would never time out. The stop is on a mark
/// this take WAITED for (100 ms or longer). A mark that was already queued — the one
/// the tail sends as it first catches up, or marks that piled up while nobody was
/// taking — says nothing about now, and is passed over. So against a broker that
/// marks, a take parks for at most about two idle intervals; against one that does
/// not, it is exactly the read timeout.
///
/// The idle stop is frame-atomic: a timeout that lands part-way through a record
/// keeps that record's bytes on the subscription and resumes it on the next call
/// (see [`Subscription::recv_event`]), so the same `sub` can be taken from again.
/// The records are already durable and the group's cursor has NOT moved, so a
/// caller that dies here sees them again.
pub fn take<S: Read + Write>(sub: &mut Subscription<S>, max: usize) -> io::Result<Vec<Record>> {
    let mut out = Vec::new();
    while out.len() < max {
        let caught_up_before = sub.marked;
        let asked = Instant::now();
        match sub.recv_event() {
            Ok(Some(Event::Delivery {
                offset,
                subject,
                body,
            })) => out.push((offset, subject, body)),
            // An idle mark this take waited for: nothing more right now.
            Ok(Some(Event::Mark { .. }))
                if caught_up_before && asked.elapsed() >= IDLE_STOP_WAIT =>
            {
                break
            }
            // The catch-up mark, or one already queued: more may follow at once. A gap
            // notice is kept on the subscription (`take_gap`), and records follow it.
            Ok(Some(Event::Mark { .. } | Event::Gap(_))) => {}
            Ok(None) => break, // the broker closed
            Err(e)
                if matches!(
                    e.kind(),
                    io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut
                ) =>
            {
                break; // idle: nothing more right now
            }
            Err(e) => return Err(e),
        }
    }
    Ok(out)
}

/// THE TWO-CONNECTION DRAIN: take at most `max` records from `sub` (a group
/// subscription) and then durably commit `group` through the last one on
/// `committer` — a SECOND connection, because `subscribe_group` consumes its client
/// and a group subscription's own connection is a one-way delivery stream. That price
/// is the reason this is a library helper rather than something every caller
/// re-invents.
///
/// The commit happens AFTER the take, so a failure between the two redelivers the
/// records rather than skipping them. But the group has moved past them by the time
/// `drain` returns: a caller that must PROCESS before committing (at-least-once into
/// an idempotent sink) calls [`take`] and commits itself.
///
/// The committer is asked BEFORE the take: one that owes itself pipelined acks
/// ([`Client::owed_acks`]) refuses the drain with [`AcksOwed`], and one out of step
/// refuses it with `BrokenPipe`, with nothing taken from `sub`. Its commit would be
/// refused the same way after the take, and the records taken would then be in
/// nobody's hands: a retry on the same `sub` — read the acks, drain again — would take
/// the records after them and commit the group past both.
///
/// A broker reaps a connection that sends no request within its first-frame timeout
/// ([`FIRST_FRAME_TIMEOUT`](crate::broker::FIRST_FRAME_TIMEOUT) by default), so a
/// FRESH `committer` whose first request is this commit fails if the take runs
/// longer than that. Make one request on it first — an attach, or
/// [`Client::hello`]; on a guarded broker the deadline runs until a capability is
/// accepted, so there only a successful attach does.
///
/// Returns the records; an empty result commits nothing.
pub fn drain<S: Read + Write, C: Read + Write>(
    sub: &mut Subscription<S>,
    committer: &mut Client<C>,
    group: &str,
    max: usize,
) -> io::Result<Vec<Record>> {
    committer.owes_nothing()?;
    let records = take(sub, max)?;
    if let Some((last, _, _)) = records.last() {
        committer.commit(group, *last)?;
    }
    Ok(records)
}

/// The top half of the producer sequence space, RESERVED for [`ack`].
///
/// Defined by the LOG ([`crate::store::ACK_SEQ_BASE`]) and re-exported here, so the
/// derivation below and the store's last-will fence read one constant: acks occupy
/// sequences at or above this value, ordinary publishes must stay below it, and the
/// fence — which asks whether a producer has been heard from since it registered its
/// will — ignores the reserved half entirely. `asb` enforces the lower half on `--seq`
/// and `--seq-file`.
pub use crate::store::ACK_SEQ_BASE;

/// THE READ-PROCESS-WRITE ACK: append the ack record AND advance `group` past
/// `offset` in ONE durable record, so the answer and the cursor can never disagree.
///
/// The `producer_seq` is [`ACK_SEQ_BASE`]` | offset`, which is what makes a retry
/// idempotent: a repeated ack for the same offset returns `deduped = true`, appends
/// nothing, and re-applies no commit — and it does so whether the retry came through
/// this helper or through `asb ack`, because both derive the key the same way.
///
/// `offset` must be below [`ACK_SEQ_BASE`] (any real log offset is, by many orders of
/// magnitude), and ordinary publishes by the same `producer_id` must stay below it too
/// — `asb` enforces that on `--seq`/`--seq-file`; a library caller must observe it
/// itself. Within those bounds an ack and an ordinary publish by one producer id never
/// share a dedup key.
///
/// An ack does not raise the producer's last-will fence: the reserved half is excluded
/// from `BrokerLog::producer_high_water`, because an ack's sequence is derived from an
/// offset rather than from an incarnation and is above every sequence a will can hold.
/// Acking under a producer id that also holds a will is therefore safe, and a will
/// registered at a sequence in the reserved half is refused.
///
/// Compatibility: an ack written by a version that keyed it on the BARE `offset` sits
/// under a different dedup key, so retrying it through this version appends a second
/// answer record (the monotone group commit is unaffected). Drain a producer's
/// in-flight acks before upgrading it.
pub fn ack<S: Read + Write>(
    client: &mut Client<S>,
    producer_id: u64,
    group: &str,
    offset: u64,
    out_subject: &str,
    out_body: &[u8],
) -> io::Result<(u64, bool)> {
    if offset >= ACK_SEQ_BASE {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "an ack's input offset must stay in the lower half of the sequence space",
        ));
    }
    client.process_and_produce(
        producer_id,
        ACK_SEQ_BASE | offset,
        out_subject,
        out_body,
        group,
        offset,
    )
}

/// A live delivery stream from the broker.
#[cfg(unix)]
pub struct Subscription<S = UnixStream> {
    stream: S,
    /// What has been read off `stream` and not yet returned; see [`RecvBuf`].
    rx: RecvBuf,
    /// Whether a `Mark` has come down this stream yet (see [`take`]).
    marked: bool,
    /// The durable head the newest `Mark` on this stream carried
    /// ([`seen_durable`](Subscription::seen_durable)).
    durable: Option<u64>,
    /// The gap notices read since the last [`take_gap`](Subscription::take_gap), as one.
    gap: Option<Gap>,
    /// Monotone broker-stamped wall time (`bt=`, unix ms; `REQUIREMENTS` R3) carried by
    /// the most recent `Delivery` read on this stream.
    last_bt: Option<u64>,
    /// The `(producer_id, producer_seq)` the most recent `Delivery` carried, on a stream that
    /// asked ([`Client::origin_stamps`]).
    last_origin: Option<(u64, u64)>,
}

/// A live delivery stream from the broker (Windows twin: TCP default, as above).
#[cfg(not(unix))]
pub struct Subscription<S = TcpStream> {
    stream: S,
    /// What has been read off `stream` and not yet returned; see [`RecvBuf`].
    rx: RecvBuf,
    /// Whether a `Mark` has come down this stream yet (see [`take`]).
    marked: bool,
    /// The durable head the newest `Mark` on this stream carried
    /// ([`seen_durable`](Subscription::seen_durable)).
    durable: Option<u64>,
    /// The gap notices read since the last [`take_gap`](Subscription::take_gap), as one.
    gap: Option<Gap>,
    /// Monotone broker-stamped wall time (`bt=`, unix ms; `REQUIREMENTS` R3) carried by
    /// the most recent `Delivery` read on this stream.
    last_bt: Option<u64>,
    /// The `(producer_id, producer_seq)` the most recent `Delivery` carried, on a stream that
    /// asked ([`Client::origin_stamps`]).
    last_origin: Option<(u64, u64)>,
}

#[cfg(unix)]
impl Subscription<UnixStream> {
    /// A handle that can end this subscription from ANOTHER thread: `recv` blocks
    /// in a socket read with no timeout, so an owner that wants to stop a tailing
    /// thread (and release the broker-side connection) shuts the socket down through
    /// this closer, which makes the blocked `recv` return `Ok(None)`.
    ///
    /// The closer holds its own handle to the socket, so while it lives, dropping the
    /// subscription alone does NOT close the connection: call
    /// [`close`](SubscriptionCloser::close), or drop both.
    /// The TCP and sealed subscriptions have the same method, returning the same
    /// [`Closer`]; an erased [`AnySubscription`] has no socket left to reach, so its
    /// closer is the one [`connect`] handed back.
    pub fn closer(&self) -> io::Result<SubscriptionCloser> {
        Closer::unix(&self.stream)
    }
}

/// The name [`Closer`] had when only a Unix-socket [`Subscription`] could make one.
/// Kept so code written against it compiles unchanged: it IS [`Closer`], so it also
/// comes from a TCP or sealed subscription and from [`connect`].
pub type SubscriptionCloser = Closer;

/// What a subscription can carry: a record, a `Mark`, or a gap notice.
/// [`Subscription::recv`] keeps its signature and SKIPS marks and notices; a caller that
/// needs the cursor reads [`recv_event`](Subscription::recv_event) instead,
/// [`recv_live`](Subscription::recv_live) turns marks into liveness, and
/// [`take_gap`](Subscription::take_gap) hands back every notice a skipping read passed.
///
/// On a `ForkSubscribe` stream the one `Mark` closes the snapshot. On a `Subscribe` or
/// `SubscribeGroup` stream that negotiated idle marks a `Mark` is the broker saying
/// it is there with nothing to deliver: once when the tail first CATCHES UP, then
/// again after each [`IDLE_MARK`](crate::broker::IDLE_MARK) with nothing written —
/// so a live idle subscription is never silent for long, and a silent one is a link
/// that has died.
#[derive(Debug, Clone, Eq)]
pub enum Event {
    /// One delivered record: `(offset, subject, body)`.
    Delivery {
        offset: u64,
        subject: String,
        body: Vec<u8>,
    },
    /// Resume from `next`; `head` is the subscriber-visible head the broker read
    /// with — the end of a bounded read, or a tail that is caught up or idle.
    /// `durable` is the broker's durable head then: every record below it is on stable
    /// media. `None` from a broker that predates the field, which serves Strict or
    /// Relaxed, never Ordered: read its tier from `Hello`'s block
    /// ([`Client::served_durability`]) — on Strict the durable head is `head`; on Relaxed
    /// nothing acked since its open (or clean close) is durable, so `head` is not. A
    /// broker older still sends no block, and may serve Relaxed without saying so: there
    /// `head` is durable only for a reader that knows its broker strict. On a broker that
    /// serves Ordered, a tail that asked for idle marks also gets a `Mark` when a full
    /// flush makes records it was delivered durable.
    Mark {
        next: u64,
        head: u64,
        durable: Option<u64>,
    },
    /// What retention gave up below the tail (`REQUIREMENTS-fabric-operations` R4,
    /// addendum A9): every record of the filter in `from..to` that this stream does not
    /// deliver was given up, and `records` is how many of them, where the broker knows
    /// (see [`Gap`]). It comes before every record the tail delivers after it. Sent only
    /// on a `Subscribe` or `SubscribeGroup` stream that asked
    /// ([`Client::gap_notices`], which `subscribe` and `subscribe_group` do).
    Gap(Gap),
}

impl PartialEq for Event {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Event::Delivery {
                    offset: a_o,
                    subject: a_s,
                    body: a_b,
                },
                Event::Delivery {
                    offset: b_o,
                    subject: b_s,
                    body: b_b,
                },
            ) => *a_o == *b_o && a_s.as_str() == b_s.as_str() && a_b.as_slice() == b_b.as_slice(),
            (
                Event::Mark {
                    next: a_n,
                    head: a_h,
                    durable: a_d,
                },
                Event::Mark {
                    next: b_n,
                    head: b_h,
                    durable: b_d,
                },
            ) => *a_n == *b_n && *a_h == *b_h && *a_d == *b_d,
            (Event::Gap(a), Event::Gap(b)) => a == b,
            _ => false,
        }
    }
}

/// Bytes a subscription asks its stream for per read, and the size its receive
/// buffer returns to after an oversized frame.
const READ_CHUNK: usize = 64 * 1024;

/// A receive buffer: the bytes read off a stream that no read has returned yet,
/// `buf[start..end]`. A subscription's replies, and a client's, are read through one;
/// so are a served connection's requests (`broker.rs`, `serve_conn`).
///
/// Frames are parsed out of this buffer rather than read off the stream with
/// `read_exact`, for three reasons. A read can TIME OUT part-way through a frame
/// (`SO_RCVTIMEO`, under [`take`]'s idle window), and `read_exact` drops the bytes it
/// had already consumed when it does, so the next read would parse a body as a
/// header; here those bytes simply stay in the buffer and the next `recv` finishes
/// the frame. One read takes every queued frame that fits, so a subscriber catching
/// up on a backlog pays one syscall per buffer rather than two per frame. And a reader
/// can ask, reading nothing, whether the next frame has already arrived whole
/// ([`holds_frame`](Self::holds_frame)), which is how the broker hands the writes a
/// client sent together to its writer together.
///
/// The buffer grows by at most its step per read — [`READ_CHUNK`], or the smaller step
/// a served connection keeps ([`with_step`](Self::with_step)) — with what the peer has
/// actually SENT, never with the length a header declares, so a peer that announces
/// a 16 MiB frame and stalls pins only what it sent.
pub(crate) struct RecvBuf {
    buf: Vec<u8>,
    start: usize,
    end: usize,
    /// How much the buffer grows per read, and what it returns to once empty.
    step: usize,
}

impl Default for RecvBuf {
    fn default() -> RecvBuf {
        RecvBuf::with_step(READ_CHUNK)
    }
}

impl RecvBuf {
    /// An empty buffer that grows `step` bytes per read (at least one) and gives back
    /// whatever it grew past one step once it empties.
    pub(crate) fn with_step(step: usize) -> RecvBuf {
        RecvBuf {
            buf: Vec::new(),
            start: 0,
            end: 0,
            step: step.max(1),
        }
    }

    /// Whether the buffer already holds the whole of the next frame, judged on its
    /// header alone and reading nothing: its length is in, and that many payload bytes
    /// after it. A frame whose header is bad counts as held, since the next
    /// [`next_frame`](Self::next_frame) answers it at once (with the error), without
    /// a read.
    pub(crate) fn holds_frame(&self) -> bool {
        let held = self.buf.get(self.start..self.end).unwrap_or(&[]);
        let Some(hdr) = held.first_chunk::<HEADER_SIZE>() else {
            return false;
        };
        match decode_frame_header_bytes(hdr) {
            Ok((len, _)) => held.len().saturating_sub(HEADER_SIZE) >= len,
            Err(_) => true,
        }
    }

    /// The payload of the next frame; `Ok(None)` when the stream closes at a frame
    /// boundary. A timeout keeps the unfinished frame for the next call; any other
    /// error discards it, since the stream cannot be resumed past one.
    pub(crate) fn next_frame(&mut self, stream: &mut impl Read) -> io::Result<Option<Vec<u8>>> {
        loop {
            // Decode the next frame if the buffer already holds all of it, reading
            // nothing; `Ok(None)` when it holds less (nothing at all included). A frame
            // that can never decode — a bad header, a length over the cap — empties the
            // buffer and is `InvalidData`.
            let held = self.buf.get(self.start..self.end).unwrap_or(&[]);
            if let Some(hdr) = held.first_chunk::<HEADER_SIZE>() {
                match decode_frame_header_bytes(hdr) {
                    Ok((len, expected_crc)) => {
                        let consumed = HEADER_SIZE.saturating_add(len);
                        if let Some(payload_slice) = held.get(HEADER_SIZE..consumed) {
                            if crc32_ieee(payload_slice) != expected_crc {
                                self.reset();
                                return Err(io::Error::new(
                                    io::ErrorKind::InvalidData,
                                    "corrupt frame",
                                ));
                            }
                            let mut payload = Vec::new();
                            payload.extend_from_slice(payload_slice);
                            self.start = self.start.saturating_add(consumed);
                            if self.start == self.end {
                                self.reset();
                            }
                            return Ok(Some(payload));
                        }
                    }
                    Err(e) => {
                        self.reset();
                        let msg = match e {
                            FrameError::TooLarge => "frame exceeds cap",
                            _ => "corrupt frame",
                        };
                        return Err(io::Error::new(io::ErrorKind::InvalidData, msg));
                    }
                }
            }
            if self.end == self.buf.len() {
                // Full: slide the unfinished frame to the front, and grow only when it
                // already fills the whole buffer.
                let len = self.end.saturating_sub(self.start);
                if self.start > 0 {
                    let mut i = 0usize;
                    while i < len {
                        if let Some(&b) = self.buf.get(self.start.saturating_add(i)) {
                            if let Some(dst) = self.buf.get_mut(i) {
                                *dst = b;
                            }
                        }
                        i = i.saturating_add(1);
                    }
                }
                self.end = len;
                self.start = 0;
                if self.end == self.buf.len() {
                    const MAX_RECV_BUF_BYTES: usize =
                        astream_wire::MAX_PAYLOAD_LEN + HEADER_SIZE + (1024 * 1024);
                    let grown = self.buf.len().saturating_add(self.step);
                    if grown > MAX_RECV_BUF_BYTES {
                        self.reset();
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "receive buffer exceeded frame ceiling",
                        ));
                    }
                    self.buf.resize(grown, 0);
                }
            }
            let Some(dst) = self.buf.get_mut(self.end..) else {
                self.reset();
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "receive buffer out of bounds",
                ));
            };
            match stream.read(dst) {
                Ok(0) => {
                    let partial = self.end.saturating_sub(self.start);
                    self.reset();
                    // As `proto::read_frame`: only a close with NOTHING of the next
                    // frame read is a close; once any byte of it — a header byte
                    // included — has arrived, the frame was cut short.
                    return if partial == 0 {
                        Ok(None)
                    } else {
                        Err(io::Error::new(
                            io::ErrorKind::UnexpectedEof,
                            "the peer closed mid-frame",
                        ))
                    };
                }
                Ok(n) => self.end = self.end.saturating_add(n),
                Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
                Err(e) => {
                    if !matches!(
                        e.kind(),
                        io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut
                    ) {
                        self.reset();
                    }
                    return Err(e);
                }
            }
        }
    }

    /// Whether nothing read is waiting here: no frame, and no part of one.
    const fn is_empty(&self) -> bool {
        self.start == self.end
    }

    /// Nothing is owed: empty the buffer, and give back whatever an oversized frame
    /// grew it by.
    fn reset(&mut self) {
        self.start = 0;
        self.end = 0;
        if self.buf.len() > self.step {
            self.buf.truncate(self.step);
            self.buf.shrink_to_fit();
        }
    }
}

impl<S: Read + Write> Subscription<S> {
    /// The underlying byte stream, for transport-level control — a timeout, a
    /// shutdown — that does not touch the record bytes. This is the escape hatch for
    /// a stream type that has no [`set_read_timeout`](Self::set_read_timeout) of its
    /// own: reach the socket through it and bound the read there. (A boxed
    /// [`AnyStream`] cannot be reached this way — erasing it hid the socket — which
    /// is why [`connect`] returns a [`Closer`] alongside it.) Do NOT read or write
    /// the stream itself — a subscription holds the bytes it has already read (the
    /// rest of a frame a timeout interrupted, and frames queued behind it), and
    /// bytes taken from underneath it are gone from the stream it resumes.
    pub const fn get_ref(&self) -> &S {
        &self.stream
    }

    /// The broker's durable head as the newest `Mark` on this stream told it (see
    /// [`Event::Mark`]) — or the client's before it subscribed. `None` before any.
    pub const fn seen_durable(&self) -> Option<u64> {
        self.durable
    }

    /// Every gap notice this stream carried since the last call ([`Event::Gap`]), as one
    /// ([`Gap::and`]): what retention gave up below the tail. For a reader that skips them
    /// — [`recv`](Self::recv), [`take`], [`drain`] — so it can still tell that records it
    /// was not delivered were given up. `None` when none came.
    pub fn take_gap(&mut self) -> Option<Gap> {
        self.gap.take()
    }

    /// The monotone broker-stamped wall time (`bt=`, unix ms; `REQUIREMENTS` R3) carried
    /// by the most recent [`Event::Delivery`] read on this subscription (`None` before any
    /// delivery, or when the subscription did not negotiate [`Client::broker_times`]).
    pub const fn last_bt_ms(&self) -> Option<u64> {
        self.last_bt
    }

    /// The `(producer_id, producer_seq)` the most recent delivery carried (`None` before the
    /// first delivery, or when the connection did not ask with [`Client::origin_stamps`]).
    pub const fn last_origin(&self) -> Option<(u64, u64)> {
        self.last_origin
    }

    /// Block until the next matching delivery; `Ok(None)` if the broker closes.
    /// A `Mark` and a gap notice are SKIPPED (this method's signature is unchanged) —
    /// read [`recv_event`](Self::recv_event) to see them, or
    /// [`take_gap`](Self::take_gap) for the notices passed.
    pub fn recv(&mut self) -> io::Result<Option<Record>> {
        loop {
            match self.recv_event()? {
                None => return Ok(None),
                Some(Event::Mark { .. } | Event::Gap(_)) => continue,
                Some(Event::Delivery {
                    offset,
                    subject,
                    body,
                }) => return Ok(Some((offset, subject, body))),
            }
        }
    }

    /// [`recv`](Self::recv) returning each record's monotone broker-stamped wall time
    /// (`bt=`, unix ms; `REQUIREMENTS` R3) alongside `(offset, subject, body)`.
    pub fn recv_stamped(&mut self) -> io::Result<Option<StampedRecord>> {
        loop {
            match self.recv_event()? {
                None => return Ok(None),
                Some(Event::Mark { .. } | Event::Gap(_)) => continue,
                Some(Event::Delivery {
                    offset,
                    subject,
                    body,
                }) => return Ok(Some((offset, subject, body, self.last_bt))),
            }
        }
    }

    /// Block until the next event — a delivery OR a `Mark`; `Ok(None)` if the broker
    /// closes.
    ///
    /// A read that TIMES OUT part-way through a frame (see
    /// [`set_read_timeout`](Subscription::set_read_timeout)) is resumable, not a
    /// desync: the bytes that arrived stay on the subscription and the next call
    /// completes the frame from where the timeout left it, so the caller sees the
    /// whole record once — never a prefix dropped on the floor and the tail of a body
    /// parsed as the next header. Any other error discards the partial frame; the
    /// stream is not resumable past it.
    pub fn recv_event(&mut self) -> io::Result<Option<Event>> {
        let Some(p) = self.rx.next_frame(&mut self.stream)? else {
            return Ok(None);
        };
        let (resp, bt_ms) = decode_reply_with_bt(&p)?;
        match resp {
            Response::Delivery {
                offset,
                subject,
                body,
            } => {
                self.last_bt = bt_ms;
                self.last_origin = decode_delivery_origin(&p);
                Ok(Some(Event::Delivery {
                    offset,
                    subject,
                    body,
                }))
            }
            Response::Mark {
                next,
                head,
                durable,
                ..
            } => {
                self.marked = true;
                if durable.is_some() {
                    self.durable = durable;
                }
                Ok(Some(Event::Mark {
                    next,
                    head,
                    durable,
                }))
            }
            Response::Gap(g) => {
                self.gap = Some(match self.gap {
                    Some(before) => before.and(g),
                    None => g,
                });
                Ok(Some(Event::Gap(g)))
            }
            other => Err(refused(other)),
        }
    }

    /// [`recv`](Self::recv) that turns a DEAD LINK into an error instead of silence:
    /// the first `Mark` this subscription reads arms a read `deadline` on its socket
    /// through `closer` (the [`Closer`] from [`connect`], or this subscription's own
    /// `closer()`), and from then on `deadline` with no byte arriving fails the call
    /// `WouldBlock`/`TimedOut`. Every `Mark` re-arms it.
    ///
    /// A `Subscribe`/`SubscribeGroup` tail is sent a `Mark` when it catches up and
    /// after every [`IDLE_MARK`](crate::broker::IDLE_MARK) with nothing to deliver, so a
    /// healthy idle subscription keeps answering the deadline, and one whose peer
    /// vanished without a FIN — power loss, a NAT or Wi-Fi change, a frozen relay —
    /// times out instead of parking for good. Pass a deadline a few idle intervals
    /// long ([`IDLE_MARK_DEADLINE`](crate::broker::IDLE_MARK_DEADLINE)).
    ///
    /// ARMING ON A MARK IS THE VERSION CHECK. A broker that predates idle marks never
    /// marks a tail, so the deadline is never armed and this is exactly `recv` — no
    /// timeouts against a long-lived older broker. The other side of that: until the
    /// first `Mark` (a backlog still being delivered) the subscription is unbounded.
    ///
    /// A timeout leaves any partial frame resumable (see
    /// [`recv_event`](Self::recv_event)), but a caller that set this deadline means
    /// "the link is gone": drop the subscription and resubscribe.
    ///
    /// A broker that sent a `Mark` and hung up before the re-arm leaves nothing to arm
    /// ([`Closer::set_read_timeout`]): the call goes on to read what the broker sent,
    /// then its close (`Ok(None)`).
    ///
    /// # Errors
    /// As `recv`; the timeout above; the `setsockopt` that arms it, but for a socket the
    /// broker already hung up.
    pub fn recv_live(&mut self, closer: &Closer, deadline: Duration) -> io::Result<Option<Record>> {
        loop {
            match self.recv_live_event(closer, deadline)? {
                None => return Ok(None),
                Some(Event::Mark { .. } | Event::Gap(_)) => {}
                Some(Event::Delivery {
                    offset,
                    subject,
                    body,
                }) => return Ok(Some((offset, subject, body))),
            }
        }
    }

    /// [`recv_live`](Self::recv_live)'s rule, event by event: the next event, a delivery
    /// OR a `Mark`, where every `Mark` arms (re-arms) the read `deadline` through
    /// `closer` before it is returned. For a reader that needs what a mark says as well
    /// as the liveness bound — the DURABLE head a durable mark carries (a notifier that
    /// pages only what is on stable media), or its `next` (a view that is exact up to
    /// it) — so it keeps astream's liveness rule instead of re-implementing it over
    /// [`recv_event`](Self::recv_event). `recv_live` is this with the marks skipped.
    ///
    /// # Errors
    /// As [`recv_live`](Self::recv_live).
    pub fn recv_live_event(
        &mut self,
        closer: &Closer,
        deadline: Duration,
    ) -> io::Result<Option<Event>> {
        let event = self.recv_event()?;
        if matches!(event, Some(Event::Mark { .. })) {
            closer.set_read_timeout(Some(deadline))?;
        }
        Ok(event)
    }
}

#[cfg(unix)]
impl Subscription<UnixStream> {
    /// Bound how long [`recv`](Self::recv) / [`recv_event`](Self::recv_event) block
    /// with nothing arriving: past it the read returns `WouldBlock`/`TimedOut`, which
    /// is how [`drain`] stops on an idle stream instead of parking forever.
    ///
    /// The timeout is on the SOCKET, so it can land part-way through a record. That
    /// is not a desync: the partial frame stays on the subscription and the next
    /// `recv` finishes it (see [`recv_event`](Self::recv_event)), so the same `sub`
    /// is safe to drain from again.
    ///
    /// On a socket the broker already hung up there is nothing to bound, and that is
    /// no error (see [`Closer::set_read_timeout`]).
    pub fn set_read_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        unless_hung_up(self.stream.set_read_timeout(d), &self.stream)
    }
}

impl Subscription<TcpStream> {
    /// The TCP twin of [`Subscription::set_read_timeout`].
    pub fn set_read_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        unless_hung_up(self.stream.set_read_timeout(d), &self.stream)
    }

    /// The TCP twin of [`Subscription::closer`]: a [`Closer`] on a duplicate of this
    /// subscription's socket, so another thread can end a `recv` parked on it.
    pub fn closer(&self) -> io::Result<Closer> {
        Closer::tcp(&self.stream)
    }
}

#[cfg(feature = "aead")]
impl Subscription<astream_aead::SealedStream<TcpStream>> {
    /// The SEALED twin of [`Subscription::set_read_timeout`] — the same idle window
    /// for a subscription from `connect_tcp_sealed`, `connect_tcp_handshake` or
    /// `connect_tcp_identity` (all three hand back a `SealedStream<TcpStream>`), so
    /// a consumer on the sealed transport can bound [`drain`] too.
    ///
    /// The timeout is set on the TCP socket UNDER the record layer, so it can land
    /// part-way through a sealed record as well as part-way through a frame. Both
    /// layers resume: the record layer keeps its partial record and its sequence
    /// counter (`astream_aead`'s `read_record`), and [`recv_event`](Self::recv_event)
    /// keeps the partial frame.
    pub fn set_read_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        let socket = self.stream.get_ref();
        unless_hung_up(socket.set_read_timeout(d), socket)
    }

    /// The SEALED twin of [`Subscription::closer`]. The duplicate is of the TCP
    /// socket UNDER the record layer — never a second `SealedStream`, which would be a
    /// second record sequence over one socket — because shutting that socket down is
    /// what unparks the reader, and it is all the closer needs.
    pub fn closer(&self) -> io::Result<Closer> {
        Closer::tcp(self.stream.get_ref())
    }
}

/// Any byte stream a broker connection can ride, so a caller that picks its transport
/// at RUNTIME — a flag, a config file — has ONE code path per verb rather than one per
/// wire. Blanket-implemented for every `Read + Write + Send` type. `Send` is a
/// supertrait because a subscription is typically pumped by a thread of its own, and
/// every transport this crate builds is `Send`.
pub trait AnyStream: Read + Write + Send {}
impl<T: Read + Write + Send> AnyStream for T {}

/// A [`Client`] whose transport has been erased — what [`connect`] returns. It IS a
/// `Client`, so it keeps the same in-step rules: the latch, and the owed-ack count
/// ([`Client::owed_acks`], [`AcksOwed`]).
pub type AnyClient = Client<Box<dyn AnyStream>>;

/// A [`Subscription`] whose transport has been erased — what an [`AnyClient`]'s
/// `subscribe` / `subscribe_group` / `fork_subscribe` return. Its idle window and its
/// shutdown live on the [`Closer`] that came with the client.
pub type AnySubscription = Subscription<Box<dyn AnyStream>>;

/// How a client reaches the broker: the runtime choice [`connect`] dispatches on.
///
/// EVERY VARIANT EXISTS IN EVERY BUILD. The sealed and handshake wires need the `aead`
/// and `handshake` features, but their variants are not cfg-gated: Cargo unifies
/// features ADDITIVELY across a build graph, so a variant that appeared only when some
/// other crate in the graph switched `aead` on would break every exhaustive `match`
/// written against the default build. [`connect`] refuses a transport this build cannot
/// speak with `ErrorKind::Unsupported` naming the missing feature instead — so a config
/// that says "sealed" still parses and still redacts its key, and fails loudly at the
/// one place it matters, never by quietly speaking plaintext.
///
/// Deliberately NOT `#[non_exhaustive]`, for the opposite reason: a caller's exhaustive
/// match over transports (what to serve, what to name) is where a NEW wire should break
/// the build and be decided on, not fall through a wildcard arm into some other wire's
/// behaviour. Static-identity connections (`connect_tcp_identity`) are not a variant:
/// they carry a keypair and a pinned host key rather than a pre-shared key, and no
/// runtime-chosen caller of this enum serves them yet.
///
/// `Debug` NEVER prints a key: it names the variant and says the key is redacted, so a
/// config logged on a bad day does not put the fleet's pre-shared key in a file.
#[derive(Clone)]
pub enum Transport {
    /// A Unix-domain socket at a filesystem path: same machine, unsealed (the socket
    /// path's permissions scope who can reach it). Unix hosts only — elsewhere
    /// [`connect`] refuses it.
    Unix,
    /// PLAINTEXT TCP to `host:port` — a trusted network only (as
    /// [`Client::connect_tcp`]).
    Tcp,
    /// TCP inside the XChaCha20-Poly1305 sealed record layer under this 32-byte
    /// pre-shared key (as `Client::connect_tcp_sealed`; feature `aead`). Boxed so
    /// moving or cloning the config does not copy the key around the stack.
    Sealed(Box<[u8; 32]>),
    /// The sealed wire behind the Rung-7 forward-secret handshake: an ephemeral X25519
    /// key agreement authenticated by this 32-byte pre-shared key (as
    /// `Client::connect_tcp_handshake`; feature `handshake`).
    Handshake(Box<[u8; 32]>),
}

impl std::fmt::Debug for Transport {
    /// The variant, and never the key.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Transport::Unix => "Unix",
            Transport::Tcp => "Tcp",
            Transport::Sealed(_) => "Sealed(<key redacted>)",
            Transport::Handshake(_) => "Handshake(<key redacted>)",
        })
    }
}

/// Ends a connection from outside the thread using it, and bounds how long that
/// thread's I/O may park — the one handle on the SOCKET under a client or subscription
/// whose stream has been erased ([`connect`]) or wrapped (a sealed record layer).
///
/// It holds a DUPLICATE descriptor of the socket. For a sealed or handshake connection
/// that is the TCP socket UNDER the record layer — never a second `SealedStream`, which
/// would be a second record sequence over one socket. Shutdown and the socket timeouts
/// are properties of the socket rather than of a descriptor, so everything done through
/// the closer applies to the connection it came from, and keeps applying after
/// `subscribe` consumes the client. Dropping a closer does nothing to the connection;
/// [`close`](Self::close) is explicit. `Send + Sync`: one closer can be shared (an
/// `Arc`) with a watchdog.
///
/// The [`AnyClient`] that [`connect`] hands back beside it shares that duplicate (it is
/// how the client's [`try_recv_publish_ack`](Client::try_recv_publish_ack) reaches the
/// socket under its erased stream), so the duplicate is closed when both are gone.
#[derive(Clone, Debug)]
pub struct Closer {
    socket: Arc<Socket>,
}

/// The socket a [`Closer`] duplicated.
#[derive(Debug)]
enum Socket {
    #[cfg(unix)]
    Unix(UnixStream),
    Tcp(TcpStream),
    #[cfg(feature = "stream")]
    Stream(crate::stream_link::LinkEnd),
}

impl Socket {
    /// Put the socket into non-blocking mode (`on`) or back into blocking mode: a
    /// property of the socket, which the stream it was duplicated from reads and writes
    /// in too (see [`Nowait::Socket`]).
    fn set_nonblocking(&self, on: bool) -> io::Result<()> {
        match self {
            #[cfg(unix)]
            Socket::Unix(s) => s.set_nonblocking(on),
            Socket::Tcp(s) => s.set_nonblocking(on),
            #[cfg(feature = "stream")]
            Socket::Stream(s) => s.set_nonblocking(on),
        }
    }
}

impl Closer {
    /// The closer's duplicate is kept out of every child (`astream_sys::close_on_fork`):
    /// a child's exec-time close of a copy, under a descriptor scan, drains the socket.
    #[cfg(unix)]
    fn unix(s: &UnixStream) -> io::Result<Closer> {
        let dup = s.try_clone()?;
        kept_from_children(&dup)?;
        Ok(Closer {
            socket: Arc::new(Socket::Unix(dup)),
        })
    }

    fn tcp(s: &TcpStream) -> io::Result<Closer> {
        let dup = s.try_clone()?;
        kept_from_children(&dup)?;
        Ok(Closer {
            socket: Arc::new(Socket::Tcp(dup)),
        })
    }

    /// Shut the socket down in BOTH directions: a `recv` (or a request's read) parked
    /// on it returns — `Ok(None)` at a frame boundary, an error part-way through one —
    /// and the broker sees the peer go away, which releases its side of the connection
    /// (and fires a registered last will). Idempotent: closing an already-closed socket
    /// is not an error, and nothing is reported.
    pub fn close(&self) {
        let _ = match &*self.socket {
            #[cfg(unix)]
            Socket::Unix(s) => s.shutdown(std::net::Shutdown::Both),
            Socket::Tcp(s) => s.shutdown(std::net::Shutdown::Both),
            #[cfg(feature = "stream")]
            Socket::Stream(s) => s.shutdown(std::net::Shutdown::Both),
        };
    }

    /// Bound how long a read on this connection parks with nothing arriving:
    /// `SO_RCVTIMEO` on the socket, so it applies to every read the client or
    /// subscription makes from now on (`None` clears it). Past it the read fails
    /// `WouldBlock`/`TimedOut`.
    ///
    /// On a SUBSCRIPTION that is an idle window, and a resumable one: the partial frame
    /// stays on the subscription ([`Subscription::recv_event`]) and the record layer
    /// keeps its partial record, so [`take`] / [`drain`] can stop and come back. On a
    /// request/reply CLIENT it is a deadline and nothing more: a request that timed out
    /// may still be answered late, so the connection is no longer in step with its
    /// replies, and the client says so — every later request on it fails `BrokenPipe`
    /// without being sent (see [`Client`]). Reconnect. That is what turns a broker that
    /// accepts and never answers from a caller parked forever into an error.
    ///
    /// A connection the broker ALREADY hung up — it answered and closed, refused a
    /// subscription, or marked a tail and went away — has nothing left to bound, and
    /// setting the bound there is no error when Apple positively observes both socket
    /// directions ended: its reads return buffered bytes, then end of stream. macOS
    /// can refuse socket options in that state with `EINVAL`; the errno alone does
    /// not establish hangup. If a zero-wait socket poll cannot establish both ends,
    /// the original refusal is returned.
    ///
    /// # Errors
    /// The `setsockopt`, but for that refusal; a zero duration is `InvalidInput` (std's
    /// own refusal, which carries no OS error).
    pub fn set_read_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        match &*self.socket {
            #[cfg(unix)]
            Socket::Unix(s) => unless_hung_up(s.set_read_timeout(d), s),
            Socket::Tcp(s) => unless_hung_up(s.set_read_timeout(d), s),
            #[cfg(feature = "stream")]
            Socket::Stream(s) => s.set_read_timeout(d),
        }
    }

    /// Bound how long a write on this connection parks on a full send buffer (a broker
    /// that stopped reading): `SO_SNDTIMEO` on the socket, `None` clears it. A write
    /// that times out may have sent PART of a frame, so the connection is no longer
    /// framed: a client refuses every later request on it (`BrokenPipe`); reconnect.
    ///
    /// On a connection the broker already hung up there is nothing to bound, and that
    /// is no error when both ends are positively observed closed (see
    /// [`set_read_timeout`](Self::set_read_timeout)): a write there fails instead of
    /// waiting for buffer space.
    ///
    /// # Errors
    /// The `setsockopt`, but for that refusal; a zero duration is `InvalidInput` (std's
    /// own refusal, which carries no OS error).
    pub fn set_write_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        match &*self.socket {
            #[cfg(unix)]
            Socket::Unix(s) => unless_hung_up(s.set_write_timeout(d), s),
            Socket::Tcp(s) => unless_hung_up(s.set_write_timeout(d), s),
            #[cfg(feature = "stream")]
            Socket::Stream(s) => s.set_write_timeout(d),
        }
    }
}

/// Preserve `socket`'s timeout refusal `set` unless Apple positively observes that
/// BOTH socket directions have ended. `EINVAL` alone is not evidence: a socket filter
/// can refuse a valid timeout before the option is applied, including on a live
/// connection whose previous timeout was `None`. An uncertain/failed poll keeps that
/// error. The probe is lazy: success, zero-duration validation, and other errors never
/// poll. It takes the socket, never a closure that polls it, so the verified lane
/// resolves the probe at every caller.
#[cfg(target_vendor = "apple")]
pub(crate) fn unless_hung_up(
    set: io::Result<()>,
    socket: &impl std::os::fd::AsFd,
) -> io::Result<()> {
    if matches!(&set, Err(e) if e.raw_os_error() == Some(XNU_EINVAL)) && socket_hung_up(socket) {
        return Ok(());
    }
    set
}

/// Off Apple a refusal is always the error (see the Apple twin).
#[cfg(not(target_vendor = "apple"))]
pub(crate) fn unless_hung_up<S>(set: io::Result<()>, _socket: &S) -> io::Result<()> {
    set
}

#[cfg(target_vendor = "apple")]
fn socket_hung_up(socket: &impl std::os::fd::AsFd) -> bool {
    #[cfg(test)]
    tests::PROBES.with(|n| n.set(n.get().saturating_add(1)));
    astream_sys::socket_hung_up(socket.as_fd())
}

/// `EINVAL` in XNU's `<sys/errno.h>` (this crate takes no `libc`).
#[cfg(target_vendor = "apple")]
const XNU_EINVAL: i32 = 22;

/// Open ONE connection to `endpoint` over `transport` — a socket path for
/// [`Transport::Unix`], `host:port` for the rest — and return it with its transport
/// erased, together with the [`Closer`] that ends it and bounds its I/O.
///
/// The closer is made HERE, at connect time, from a duplicate of the socket under
/// whatever wrapper the transport adds, because once the stream is boxed nothing can
/// reach that socket again — and it outlives the `subscribe` that consumes the client,
/// which is when a caller needs it most (to end a `recv` parked on another thread, or
/// to give a group subscription its idle window).
///
/// `connect_timeout` bounds ESTABLISHING the connection, and nothing after it:
///
/// - **TCP** (all three TCP transports): each address the endpoint resolves to is tried
///   in turn with `TcpStream::connect_timeout` (see
///   [`Client::connect_tcp_timeout`]), so a black-holed address fails `TimedOut` after
///   the bound instead of after the OS's SYN-retry schedule. The bound is per address,
///   and name resolution is not bounded (std's resolver has no timeout): an IP-literal
///   endpoint makes it a hard bound.
/// - **Sealed / handshake**: the bound also REPLACES the built-in deadline on the
///   transport's handshake I/O (5 s sealed, 10 s key agreement), so a peer that accepts
///   and never answers the hello costs `connect_timeout`, not the default.
/// - **Unix**: not applied. std has no bounded Unix-socket connect; a local connect
///   fails at once when nothing listens, and can park only while a LIVE listener's
///   accept backlog is full.
///
/// `None` is exactly each transport's own constructor — [`Client::connect`],
/// [`Client::connect_tcp`], `Client::connect_tcp_sealed`,
/// `Client::connect_tcp_handshake` — including their built-in handshake deadlines.
/// Either way every stream comes back BLOCKING: bound requests and deliveries with
/// [`Closer::set_read_timeout`] / [`Closer::set_write_timeout`]. Every TCP transport
/// gets `TCP_NODELAY`, as every TCP constructor here does.
///
/// # Errors
/// `Unsupported`, naming what is missing, for a transport this build cannot speak
/// ([`Transport::Sealed`] without the `aead` feature, [`Transport::Handshake`] without
/// `handshake`, [`Transport::Unix`] off a unix host); `InvalidInput` for a zero
/// `connect_timeout`; otherwise the connect, the handshake (a broker without the key is
/// refused HERE, not at the first verb), or the descriptor duplication the closer needs.
pub fn connect(
    transport: &Transport,
    endpoint: &str,
    connect_timeout: Option<Duration>,
) -> io::Result<(AnyClient, Closer)> {
    if connect_timeout == Some(Duration::ZERO) {
        // Refused up front so every transport says the same thing: std refuses a zero
        // TCP connect timeout itself, but a Unix connect would silently ignore it.
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "a zero connect timeout bounds nothing: pass None for the OS default, or a positive duration",
        ));
    }
    match transport {
        Transport::Unix => connect_unix(endpoint),
        Transport::Tcp => {
            let s = dial_tcp(endpoint, connect_timeout)?;
            let closer = Closer::tcp(&s)?;
            Ok(erase(s, closer))
        }
        Transport::Sealed(key) => connect_sealed(endpoint, key.as_ref(), connect_timeout),
        Transport::Handshake(key) => connect_handshake(endpoint, key.as_ref(), connect_timeout),
    }
}

/// A client over a stream the embedder already authenticated, and the [`Closer`] that ends it
/// and bounds its I/O through the stream itself: no descriptor is duplicated. The stream comes
/// back as it was handed over. The broker's side is
/// [`Broker::serve_stream`](crate::Broker::serve_stream).
#[cfg(feature = "stream")]
#[must_use]
pub fn connect_stream(link: Arc<dyn crate::stream_link::StreamLink>) -> (AnyClient, Closer) {
    connect_stream_end(crate::stream_link::LinkEnd::new(link))
}

#[cfg(feature = "stream")]
pub(crate) fn connect_stream_end(end: crate::stream_link::LinkEnd) -> (AnyClient, Closer) {
    let closer = Closer {
        socket: Arc::new(Socket::Stream(end.clone())),
    };
    erase(end, closer)
}

/// Box a connected stream behind [`AnyStream`], beside its closer. The box hides the
/// socket from the client, so the client shares the closer's duplicate of it, for
/// [`Client::try_recv_publish_ack`] ([`Nowait::Socket`]): no second descriptor.
fn erase<S: AnyStream + 'static>(stream: S, closer: Closer) -> (AnyClient, Closer) {
    let mut client: AnyClient = Client::from_stream(Box::new(stream));
    client.nowait = Nowait::Socket(Arc::clone(&closer.socket));
    (client, closer)
}

#[cfg(unix)]
fn connect_unix(endpoint: &str) -> io::Result<(AnyClient, Closer)> {
    let s = UnixStream::connect(endpoint)?;
    kept_from_children(&s)?;
    let closer = Closer::unix(&s)?;
    Ok(erase(s, closer))
}

#[cfg(not(unix))]
fn connect_unix(_endpoint: &str) -> io::Result<(AnyClient, Closer)> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "Transport::Unix needs a unix host (std has no Unix-domain sockets here); use Transport::Tcp",
    ))
}

#[cfg(feature = "aead")]
fn connect_sealed(
    endpoint: &str,
    key: &[u8; 32],
    connect_timeout: Option<Duration>,
) -> io::Result<(AnyClient, Closer)> {
    let stream = dial_tcp(endpoint, connect_timeout)?;
    let sealed = seal_tcp(
        stream,
        *key,
        connect_timeout.unwrap_or(SEALED_HANDSHAKE_TIMEOUT),
    )?;
    let closer = Closer::tcp(sealed.get_ref())?;
    Ok(erase(sealed, closer))
}

/// Without `aead` there is no record layer to seal with, and a sealed transport must
/// never quietly become a plaintext one.
#[cfg(not(feature = "aead"))]
fn connect_sealed(
    _endpoint: &str,
    _key: &[u8; 32],
    _connect_timeout: Option<Duration>,
) -> io::Result<(AnyClient, Closer)> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "Transport::Sealed needs astream-broker built with the `aead` feature",
    ))
}

#[cfg(feature = "handshake")]
fn connect_handshake(
    endpoint: &str,
    psk: &[u8; 32],
    connect_timeout: Option<Duration>,
) -> io::Result<(AnyClient, Closer)> {
    let stream = dial_tcp(endpoint, connect_timeout)?;
    let sealed = agree_tcp(
        stream,
        psk,
        connect_timeout.unwrap_or(KEY_AGREEMENT_TIMEOUT),
    )?;
    let closer = Closer::tcp(sealed.get_ref())?;
    Ok(erase(sealed, closer))
}

/// Without `handshake` there is no key agreement, and falling back to the plain
/// sealed wire would silently drop the forward secrecy the caller asked for.
#[cfg(not(feature = "handshake"))]
fn connect_handshake(
    _endpoint: &str,
    _psk: &[u8; 32],
    _connect_timeout: Option<Duration>,
) -> io::Result<(AnyClient, Closer)> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "Transport::Handshake needs astream-broker built with the `handshake` feature",
    ))
}

#[cfg(feature = "identity")]
pub(crate) fn connect_identity(
    endpoint: &str,
    identity: &astream_aead::IdentityKeypair,
    expected_server: &[u8; astream_aead::ID_PUB_LEN],
    connect_timeout: Option<Duration>,
) -> io::Result<(AnyClient, Closer)> {
    if connect_timeout == Some(Duration::ZERO) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "a zero connect timeout bounds nothing: pass None for the OS default, or a positive duration",
        ));
    }
    let stream = dial_tcp(endpoint, connect_timeout)?;
    let hs_timeout = connect_timeout.unwrap_or(Duration::from_secs(10));
    stream.set_read_timeout(Some(hs_timeout))?;
    stream.set_write_timeout(Some(hs_timeout))?;
    let sealed = astream_aead::client_identity_handshake(stream, identity, expected_server)?;
    sealed.get_ref().set_read_timeout(None)?;
    sealed.get_ref().set_write_timeout(None)?;
    let closer = Closer::tcp(sealed.get_ref())?;
    Ok(erase(sealed, closer))
}

#[cfg(test)]
mod tests {
    use super::{RecvBuf, READ_CHUNK};
    use crate::proto::read_frame;
    use astream_wire::{Frame, HEADER_SIZE, MAX_PAYLOAD_LEN};
    use std::io::{self, Read};

    #[cfg(target_vendor = "apple")]
    thread_local! {
        /// How many times `socket_hung_up` polled on this thread: the probe `unless_hung_up`
        /// makes only for an `EINVAL` refusal.
        pub(super) static PROBES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    }

    /// A stream that plays `script` one read at a time: `Some(n)` hands out the next
    /// `n` bytes (fewer at the end), `None` is a read timeout. Past the script it is
    /// at EOF.
    struct Scripted {
        bytes: Vec<u8>,
        pos: usize,
        script: Vec<Option<usize>>,
        step: usize,
    }

    impl Scripted {
        fn new(bytes: Vec<u8>, script: Vec<Option<usize>>) -> Scripted {
            Scripted {
                bytes,
                pos: 0,
                script,
                step: 0,
            }
        }
    }

    impl Read for Scripted {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            let Some(&step) = self.script.get(self.step) else {
                return Ok(0);
            };
            self.step += 1;
            let Some(n) = step else {
                return Err(io::Error::new(io::ErrorKind::TimedOut, "scripted"));
            };
            let n = n.min(buf.len()).min(self.bytes.len() - self.pos);
            buf[..n].copy_from_slice(&self.bytes[self.pos..self.pos + n]);
            self.pos += n;
            Ok(n)
        }
    }

    fn framed(payloads: &[Vec<u8>]) -> Vec<u8> {
        payloads
            .iter()
            .flat_map(|p| Frame::new(p.clone()).encode().unwrap())
            .collect()
    }

    /// Every frame comes back whole and in order however the bytes are split — with a
    /// timeout after every single byte, or with every frame in one read — and a frame
    /// bigger than the resting buffer gives its growth back.
    #[test]
    fn frames_survive_any_split_and_a_timeout_at_every_byte() {
        let payloads = vec![b"a".to_vec(), vec![], vec![7u8; 70_000], b"z".to_vec()];
        let bytes = framed(&payloads);
        let byte_by_byte = (0..bytes.len()).flat_map(|_| [Some(1), None]).collect();
        let all_at_once = vec![Some(usize::MAX); bytes.len()];
        for script in [byte_by_byte, all_at_once] {
            let mut s = Scripted::new(bytes.clone(), script);
            let mut rx = RecvBuf::default();
            let mut got = Vec::new();
            loop {
                match rx.next_frame(&mut s) {
                    Ok(Some(p)) => got.push(p),
                    Ok(None) => break,
                    Err(e) if e.kind() == io::ErrorKind::TimedOut => continue,
                    Err(e) => panic!("{e}"),
                }
            }
            assert_eq!(got, payloads);
            assert!(rx.buf.len() <= READ_CHUNK);
        }
    }

    /// A stream cut at EVERY byte of a frame is classified as `proto::read_frame`
    /// classifies it: only a cut before the first byte is a close (`Ok(None)`); a cut
    /// after any of its bytes — inside the header as well as inside the payload — is
    /// a frame cut short (`UnexpectedEof`).
    #[test]
    fn a_close_mid_frame_is_classified_like_read_frame() {
        // A captured timeout refusal is still an error on a live or half-closed
        // socket. Only the actual both-directions hangup may suppress Apple EINVAL.
        #[cfg(target_vendor = "apple")]
        {
            use super::{socket_hung_up, unless_hung_up, XNU_EINVAL};
            use std::net::Shutdown;
            use std::os::unix::net::UnixStream;

            let (ours, peer) = UnixStream::pair().unwrap();
            let refused = || Err(io::Error::from_raw_os_error(XNU_EINVAL));
            let probes = || PROBES.with(std::cell::Cell::get);
            assert!(!socket_hung_up(&ours));
            assert_eq!(
                unless_hung_up(refused(), &ours).unwrap_err().raw_os_error(),
                Some(XNU_EINVAL),
                "negative evidence preserves the original error"
            );
            peer.shutdown(Shutdown::Write).unwrap();
            assert!(!socket_hung_up(&ours), "read EOF is not write shutdown");
            assert_eq!(
                unless_hung_up(refused(), &ours).unwrap_err().raw_os_error(),
                Some(XNU_EINVAL)
            );
            drop(peer);
            assert!(socket_hung_up(&ours));
            let before = probes();
            unless_hung_up(refused(), &ours).unwrap();
            assert_eq!(probes(), before + 1, "an EINVAL refusal polls, once");
            // On the hung-up socket, which would excuse a refusal: success stays
            // success, and any other error stays that error, and neither polls (the
            // probe is lazy). NC: a probe made before the refusal is read polls them.
            unless_hung_up(Ok(()), &ours).unwrap();
            for error in [
                io::Error::new(io::ErrorKind::InvalidInput, "zero timeout"),
                io::Error::from_raw_os_error(5),
            ] {
                let kind = error.kind();
                let errno = error.raw_os_error();
                let got = unless_hung_up(Err(error), &ours).unwrap_err();
                assert_eq!((got.kind(), got.raw_os_error()), (kind, errno));
            }
            assert_eq!(probes(), before + 1, "success and other errors never poll");
        }
        let bytes = framed(&[b"payload".to_vec()]);
        for cut in 0..bytes.len() {
            let mut s = Scripted::new(bytes[..cut].to_vec(), vec![Some(usize::MAX)]);
            let ours = RecvBuf::default().next_frame(&mut s).map_err(|e| e.kind());
            let theirs = read_frame(&mut &bytes[..cut]).map_err(|e| e.kind());
            assert_eq!(ours, theirs, "cut at {cut}");
            let expected = if cut == 0 {
                Ok(None)
            } else {
                Err(io::ErrorKind::UnexpectedEof)
            };
            assert_eq!(
                ours, expected,
                "cut at {cut} (header is {HEADER_SIZE} bytes)"
            );
        }
    }

    /// A broker that answers `Hello` with a nonce, and holds every `Attach`
    /// acknowledgement back until `ring` of them have arrived — reading earlier gets
    /// `WouldBlock`, as a socket whose peer has not answered yet would.
    #[cfg(feature = "cap")]
    struct RingBroker {
        written: Vec<u8>,
        ring: usize,
        nonce: [u8; 32],
        pending: Vec<u8>,
        answered: usize,
    }

    #[cfg(feature = "cap")]
    impl RingBroker {
        fn requests(&self) -> Vec<crate::proto::Request> {
            let mut at = &self.written[..];
            let mut out = Vec::new();
            while let Some(p) = read_frame(&mut at).unwrap() {
                out.push(crate::proto::decode_request(&p).unwrap());
            }
            out
        }
    }

    #[cfg(feature = "cap")]
    impl io::Write for RingBroker {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            self.written.extend_from_slice(buf);
            Ok(buf.len())
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    #[cfg(feature = "cap")]
    impl Read for RingBroker {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            use crate::proto::{encode_response, Request, Response};
            if self.pending.is_empty() {
                let reqs = self.requests();
                let reply = |r: &Response| Frame::new(encode_response(r)).encode().unwrap();
                if self.answered == 0 && reqs == [Request::Hello] {
                    self.pending = reply(&Response::Nonce {
                        ext: crate::proto::NonceExt::default(),
                        log: None,
                        nonce: self.nonce.to_vec(),
                    });
                } else if self.answered == 1 && reqs.len() == 1 + self.ring {
                    for _ in 0..self.ring {
                        self.pending.extend(reply(&Response::Mark {
                            next: 3,
                            head: 3,
                            resume: String::new(),
                            durable: None,
                            oldest: None,
                        }));
                    }
                } else {
                    return Err(io::Error::new(io::ErrorKind::WouldBlock, "not yet"));
                }
                self.answered += 1;
            }
            let n = self.pending.len().min(buf.len());
            buf[..n].copy_from_slice(&self.pending[..n]);
            self.pending.drain(..n);
            Ok(n)
        }
    }

    /// `attach_all` sends ONE `Hello` and then every `Attach` before it reads an
    /// acknowledgement — each proof over that one nonce — so a ring costs two round
    /// trips. A client that waited for each acknowledgement (or said `Hello` per
    /// grant, as `attach` once did) reads before the broker answers and fails here.
    #[cfg(feature = "cap")]
    #[test]
    fn attach_all_pipelines_a_ring_under_one_hello() {
        use crate::proto::Request;
        let tags = [[1u8; 32], [2u8; 32], [3u8; 32]];
        let grants = ["ro:/a/>", "ro:/b/>", "rw:/c/>"];
        let mut c = super::Client::from_stream(RingBroker {
            written: Vec::new(),
            ring: grants.len(),
            nonce: [9u8; 32],
            pending: Vec::new(),
            answered: 0,
        });
        let mark = c
            .attach_all(grants.iter().zip(&tags).map(|(g, t)| (*g, &t[..])))
            .unwrap();
        assert_eq!(mark, Some((3, 3)));
        let wire = c.into_stream();
        let reqs = wire.requests();
        assert_eq!(reqs[0], Request::Hello);
        assert_eq!(reqs.len(), 1 + grants.len(), "one Hello for the whole ring");
        for ((req, grant), tag) in reqs[1..].iter().zip(grants).zip(&tags) {
            let proof = astream_cap::attach_proof(tag, &[9u8; 32], grant);
            assert_eq!(
                req,
                &Request::Attach {
                    grant: grant.to_string(),
                    proof: proof.to_vec(),
                }
            );
        }
    }

    /// A header declaring more than the cap is refused on the header alone, before a
    /// byte of its payload is buffered.
    #[test]
    fn an_oversized_header_is_refused_before_its_payload_is_read() {
        let mut hdr = Frame::new(vec![]).encode().unwrap();
        hdr[4..8].copy_from_slice(&((MAX_PAYLOAD_LEN + 1) as u32).to_le_bytes());
        let mut s = Scripted::new(hdr, vec![Some(usize::MAX), Some(usize::MAX)]);
        let e = RecvBuf::default().next_frame(&mut s).unwrap_err();
        assert_eq!(e.kind(), io::ErrorKind::InvalidData);
        assert_eq!(s.step, 1, "one read: the header's");
    }

    #[test]
    fn credit_window_state_machine_preserves_invariant() {
        let mut cw = super::CreditWindow::new(4);
        assert_eq!(cw.acked_seq(), 0);
        assert_eq!(cw.next_send(), 0);
        assert_eq!(cw.credit_horizon(), 4);
        assert!(cw.can_send());

        for expected_next in 1..=4 {
            assert!(cw.try_send());
            assert_eq!(cw.next_send(), expected_next);
            assert!(cw.acked_seq() <= cw.next_send() && cw.next_send() <= cw.credit_horizon());
        }
        // Window is now exhausted (`next_send == 4 == credit_horizon`).
        assert!(!cw.can_send());
        assert!(!cw.try_send());
        assert_eq!(cw.in_flight(), 4);

        // Acknowledge 2 frames; stale ack (1) does not regress; overshooting ack (99)
        // is clamped to `next_send == 4`.
        assert_eq!(cw.record_ack(2), 2);
        assert_eq!(cw.record_ack(1), 2);
        assert_eq!(cw.in_flight(), 2);

        // Granting sliding-window credit of 4 moves horizon from 4 to `2 + 4 = 6`.
        assert_eq!(cw.grant_window(4), 6);
        // Stale credit grant (3 < 6) never regresses horizon.
        assert_eq!(cw.grant_credit(3), 6);
        assert!(cw.can_send());
        assert!(cw.try_send());
        assert_eq!(cw.next_send(), 5);
        assert_eq!(cw.record_ack(99), 5);
        assert_eq!(cw.in_flight(), 0);
    }
}

/// THE OWED-ACK GUARD. A pipelined publish leaves its ack on the stream, and the broker
/// answers a connection's requests in order, so until that ack is read every request
/// that reads its own reply would read it instead. The client counts what it owes and
/// refuses such a request with [`AcksOwed`], writing nothing and reading nothing.
///
/// Two halves. Against a REAL broker: a commit sent behind an owed publish is refused
/// and appends nothing, and goes through once the ack is read — and, the NEGATIVE
/// CONTROL, with the guard switched off (`unguarded`, which only these tests set) the
/// same commit returns the publish's offset as its own, and a commit behind a REFUSED
/// publish returns that publish's refusal as its own. Against a scripted stream that
/// records every byte written: every verb that reads its own reply is refused with the
/// count while acks are owed, with not one byte written and not one read, and the
/// count follows what was written and read — a frame refused before it is written owes
/// nothing, a write that failed owes nothing (it latched the client), a read that
/// failed zeroes what was left (it latched the client too), a refused publish's
/// `Error` pays its ack, a pipelined retire owes its ack as a publish does, and a
/// `recv_publish_ack` with nothing owed reads nothing. And [`drain`](super::drain),
/// against a real broker, asks its committer before it takes, so a drain refused for
/// an owed ack leaves its records on the subscription.
#[cfg(test)]
mod owed_acks {
    use super::{acks_owed, broker_refusal, AcksOwed, Client, Walk};
    use crate::logid::LogIdentity;
    use crate::proto::{decode_request, encode_response, read_frame, Request, Response};
    use astream_wire::{Frame, MAX_PAYLOAD_LEN};
    use std::io::{self, Read, Write};
    use std::sync::{Arc, Mutex};
    use std::time::Duration;

    /// The refusal a request behind `owed` unread acks must get: typed, of its own
    /// kind, and not a broker refusal.
    fn assert_refused_owing(what: &str, e: &io::Error, owed: u64) {
        assert_eq!(e.kind(), io::ErrorKind::ResourceBusy, "{what}: {e}");
        assert_eq!(acks_owed(e), Some(&AcksOwed { owed }), "{what}: {e:?}");
        assert!(broker_refusal(e).is_none(), "{what}: not the broker's");
    }

    /// A served broker, and the scratch directory its log and socket (`sock`) live in.
    #[cfg(unix)]
    type Served = (
        crate::test_scratch::Scratch,
        crate::Broker,
        crate::BrokerHandle,
    );

    /// A real broker over a Unix socket in its own scratch directory.
    #[cfg(unix)]
    fn broker(tag: &str) -> Served {
        let root = crate::test_scratch::Scratch::new(tag);
        let b = crate::Broker::open(root.path().join("log")).unwrap();
        let h = b.serve(root.path().join("sock")).unwrap();
        (root, b, h)
    }

    /// `send_publish`, then `commit`: the commit is refused, typed, and the next frame
    /// is still the publish's ack. Read it, and the same commit goes through and
    /// returns its OWN record's offset, the one after the publish; a head query on the
    /// same connection — answered only after every request written before it — then
    /// counts exactly the publish and one commit, so the refused commit was never sent.
    #[cfg(unix)]
    #[test]
    fn a_commit_behind_an_owed_ack_is_refused_and_sends_nothing() {
        let (root, _b, _h) = broker("owed-commit");
        let mut c = Client::connect(root.path().join("sock")).unwrap();
        c.send_publish(1, 1, "/o/a", b"owed").unwrap();
        assert_eq!(c.owed_acks(), 1);

        let e = c.commit("g", 1).unwrap_err();
        assert_refused_owing("commit", &e, 1);
        assert_eq!(c.owed_acks(), 1, "a refusal pays nothing");

        assert_eq!(
            c.recv_publish_ack().unwrap(),
            (0, false),
            "the publish's ack"
        );
        assert_eq!(c.owed_acks(), 0);
        assert_eq!(c.commit("g", 1).unwrap(), 1, "the commit's own record");
        let (rows, (next, head)) = c.fetch(0, "/o/>", 0).unwrap();
        assert_eq!(
            (rows.len(), next, head),
            (0, 0, 2),
            "one publish and one commit: the refused commit appended nothing"
        );
    }

    /// The same behind a publish the broker REFUSES: the commit is refused for the
    /// owed ack, the publish's refusal comes back where it belongs — from
    /// `recv_publish_ack`, paying the ack — and the commit then goes through.
    #[cfg(unix)]
    #[test]
    fn a_refused_owed_publish_is_answered_to_its_own_ack() {
        let (root, _b, _h) = broker("owed-refused");
        let mut c = Client::connect(root.path().join("sock")).unwrap();
        c.send_publish(1, 1, "no-slash", b"refused").unwrap();
        assert_refused_owing("commit", &c.commit("g", 0).unwrap_err(), 1);
        let e = c.recv_publish_ack().unwrap_err();
        let r = broker_refusal(&e).expect("the publish's own refusal");
        assert!(r.msg.contains("bad subject"), "{r}");
        assert_eq!(
            c.owed_acks(),
            0,
            "a refusal is a whole reply: it pays its ack"
        );
        assert_eq!(c.commit("g", 0).unwrap(), 0, "the commit's own record");
    }

    /// NEGATIVE CONTROL: the guard switched off, as every client was before it. The
    /// commit sent behind the owed publish reads the publish's ack and returns ITS
    /// offset, with no error; the commit's own ack is left for the next read. Behind a
    /// refused publish, the commit returns the publish's refusal as its own.
    #[cfg(unix)]
    #[test]
    fn without_the_guard_a_commit_takes_the_owed_publishs_answer() {
        let (root, _b, _h) = broker("owed-unguarded");
        let mut c = Client::connect(root.path().join("sock")).unwrap();
        c.unguarded = true;
        c.send_publish(1, 1, "/o/a", b"owed").unwrap();
        assert_eq!(
            c.commit("g", 1).unwrap(),
            0,
            "the PUBLISH's offset, taken for the commit's"
        );
        assert_eq!(
            c.recv_publish_ack().unwrap(),
            (1, false),
            "the commit's own ack, read as the publish's"
        );

        c.send_publish(1, 2, "no-slash", b"refused").unwrap();
        let e = c.commit("g", 2).unwrap_err();
        let r = broker_refusal(&e).expect("a refusal, but the publish's");
        assert!(r.msg.contains("bad subject"), "{r}");
    }

    /// One end of an in-memory connection: reads play `replies` (bytes the test queued),
    /// then EOF; every byte written lands in `written`, which the test keeps a handle
    /// on because a subscribing verb consumes the client. `fail_writes` fails every
    /// write, having written nothing.
    struct Recorder {
        replies: Vec<u8>,
        written: Arc<Mutex<Vec<u8>>>,
        fail_writes: bool,
    }

    impl Read for Recorder {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            let n = buf.len().min(self.replies.len());
            buf[..n].copy_from_slice(&self.replies[..n]);
            self.replies.drain(..n);
            Ok(n)
        }
    }

    impl Write for Recorder {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            if self.fail_writes {
                return Err(io::Error::new(io::ErrorKind::TimedOut, "scripted"));
            }
            self.written.lock().unwrap().extend_from_slice(buf);
            Ok(buf.len())
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    fn frame(r: &Response) -> Vec<u8> {
        Frame::new(encode_response(r)).encode().unwrap()
    }

    fn ack(offset: u64) -> Vec<u8> {
        frame(&Response::PublishAck {
            offset,
            deduped: false,
        })
    }

    /// Every request a [`Recorder`] was sent, decoded.
    fn requests(written: &Mutex<Vec<u8>>) -> Vec<Request> {
        let bytes = written.lock().unwrap().clone();
        let mut at = &bytes[..];
        let mut out = Vec::new();
        while let Some(p) = read_frame(&mut at).unwrap() {
            out.push(decode_request(&p).expect("a request this client wrote"));
        }
        out
    }

    /// A client on a [`Recorder`] that has pipelined two publishes and reads nothing
    /// yet: what is queued for it is their two acks, then `then`.
    fn owing_two(then: &[u8]) -> (Client<Recorder>, Arc<Mutex<Vec<u8>>>) {
        let written = Arc::new(Mutex::new(Vec::new()));
        let mut replies = [ack(0), ack(1)].concat();
        replies.extend_from_slice(then);
        let mut c = Client::from_stream(Recorder {
            replies,
            written: Arc::clone(&written),
            fail_writes: false,
        });
        c.send_publish(1, 1, "/o/a", b"one").unwrap();
        c.send_publish(1, 2, "/o/a", b"two").unwrap();
        assert_eq!(c.owed_acks(), 2);
        (c, written)
    }

    fn fresh_client(replies: Vec<u8>) -> (Client<Recorder>, Arc<Mutex<Vec<u8>>>) {
        let written = Arc::new(Mutex::new(Vec::new()));
        let mut client = Client::from_stream(Recorder {
            replies,
            written: Arc::clone(&written),
            fail_writes: false,
        });
        client.ext.requests = Some(crate::proto::REQUEST_FRESH_PUBLISH);
        (client, written)
    }

    fn fresh<'a>(seq: u64, body: &'a [u8]) -> super::FreshPublish<'a> {
        super::FreshPublish {
            producer_id: 7,
            producer_seq: seq,
            subject: "/fresh",
            body,
        }
    }

    #[test]
    fn fresh_send_requires_an_offer_and_preserves_fifo_refusals() {
        use crate::proto::{ERR_FRESH_FENCED, ERR_FRESH_HELD};
        let replies = [
            ack(10),
            frame(&Response::Error {
                code: ERR_FRESH_HELD,
                msg: "held".into(),
            }),
            frame(&Response::Error {
                code: ERR_FRESH_FENCED,
                msg: "fenced".into(),
            }),
            ack(11),
        ]
        .concat();
        let (mut client, written) = fresh_client(replies);
        client.ext.requests = None;
        assert!(!client.supports_fresh_publish());
        for burst in [&[][..], &[fresh(1, b"one")][..]] {
            assert_eq!(
                client.send_fresh_pipelined(burst).unwrap_err().kind(),
                io::ErrorKind::Unsupported
            );
        }
        assert!(written.lock().unwrap().is_empty());
        assert_eq!(client.owed_acks(), 0);
        client.ext.requests = Some(crate::proto::REQUEST_FRESH_PUBLISH);
        assert!(client.supports_fresh_publish());
        client.send_fresh_pipelined(&[]).unwrap();
        assert!(written.lock().unwrap().is_empty());
        client
            .send_fresh_pipelined(&[fresh(1, b"one"), fresh(2, b"two"), fresh(3, b"three")])
            .unwrap();
        assert_eq!(client.owed_acks(), 3);
        assert_eq!(client.recv_publish_ack().unwrap(), (10, false));
        let held = client.recv_publish_ack().unwrap_err();
        let held = broker_refusal(&held).unwrap();
        assert!(held.is_fresh_held() && !held.is_fresh_fenced() && !held.is_permanent());
        let fenced = client.recv_publish_ack().unwrap_err();
        let fenced = broker_refusal(&fenced).unwrap();
        assert!(fenced.is_fresh_fenced() && !fenced.is_fresh_held() && !fenced.is_permanent());
        assert_eq!(client.owed_acks(), 0);
        assert_eq!(
            client.publish(7, 4, "/ordinary", b"unchanged").unwrap(),
            (11, false)
        );
        let sent = requests(&written);
        assert_eq!(sent.len(), 4);
        for (index, body) in [b"one".as_slice(), b"two".as_slice(), b"three".as_slice()]
            .iter()
            .enumerate()
        {
            assert_eq!(
                sent[index],
                Request::FreshPublish {
                    producer_id: 7,
                    producer_seq: index as u64 + 1,
                    subject: "/fresh".into(),
                    body: body.to_vec(),
                }
            );
        }
        assert!(matches!(sent[3], Request::Publish { .. }));
    }

    #[test]
    fn fresh_send_checks_the_whole_window_and_all_frames_before_writing() {
        let (mut client, written) = fresh_client(Vec::new());
        let tiny = fresh(1, b"");
        assert!(client.send_fresh_pipelined(&vec![tiny; 513]).is_err());
        assert!(written.lock().unwrap().is_empty());
        client.owed = u64::MAX;
        assert!(client.send_fresh_pipelined(&[tiny]).is_err());
        assert_eq!(client.owed_acks(), u64::MAX);
        client.owed = 511;
        assert!(client.send_fresh_pipelined(&[tiny, tiny]).is_err());
        assert!(written.lock().unwrap().is_empty());
        client.owed = 0;
        let huge = vec![0; MAX_PAYLOAD_LEN];
        assert_eq!(
            client
                .send_fresh_pipelined(&[tiny, fresh(2, &huge)])
                .unwrap_err()
                .kind(),
            io::ErrorKind::InvalidData
        );
        assert!(
            written.lock().unwrap().is_empty(),
            "a bad later frame sends no prefix"
        );
        assert_eq!(client.owed_acks(), 0);
        drop(huge);
        client.send_fresh_pipelined(&vec![tiny; 512]).unwrap();
        assert_eq!(client.owed_acks(), 512);
        assert_eq!(requests(&written).len(), 512);
        let before = written.lock().unwrap().len();
        assert!(client.send_fresh_pipelined(&[tiny]).is_err());
        assert_eq!(written.lock().unwrap().len(), before);
    }

    #[test]
    fn fresh_send_counts_frame_headers_at_the_byte_cap() {
        struct Count(usize);
        impl Read for Count {
            fn read(&mut self, _: &mut [u8]) -> io::Result<usize> {
                Ok(0)
            }
        }
        impl Write for Count {
            fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
                self.0 += bytes.len();
                Ok(bytes.len())
            }
            fn flush(&mut self) -> io::Result<()> {
                Ok(())
            }
        }
        let mut client = Client::from_stream(Count(0));
        client.ext.requests = Some(crate::proto::REQUEST_FRESH_PUBLISH);
        let overhead = crate::proto::fresh_publish_frame_len("/fresh".len(), 0).unwrap();
        let exact = super::MAX_FRESH_PIPELINE_BYTES - overhead;
        let body = vec![0; exact + 1];
        assert_eq!(
            client
                .send_fresh_pipelined(&[fresh(1, &body)])
                .unwrap_err()
                .kind(),
            io::ErrorKind::InvalidInput
        );
        assert_eq!(client.stream.0, 0);
        assert_eq!(client.owed_acks(), 0);
        client
            .send_fresh_pipelined(&[fresh(1, &body[..exact])])
            .unwrap();
        assert_eq!(client.stream.0, super::MAX_FRESH_PIPELINE_BYTES);
        assert_eq!(client.owed_acks(), 1);
        drop(body);
        let body = vec![0; 1024 * 1024];
        let before = client.stream.0;
        assert_eq!(
            client
                .send_fresh_pipelined(&vec![fresh(2, &body); 16])
                .unwrap_err()
                .kind(),
            io::ErrorKind::InvalidInput
        );
        assert_eq!(
            client.stream.0, before,
            "individually valid frames exceed the aggregate cap"
        );
        assert_eq!(client.owed_acks(), 1);
    }

    #[test]
    fn a_partial_fresh_write_latches_unknown_outcomes() {
        struct Partial {
            left: usize,
            wrote: usize,
        }
        impl Read for Partial {
            fn read(&mut self, _: &mut [u8]) -> io::Result<usize> {
                Ok(0)
            }
        }
        impl Write for Partial {
            fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
                if self.left == 0 {
                    return Err(io::ErrorKind::BrokenPipe.into());
                }
                let n = self.left.min(bytes.len());
                self.left -= n;
                self.wrote += n;
                Ok(n)
            }
            fn flush(&mut self) -> io::Result<()> {
                Ok(())
            }
        }
        let mut client = Client::from_stream(Partial { left: 20, wrote: 0 });
        client.ext.requests = Some(crate::proto::REQUEST_FRESH_PUBLISH);
        assert_eq!(
            client
                .send_fresh_pipelined(&[fresh(1, b"one"), fresh(2, b"two")])
                .unwrap_err()
                .kind(),
            io::ErrorKind::BrokenPipe
        );
        assert_eq!(client.stream.wrote, 20);
        assert_eq!(client.owed_acks(), 0);
        assert_eq!(
            client.recv_publish_ack().unwrap_err().kind(),
            io::ErrorKind::BrokenPipe
        );
        assert_eq!(
            client.send_fresh_pipelined(&[]).unwrap_err().kind(),
            io::ErrorKind::BrokenPipe
        );
        assert_eq!(client.stream.wrote, 20);
    }

    /// EVERY request that reads its own reply is refused with the count while two acks
    /// are owed, writing nothing and reading nothing: afterwards the stream holds just
    /// the two publishes, and the two acks queued for them are read by the two
    /// `recv_publish_ack`s, in order. The client was never latched: a commit then goes
    /// through, answered by the reply queued after the acks.
    #[test]
    fn every_request_that_reads_its_own_reply_is_refused_while_acks_are_owed() {
        let log = LogIdentity {
            id: [7; 16],
            generation: 0,
        };
        type Verb = Box<dyn Fn(&mut Client<Recorder>) -> io::Result<()>>;
        let mut verbs: Vec<(&str, Verb)> = vec![
            ("hello", Box::new(|c| c.hello().map(drop))),
            ("hello_identity", Box::new(|c| c.hello_identity().map(drop))),
            ("log_identity", Box::new(|c| c.log_identity().map(drop))),
            (
                "attach_with_proof",
                Box::new(|c| c.attach_with_proof("ro:/o/>", &[0; 32]).map(drop)),
            ),
            (
                "publish",
                Box::new(|c| c.publish(1, 3, "/o/a", b"x").map(drop)),
            ),
            (
                "publish_pipelined",
                Box::new(|c| c.publish_pipelined(1, "/o/a", &[b"x"], 4).map(drop)),
            ),
            (
                "retire_subject",
                Box::new(|c| c.retire_subject(1, "/o/a").map(drop)),
            ),
            (
                "retire",
                Box::new(move |c| c.retire(1, "/o/a", 0, log).map(drop)),
            ),
            ("commit", Box::new(|c| c.commit("g", 0).map(drop))),
            (
                "process_and_produce",
                Box::new(|c| c.process_and_produce(1, 3, "/o/b", b"x", "g", 0).map(drop)),
            ),
            (
                "ack",
                Box::new(|c| super::ack(c, 1, "g", 0, "/o/b", b"x").map(drop)),
            ),
            ("will", Box::new(|c| c.will(1, 3, "/o/w", b"x").map(drop))),
            ("keepalive", Box::new(|c| c.keepalive().map(drop))),
            (
                "keepalive_if_idle",
                Box::new(|c| c.keepalive_if_idle(Duration::ZERO).map(drop)),
            ),
            ("idle_marks", Box::new(|c| c.idle_marks().map(drop))),
            (
                "subject_budget",
                Box::new(|c| c.subject_budget(1).map(drop)),
            ),
            ("fetch", Box::new(|c| c.fetch(0, "/o/>", 8).map(drop))),
            ("fetch head", Box::new(|c| c.fetch(0, "/o/>", 0).map(drop))),
            ("oldest", Box::new(|c| c.oldest("/o/>").map(drop))),
            ("last", Box::new(|c| c.last("/o/>", "", 8).map(drop))),
            (
                "last_page",
                Box::new(|c| c.last_page("/o/>", "", 8).map(drop)),
            ),
            (
                "last_walk",
                Box::new(|c| c.last_walk("/o/>", "", 8, |_| Ok(Walk::Continue)).map(drop)),
            ),
            ("last_all", Box::new(|c| c.last_all("/o/>").map(drop))),
            ("broker_times", Box::new(|c| c.broker_times().map(drop))),
            ("stats", Box::new(|c| c.stats("/o/>").map(drop))),
            (
                "fetch_stamped",
                Box::new(|c| c.fetch_stamped(0, "/o/>", 8).map(drop)),
            ),
            (
                "fetch_told_stamped",
                Box::new(|c| c.fetch_told_stamped(0, "/o/>", 8).map(drop)),
            ),
            (
                "last_stamped",
                Box::new(|c| c.last_stamped("/o/>", "", 8).map(drop)),
            ),
            (
                "last_page_stamped",
                Box::new(|c| c.last_page_stamped("/o/>", "", 8).map(drop)),
            ),
            (
                "last_all_stamped",
                Box::new(|c| c.last_all_stamped("/o/>").map(drop)),
            ),
        ];
        #[cfg(feature = "cap")]
        {
            verbs.push((
                "attach",
                Box::new(|c| c.attach("ro:/o/>", &[0; 32]).map(drop)),
            ));
            verbs.push((
                "attach_all",
                Box::new(|c| c.attach_all([("ro:/o/>", &[0u8; 32][..])]).map(drop)),
            ));
        }
        let (mut c, written) = owing_two(&ack(2));
        let sent = written.lock().unwrap().len();
        for (what, verb) in &verbs {
            let e = verb(&mut c).expect_err(what);
            assert_refused_owing(what, &e, 2);
            assert_eq!(
                written.lock().unwrap().len(),
                sent,
                "{what}: nothing written"
            );
            assert_eq!(c.owed_acks(), 2, "{what}: nothing paid");
        }
        verbs.clear();

        assert_eq!(c.recv_publish_ack().unwrap(), (0, false));
        assert_eq!(c.recv_publish_ack().unwrap(), (1, false));
        assert_eq!(c.owed_acks(), 0);
        assert_eq!(c.commit("g", 2).unwrap(), 2, "in step: its own reply");
        let reqs = requests(&written);
        assert_eq!(reqs.len(), 3, "two publishes and the commit: {reqs:?}");
        assert!(matches!(reqs[2], Request::Commit { .. }), "{reqs:?}");
    }

    /// The verbs that CONSUME the client: each is refused the same way, and the stream
    /// it would have taken over carries nothing but the two publishes. The refusal
    /// drops the client, so the stream is gone with it — closed, the two acks unread:
    /// the test's handle on what was written is the last one left.
    #[test]
    fn a_subscription_is_refused_while_acks_are_owed() {
        type Subscribe = fn(Client<Recorder>) -> io::Result<super::Subscription<Recorder>>;
        let verbs: [(&str, Subscribe); 5] = [
            ("subscribe", |c| c.subscribe(0, "/o/>")),
            ("subscribe_stamped", |c| c.subscribe_stamped(0, "/o/>")),
            ("subscribe_group", |c| c.subscribe_group("g", "/o/>")),
            ("subscribe_group_stamped", |c| {
                c.subscribe_group_stamped("g", "/o/>")
            }),
            ("fork_subscribe", |c| {
                c.fork_subscribe(0, "/o/a", b"x", "/o/>")
            }),
        ];
        for (what, verb) in verbs {
            let (c, written) = owing_two(&[]);
            let Err(e) = verb(c) else {
                panic!("{what}: subscribed past two owed acks");
            };
            assert_refused_owing(what, &e, 2);
            assert_eq!(requests(&written).len(), 2, "{what}: the publishes alone");
            assert_eq!(
                Arc::strong_count(&written),
                1,
                "{what}: the refusal dropped the client and its stream"
            );
        }
    }

    /// The count follows what was WRITTEN and READ. A publish too large to frame is
    /// refused before a byte is written and owes nothing, and the client stays in step.
    /// A `recv_publish_ack` with nothing owed is `InvalidInput` and reads nothing: the
    /// reply queued behind it is still there for the request it belongs to. A publish
    /// whose write fails owes nothing — it latched the client, so the next request and
    /// the next `recv_publish_ack` alike are `BrokenPipe`, never `AcksOwed`.
    #[test]
    fn the_count_follows_what_was_written_and_read() {
        let written = Arc::new(Mutex::new(Vec::new()));
        let mut c = Client::from_stream(Recorder {
            replies: ack(5),
            written: Arc::clone(&written),
            fail_writes: false,
        });
        let huge = vec![0u8; MAX_PAYLOAD_LEN + 1];
        let e = c.send_publish(1, 1, "/o/a", &huge).unwrap_err();
        assert_eq!(e.kind(), io::ErrorKind::InvalidData, "{e}");
        assert_eq!(c.owed_acks(), 0, "an unframeable publish owes nothing");
        assert!(written.lock().unwrap().is_empty());

        let e = c.recv_publish_ack().unwrap_err();
        assert_eq!(e.kind(), io::ErrorKind::InvalidInput, "{e}");
        assert!(acks_owed(&e).is_none());
        assert_eq!(
            c.commit("g", 5).unwrap(),
            5,
            "the queued reply was not read"
        );

        let mut c = Client::from_stream(Recorder {
            replies: ack(0),
            written: Arc::new(Mutex::new(Vec::new())),
            fail_writes: true,
        });
        let e = c.send_publish(1, 1, "/o/a", b"lost").unwrap_err();
        assert_eq!(e.kind(), io::ErrorKind::TimedOut, "{e}");
        assert_eq!(c.owed_acks(), 0, "a failed write owes nothing");
        for e in [
            c.commit("g", 0).unwrap_err(),
            c.recv_publish_ack().unwrap_err(),
        ] {
            assert_eq!(e.kind(), io::ErrorKind::BrokenPipe, "{e}");
            assert!(acks_owed(&e).is_none());
        }
    }

    /// A LATCHED client owes nothing: once a read fails part-way through the acks it
    /// was owed (here the broker closes after the first of two), nothing is read on it
    /// again, so nothing it was owed can be paid, and the count is zero. A caller that
    /// reads acks while `owed_acks()` is above zero therefore stops, where a count
    /// that stayed at one would spin on a `BrokenPipe` that pays nothing. The same for
    /// a blocking `publish` whose own ack read fails, on a client that never pipelined.
    #[test]
    fn a_latched_client_owes_nothing() {
        let mut c = Client::from_stream(Recorder {
            replies: ack(0),
            written: Arc::new(Mutex::new(Vec::new())),
            fail_writes: false,
        });
        c.send_publish(1, 1, "/o/a", b"one").unwrap();
        c.send_publish(1, 2, "/o/a", b"two").unwrap();
        let mut answers = Vec::new();
        while c.owed_acks() > 0 {
            assert!(answers.len() < 2, "two acks owed, read: {answers:?}");
            answers.push(c.recv_publish_ack().map_err(|e| e.kind()));
        }
        assert_eq!(
            answers,
            [Ok((0, false)), Err(io::ErrorKind::UnexpectedEof)],
            "the first ack, then the close that latched the client"
        );
        let e = c.recv_publish_ack().unwrap_err();
        assert_eq!(e.kind(), io::ErrorKind::BrokenPipe, "{e}");
        assert_eq!(c.owed_acks(), 0);

        let mut c = Client::from_stream(Recorder {
            replies: Vec::new(),
            written: Arc::new(Mutex::new(Vec::new())),
            fail_writes: false,
        });
        let e = c.publish(1, 1, "/o/a", b"x").unwrap_err();
        assert_eq!(e.kind(), io::ErrorKind::UnexpectedEof, "{e}");
        assert_eq!(c.owed_acks(), 0, "a blocking publish whose ack read failed");
    }

    /// A pipelined RETIRE owes its ack as a pipelined publish does. `retire` reads the
    /// one ack its own `send_retire` wrote and owes nothing afterwards. A
    /// `send_retire` adds one owed ack: a commit behind it is refused, with nothing
    /// written, until `recv_publish_ack` reads the retire's ack, and the commit then
    /// reads its own reply rather than the retire's.
    #[test]
    fn a_pipelined_retire_owes_its_ack() {
        let log = LogIdentity {
            id: [7; 16],
            generation: 0,
        };
        let written = Arc::new(Mutex::new(Vec::new()));
        let mut c = Client::from_stream(Recorder {
            replies: [ack(4), ack(5), ack(6)].concat(),
            written: Arc::clone(&written),
            fail_writes: false,
        });
        assert_eq!(
            c.retire(1, "/o/a", 0, log).unwrap(),
            (4, false),
            "retire reads its own ack"
        );
        assert_eq!(c.owed_acks(), 0);

        c.send_retire(1, "/o/a", 0, log).unwrap();
        assert_eq!(c.owed_acks(), 1);
        let sent = written.lock().unwrap().len();
        assert_refused_owing("commit", &c.commit("g", 0).unwrap_err(), 1);
        assert_eq!(written.lock().unwrap().len(), sent, "nothing written");
        assert_eq!(
            c.recv_publish_ack().unwrap(),
            (5, false),
            "the retire's ack"
        );
        assert_eq!(c.owed_acks(), 0);
        assert_eq!(c.commit("g", 0).unwrap(), 6, "the commit's own reply");
        let reqs = requests(&written);
        assert!(
            matches!(
                reqs[..],
                [
                    Request::Retire { .. },
                    Request::Retire { .. },
                    Request::Commit { .. }
                ]
            ),
            "{reqs:?}"
        );
    }

    /// [`drain`](super::drain) asks its committer BEFORE it takes. A commit refused
    /// for an owed ack after the take would leave the taken records in nobody's
    /// hands, and the retry the refusal calls for (read the ack, drain again) would
    /// take the records after them and commit past both. So the drain is refused with
    /// nothing taken, and once the ack is read the same drain on the same
    /// subscription hands over the same two records.
    #[cfg(unix)]
    #[test]
    fn a_drain_whose_committer_owes_an_ack_takes_nothing() {
        let (root, _b, _h) = broker("owed-drain");
        let sock = root.path().join("sock");
        let mut p = Client::connect(&sock).unwrap();
        assert_eq!(p.publish(1, 1, "/o/a", b"zero").unwrap(), (0, false));
        assert_eq!(p.publish(1, 2, "/o/a", b"one").unwrap(), (1, false));
        let mut sub = Client::connect(&sock)
            .unwrap()
            .subscribe_group("g", "/o/a")
            .unwrap();
        // A hang detector: both records are on the log, so the take ends on them.
        sub.set_read_timeout(Some(Duration::from_secs(60))).unwrap();

        let mut c = Client::connect(&sock).unwrap();
        c.send_publish(2, 1, "/o/b", b"owed").unwrap();
        let e = super::drain(&mut sub, &mut c, "g", 2).unwrap_err();
        assert_refused_owing("drain", &e, 1);
        assert_eq!(c.recv_publish_ack().unwrap(), (2, false));

        let got = super::drain(&mut sub, &mut c, "g", 2).unwrap();
        let offsets: Vec<u64> = got.iter().map(|r| r.0).collect();
        assert_eq!(
            offsets,
            [0, 1],
            "the records the refused drain left on the subscription"
        );
    }
}

/// THE NON-BLOCKING PUBLISHER: a pipelined commit ([`Client::send_commit`]) and an ack
/// read without waiting ([`Client::try_recv_publish_ack`]) — what a caller whose one
/// loop has other work needs so that it does not park on its own broker's flush for
/// each ack. (Its writes stay blocking writes; see the module documentation.)
///
/// Three properties, each with its negative control.
///
/// - A pipelined commit OWES ITS ACK like a publish and lands as a commit, in send
///   order between the publishes around it, over a real broker; the control is a
///   client with the owed-ack guard off, whose fetch behind the commit takes the
///   commit's ack for its reply and latches.
/// - A try is FRAME-ATOMIC wherever the stream stops: a scripted stream gives every
///   byte in its own read with a dry read (`WouldBlock`) before each, and the tries
///   answer the three owed replies exactly, each after one `None` per byte; a blocking
///   read finishes a frame a try began at every split point, and a read that brings a
///   frame and a half keeps the half. The control reads with `proto::read_frame`, the
///   blocking read a naive try would use, which drops every byte a dry read cut off,
///   so its first answer is the reply queued AFTER the three owed acks.
/// - A try DOES NOT WAIT, and puts the socket back: over a real broker, on every
///   transport [`connect`] dials (an [`AnyClient`]) — the Unix socket aterm's bus is
///   served on, plaintext TCP, the sealed wire, the same wire behind the handshake —
///   and from every typed constructor (whose client switches its own socket), with
///   the writer held before it answers a committed batch (`Broker::pause_next_acks`),
///   a try and a `send_commit` return under a one-minute hang detector that would
///   otherwise shut the connection down, and the blocking reads after them wait for
///   the acks; a burst and its commit are read by trying, in send order. The control
///   leaves the socket non-blocking after the try: the blocking read that should wait
///   for the held ack answers `WouldBlock` at once and latches the client. A
///   `TimedOut` is "not yet" only where a read timeout can fire (a stream read as it
///   is); on a socket the client switched itself it is the dead connection's, and
///   latches the client.
#[cfg(test)]
mod ack_split {
    use super::{acks_owed, broker_refusal, AcksOwed, AnyClient, Client, Closer, Transport};
    use super::{TryMutant, Walk};
    use crate::proto::{
        decode_request, encode_response, read_frame, Request, Response, ERR_BAD_SUBJECT,
    };
    use astream_wire::Frame;
    use std::collections::VecDeque;
    use std::io::{self, Read, Write};
    use std::net::TcpStream;
    use std::sync::{mpsc, Arc, Mutex};
    use std::time::{Duration, Instant};

    /// Every wait here is bounded by this HANG DETECTOR, never by a latency budget.
    const HANG: Duration = Duration::from_secs(60);

    /// One read of a [`Trickle`].
    #[derive(Clone, Copy, Debug)]
    enum Step {
        /// Hand out at most this many bytes.
        Give(usize),
        /// Answer `WouldBlock`: what a non-blocking socket with nothing to give answers.
        Dry,
        /// Answer `TimedOut`: what a read timeout answers on Windows, and what a dead
        /// TCP connection (`ETIMEDOUT`) answers on any host.
        Lapse,
    }

    /// One end of an in-memory connection whose reads follow a script, one step per
    /// read; past the script every read hands out all that is left, and then EOF (a
    /// blocking stream that has it all). Every byte written lands in `written`.
    struct Trickle {
        bytes: VecDeque<u8>,
        script: VecDeque<Step>,
        written: Arc<Mutex<Vec<u8>>>,
    }

    impl Read for Trickle {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            let n = match self.script.pop_front() {
                Some(Step::Dry) => return Err(io::ErrorKind::WouldBlock.into()),
                Some(Step::Lapse) => return Err(io::ErrorKind::TimedOut.into()),
                Some(Step::Give(n)) => n,
                None => usize::MAX,
            };
            let n = n.min(buf.len()).min(self.bytes.len());
            for (slot, byte) in buf.iter_mut().zip(self.bytes.drain(..n)) {
                *slot = byte;
            }
            Ok(n)
        }
    }

    impl Write for Trickle {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            self.written.lock().unwrap().extend_from_slice(buf);
            Ok(buf.len())
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    fn frame(r: &Response) -> Vec<u8> {
        Frame::new(encode_response(r)).encode().unwrap()
    }

    fn ack(offset: u64) -> Vec<u8> {
        frame(&Response::PublishAck {
            offset,
            deduped: false,
        })
    }

    /// What [`owing_three`]'s client is owed, in order — an ack, the second publish's
    /// refusal, the commit's ack — with each frame's length, and then the reply to the
    /// blocking commit sent after them.
    fn replies() -> (Vec<u8>, [usize; 3]) {
        let owed = [
            ack(10),
            frame(&Response::Error {
                code: ERR_BAD_SUBJECT,
                msg: "bad subject \"no-slash\"".to_string(),
            }),
            ack(12),
        ];
        let lens = [owed[0].len(), owed[1].len(), owed[2].len()];
        let mut bytes = owed.concat();
        bytes.extend_from_slice(&ack(13));
        (bytes, lens)
    }

    /// A client on a [`Trickle`] playing `script` over [`replies`], which has
    /// pipelined two publishes and a commit and read nothing yet.
    fn owing_three(script: Vec<Step>) -> (Client<Trickle>, Arc<Mutex<Vec<u8>>>) {
        let written = Arc::new(Mutex::new(Vec::new()));
        let mut c = Client::from_stream(Trickle {
            bytes: replies().0.into(),
            script: script.into(),
            written: Arc::clone(&written),
        });
        c.send_publish(1, 1, "/o/a", b"one").unwrap();
        c.send_publish(1, 2, "no-slash", b"two").unwrap();
        c.send_commit("g", 1).unwrap();
        assert_eq!(
            c.owed_acks(),
            3,
            "the commit owes its ack as each publish does"
        );
        (c, written)
    }

    /// An answer as the tests compare it: the ack, or the refusal's code (`None` for
    /// an error that is not a refusal).
    type Answer = Result<(u64, bool), Option<u8>>;

    fn answer(r: io::Result<(u64, bool)>) -> Answer {
        r.map_err(|e| broker_refusal(&e).map(|r| r.code))
    }

    /// The three owed answers, in order.
    const OWED: [Answer; 3] = [Ok((10, false)), Err(Some(ERR_BAD_SUBJECT)), Ok((12, false))];

    /// Try until the three owed answers are in hand, counting the `None`s before each.
    fn try_the_three(c: &mut Client<Trickle>) -> (Vec<Answer>, [usize; 3]) {
        let mut answers = Vec::new();
        let mut nones = [0usize; 3];
        while c.owed_acks() > 0 {
            let at = answers.len();
            assert!(at < 3, "three owed, answered: {answers:?}");
            match c.try_recv_publish_ack() {
                Ok(None) => nones[at] += 1,
                Ok(Some(a)) => answers.push(Ok(a)),
                Err(e) => answers.push(answer(Err(e))),
            }
        }
        (answers, nones)
    }

    /// Every request a [`Trickle`] was sent, decoded.
    fn requests(written: &Mutex<Vec<u8>>) -> Vec<Request> {
        let bytes = written.lock().unwrap().clone();
        let mut at = &bytes[..];
        let mut out = Vec::new();
        while let Some(p) = read_frame(&mut at).unwrap() {
            out.push(decode_request(&p).expect("a request this client wrote"));
        }
        out
    }

    /// The owed-ack refusal a request behind `owed` unread acks must get.
    fn assert_refused_owing(what: &str, e: &io::Error, owed: u64) {
        assert_eq!(acks_owed(e), Some(&AcksOwed { owed }), "{what}: {e:?}");
    }

    /// **A TRY FINISHES THE FRAME IT BEGAN, WHEREVER THE STREAM STOPS.** Every byte of
    /// the three owed replies comes in a read of its own, with a dry read before each:
    /// the tries answer one `None` per byte of each frame and then the frame's own
    /// answer — the first ack, the second publish's refusal (which pays its ack and
    /// leaves the client in step), the commit's ack — and the client owes nothing.
    /// A try with nothing owed is `InvalidInput` and reads nothing, so the blocking
    /// commit after it reads its own reply; the stream carries the two publishes and
    /// the two commits.
    #[test]
    fn a_try_finishes_the_frame_it_began_wherever_the_stream_stops() {
        let (_, lens) = replies();
        let owed_bytes: usize = lens.iter().sum();
        let script = (0..owed_bytes)
            .flat_map(|_| [Step::Dry, Step::Give(1)])
            .collect();
        let (mut c, written) = owing_three(script);
        let (answers, nones) = try_the_three(&mut c);
        assert_eq!(answers, OWED, "each owed reply, in order");
        assert_eq!(
            nones, lens,
            "one None per byte of each frame, then its answer"
        );

        let e = c.try_recv_publish_ack().unwrap_err();
        assert_eq!(e.kind(), io::ErrorKind::InvalidInput, "{e}");
        assert_eq!(c.commit("g", 3).unwrap(), 13, "in step: its own reply");
        let reqs = requests(&written);
        assert!(
            matches!(
                reqs[..],
                [
                    Request::Publish { .. },
                    Request::Publish { .. },
                    Request::Commit { upto: 1, .. },
                    Request::Commit { upto: 3, .. },
                ]
            ),
            "{reqs:?}"
        );
    }

    /// **NEGATIVE CONTROL: A TRY ON THE BLOCKING READ TEARS THE FRAME.** The same
    /// replies, every byte in a read of its own with a dry read before it (and one
    /// after the last), read by a try built on `proto::read_frame`
    /// (`TryMutant::Torn`), whose `read_exact` drops the header byte it had when a dry
    /// read stopped it: every byte of the three owed replies is eaten, each read as
    /// "not yet", and the first answer the client hands back is the reply queued AFTER
    /// them — the blocking commit's, taken, with no error, for the first publish's ack.
    #[test]
    fn torn_a_try_on_the_blocking_read_answers_a_later_reply_for_the_first_ack() {
        let (_, lens) = replies();
        let owed_bytes: usize = lens.iter().sum();
        let script = (0..owed_bytes)
            .flat_map(|_| [Step::Dry, Step::Give(1)])
            .chain([Step::Dry])
            .collect();
        let (mut c, _written) = owing_three(script);
        c.try_mutant = TryMutant::Torn;
        let started = Instant::now();
        let first = loop {
            assert!(started.elapsed() < HANG, "hang detector");
            if let Some(a) = c.try_recv_publish_ack().map_err(|e| e.kind()).transpose() {
                break a;
            }
        };
        assert_eq!(
            first,
            Ok((13, false)),
            "the reply queued after the three owed acks"
        );
        assert_eq!(c.owed_acks(), 2, "and it paid the first owed ack with it");
    }

    /// **A BLOCKING READ FINISHES A FRAME A TRY BEGAN, AT EVERY SPLIT.** For every split
    /// of the first ack, a try reads its first part and answers `None`, and
    /// `recv_publish_ack` finishes it; the two after it are read blocking too. A read
    /// that brings a frame and a half answers the frame, KEEPS the half — the next try
    /// answers `None` on a dry read rather than tearing it — and the blocking read
    /// finishes the half. A stream that closes part-way through a frame a try began is
    /// `UnexpectedEof`, latches the client and zeroes what it owes.
    #[test]
    fn a_blocking_read_finishes_a_frame_a_try_began() {
        let (bytes, lens) = replies();
        for k in 1..lens[0] {
            let (mut c, _) = owing_three(vec![Step::Give(k), Step::Dry]);
            assert_eq!(c.try_recv_publish_ack().unwrap(), None, "split at {k}");
            let rest: Vec<_> = (0..3).map(|_| answer(c.recv_publish_ack())).collect();
            assert_eq!(rest, OWED, "split at {k}");
        }

        let half = lens[0] + lens[1] / 2;
        let (mut c, _) = owing_three(vec![Step::Give(half), Step::Dry]);
        assert_eq!(c.try_recv_publish_ack().unwrap(), Some((10, false)));
        assert_eq!(c.try_recv_publish_ack().unwrap(), None, "the half is kept");
        assert_eq!(answer(c.recv_publish_ack()), OWED[1]);
        assert_eq!(
            answer(c.try_recv_publish_ack().map(Option::unwrap)),
            OWED[2]
        );

        let mut c = Client::from_stream(Trickle {
            bytes: bytes[..5].to_vec().into(),
            script: vec![Step::Give(5), Step::Dry].into(),
            written: Arc::new(Mutex::new(Vec::new())),
        });
        c.send_publish(1, 1, "/o/a", b"one").unwrap();
        assert_eq!(c.try_recv_publish_ack().unwrap(), None);
        let e = c.try_recv_publish_ack().unwrap_err();
        assert_eq!(e.kind(), io::ErrorKind::UnexpectedEof, "{e}");
        assert_eq!(c.owed_acks(), 0, "latched: nothing it owed can be paid");
        let e = c.try_recv_publish_ack().unwrap_err();
        assert_eq!(e.kind(), io::ErrorKind::BrokenPipe, "{e}");
    }

    /// **A TIMEOUT IS "NOT YET" ONLY WHERE A READ TIMEOUT CAN HAVE FIRED.** A client made
    /// `from_stream` reads as its stream reads, so a read that answers `TimedOut` — a
    /// read timeout, as Windows reports one — is "not yet": the try answers `None`,
    /// owing what it owed, and the next try the ack. A client that switches its socket
    /// non-blocking itself (here the same stream, given a mode switch that does nothing,
    /// in place of the socket a constructor reaches) has no read timeout that could
    /// fire: a dry read is still `None`, but a `TimedOut` is the connection's own
    /// (`ETIMEDOUT`, retransmission or keepalive giving up on the peer), so the try
    /// returns it as the failure it is and latches the client, owing nothing.
    #[test]
    fn a_timeout_is_not_yet_only_where_a_read_timeout_can_fire() {
        let (mut c, _) = owing_three(vec![Step::Lapse]);
        assert_eq!(c.try_recv_publish_ack().unwrap(), None, "a read timeout");
        assert_eq!(c.owed_acks(), 3, "a None pays nothing");
        assert_eq!(c.try_recv_publish_ack().unwrap(), Some((10, false)));

        let (c, _) = owing_three(vec![Step::Dry, Step::Lapse]);
        let mut c = c.nowait_by(|_, _| Ok(()));
        assert_eq!(c.try_recv_publish_ack().unwrap(), None, "a dry read");
        let e = c.try_recv_publish_ack().unwrap_err();
        assert_eq!(e.kind(), io::ErrorKind::TimedOut, "the connection's: {e}");
        assert_eq!(c.owed_acks(), 0, "latched: nothing it owed can be paid");
        let e = c.try_recv_publish_ack().unwrap_err();
        assert_eq!(e.kind(), io::ErrorKind::BrokenPipe, "{e}");
    }

    /// **A BROKER THAT ANSWERED AND HUNG UP IS STILL READ.** Over a real socket pair
    /// (the typed Unix client's own mode switch): two acks are written and the far end
    /// shut down before the client reads; the tries switch a socket whose peer is gone
    /// into and out of non-blocking mode, answer both acks, and then report the close as
    /// `UnexpectedEof`, which latches the client.
    #[cfg(unix)]
    #[test]
    fn a_broker_that_answered_and_hung_up_is_still_read() {
        use std::os::unix::net::UnixStream;
        let (near, mut far) = UnixStream::pair().unwrap();
        let mut c = Client::from_stream(near).nowait_by(UnixStream::set_nonblocking);
        c.send_publish(1, 1, "/o/a", b"one").unwrap();
        c.send_publish(1, 2, "/o/a", b"two").unwrap();
        c.send_publish(1, 3, "/o/a", b"three").unwrap();
        far.write_all(&[ack(0), ack(1)].concat()).unwrap();
        far.shutdown(std::net::Shutdown::Both).unwrap();
        drop(far);
        assert_eq!(c.try_recv_publish_ack().unwrap(), Some((0, false)));
        assert_eq!(c.try_recv_publish_ack().unwrap(), Some((1, false)));
        let e = c.try_recv_publish_ack().unwrap_err();
        assert_eq!(e.kind(), io::ErrorKind::UnexpectedEof, "{e}");
        assert_eq!(c.owed_acks(), 0);
    }

    /// A connection a case opens, and the [`Closer`] on its socket that the hang
    /// detector shuts it down with and a subscription's read is bounded by.
    type Dialed<S> = (Client<S>, Arc<Closer>);

    /// The keys a broker served with static identity is reached with — this client's
    /// key and the broker's host key — which only its typed constructor takes
    /// ([`Client::connect_tcp_identity`]; no [`Transport`] names it).
    #[cfg(feature = "identity")]
    type IdentityKeys = (
        astream_aead::IdentityKeypair,
        [u8; astream_aead::ID_PUB_LEN],
    );

    /// A served broker, and how to reach it: [`super::connect`] over one transport, as
    /// aterm does, which hands back an erased [`AnyClient`] beside its [`Closer`]; or a
    /// typed constructor, whose client switches its own socket's mode
    /// ([`Nowait::Stream`](super::Nowait::Stream)).
    struct Served {
        _root: crate::test_scratch::Scratch,
        broker: crate::Broker,
        _handle: crate::BrokerHandle,
        /// The transport `connect` reaches it over; `None` for a broker no
        /// [`Transport`] names (static identity).
        transport: Option<Transport>,
        /// The keys a broker served with static identity is reached with.
        #[cfg(feature = "identity")]
        identity: Option<Box<IdentityKeys>>,
        endpoint: String,
    }

    impl Served {
        /// A fresh broker in a scratch directory of its own, served by `serve`, which
        /// answers its handle, the transport `connect` reaches it over, and where.
        fn on(
            tag: &str,
            serve: impl FnOnce(
                &crate::Broker,
                &std::path::Path,
            ) -> (crate::BrokerHandle, Option<Transport>, String),
        ) -> Served {
            let root = crate::test_scratch::Scratch::new(tag);
            let broker = crate::Broker::open(root.path().join("log")).unwrap();
            let (handle, transport, endpoint) = serve(&broker, root.path());
            Served {
                _root: root,
                broker,
                _handle: handle,
                transport,
                #[cfg(feature = "identity")]
                identity: None,
                endpoint,
            }
        }

        /// On a Unix socket, as aterm's bus is served.
        #[cfg(unix)]
        fn unix(tag: &str) -> Served {
            Served::on(tag, |broker, dir| {
                let sock = dir.join("sock");
                let handle = broker.serve(&sock).unwrap();
                let endpoint = sock.to_string_lossy().into_owned();
                (handle, Some(Transport::Unix), endpoint)
            })
        }

        /// On plaintext TCP, on loopback: the transport every platform has.
        fn tcp(tag: &str) -> Served {
            Served::on(tag, |broker, _| {
                let handle = broker.serve_tcp("127.0.0.1:0").unwrap();
                let endpoint = handle.tcp_addr().expect("a TCP listener").to_string();
                (handle, Some(Transport::Tcp), endpoint)
            })
        }

        /// On the sealed wire: the record layer between the client and its socket.
        #[cfg(feature = "aead")]
        fn sealed(tag: &str) -> Served {
            let key = [7u8; astream_aead::KEY_LEN];
            Served::on(tag, |broker, _| {
                let handle = broker.serve_tcp_sealed("127.0.0.1:0", key).unwrap();
                let endpoint = handle.tcp_addr().expect("a TCP listener").to_string();
                (handle, Some(Transport::Sealed(Box::new(key))), endpoint)
            })
        }

        /// On the sealed wire behind the forward-secret handshake: the same record
        /// layer, under a session key the two ends agreed.
        #[cfg(feature = "handshake")]
        fn handshake(tag: &str) -> Served {
            let psk = [9u8; astream_aead::KEY_LEN];
            Served::on(tag, |broker, _| {
                let handle = broker.serve_tcp_handshake("127.0.0.1:0", psk).unwrap();
                let endpoint = handle.tcp_addr().expect("a TCP listener").to_string();
                (handle, Some(Transport::Handshake(Box::new(psk))), endpoint)
            })
        }

        /// On the sealed wire behind static identity: the broker allow-lists one client
        /// key and presents a host key that client pins.
        #[cfg(feature = "identity")]
        fn identity(tag: &str) -> Served {
            let host = astream_aead::IdentityKeypair::generate();
            let host_pub = host.public();
            let client = astream_aead::IdentityKeypair::generate();
            let client_pub = client.public();
            let mut s = Served::on(tag, |broker, _| {
                let handle = broker
                    .serve_tcp_identity("127.0.0.1:0", host, vec![client_pub])
                    .unwrap();
                let endpoint = handle.tcp_addr().expect("a TCP listener").to_string();
                (handle, None, endpoint)
            });
            s.identity = Some(Box::new((client, host_pub)));
            s
        }

        /// A connection through [`super::connect`]: an [`AnyClient`], as aterm's bridge
        /// has one.
        fn dial(&self) -> Dialed<Box<dyn super::AnyStream>> {
            let transport = self
                .transport
                .as_ref()
                .expect("connect dials no identity transport");
            let (c, closer): (AnyClient, Closer) =
                super::connect(transport, &self.endpoint, None).expect("a connection");
            (c, Arc::new(closer))
        }

        /// A connection from [`Client::connect`], the typed Unix constructor.
        #[cfg(unix)]
        fn typed_unix(&self) -> Dialed<std::os::unix::net::UnixStream> {
            let c = Client::connect(&self.endpoint).expect("a connection");
            let closer = Closer::unix(&c.stream).expect("a duplicate of its socket");
            (c, Arc::new(closer))
        }

        /// A connection from [`Client::connect_tcp`].
        fn typed_tcp(&self) -> Dialed<TcpStream> {
            let c = Client::connect_tcp(self.endpoint.as_str()).expect("a connection");
            let closer = Closer::tcp(&c.stream).expect("a duplicate of its socket");
            (c, Arc::new(closer))
        }

        /// A connection from [`Client::connect_tcp_timeout`].
        fn typed_tcp_timeout(&self) -> Dialed<TcpStream> {
            let c =
                Client::connect_tcp_timeout(self.endpoint.as_str(), HANG).expect("a connection");
            let closer = Closer::tcp(&c.stream).expect("a duplicate of its socket");
            (c, Arc::new(closer))
        }

        /// A connection from [`Client::connect_tcp_sealed`].
        #[cfg(feature = "aead")]
        fn typed_sealed(&self) -> Dialed<astream_aead::SealedStream<TcpStream>> {
            let Some(Transport::Sealed(key)) = &self.transport else {
                panic!("not served sealed");
            };
            let c =
                Client::connect_tcp_sealed(self.endpoint.as_str(), **key).expect("a connection");
            let closer = Closer::tcp(c.stream.get_ref()).expect("a duplicate of its socket");
            (c, Arc::new(closer))
        }

        /// A connection from [`Client::connect_tcp_handshake`].
        #[cfg(feature = "handshake")]
        fn typed_handshake(&self) -> Dialed<astream_aead::SealedStream<TcpStream>> {
            let Some(Transport::Handshake(psk)) = &self.transport else {
                panic!("not served behind the handshake");
            };
            let c =
                Client::connect_tcp_handshake(self.endpoint.as_str(), **psk).expect("a connection");
            let closer = Closer::tcp(c.stream.get_ref()).expect("a duplicate of its socket");
            (c, Arc::new(closer))
        }

        /// A connection from [`Client::connect_tcp_identity`].
        #[cfg(feature = "identity")]
        fn typed_identity(&self) -> Dialed<astream_aead::SealedStream<TcpStream>> {
            let Some((client, host)) = self.identity.as_deref() else {
                panic!("not served behind identity");
            };
            let c = Client::connect_tcp_identity(self.endpoint.as_str(), client.clone(), *host)
                .expect("a connection");
            let closer = Closer::tcp(c.stream.get_ref()).expect("a duplicate of its socket");
            (c, Arc::new(closer))
        }
    }

    /// Where consumer group `g` resumes: the offset of its first delivery of `/o/a`,
    /// on a connection of its own.
    fn group_resumes_at<S: Read + Write>((c, closer): Dialed<S>) -> u64 {
        closer.set_read_timeout(Some(HANG)).unwrap();
        let mut sub = c.subscribe_group("g", "/o/a").unwrap();
        sub.recv().unwrap().expect("a delivery").0
    }

    /// Run `f`, a call that must not wait, under the HANG DETECTOR: should it park for
    /// [`HANG`], the connection is shut down through `closer`, so the parked read
    /// returns and this fails naming `what` — rather than the run hanging.
    fn unparked<T>(closer: &Arc<Closer>, what: &str, f: impl FnOnce() -> T) -> T {
        let (done, wait) = mpsc::channel::<()>();
        let dog = {
            let closer = Arc::clone(closer);
            std::thread::spawn(move || {
                let fired = matches!(
                    wait.recv_timeout(HANG),
                    Err(mpsc::RecvTimeoutError::Timeout)
                );
                if fired {
                    closer.close();
                }
                fired
            })
        };
        let out = f();
        drop(done);
        assert!(
            !dog.join().unwrap(),
            "{what} waited: the hang detector shut the connection down"
        );
        out
    }

    /// Read every owed ack by TRYING, as a loop with other work would between tries,
    /// until none is owed: the answers in order. Bounded by the hang detector.
    fn by_trying<S: Read + Write>(c: &mut Client<S>) -> Vec<(u64, bool)> {
        let started = Instant::now();
        let mut got = Vec::new();
        while c.owed_acks() > 0 {
            match c.try_recv_publish_ack().expect("an ack") {
                Some(a) => got.push(a),
                None => {
                    assert!(
                        started.elapsed() < HANG,
                        "hang detector: {} acks still owed",
                        c.owed_acks()
                    );
                    std::thread::sleep(Duration::from_millis(1));
                }
            }
        }
        got
    }

    /// **A PIPELINED COMMIT OWES ITS ACK AND LANDS AS A COMMIT, IN SEND ORDER.** A
    /// publish, a commit of group `g` to 0 and a publish are written without a read;
    /// three acks are owed, so a head query is refused with nothing sent; the acks come
    /// back in send order — the commit's is its own record's offset, 1, between the
    /// publishes' 0 and 2 — the head counts the three records, and the group resumes
    /// past 0: its first delivery is 2, the commit record at 1 being hidden.
    fn a_pipelined_commit_owes_its_ack_and_lands_between_its_publishes<S: Read + Write>(
        _: &Served,
        dial: impl Fn() -> Dialed<S>,
    ) {
        let (mut c, _closer) = dial();
        c.send_publish(1, 1, "/o/a", b"zero").unwrap();
        c.send_commit("g", 0).unwrap();
        c.send_publish(1, 2, "/o/a", b"two").unwrap();
        assert_eq!(c.owed_acks(), 3);
        assert_refused_owing("fetch", &c.fetch(0, "/o/>", 0).unwrap_err(), 3);
        let acks: Vec<_> = (0..3).map(|_| c.recv_publish_ack().unwrap()).collect();
        assert_eq!(acks, [(0, false), (1, false), (2, false)], "in send order");
        let (_, (_, head)) = c.fetch(0, "/o/>", 0).unwrap();
        assert_eq!(head, 3, "two publishes and the commit");
        assert_eq!(group_resumes_at(dial()), 2, "past the commit's upto, 0");
    }

    /// **NEGATIVE CONTROL: WITHOUT THE GUARD, A FETCH BEHIND A PIPELINED COMMIT TAKES ITS
    /// ACK.** The owed-ack guard off (`unguarded`): the commit's ack is the next frame on
    /// the stream, so the head query sent behind it reads that `PublishAck` as its
    /// reply, fails `InvalidData`, and latches the client; the count is what keeps a
    /// request that reads its own reply off a commit's ack.
    fn without_the_guard_a_fetch_behind_a_pipelined_commit_takes_its_ack<S: Read + Write>(
        _: &Served,
        dial: impl Fn() -> Dialed<S>,
    ) {
        let (mut c, _closer) = dial();
        c.unguarded = true;
        c.send_commit("g", 0).unwrap();
        let e = c.fetch(0, "/o/>", 0).unwrap_err();
        assert_eq!(
            e.kind(),
            io::ErrorKind::InvalidData,
            "the commit's ack: {e}"
        );
        let e = c.last("/o/>", "", 8).unwrap_err();
        assert_eq!(e.kind(), io::ErrorKind::BrokenPipe, "latched: {e}");
    }

    /// **A TRY DOES NOT WAIT FOR AN ACK THE BROKER HOLDS, AND PUTS THE SOCKET BACK.** The
    /// writer is held after it commits a publish's batch and before it answers it
    /// (`pause_next_acks`). A try returns `None` under the hang detector, paying
    /// nothing, and the client is in step (a head query is refused for the owed ack);
    /// a `send_commit` returns too, and a second try. Once the writer goes on, the
    /// blocking reads wait for both acks — the socket is blocking again — and the
    /// commit moved the group. Then a burst of 64 publishes, a commit and a publish
    /// are read by trying alone, in send order, and the connection is in step after.
    /// A client that could not reach its socket's mode (one left
    /// [`Nowait::AsIs`](super::Nowait::AsIs) over a blocking socket) parks in the first
    /// try until the hang detector shuts it down.
    fn a_try_does_not_wait_for_an_ack_the_broker_holds<S: Read + Write>(
        s: &Served,
        dial: impl Fn() -> Dialed<S>,
    ) {
        let (mut c, closer) = dial();
        let held = s.broker.pause_next_acks();
        c.send_publish(1, 1, "/o/a", b"held").unwrap();
        assert!(held.wait_at_most(HANG), "the writer holds the batch's acks");
        let tried = unparked(&closer, "a try", || c.try_recv_publish_ack());
        assert_eq!(tried.unwrap(), None);
        assert_eq!(c.owed_acks(), 1, "a None pays nothing");
        assert_refused_owing("fetch", &c.fetch(0, "/o/>", 0).unwrap_err(), 1);
        unparked(&closer, "send_commit", || c.send_commit("g", 0)).unwrap();
        assert_eq!(c.owed_acks(), 2);
        let tried = unparked(&closer, "a second try", || c.try_recv_publish_ack());
        assert_eq!(tried.unwrap(), None);
        held.resume();
        assert_eq!(c.recv_publish_ack().unwrap(), (0, false), "the publish's");
        assert_eq!(c.recv_publish_ack().unwrap(), (1, false), "the commit's");
        assert_eq!(c.publish(1, 2, "/o/a", b"after").unwrap(), (2, false));
        assert_eq!(group_resumes_at(dial()), 2, "past the commit's upto, 0");

        for seq in 3..=66 {
            c.send_publish(1, seq, "/o/a", b"burst").unwrap();
        }
        c.send_commit("g", 66).unwrap();
        c.send_publish(1, 67, "/o/a", b"last").unwrap();
        let acks = by_trying(&mut c);
        let want: Vec<_> = (3..=68).map(|off| (off, false)).collect();
        assert_eq!(
            acks, want,
            "64 publishes, the commit at 67, a publish at 68"
        );
        let mut seen = 0;
        c.last_walk("/o/>", "", 8, |_| {
            seen += 1;
            Ok(Walk::Continue)
        })
        .unwrap();
        assert_eq!(seen, 1, "in step after the tries: one subject, read whole");
    }

    /// **NEGATIVE CONTROL: A TRY THAT LEAVES THE SOCKET NON-BLOCKING BREAKS THE NEXT
    /// WAIT.** The same held ack, read by a try that does not put the socket back
    /// (`TryMutant::KeepsNowait`): the try answers `None` as before, but the blocking
    /// read that must wait for the held ack answers `WouldBlock` at once and latches
    /// the client, so the ack can never be paid. That `WouldBlock` is also what shows
    /// the try reached the socket the stream reads: the mode it set is the mode the
    /// stream's next read met.
    fn a_try_that_leaves_the_socket_non_blocking_breaks_the_next_wait<S: Read + Write>(
        s: &Served,
        dial: impl Fn() -> Dialed<S>,
    ) {
        let (mut c, closer) = dial();
        c.try_mutant = TryMutant::KeepsNowait;
        let held = s.broker.pause_next_acks();
        c.send_publish(1, 1, "/o/a", b"held").unwrap();
        assert!(held.wait_at_most(HANG), "the writer holds the batch's acks");
        let tried = unparked(&closer, "a try", || c.try_recv_publish_ack());
        assert_eq!(tried.unwrap(), None);
        let e = unparked(&closer, "the blocking read", || c.recv_publish_ack()).unwrap_err();
        assert_eq!(e.kind(), io::ErrorKind::WouldBlock, "{e}");
        assert_eq!(c.owed_acks(), 0, "latched: the held ack can never be paid");
        held.resume();
    }

    /// Each `$case` as a test of its own, on a fresh broker that `$serve` serves,
    /// reached through the [`Served`] method `$dial`, in a module named for how the
    /// client is reached (`ack_split::<module>::<case>`).
    macro_rules! cases {
        ($(#[$attr:meta])* $module:ident: $serve:ident, $dial:ident => $($case:ident),+ $(,)?) => {
            $(#[$attr])*
            mod $module {
                use super::Served;
                $(
                    #[test]
                    fn $case() {
                        let s = Served::$serve(stringify!($module));
                        super::$case(&s, || s.$dial());
                    }
                )+
            }
        };
    }

    // Every case on each transport `connect` dials, each connection an AnyClient whose
    // try switches the mode of the socket the Closer duplicated: the Unix socket
    // aterm's bus is served on, plaintext TCP (what every platform has), the sealed
    // wire, whose record layer keeps a record that partly arrived and the plaintext it
    // has not handed out, and the same wire behind the forward-secret handshake.

    cases!(#[cfg(unix)] unix: unix, dial =>
        a_pipelined_commit_owes_its_ack_and_lands_between_its_publishes,
        without_the_guard_a_fetch_behind_a_pipelined_commit_takes_its_ack,
        a_try_does_not_wait_for_an_ack_the_broker_holds,
        a_try_that_leaves_the_socket_non_blocking_breaks_the_next_wait,
    );

    cases!(tcp: tcp, dial =>
        a_pipelined_commit_owes_its_ack_and_lands_between_its_publishes,
        without_the_guard_a_fetch_behind_a_pipelined_commit_takes_its_ack,
        a_try_does_not_wait_for_an_ack_the_broker_holds,
        a_try_that_leaves_the_socket_non_blocking_breaks_the_next_wait,
    );

    cases!(#[cfg(feature = "aead")] sealed: sealed, dial =>
        a_pipelined_commit_owes_its_ack_and_lands_between_its_publishes,
        without_the_guard_a_fetch_behind_a_pipelined_commit_takes_its_ack,
        a_try_does_not_wait_for_an_ack_the_broker_holds,
        a_try_that_leaves_the_socket_non_blocking_breaks_the_next_wait,
    );

    cases!(#[cfg(feature = "handshake")] handshake: handshake, dial =>
        a_pipelined_commit_owes_its_ack_and_lands_between_its_publishes,
        without_the_guard_a_fetch_behind_a_pipelined_commit_takes_its_ack,
        a_try_does_not_wait_for_an_ack_the_broker_holds,
        a_try_that_leaves_the_socket_non_blocking_breaks_the_next_wait,
    );

    // The two that rest on the try's mode switch, on each TYPED constructor, whose
    // client switches its own socket (`nowait_by`): without that wiring the client is
    // `AsIs` over a blocking socket, the first case's try parks until the hang
    // detector shuts it down, and the second's never returns to show `WouldBlock`.

    cases!(#[cfg(unix)] typed_unix: unix, typed_unix =>
        a_try_does_not_wait_for_an_ack_the_broker_holds,
        a_try_that_leaves_the_socket_non_blocking_breaks_the_next_wait,
    );

    cases!(typed_tcp: tcp, typed_tcp =>
        a_try_does_not_wait_for_an_ack_the_broker_holds,
        a_try_that_leaves_the_socket_non_blocking_breaks_the_next_wait,
    );

    cases!(typed_tcp_timeout: tcp, typed_tcp_timeout =>
        a_try_does_not_wait_for_an_ack_the_broker_holds,
        a_try_that_leaves_the_socket_non_blocking_breaks_the_next_wait,
    );

    cases!(#[cfg(feature = "aead")] typed_sealed: sealed, typed_sealed =>
        a_try_does_not_wait_for_an_ack_the_broker_holds,
        a_try_that_leaves_the_socket_non_blocking_breaks_the_next_wait,
    );

    cases!(#[cfg(feature = "handshake")] typed_handshake: handshake, typed_handshake =>
        a_try_does_not_wait_for_an_ack_the_broker_holds,
        a_try_that_leaves_the_socket_non_blocking_breaks_the_next_wait,
    );

    cases!(#[cfg(feature = "identity")] typed_identity: identity, typed_identity =>
        a_try_does_not_wait_for_an_ack_the_broker_holds,
        a_try_that_leaves_the_socket_non_blocking_breaks_the_next_wait,
    );
}
