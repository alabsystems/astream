//! The broker daemon: a thread-per-connection server over a Unix-domain socket or TCP
//! (plaintext; AEAD-sealed with the `aead` feature; capability-guarded with the `cap`
//! feature), one `Mutex<BrokerLog>` + `Condvar` for the single-writer log and live
//! tail, and a group-commit writer thread that every durable mutation funnels through.
//!
//! Lock discipline (the crux): the log `Mutex` is held ONLY for staging/committing a
//! batch (incl. its fsync) or a short catch-up pointer copy (at most [`TAIL_CHUNK`]
//! records per hold) — NEVER across a socket write, a follower round-trip, or a
//! `Condvar` wait. So a slow/dead consumer (or follower) blocks only its own thread,
//! never other consumers. The tail wakes via `Condvar` (no sleeps, no poll); the wait
//! predicate reads the visible `head` under the same lock the writer advances it
//! under, so a commit landing between "caught up" and "wait" is never missed.
//!
//! Lifecycle: the acceptor polls a non-blocking listener and the `running` flag.
//! Shutdown flips the flag, force-closes every registered connection socket (a thread
//! parked in a socket read/write returns at once), joins the acceptor and the writer,
//! then releases the log's file lock. A `Broker` dropped without ever serving stops
//! its own writer thread.

use crate::brecord::{BrokerRecord, GroupCommit};
use crate::proto::{
    append_delivery_frame, append_frame, decode_request, decode_response, encode_replicate,
    encode_response, read_frame, write_frame, Request, Response,
};
use crate::store::{
    is_hidden_subject, replicated_reserved_msg, reserved_msg, BrokerLog, Durability,
    InjectedFaults, StageErr, WillRecord, COMMIT_SUBJECT,
};
use astream_wire::{Filter, Offset, Subject};
use std::collections::HashMap;
use std::io::{self, Read, Write};
use std::net::{
    IpAddr, Ipv4Addr, Ipv6Addr, Shutdown, SocketAddr, TcpListener, TcpStream, ToSocketAddrs,
};
#[cfg(unix)]
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::Path;
#[cfg(unix)]
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::mpsc::{self, Receiver, Sender};
use std::sync::{Arc, Condvar, Mutex};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

/// An object-safe handle that can force-close a connection's socket (both directions),
/// so [`BrokerHandle::shutdown`] can unblock a connection thread parked in a socket
/// read/write and let it (and its ack-writer thread + fds) be reaped promptly. Kept
/// separate from [`Stream`] because `Stream::try_clone -> Self` makes `Stream` itself
/// not object-safe.
trait ConnShutdown: Send + Sync {
    fn shutdown_both(&self);
    /// Shut only the write direction: the peer reads EOF, and may still write.
    fn shutdown_write(&self);
}
#[cfg(unix)]
impl ConnShutdown for UnixStream {
    fn shutdown_both(&self) {
        let _ = self.shutdown(Shutdown::Both);
    }
    fn shutdown_write(&self) {
        let _ = self.shutdown(Shutdown::Write);
    }
}
impl ConnShutdown for TcpStream {
    fn shutdown_both(&self) {
        let _ = self.shutdown(Shutdown::Both);
    }
    fn shutdown_write(&self) {
        let _ = self.shutdown(Shutdown::Write);
    }
}

/// One durable mutation queued to the single writer thread. The connection thread
/// blocks on `ack` until the writer's batch fsync makes the record durable (or fails).
struct WriteOp {
    kind: WriteKind,
    ack: Sender<AckResult>,
}

/// `Ok((offset, deduped))` once durable, or `Err(message)` if the op or its batch
/// failed (e.g. the batch fsync errored — the record is then NOT durable).
type AckResult = Result<(u64, bool), String>;

enum WriteKind {
    Publish {
        producer_id: u64,
        producer_seq: u64,
        subject: String,
        body: Vec<u8>,
    },
    Commit {
        group: String,
        upto: u64,
    },
    ProcessAndProduce {
        producer_id: u64,
        producer_seq: u64,
        out_subject: String,
        out_body: Vec<u8>,
        group: String,
        upto: u64,
    },
    /// A record shipped by a leader, to be appended at exactly its leader offset
    /// (see [`Request::Replicate`]).
    Replicate {
        rec: BrokerRecord,
    },
    /// Bind a producer id to the principal a capability names, durably (a hidden
    /// `/a/bind` record). Checked and appended under the writer's lock, so two
    /// connections racing to bind colliding ids can never both succeed.
    #[cfg_attr(not(feature = "cap"), allow(dead_code))]
    Bind {
        producer_id: u64,
        principal: String,
    },
    /// Persist a connection's registered last will (a hidden `/a/will` record).
    WillRegister {
        will: WillRecord,
    },
    /// Fire a registered will as an ordinary, FENCED publish — when its connection
    /// ends, or on broker open for every will the log still holds.
    WillFire {
        will: WillRecord,
    },
}

/// Upper bound on records folded into one group-commit fsync. The batch self-tunes to
/// offered concurrency (everything queued while the previous fsync ran is drained at
/// once); this only caps a single fsync's fan-in so one batch cannot grow unbounded.
const BATCH_MAX: usize = 4096;

/// How often the idle writer wakes to observe shutdown (it otherwise blocks on the
/// queue and processes a batch the instant work arrives — no added publish latency).
const WRITER_IDLE_POLL: Duration = Duration::from_millis(100);

/// How often the acceptor re-checks `running` between non-blocking `accept()` calls.
/// The listener is non-blocking and polled (NOT a blocking accept + a one-shot
/// self-connect wakeup, which races: the acceptor could consume the wakeup while still
/// observing a stale `running` and re-block forever). Bounds connection-setup latency;
/// it does not touch the publish hot path.
const ACCEPT_POLL: Duration = Duration::from_millis(20);

/// Deadline for a connection to complete the Rung-7 handshake. Bounds the
/// pre-handshake read/write so a silent or slow peer that TCP-connects and stalls
/// cannot park a connection thread + fd indefinitely (a slowloris DoS on the one
/// read no key gates yet). Cleared to blocking once the handshake completes.
#[cfg(feature = "handshake")]
const HANDSHAKE_TIMEOUT: Duration = Duration::from_secs(10);

/// Max un-acked publishes allowed in flight on ONE pipelined connection. Bounds
/// per-connection memory and provides flow control: when this many acks are pending,
/// the read half blocks (which back-pressures the client via the socket buffer)
/// instead of buffering unboundedly. A well-behaved client keeps its window well under
/// this (see [`crate::client::Client::publish_pipelined`]).
const PIPELINE_DEPTH: usize = 1024;

/// DEFAULT write timeout for a served connection — the request thread's writes and the
/// pipelined ack-writer's alike (they share one socket, so they share one bound), until
/// a streaming verb raises it to [`STREAM_WRITE_TIMEOUT`]. A client that pipelines
/// without reading its acks can wedge its OWN connection (its socket buffers fill, the
/// ack-writer blocks, the bounded ack queue fills, the read half blocks) — purely
/// self-inflicted, affecting no other connection. This bound reaps such a wedged
/// connection in bounded time rather than hanging it indefinitely; it is also generous
/// enough for a legitimately slow consumer. (A graceful broker shutdown reaps it
/// immediately via the conn registry.) Overridable per broker with
/// [`Broker::set_write_timeout`].
pub const ACK_WRITE_TIMEOUT: Duration = Duration::from_secs(10);

/// Write timeout for a STREAMING verb, once it has taken the socket over
/// (`Subscribe`/`SubscribeGroup` via `tail_loop`, and `ForkSubscribe`, which delivers
/// its snapshot on the request thread). Deliberately looser than the ack bound: the
/// peer is a reader folding records as they arrive, not a client that owes an ack, so
/// a slow-but-healthy consumer must not be torn down. Still bounded, so a wedged
/// delivery errors out instead of hanging the thread forever.
///
/// This is a FLOOR, not an override: a streaming verb runs under the larger of this and
/// whatever [`Broker::set_write_timeout`] configured, so it only ever RAISES the bound
/// (a configured 60s is never narrowed to 30s on the path that needs the most room).
pub const STREAM_WRITE_TIMEOUT: Duration = Duration::from_secs(30);

/// The write bound a streaming verb runs under: the connection's configured bound, or
/// [`STREAM_WRITE_TIMEOUT`] if that is larger. Never less than either.
fn stream_write_timeout(shared: &Shared) -> Duration {
    Duration::from_millis(shared.write_timeout_ms.load(Ordering::Relaxed)).max(STREAM_WRITE_TIMEOUT)
}

/// How long a freshly accepted connection may take to deliver its FIRST complete
/// frame — and, on a GUARDED broker (`Broker::open_guarded`, feature `cap`), to have
/// a capability ACCEPTED. Until a request has arrived nothing is known about an
/// UNAUTHENTICATED peer, so a socket that connects and then idles — or trickles a
/// length prefix and stops — is reaped instead of pinning a thread and a frame buffer
/// indefinitely.
///
/// On a guarded broker a request proves nothing either: `Hello`, a refused `Attach`
/// and every request an empty keyring refuses are free for anyone to send. There the
/// deadline runs from accept until an `Attach` succeeds, however many frames arrive
/// before it, and a connection still unattached at the deadline is refused (an
/// `unauthorized` error) and closed; otherwise a peer could say `Hello` and hold one of
/// the [`MAX_CONNS`] slots for good. That deadline is absolute: each read is bounded
/// by the time left, so neither a stream of frames nor a frame sent a byte at a time
/// extends it. (On the sealed transports the time left is re-armed once per sealed
/// record rather than per byte, so only a peer holding the transport key can stretch
/// a record past it.)
///
/// The bound is applied on every transport, including the sealed one whose handshake
/// has already proved the peer holds the key: an idle keyed client is reaped too.
/// Lifted once the first frame is in (guarded: once a capability is accepted): an
/// established, idle producer is reaped by shutdown's force-close instead, not by a
/// timer. Tunable per broker via [`Broker::set_first_frame_timeout`].
pub const FIRST_FRAME_TIMEOUT: Duration = Duration::from_secs(30);

/// How many capabilities one connection's KEYRING may hold. A connection presents
/// several narrow grants (read one subtree, commit under another, publish as a bound
/// principal in a third) rather than one wide one, and each request is authorized
/// EXISTENTIALLY over the ring. The bound keeps an attacker from making the per-request
/// check (linear in the ring) expensive.
pub const MAX_KEYRING: usize = 16;

/// The longest subject, filter, consumer-group name, `Last` cursor or capability
/// grant a request may carry, in bytes. The frame cap alone would admit a 16 MiB name,
/// and parsing and matching one costs many times its size (a filter's segment
/// vectors; a subject's segment vector per keyring entry), so a request over this is
/// refused before anything parses it. Far above any real subject.
pub const MAX_NAME_LEN: usize = 4096;

/// Unix milliseconds, for the capability-expiry gate.
///
/// The wall clock is read HERE, at the connection boundary, and never inside
/// `astream-cap` — that crate is on the deterministic side of the effect seam,
/// where a clock read would make a replay depend on when it ran. A clock that
/// cannot be read at all yields 0, which expires nothing: a broken clock must
/// not become a way to revoke a fleet's capabilities, and it must not become a
/// way to resurrect them either (0 is before every real `exp`).
fn now_unix_ms() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_millis() as u64)
}

/// `Some(now)` once the authority that admitted a streaming verb has lapsed:
/// `until` is the unix-ms instant from `cap_authorized_until`, and `u64::MAX` —
/// the value on an unguarded broker, and for grants without an expiry — never
/// lapses (and reads no clock).
fn lapsed(until: u64) -> Option<u64> {
    if until == u64::MAX {
        return None;
    }
    let now = now_unix_ms();
    (now >= until).then_some(now)
}

/// End a streaming verb whose authority lapsed at `until`: flush what `out` already
/// gathered (it was read while authorized), then say why the stream ends.
fn end_lapsed<S: Write>(stream: &mut S, out: &mut Vec<u8>, until: u64, now: u64) -> io::Result<()> {
    append_frame(
        out,
        &encode_response(&Response::Error {
            code: 5,
            msg: format!("unauthorized: capability expired at {until} (now {now}, unix ms)"),
        }),
    )?;
    flush_egress(stream, out)
}

/// A fresh 32-byte nonce for one connection's capability handshake.
///
/// HONEST BOUNDARY: what the protocol needs from this value is FRESHNESS — an
/// `Attach`'s proof is `HMAC-SHA256(tag, nonce ‖ grant)`, so a proof captured from
/// another connection is refused because that connection's nonce was a different
/// value. It is built from std alone: four independent `RandomState`s (each seeded
/// from the OS once per thread, then incremented per construction), a process-wide
/// counter and the wall clock. That is not an OS CSPRNG read per nonce — std exposes
/// none on the stable toolchain, and the DEFAULT broker has no dependency that does
/// (adding one would break the zero-third-party rule this crate keeps). It is a
/// distinct, hard-to-predict value per connection; it is not claimed to be
/// cryptographically random.
fn fresh_nonce() -> [u8; 32] {
    use std::collections::hash_map::RandomState;
    use std::hash::{BuildHasher, Hasher};
    static NONCE_SEQ: AtomicU64 = AtomicU64::new(0);
    let seq = NONCE_SEQ.fetch_add(1, Ordering::Relaxed);
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos() as u64)
        .unwrap_or(0);
    let mut out = [0u8; 32];
    for (i, chunk) in out.chunks_mut(8).enumerate() {
        let mut h = RandomState::new().build_hasher();
        h.write_u64(seq);
        h.write_u64(i as u64);
        h.write_u64(now);
        chunk.copy_from_slice(&h.finish().to_le_bytes());
    }
    out
}

/// Records a streaming verb copies out of the log under ONE hold of its lock: a
/// subscriber catching up from an old cursor, or a `ForkSubscribe` snapshot, reads the
/// log this many records at a time and releases the lock between them. The copy is of
/// shared `Arc` handles (no payload), but it is one per record, so without this bound
/// a reader starting at offset 0 of a long log would hold every publisher off for a
/// copy of the whole log. Delivery is unchanged by it: in order, exactly once, across
/// every chunk boundary.
pub const TAIL_CHUNK: usize = 4096;

/// Records ONE [`Request::Fetch`] may scan, whatever its filter matches. A bounded
/// read is bounded in WORK, not only in output: without this a sparse filter over a
/// long log would hold the log lock for a whole-history walk, which a read-only
/// holder could loop to stall ingest. A page that scans this many records and matches
/// none still advances the client's cursor (`Mark.next` counts scanned records), so
/// paging always makes progress.
pub const FETCH_SCAN_MAX: usize = 65536;

/// Index entries ONE [`Request::Last`] may visit, matched or not — `Fetch`'s bound,
/// worn by the sibling verb. The last-value index is ordered by subject, so a page
/// starts with an `O(log n)` seek to the filter's literal prefix; but a filter whose
/// matches are SPARSE inside that prefix (`/f/F/pub/*/*/ack/<B>` over an index holding
/// one `ack` subject per member per barrier ever issued) pays a parse and a match test
/// for every entry it skips, with the log lock held — the whole-index walk a read-only
/// holder could loop to stall ingest. A page cut off here still advances the client's
/// cursor, so paging always progresses; `last_page` re-takes the lock and continues
/// the walk when the entry it stopped on is one the caller's filter does not cover, so
/// what reaches the wire as `Mark.resume` is never a subject outside that filter.
pub const LAST_SCAN_MAX: usize = 65536;

/// Rows ONE [`Request::Last`] may DELIVER, whatever the client asked for. `max` is a
/// client-chosen `u32` on the wire; without this clamp a single request could ask the
/// broker to clone and frame every subject it has ever seen. The client pages instead,
/// through `Mark.resume`.
pub const LAST_PAGE_MAX: u32 = 4096;

/// How many `LAST_SCAN_MAX`-bounded rounds ONE [`Request::Last`] may take while it
/// looks for a resume position the caller's own filter covers. Each round takes and
/// releases the log lock, so this bounds a request's total CPU, never a lock hold. See
/// `last_page`: past it the request is refused rather than answered with a cursor
/// naming a subject outside the filter (and outside the grant that contained it).
pub const LAST_RESUME_ROUNDS: usize = 64;

/// Cap on simultaneously open connections (each is a thread, plus an ack-writer thread
/// once it writes). Beyond it a new connection is answered with an error and closed,
/// so an unauthenticated flood cannot exhaust threads/fds — the broker keeps serving
/// the connections it has. Generous for a fleet of agents; a hard bound, not tuning.
/// Tunable per broker via [`Broker::set_max_conns`].
pub const MAX_CONNS: usize = 1024;

/// How long a connection refused at [`MAX_CONNS`] stays open after its refusal,
/// reading and discarding what the client sends (see `linger_refused`).
const REFUSAL_LINGER: Duration = Duration::from_millis(500);

/// How many refused connections may linger at once. Past it a refusal closes at once,
/// so a flood cannot turn the lingering into a thread sink.
const MAX_LINGERING_REFUSALS: usize = 64;

/// Socket timeout (connect / read / write) on a leader's link to a follower, and the
/// bound on how long a batch can wait on a follower that never answers: a timed-out
/// follower is a FAILED confirmation for that batch (its link is dropped and
/// re-established on the next batch), never an indefinite stall of the writer.
/// [`Broker::open_replicated_with`] takes an explicit value.
pub const REPLICA_IO_TIMEOUT: Duration = Duration::from_secs(5);

/// Records the leader keeps in flight to a follower before draining their acks —
/// pipelined shipping (the follower's ack-writer streams them back in order), bounded
/// well under the follower's `PIPELINE_DEPTH` so the two sides can never wedge.
const REPLICA_WINDOW: usize = 256;

/// The connection abstraction the broker serves over: any byte stream with the two
/// socket timeouts the tail loop needs. Implemented for a local Unix socket
/// (same-machine), plaintext TCP (multi-machine on a TRUSTED network), and — with
/// the `aead` feature — an XChaCha20-Poly1305 `SealedStream` over TCP (confidential
/// and authenticated: [`Broker::serve_tcp_sealed`]). The same Frame protocol rides
/// all three; capability enforcement (the `cap` feature, [`Broker::open_guarded`])
/// is orthogonal to the transport.
trait Stream: Read + Write + Send + Sized + ConnShutdown + 'static {
    fn set_read_timeout(&self, d: Option<Duration>) -> io::Result<()>;
    fn set_write_timeout(&self, d: Option<Duration>) -> io::Result<()>;
    /// A second handle to the same socket, so the read half (draining requests) and
    /// the ack-writer half (streaming acks back) run concurrently — single-connection
    /// pipelining. Read and write are independent directions on the same fd.
    fn try_clone(&self) -> io::Result<Self>;
}
#[cfg(unix)]
impl Stream for UnixStream {
    fn set_read_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        UnixStream::set_read_timeout(self, d)
    }
    fn set_write_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        UnixStream::set_write_timeout(self, d)
    }
    fn try_clone(&self) -> io::Result<Self> {
        UnixStream::try_clone(self)
    }
}
impl Stream for TcpStream {
    fn set_read_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        TcpStream::set_read_timeout(self, d)
    }
    fn set_write_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        TcpStream::set_write_timeout(self, d)
    }
    fn try_clone(&self) -> io::Result<Self> {
        TcpStream::try_clone(self)
    }
}

/// Where the broker listens, so shutdown can clean up the endpoint (unlink a Unix
/// socket) and [`BrokerHandle::tcp_addr`] can report a bound TCP address.
/// The Unix-socket endpoint is cfg(unix): std has no Unix-domain sockets on
/// Windows, where TCP ([`Broker::serve_tcp`]) is the only transport.
enum Endpoint {
    #[cfg(unix)]
    Unix(PathBuf),
    Tcp(String),
}

/// Map a bound socket address to one that can be *connected to*, for
/// [`BrokerHandle::tcp_addr`]: an unspecified host (`0.0.0.0` / `::`) becomes
/// loopback, keeping the port, so a port-0 bind reports an address a local client can
/// dial. A concrete host is returned unchanged. (`SocketAddr`'s `Display` brackets
/// IPv6 for us.) Shutdown does not depend on it — the acceptor polls `running`.
fn connectable_addr(addr: SocketAddr) -> String {
    if addr.ip().is_unspecified() {
        let loopback = match addr.ip() {
            IpAddr::V4(_) => IpAddr::V4(Ipv4Addr::LOCALHOST),
            IpAddr::V6(_) => IpAddr::V6(Ipv6Addr::LOCALHOST),
        };
        SocketAddr::new(loopback, addr.port()).to_string()
    } else {
        addr.to_string()
    }
}

/// How often a parked subscriber wakes to probe whether its peer disconnected (a
/// never-matching subscriber never writes, so it would otherwise never notice a
/// dead client). This is a liveness heartbeat, NOT a delivery poll — a publish
/// still wakes the tail immediately via the `Condvar`.
const LIVENESS_POLL: Duration = Duration::from_millis(200);

/// How long ONE liveness probe may block reading the subscriber's socket. The probe
/// is a timed `read` (see `peer_gone`), and while the tail sits in it a publish's
/// `Condvar` wakeup finds nobody waiting — the record waits out the probe instead.
/// Every subscriber idle past `LIVENESS_POLL` probes, so this timeout is added to
/// the delivery latency of whatever is published during the probe: keep it the
/// shortest the socket accepts.
const PEER_PROBE_TIMEOUT: Duration = Duration::from_millis(1);

struct Shared {
    log: Mutex<BrokerLog>,
    tail: Condvar,
    /// The SUBSCRIBER-VISIBLE head: subscribers are delivered records below it. In the
    /// Strict/Relaxed tiers it is the log's durable head (advanced under the log lock
    /// as each batch commits). In the Replicated tier it is the QUORUM WATERMARK — the
    /// offset below which a quorum of followers holds every record — so a leader-side
    /// consumer never reads a record no follower has yet.
    head: AtomicU64,
    running: AtomicBool,
    /// Producers enqueue durable mutations here; the single writer thread drains and
    /// group-commits them. Keeping all writes on one thread means dedup + the offset
    /// spine advance in order with no cross-thread append race.
    writes: Sender<WriteOp>,
    /// Live connection sockets (a clone per accepted connection), so shutdown can
    /// force-close any thread parked in a blocking socket read/write and reap it.
    conns: Mutex<HashMap<u64, Box<dyn ConnShutdown>>>,
    conn_seq: AtomicU64,
    /// `Some` in the Replicated durability tier: after each batch commits locally, the
    /// writer ships every not-yet-confirmed record to the followers and an `ack` is
    /// gated on the quorum watermark.
    replicator: Option<Replicator>,
    /// `Some` when the broker enforces capabilities on the accept path (built with
    /// the `cap` feature via `open_guarded`): every non-`Attach` request must be
    /// authorized by the connection's presented capability. `None` = no enforcement.
    #[cfg_attr(not(feature = "cap"), allow(dead_code))]
    cap_secret: Option<Vec<u8>>,
    /// [`FIRST_FRAME_TIMEOUT`], in milliseconds ([`Broker::set_first_frame_timeout`]).
    first_frame_timeout_ms: AtomicU64,
    /// How long ONE response write on a served connection may block before the
    /// connection is torn down, in milliseconds ([`Broker::set_write_timeout`]).
    write_timeout_ms: AtomicU64,
    /// [`MAX_CONNS`] ([`Broker::set_max_conns`]).
    max_conns: AtomicUsize,
    /// Connections refused at the cap that are still lingering (`linger_refused`).
    refusing: AtomicUsize,
    /// [`Broker::on_last_scan_round`]: the test seam fired at each `last_page` round
    /// boundary. `None` — and one uncontended lock per boundary, never per record —
    /// unless a test installs one.
    #[allow(clippy::type_complexity)]
    last_round_hook: Mutex<Option<Arc<dyn Fn(usize) + Send + Sync>>>,
}

/// Leader-side replication for the Replicated durability tier. Each follower link
/// tracks the follower's CONFIRMED PREFIX (`upto`); every batch re-ships each follower
/// every committed record from its own prefix to the head (followers append at the
/// leader's exact offset and dedup what they already hold, so this is idempotent and
/// catches a follower up after a link drop), and the batch's acks are gated on the
/// QUORUM WATERMARK — the `quorum`-th highest prefix. A Replicated `ack` therefore
/// means a quorum of followers holds the record in memory: it survives the loss of
/// the leader node, but NOT a full-cluster power loss; the dial's middle setting
/// (Kafka's default posture). The local write is Relaxed (page cache), so durability
/// comes from the replicas, not fsync. Nothing here is vacuous: a deduped retry, a
/// pure commit, or an op in a batch whose replication failed is acked ONLY once its
/// offset is below the watermark.
struct Replicator {
    links: Mutex<Vec<FollowerLink>>,
    /// Per-link socket clones so [`BrokerHandle::shutdown`] can force-close a follower
    /// link the writer is parked on (a follower that never answers) without waiting
    /// for the I/O timeout.
    kill: Mutex<Vec<Option<TcpStream>>>,
    quorum: usize,
    io_timeout: Duration,
}

/// One follower's replication link, driven only by the writer thread.
struct FollowerLink {
    addr: String,
    /// `None` while the link is down (dropped after an I/O error / timeout); it is
    /// re-established on the next batch. A per-record REFUSAL from the follower (a
    /// `Response::Error`) does not drop the link — the stream stays in sync.
    stream: Option<TcpStream>,
    /// This follower's CONFIRMED PREFIX: it has acknowledged every leader record with
    /// offset `< upto`, in order. What a follower confirmed, it holds, even if the link
    /// later drops — and the point re-shipping resumes from. It starts at the leader
    /// log's retention BASE: nothing below it exists to ship. Reset to 0 only when the
    /// follower reports a GAP (it restarted having lost its tail, or never held the
    /// records below the base): shipping then starts over from 0 on the next batch and
    /// the follower dedups what it still holds — unless retention has pruned the
    /// leader's log above 0, in which case the records it lacks are gone and it is LEFT
    /// BEHIND, shipped nothing more (see [`Replicator::replicate`]).
    upto: u64,
    /// `Some(reason)` once the follower REFUSED a record in a way SHIPPING CANNOT
    /// REPAIR — a different record already at that offset (its log diverged from the
    /// leader's), or unauthorized — so its prefix can never grow: no more is shipped
    /// to it. Its stuck `upto` still counts toward the quorum for the prefix it really
    /// did confirm — an honest count, never a silent desync — but it can never advance
    /// the watermark past that point, and it is not counted at all when deciding where
    /// a batch's re-ship starts ([`Replicator::min_upto`]). Cleared only by reopening
    /// the leader.
    ///
    /// A TRANSIENT refusal (the follower is at its connection cap, its disk errored,
    /// its log is poisoned) is NOT a fence: it merely ends the confirmed prefix for
    /// that batch, and shipping resumes from the same point on the next one.
    fenced: Option<String>,
    /// Set when `Replicator::redial` has just dialed `stream` for this batch: a fresh
    /// link that fails is down for the rest of the batch, where a stale one (the
    /// follower may have closed an idle connection) is re-dialed once.
    fresh: bool,
}

/// Dial a follower with the replication timeouts applied to the socket.
fn connect_follower(addr: &str, timeout: Duration) -> io::Result<TcpStream> {
    let mut last = io::Error::new(
        io::ErrorKind::NotFound,
        format!("follower {addr}: no address"),
    );
    for sa in addr.to_socket_addrs()? {
        match TcpStream::connect_timeout(&sa, timeout) {
            Ok(s) => {
                s.set_nodelay(true)?;
                s.set_read_timeout(Some(timeout))?;
                s.set_write_timeout(Some(timeout))?;
                return Ok(s);
            }
            Err(e) => last = e,
        }
    }
    Err(last)
}

impl FollowerLink {
    /// Ship one window of `records` (contiguous, `records[0].seq == self.upto`) over
    /// `stream` (taken out of `self.stream` by the caller): write up to
    /// [`REPLICA_WINDOW`] Replicate requests, then read their acks in order, advancing
    /// `upto` past each record the follower confirms IN ORDER. `Ok(n)` with `n` equal
    /// to the window means every record was confirmed (keep going); `n` short of it
    /// means a record was refused, acked out of order, or the broker is stopping (stop
    /// — the link stays in sync because the window's remaining acks were drained). A
    /// GAP refusal resets `upto` to 0 (re-ship from scratch next batch, if the leader
    /// still holds offset 0; see `upto`); a DIVERGENCE or an authorization refusal
    /// fences the link; any other refusal is transient and only ends this batch. `Err`
    /// is an I/O error / timeout / EOF: the link is down.
    fn ship_window(
        &mut self,
        stream: &mut TcpStream,
        records: &[Arc<BrokerRecord>],
        running: &AtomicBool,
    ) -> io::Result<usize> {
        if !running.load(Ordering::Relaxed) {
            return Ok(0);
        }
        let window = &records[..records.len().min(REPLICA_WINDOW)];
        for r in window {
            let payload = encode_replicate(
                r.seq.0,
                r.producer_id,
                r.producer_seq,
                &r.subject,
                &r.body,
                r.commit.as_ref().map(|c| (c.group.as_str(), c.upto)),
            );
            write_frame(stream, &payload)?;
        }
        let mut confirmed = 0usize;
        let mut stopped = false;
        for r in window {
            let payload = read_frame(stream)?
                .ok_or_else(|| io::Error::new(io::ErrorKind::UnexpectedEof, "follower closed"))?;
            if stopped {
                continue; // drain, so the stream stays in sync for the next batch
            }
            match decode_response(&payload) {
                Some(Response::PublishAck { offset, .. })
                    if offset == r.seq.0 && self.upto == r.seq.0 =>
                {
                    self.upto = r.seq.0.saturating_add(1);
                    confirmed += 1;
                }
                // Refused: the confirmed prefix ends here and nothing after it counts.
                // A gap means the follower's log is SHORTER than the prefix this link
                // confirmed (it restarted having lost its tail): start over from 0
                // next batch. A DIVERGENCE (a different record already at that offset)
                // or an authorization refusal cannot be repaired by shipping, ever:
                // fence the link. ANYTHING ELSE is TRANSIENT — the follower is at its
                // connection cap, its disk errored, its log is poisoned — and must NOT
                // fence a follower the leader could still catch up: the prefix simply
                // ends here for this batch and shipping resumes from it on the next.
                Some(Response::Error { msg, .. }) => {
                    if msg.starts_with("replica gap") {
                        self.upto = 0;
                    } else if msg.starts_with("replica diverged") || msg.starts_with("unauthorized")
                    {
                        self.fenced = Some(msg);
                    }
                    stopped = true;
                }
                // Acked out of order: the confirmed prefix ends here. The rest of the
                // window is still drained below, so the stream stays in sync and is
                // reused on the next batch.
                Some(Response::PublishAck { .. }) => stopped = true,
                _ => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "unexpected follower response",
                    ))
                }
            }
        }
        Ok(confirmed)
    }

    fn reconnect(
        &mut self,
        i: usize,
        timeout: Duration,
        running: &AtomicBool,
        kill: &Mutex<Vec<Option<TcpStream>>>,
    ) -> Option<TcpStream> {
        if !running.load(Ordering::Relaxed) {
            return None;
        }
        let s = connect_follower(&self.addr, timeout).ok()?;
        kill.lock().unwrap()[i] = s.try_clone().ok();
        Some(s)
    }

    /// Ship `records` (leader offsets `[self.upto, ..)`, contiguous), window by window,
    /// advancing `upto` as the follower confirms. A link that is down (its re-dial at
    /// the start of the batch failed) ships nothing. A stale link that fails mid-way is
    /// re-dialed ONCE and shipping resumes from the confirmed prefix (the follower
    /// dedups anything it already held — e.g. after it closed an idle connection); a
    /// fresh link that fails is dropped and this follower confirms nothing more this
    /// batch. `i` indexes this link's shutdown handle in `kill`.
    fn ship(
        &mut self,
        i: usize,
        records: &[Arc<BrokerRecord>],
        timeout: Duration,
        running: &AtomicBool,
        kill: &Mutex<Vec<Option<TcpStream>>>,
    ) {
        let base = match records.first() {
            Some(r) => r.seq.0,
            None => return,
        };
        let mut fresh = std::mem::take(&mut self.fresh);
        let Some(mut stream) = self.stream.take() else {
            return;
        };
        let mut pos = 0usize;
        while pos < records.len() {
            let want = (records.len() - pos).min(REPLICA_WINDOW);
            match self.ship_window(&mut stream, &records[pos..], running) {
                Ok(n) => {
                    pos += n;
                    if n < want {
                        break; // refused / out of order / stopping: prefix ends here
                    }
                }
                Err(_) => {
                    kill.lock().unwrap()[i] = None;
                    drop(stream);
                    if fresh {
                        return; // down: confirms nothing more this batch
                    }
                    // A stale link: re-dial once and resume from the confirmed prefix.
                    pos = usize::try_from(self.upto.saturating_sub(base)).unwrap_or(usize::MAX);
                    match self.reconnect(i, timeout, running, kill) {
                        Some(s) => {
                            fresh = true;
                            stream = s;
                        }
                        None => return,
                    }
                }
            }
        }
        self.stream = Some(stream);
    }
}

impl Replicator {
    /// Re-dial every follower whose link is down (and not fenced) — at the start of a
    /// batch, before it reads the log for them. One that answers is caught up in this
    /// same batch; one still down is left out of the re-ship base (`min_upto`).
    fn redial(&self, running: &AtomicBool) {
        let mut links = self.links.lock().unwrap();
        for (i, link) in links.iter_mut().enumerate() {
            link.fresh = false; // fresh only for the batch that dialed it
            if link.fenced.is_none() && link.stream.is_none() {
                link.stream = link.reconnect(i, self.io_timeout, running, &self.kill);
                link.fresh = link.stream.is_some();
            }
        }
    }

    /// The lowest confirmed prefix over the followers a batch can still ship to:
    /// where the re-ship must start so every LIVE follower is caught up from ITS OWN
    /// prefix. `floor` is the leader log's retention base.
    ///
    /// DOWN LINKS ARE NOT COUNTED either: nothing reaches a follower whose re-dial just
    /// failed, and the slice below its prefix — cloned under the log lock, one `Arc`
    /// per record — would grow with every batch for as long as it stays down.
    ///
    /// FENCED LINKS ARE NOT COUNTED, because `replicate` skips them: nothing is ever
    /// shipped to a diverged or unauthorized follower, so its `upto` is frozen for the
    /// life of the leader. Counting it would pin this base at that frozen offset, and
    /// the base is the start of a slice the writer clones UNDER THE LOG LOCK — one
    /// `Arc` per record, `head - upto` of them, growing without bound, on every batch,
    /// for a copy the healthy followers then skip in full. `fallback` (the head) is the
    /// answer when no link can be shipped to at all, so that slice is empty rather than
    /// the whole log.
    ///
    /// LINKS BEHIND `floor` ARE NOT COUNTED, for the same reason: retention pruned the
    /// records they lack, `replicate` never ships to them again, and their `upto` is as
    /// frozen as a fenced link's.
    fn min_upto(&self, floor: u64, fallback: u64) -> u64 {
        self.links
            .lock()
            .unwrap()
            .iter()
            .filter(|l| l.fenced.is_none() && l.stream.is_some() && l.upto >= floor)
            .map(|l| l.upto)
            .min()
            .unwrap_or(fallback)
    }

    /// Ship every committed-but-unconfirmed record to each follower (from that
    /// follower's own confirmed prefix; `records` is contiguous from its first
    /// record's offset), then return the QUORUM WATERMARK: the offset below which at
    /// least `quorum` followers hold every record. Never vacuous — with nothing to
    /// ship, or every follower down or fenced, the watermark simply does not advance.
    ///
    /// The slice's base is its FIRST RECORD's offset, not the offset the caller asked
    /// `read_from` for: retention may have pruned the log above that, and `read_from`
    /// clamps up to the first retained record. A follower whose prefix is below the
    /// slice lacks records the leader no longer holds: it is left behind, shipped
    /// nothing, counted in the watermark only for the prefix it confirmed.
    fn replicate(&self, records: &[Arc<BrokerRecord>], running: &AtomicBool) -> u64 {
        let mut links = self.links.lock().unwrap();
        let base = records.first().map_or(u64::MAX, |r| r.seq.0);
        for (i, link) in links.iter_mut().enumerate() {
            if !running.load(Ordering::Relaxed) {
                break;
            }
            if link.fenced.is_some() {
                continue; // diverged / unauthorized: nothing shipped can repair it
            }
            let Some(skip) = link.upto.checked_sub(base) else {
                continue; // its prefix is below this slice (pruned): nothing to ship
            };
            let skip = usize::try_from(skip)
                .unwrap_or(usize::MAX)
                .min(records.len());
            let todo = &records[skip..];
            if todo.is_empty() {
                continue;
            }
            link.ship(i, todo, self.io_timeout, running, &self.kill);
        }
        Self::watermark(&links, self.quorum)
    }

    fn watermark(links: &[FollowerLink], quorum: usize) -> u64 {
        let mut uptos: Vec<u64> = links.iter().map(|l| l.upto).collect();
        uptos.sort_unstable_by(|a, b| b.cmp(a));
        uptos.get(quorum.saturating_sub(1)).copied().unwrap_or(0)
    }

    /// Force-close every live follower socket so a writer parked on a follower that
    /// never answers returns immediately (shutdown must not wait out the I/O timeout).
    fn shutdown_links(&self) {
        for k in self.kill.lock().unwrap().iter_mut() {
            if let Some(s) = k.take() {
                let _ = s.shutdown(Shutdown::Both);
            }
        }
    }
}

/// Deregisters a connection from [`Shared::conns`] on drop, so every `handle_conn`
/// return path (clean EOF, error, or a streaming verb taking over) cleans up.
struct ConnGuard<'a> {
    shared: &'a Arc<Shared>,
    id: u64,
}
impl Drop for ConnGuard<'_> {
    fn drop(&mut self) {
        self.shared.conns.lock().unwrap().remove(&self.id);
    }
}

/// A broker over one durable [`BrokerLog`].
pub struct Broker {
    shared: Arc<Shared>,
    /// The group-commit writer thread, handed to the [`BrokerHandle`] on `serve` so
    /// shutdown can join it. If it is still here when the `Broker` drops (never
    /// served), `Drop` stops and joins it.
    writer: Mutex<Option<JoinHandle<()>>>,
}

impl Broker {
    /// Open (creating if absent) a broker backed by the Strict durable log at `log_path`.
    pub fn open(log_path: impl AsRef<Path>) -> io::Result<Broker> {
        Broker::open_with(log_path, Durability::Strict)
    }

    /// Open a broker at the given [`Durability`] tier (Strict fsyncs every batch;
    /// Relaxed acks on page-cache write — lower latency, survives process crash but not
    /// power loss). The log is exclusively locked while open (a second broker on the
    /// same log fails `AlreadyExists`), and refuses to open a corrupt log — see
    /// [`BrokerLog::open_with`].
    pub fn open_with(log_path: impl AsRef<Path>, durability: Durability) -> io::Result<Broker> {
        let log = BrokerLog::open_with(log_path, durability)?;
        Ok(Self::start(log, None, None))
    }

    /// Open a broker that serves as a REPLICATION TARGET: a follower a leader ships
    /// `Replicate` records to. Exactly [`open_with`](Self::open_with) at the same tier,
    /// plus the log declared a replica before it takes its first record — the tier is
    /// the operator's choice here as everywhere else, and `open_replica` is
    /// [`open`](Self::open)'s Strict default.
    ///
    /// A follower brought up on an EMPTY log never needs this: the first record a
    /// leader ships to a still-empty log declares it. It is REQUIRED for the other
    /// case — a follower seeded from a copy of the leader's log, whose log already has
    /// records but has never taken one through replication. A replicated record
    /// accepted beside records that were already there does NOT declare it, because
    /// accepting one says nothing about whose log it is (any client can send a
    /// `Replicate`), so on a seeded follower the declaration is the only thing that
    /// tells the two apart.
    ///
    /// WHAT BEING A REPLICA MEANS, EXACTLY: this broker appends nothing to the log on
    /// its OWN initiative — it does not fire the wills the log holds when it opens
    /// (they are the leader's, and they fire there). That is the whole of what the
    /// marker enforces.
    ///
    /// It does NOT make the log append-proof. A client that reaches this broker's
    /// listener can still `Publish`, `Commit` or `ProcessAndProduce`, and the record
    /// lands at the follower's own next offset — after which the leader's next ship to
    /// that offset is refused `Diverged`, the link is fenced for good, and with
    /// quorum == follower count every later leader publish answers "not replicated to
    /// quorum". So do not expose a replica's listener to publishers: a monitoring
    /// script or a bridge pointed at the wrong endpoint is enough to make the cluster
    /// write-unavailable.
    pub fn open_replica(log_path: impl AsRef<Path>) -> io::Result<Broker> {
        Self::open_replica_with(log_path, Durability::Strict)
    }

    /// [`open_replica`](Self::open_replica) at an explicit [`Durability`] tier.
    pub fn open_replica_with(
        log_path: impl AsRef<Path>,
        durability: Durability,
    ) -> io::Result<Broker> {
        let mut log = BrokerLog::open_with(log_path, durability)?;
        log.declare_replica()?;
        Ok(Self::start(log, None, None))
    }

    /// Open a broker whose durable log is ENCRYPTED AT REST: every record's payload
    /// is sealed on disk under `key` (XChaCha20-Poly1305), so the forensic value of
    /// the log — a verbatim recording of every keystroke and screen frame — is gone
    /// to anyone without the key. The wire protocol and all in-memory behaviour are
    /// unchanged; recovery decrypts, and refuses (rather than discards) on a wrong key
    /// or a tampered log. Off by default (the `at-rest` feature). Strict.
    #[cfg(feature = "at-rest")]
    pub fn open_encrypted(log_path: impl AsRef<Path>, key: [u8; 32]) -> io::Result<Broker> {
        let log = BrokerLog::open_encrypted(log_path, key)?;
        Ok(Self::start(log, None, None))
    }

    /// [`open_encrypted`](Self::open_encrypted) at a chosen [`Durability`].
    #[cfg(feature = "at-rest")]
    pub fn open_encrypted_with(
        log_path: impl AsRef<Path>,
        durability: Durability,
        key: [u8; 32],
    ) -> io::Result<Broker> {
        let log = BrokerLog::open_encrypted_with(log_path, durability, key)?;
        Ok(Self::start(log, None, None))
    }

    /// [`open_encrypted`](Self::open_encrypted) with ANTI-ROLLBACK: an authenticated
    /// monotonic head watermark is maintained and verified, so a write-capable attacker
    /// cannot silently truncate the log to an earlier state. A rolled-back log (or a
    /// deleted watermark on a non-empty log) is refused. Bootstrap once with
    /// [`open_encrypted_verified_init`](Self::open_encrypted_verified_init). Strict.
    #[cfg(feature = "anti-rollback")]
    pub fn open_encrypted_verified(
        log_path: impl AsRef<Path>,
        key: [u8; 32],
    ) -> io::Result<Broker> {
        let log = BrokerLog::open_encrypted_verified(log_path, key)?;
        Ok(Self::start(log, None, None))
    }

    /// Bootstrap [`open_encrypted_verified`](Self::open_encrypted_verified): establish
    /// the head watermark at the current head (first adoption of anti-rollback).
    #[cfg(feature = "anti-rollback")]
    pub fn open_encrypted_verified_init(
        log_path: impl AsRef<Path>,
        key: [u8; 32],
    ) -> io::Result<Broker> {
        let log = BrokerLog::open_encrypted_verified_init(log_path, key)?;
        Ok(Self::start(log, None, None))
    }

    /// RETENTION: compact the durable log, dropping records with offset `< min_offset`
    /// (kept records keep their absolute offsets). A consumer below the new base
    /// catches up from the earliest retained. Cold + explicit; returns the number of
    /// records dropped. Off by default (the `retention` feature).
    #[cfg(feature = "retention")]
    pub fn retain_before(&self, min_offset: u64) -> io::Result<u64> {
        let mut log = self.shared.log.lock().unwrap();
        log.retain_before(Offset(min_offset))
    }

    /// Spawn the writer over an opened log.
    fn start(
        log: BrokerLog,
        replicator: Option<Replicator>,
        cap_secret: Option<Vec<u8>>,
    ) -> Broker {
        // Strict/Relaxed: everything durable is visible. Replicated: only what a quorum
        // already confirmed (the caller caught the followers up before handing us
        // the replicator, so the watermark is the current one).
        let head = match &replicator {
            Some(rep) => Replicator::watermark(&rep.links.lock().unwrap(), rep.quorum),
            None => log.head().0,
        };
        let (writes, rx) = mpsc::channel::<WriteOp>();
        let shared = Arc::new(Shared {
            log: Mutex::new(log),
            tail: Condvar::new(),
            head: AtomicU64::new(head),
            running: AtomicBool::new(true),
            writes,
            conns: Mutex::new(HashMap::new()),
            conn_seq: AtomicU64::new(0),
            replicator,
            cap_secret,
            first_frame_timeout_ms: AtomicU64::new(FIRST_FRAME_TIMEOUT.as_millis() as u64),
            write_timeout_ms: AtomicU64::new(ACK_WRITE_TIMEOUT.as_millis() as u64),
            max_conns: AtomicUsize::new(MAX_CONNS),
            refusing: AtomicUsize::new(0),
            last_round_hook: Mutex::new(None),
        });
        let w_shared = shared.clone();
        let writer = thread::spawn(move || writer_loop(&w_shared, rx));
        // A BROKER RESTART IS A PRESENCE EPOCH — for a broker that OWNS its log.
        // Every connection died with no connection thread left to fire its will, so on
        // open every will the log still holds is fired through the same fence. A
        // producer that reconnects and publishes above its will's sequence suppresses
        // it; a will that already fired dedups to a no-op; a producer that really died
        // is marked gone exactly once. Without this a node that died while the broker
        // was down would read `live` forever.
        //
        // NOT ON A REPLICA. A replication target's log is the LEADER's spine, and the
        // wills on it are the leader's — shipped like every other record. Firing one
        // here would append, at this follower's own next offset, a record the leader
        // does not have: a forged death notice for a node that is still live, a log
        // that is no longer a prefix of the leader's, and — at the leader's next ship
        // to that offset — a `Diverged` refusal that fences the link for good. Whose
        // log this is, is a durable property of the log itself
        // ([`BrokerLog::is_replica`]), so a follower restarted through plain
        // [`Broker::open`] is still a follower.
        let pending = {
            let log = shared.log.lock().unwrap();
            if log.is_replica() {
                Vec::new()
            } else {
                log.pending_wills()
            }
        };
        for will in pending {
            fire_will(&shared, will);
        }
        Broker {
            shared,
            writer: Mutex::new(Some(writer)),
        }
    }

    /// Open a broker that ENFORCES capabilities on its accept path: every
    /// connection must `Attach` a capability (a signed astream_wire Filter) that
    /// grants each subject it publishes and contains each filter it subscribes;
    /// unauthorized requests are refused. Without the `cap` feature there is no way
    /// to set a secret, so the default broker never enforces (and stays zero-dep).
    ///
    /// An EMPTY `secret` is refused (`InvalidInput`): an HMAC under an empty key is
    /// computable by anyone, so it would admit any capability anyone cares to mint.
    ///
    /// A connection must have a capability accepted within [`FIRST_FRAME_TIMEOUT`] of
    /// connecting ([`set_first_frame_timeout`](Self::set_first_frame_timeout)), or it
    /// is refused and closed: nothing it can send before that authenticates it.
    #[cfg(feature = "cap")]
    pub fn open_guarded(log_path: impl AsRef<Path>, secret: Vec<u8>) -> io::Result<Broker> {
        if secret.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "open_guarded: the capability secret is empty, so anyone could mint a \
                 capability it accepts",
            ));
        }
        let log = BrokerLog::open_with(log_path, Durability::Strict)?;
        Ok(Self::start(log, None, Some(secret)))
    }

    /// Open a broker in the REPLICATED durability tier. The local write is page-cache
    /// (Relaxed, no fsync); an `ack` ADDITIONALLY requires a `quorum` of `follower_addrs`
    /// (other brokers reachable over TCP — ordinary `serve_tcp` brokers) to hold the
    /// record in memory. So an acked record survives the loss of the leader node — a
    /// follower holds it — though not a full-cluster power loss. This is the dial's
    /// middle setting (Kafka's default posture: durability from replicas, not fsync).
    ///
    /// The leader ships every committed record (data, commit records, and their
    /// annotations) at its exact leader offset, so a follower's log is an identical
    /// prefix of the leader's; shipping resumes from each follower's confirmed prefix,
    /// so a follower whose link dropped is caught up automatically once it is back,
    /// and an ack — for a new record, a deduped retry, or a pure commit — is given only
    /// once the record is below the quorum watermark. Leader-side subscribers are
    /// delivered only quorum-confirmed records.
    ///
    /// At open, every follower is dialed and the reachable ones are caught up to the
    /// local log (an error if a quorum does not confirm it — a follower refused or
    /// diverged). A follower that cannot be dialed is a DOWN link, re-dialed on every
    /// batch and caught up when it is back — unless fewer than `quorum` followers are
    /// reachable, which is refused as a configuration error. `quorum` is clamped to
    /// `1..=followers.len()`, and a follower-less "replicated" broker is refused
    /// (`InvalidInput`) rather than degrading silently to Relaxed with a vacuous quorum.
    /// A follower whose log DIVERGED (a different record at an offset the leader ships)
    /// is fenced: nothing more is shipped to it and it never counts toward the quorum.
    /// A log compacted by retention opens too: shipping starts at its base, and a
    /// follower that lacks records below the base — gone from the leader — cannot be
    /// caught up, so it is left behind, counting toward the quorum only for what it
    /// holds. Follower round-trips use [`REPLICA_IO_TIMEOUT`]-bounded sockets: a follower
    /// that never answers fails that batch's confirmation rather than stalling the
    /// writer, and shutdown force-closes the links.
    pub fn open_replicated(
        log_path: impl AsRef<Path>,
        follower_addrs: &[String],
        quorum: usize,
    ) -> io::Result<Broker> {
        Self::open_replicated_with(log_path, follower_addrs, quorum, REPLICA_IO_TIMEOUT)
    }

    /// [`open_replicated`](Self::open_replicated) with an explicit follower I/O timeout
    /// (connect / per-read / per-write on each follower link; the bound on how long a
    /// batch waits on an unresponsive follower).
    pub fn open_replicated_with(
        log_path: impl AsRef<Path>,
        follower_addrs: &[String],
        quorum: usize,
        replica_timeout: Duration,
    ) -> io::Result<Broker> {
        if follower_addrs.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "the Replicated tier needs at least one follower (no replica means no \
                 quorum, which would silently be the Relaxed tier)",
            ));
        }
        let log = BrokerLog::open_with(log_path, Durability::Relaxed)?;
        // Every link's confirmed prefix starts at the log's retention BASE: records
        // below it were pruned, so there is nothing below it to ship or confirm.
        let base = log.base().0;
        let quorum = quorum.clamp(1, follower_addrs.len());
        let mut links = Vec::with_capacity(follower_addrs.len());
        let mut kill = Vec::with_capacity(follower_addrs.len());
        let mut live = 0usize;
        let mut last_err: Option<io::Error> = None;
        for addr in follower_addrs {
            // A follower that cannot be dialed now is a DOWN link (re-dialed on every
            // batch, then caught up), not a fatal error — unless so many are down that
            // the quorum could never be met, which is a configuration error to fail
            // fast on rather than a broker that refuses every ack.
            let stream = match connect_follower(addr, replica_timeout) {
                Ok(s) => {
                    live += 1;
                    kill.push(s.try_clone().ok());
                    Some(s)
                }
                Err(e) => {
                    last_err = Some(e);
                    kill.push(None);
                    None
                }
            };
            links.push(FollowerLink {
                addr: addr.clone(),
                stream,
                upto: base,
                fenced: None,
                fresh: false,
            });
        }
        if live < quorum {
            let e = last_err.unwrap_or_else(|| io::Error::other("no follower reachable"));
            return Err(io::Error::new(
                e.kind(),
                format!(
                    "Replicated tier: only {live} of {} followers reachable, so a quorum of \
                     {quorum} could never confirm anything ({e})",
                    follower_addrs.len()
                ),
            ));
        }
        let rep = Replicator {
            links: Mutex::new(links),
            kill: Mutex::new(kill),
            quorum,
            io_timeout: replica_timeout,
        };
        // CATCH-UP: bring every follower up to the local log before serving, so the
        // leader starts with its visible head at the quorum watermark and a follower
        // restarted with its log intact merely confirms what it already holds.
        let head = log.head().0;
        let backlog = log.read_from(Offset(base));
        let wm = rep.replicate(&backlog, &AtomicBool::new(true));
        if wm < head {
            return Err(io::Error::other(format!(
                "Replicated tier: a quorum confirmed only {wm} of the {head} local records \
                 at open (a follower refused, diverged, or timed out)"
            )));
        }
        Ok(Self::start(log, Some(rep), None))
    }

    /// The durable head of the log (its record count; the offset the next commit
    /// takes).
    pub fn head(&self) -> u64 {
        self.shared.log.lock().unwrap().head().0
    }

    /// The SUBSCRIBER-VISIBLE head. Equal to [`head`](Self::head) in the Strict and
    /// Relaxed tiers; in the Replicated tier it is the quorum watermark — records at or
    /// above it are committed locally but not yet held by a quorum of followers, so
    /// they are neither acked nor delivered.
    pub fn visible_head(&self) -> u64 {
        self.shared.head.load(Ordering::Relaxed)
    }

    /// Arm (or clear) the log's documented fault-injection seam — see
    /// [`InjectedFaults`]. A test hook; inert unless called.
    pub fn inject_faults(&self, faults: InjectedFaults) {
        self.shared.log.lock().unwrap().inject_faults(faults);
    }

    /// Override how long a freshly accepted connection may take to send its first
    /// complete frame — on a guarded broker, to have a capability accepted — before it
    /// is reaped (default [`FIRST_FRAME_TIMEOUT`], 30 s). Applies to connections
    /// accepted after the call.
    pub fn set_first_frame_timeout(&self, timeout: Duration) {
        self.shared.first_frame_timeout_ms.store(
            timeout.as_millis().clamp(1, u64::MAX as u128) as u64,
            Ordering::Relaxed,
        );
    }

    /// Override how long ONE response write on a served connection may block before
    /// the connection is torn down (default [`ACK_WRITE_TIMEOUT`], 10 s). A peer that
    /// stops reading otherwise parks the connection thread inside `write_all` for good,
    /// holding its fd and its [`MAX_CONNS`] slot with it. Applies to connections
    /// accepted after the call.
    ///
    /// It bounds EVERY write on the connection: the request thread's, and the pipelined
    /// ack-writer's, which runs on a `try_clone` of the same socket and takes this value
    /// too (`SO_SNDTIMEO` belongs to the socket, not to the descriptor, so the two
    /// halves cannot hold different bounds). A streaming verb — `Subscribe`, `SubscribeGroup`, `ForkSubscribe` — raises it to
    /// [`STREAM_WRITE_TIMEOUT`] once it takes the socket over.
    pub fn set_write_timeout(&self, timeout: Duration) {
        self.shared.write_timeout_ms.store(
            timeout.as_millis().clamp(1, u64::MAX as u128) as u64,
            Ordering::Relaxed,
        );
    }

    /// Override the cap on simultaneously open connections (default [`MAX_CONNS`],
    /// 1024); a connection beyond it is answered with an error and closed.
    pub fn set_max_conns(&self, max: usize) {
        self.shared.max_conns.store(max, Ordering::Relaxed);
    }

    /// Run `hook` at every `Last` SCAN-ROUND BOUNDARY: after a round has added its
    /// rows, before the next round re-takes the log lock — the exact window a
    /// concurrent publisher gets. The argument is the index of the round that just
    /// finished.
    ///
    /// A test hook; inert unless called. It exists so a test can OCCUPY that window
    /// instead of racing for it — the hook runs on the connection's own thread with
    /// the log lock released, so it may publish through a second connection and block
    /// on the ack, and the walk does not resume until it returns.
    pub fn on_last_scan_round(&self, hook: impl Fn(usize) + Send + Sync + 'static) {
        *self.shared.last_round_hook.lock().unwrap() = Some(Arc::new(hook));
    }

    /// Bind the Unix socket at `socket_path` and start accepting clients. Returns a
    /// [`BrokerHandle`] that shuts the broker down and unlinks the socket on demand.
    /// A leftover socket file is unlinked only if nobody answers on it (stale, from a
    /// crashed broker); a LIVE broker there is `AddrInUse`, never silently displaced,
    /// and a path that is not a socket at all is `AlreadyExists`, never removed.
    /// cfg(unix): std has no Unix-domain sockets on Windows — use
    /// [`serve_tcp`](Self::serve_tcp) there.
    #[cfg(unix)]
    pub fn serve(&self, socket_path: impl AsRef<Path>) -> io::Result<BrokerHandle> {
        use std::os::unix::fs::FileTypeExt;
        let socket_path = socket_path.as_ref().to_path_buf();
        if let Ok(meta) = std::fs::symlink_metadata(&socket_path) {
            if !meta.file_type().is_socket() {
                return Err(io::Error::new(
                    io::ErrorKind::AlreadyExists,
                    format!(
                        "{}: exists and is not a socket; refusing to replace it",
                        socket_path.display()
                    ),
                ));
            }
            match UnixStream::connect(&socket_path) {
                Ok(_live) => {
                    return Err(io::Error::new(
                        io::ErrorKind::AddrInUse,
                        format!(
                            "{}: a broker is already listening on this socket",
                            socket_path.display()
                        ),
                    ))
                }
                Err(_) => {
                    let _ = std::fs::remove_file(&socket_path); // stale: nobody answers
                }
            }
        }
        let listener = UnixListener::bind(&socket_path)?;
        listener.set_nonblocking(true)?;
        let shared = self.shared.clone();
        let acceptor = thread::Builder::new().spawn(move || {
            // Non-blocking accept + poll: shutdown just flips `running` and the acceptor
            // observes it within ACCEPT_POLL — no racy one-shot self-connect wakeup.
            while shared.running.load(Ordering::Relaxed) {
                match listener.accept() {
                    Ok((s, _)) => {
                        // Stopping: close what the backlog handed us instead of
                        // spawning a handler shutdown could miss.
                        if !shared.running.load(Ordering::Relaxed) {
                            break;
                        }
                        // Accepted sockets MUST be blocking (the frame reader uses
                        // read_exact); do not inherit the listener's non-blocking mode.
                        let _ = s.set_nonblocking(false);
                        let sh = shared.clone();
                        // Detached per-connection thread; ends when its socket ends.
                        // A spawn that fails (thread exhaustion) drops this socket and
                        // keeps accepting — `thread::spawn` would panic the acceptor.
                        let _ = thread::Builder::new().spawn(move || {
                            let _ = handle_conn(&sh, s);
                        });
                    }
                    Err(ref e) if e.kind() == io::ErrorKind::WouldBlock => {
                        thread::sleep(ACCEPT_POLL);
                    }
                    // A transient accept() error (EMFILE/ENFILE/EINTR/ECONNABORTED) must
                    // NOT kill the listener — back off briefly. Only shutdown stops it.
                    Err(_) => thread::sleep(ACCEPT_POLL),
                }
            }
        })?;
        Ok(BrokerHandle {
            shared: self.shared.clone(),
            acceptor: Some(acceptor),
            writer: self.writer.lock().unwrap().take(),
            endpoint: Endpoint::Unix(socket_path),
        })
    }

    /// Like [`serve`](Self::serve) but over TCP — multi-machine, PLAINTEXT and
    /// unauthenticated, so for a TRUSTED network only (the sealed transport is
    /// `serve_tcp_sealed`, with the `aead` feature). Binds `addr` (use `127.0.0.1:0`
    /// for an ephemeral port) and serves the SAME Frame protocol. Returns the handle;
    /// read the bound address from it if you bound port 0.
    pub fn serve_tcp(&self, addr: impl std::net::ToSocketAddrs) -> io::Result<BrokerHandle> {
        // Identity wrap: the raw TcpStream IS the connection stream.
        self.serve_tcp_with(addr, Ok)
    }

    /// Like [`serve_tcp`](Self::serve_tcp) but the transport is **confidential and
    /// authenticated**: every connection is wrapped in an XChaCha20-Poly1305
    /// [`SealedStream`](astream_aead::SealedStream) under the pre-shared `key`, so
    /// the same `Frame` protocol rides inside an encrypted, ordered record layer.
    /// Each connection opens with the sealed handshake — a fresh hello from each
    /// side, bound with the direction and the record sequence into every record's
    /// AAD, and a key-confirming record each way — so a peer that lacks the key is
    /// refused inside the handshake (it is never handed a frame), and a record
    /// recorded from any other connection or direction cannot be replayed into
    /// this one. Unauthenticated peers are bounded on the accept path: a handshake
    /// must complete within a deadline, only a fixed number of connections may sit
    /// in one at once, and none can force an allocation beyond an empty confirm
    /// record. A client connects with [`crate::client::Client::connect_tcp_sealed`]. This is the
    /// AEAD wire the capability mint's authorization half does not cover.
    #[cfg(feature = "aead")]
    pub fn serve_tcp_sealed(
        &self,
        addr: impl std::net::ToSocketAddrs,
        key: [u8; astream_aead::KEY_LEN],
    ) -> io::Result<BrokerHandle> {
        self.serve_tcp_with(addr, move |s| {
            astream_aead::SealedStream::handshake_server(s, key)
        })
    }

    /// Like [`serve_tcp_sealed`](Self::serve_tcp_sealed) but with **forward secrecy**:
    /// each connection first runs the Rung-7 key-agreement handshake (ephemeral
    /// X25519 authenticated by the pre-shared `psk`), so the per-session key is
    /// fresh and a later `psk` compromise cannot decrypt past traffic. The handshake
    /// runs in the connection's own thread; a peer that fails it (wrong protocol,
    /// non-contributory point) is dropped. A client connects with
    /// [`crate::client::Client::connect_tcp_handshake`].
    #[cfg(feature = "handshake")]
    pub fn serve_tcp_handshake(
        &self,
        addr: impl std::net::ToSocketAddrs,
        psk: [u8; astream_aead::KEY_LEN],
    ) -> io::Result<BrokerHandle> {
        self.serve_tcp_with(addr, move |s| {
            // Bound the handshake I/O: a peer that connects then stalls (sends
            // nothing, or a partial message) must not park this thread + fd
            // forever — nothing gates the pre-handshake read, so an unauthenticated
            // slowloris would otherwise exhaust threads unbounded. Reset to blocking
            // once the handshake completes; the request loop and tail_loop then set
            // their own timeouts.
            s.set_read_timeout(Some(HANDSHAKE_TIMEOUT))?;
            s.set_write_timeout(Some(HANDSHAKE_TIMEOUT))?;
            let sealed = astream_aead::server_handshake(s, &psk)?;
            sealed.get_ref().set_read_timeout(None)?;
            sealed.get_ref().set_write_timeout(None)?;
            Ok(sealed)
        })
    }

    /// Like [`serve_tcp_handshake`](Self::serve_tcp_handshake) but with **static
    /// public-key identity and no shared secret** (Rung 8): each connection runs a
    /// mutual signed-DH (SIGMA/Ed25519) handshake — the broker proves its host
    /// `identity`, and the client's identity must be in `authorized_clients`. The
    /// session key still comes from the ephemeral DH alone, so forward secrecy
    /// survives even an identity-key compromise. The handshake runs in the
    /// connection's own thread under the same deadline. A client connects with
    /// [`crate::client::Client::connect_tcp_identity`].
    #[cfg(feature = "identity")]
    pub fn serve_tcp_identity(
        &self,
        addr: impl std::net::ToSocketAddrs,
        identity: astream_aead::IdentityKeypair,
        authorized_clients: Vec<[u8; astream_aead::ID_PUB_LEN]>,
    ) -> io::Result<BrokerHandle> {
        self.serve_tcp_with(addr, move |s| {
            s.set_read_timeout(Some(HANDSHAKE_TIMEOUT))?;
            s.set_write_timeout(Some(HANDSHAKE_TIMEOUT))?;
            let (sealed, _client_id) =
                astream_aead::server_identity_handshake(s, &identity, &authorized_clients)?;
            sealed.get_ref().set_read_timeout(None)?;
            sealed.get_ref().set_write_timeout(None)?;
            Ok(sealed)
        })
    }

    /// Shared TCP accept loop, generic over how each accepted [`TcpStream`] is
    /// wrapped into the per-connection [`Stream`] (`Ok` for plaintext, the sealed
    /// handshake for the AEAD transport). The wrap runs on the connection's own
    /// thread, never on the acceptor, under pre-authentication bounds — a deadline
    /// and a cap on how many connections may be inside their wrap at once — so a
    /// peer that cannot authenticate can hold up neither other accepts nor a
    /// thread for long (the sealed handshake itself bounds memory: it allocates
    /// nothing an unkeyed peer can size). The cap counts connections INSIDE the
    /// wrap, so the instant plaintext wrap never holds a slot and a burst of
    /// plaintext accepts is never refused by it. A connection that fails to wrap
    /// is dropped.
    fn serve_tcp_with<S, F>(
        &self,
        addr: impl std::net::ToSocketAddrs,
        wrap: F,
    ) -> io::Result<BrokerHandle>
    where
        S: Stream,
        F: Fn(TcpStream) -> io::Result<S> + Send + Sync + 'static,
    {
        // How long a connection may take to complete its wrap (the sealed handshake):
        // the socket read timeout until the wrap returns, lifted once it has — the
        // protocol above sets its own timeouts.
        const PREAUTH_TIMEOUT: Duration = Duration::from_secs(5);
        // How many connections may sit inside the wrap at once; an accept beyond
        // it is dropped at once rather than given a thread.
        const MAX_PREAUTH_CONNS: usize = 64;

        let listener = TcpListener::bind(addr)?;
        // Report a *connectable* address: a wildcard bind (0.0.0.0 / ::) is not a valid
        // destination for a client, so map an unspecified host to loopback (keeping
        // the port) for `tcp_addr`. Shutdown polls `running`; it never dials this.
        let bound = connectable_addr(listener.local_addr()?);
        listener.set_nonblocking(true)?;
        let shared = self.shared.clone();
        let wrap = Arc::new(wrap);
        let acceptor = thread::Builder::new().spawn(move || {
            // Connections currently INSIDE their wrap (the sealed handshake): the
            // pre-authentication population. Counted on the connection thread
            // around the wrap itself — so an instant wrap (plaintext) holds a slot
            // for no measurable time — and pre-checked here so a peer beyond the
            // cap is dropped without being given a thread.
            let preauth = Arc::new(std::sync::atomic::AtomicUsize::new(0));
            while shared.running.load(Ordering::Relaxed) {
                match listener.accept() {
                    Ok((s, _)) => {
                        let _ = s.set_nonblocking(false); // frame reader needs blocking
                        let _ = s.set_nodelay(true);
                        if preauth.load(Ordering::Acquire) >= MAX_PREAUTH_CONNS {
                            drop(s);
                            continue;
                        }
                        // The pre-authentication deadline: armed BEFORE the wrap;
                        // the connection thread lifts it once the wrap succeeded.
                        let _ = s.set_read_timeout(Some(PREAUTH_TIMEOUT));
                        let sh = shared.clone();
                        let wrap = Arc::clone(&wrap);
                        let preauth = Arc::clone(&preauth);
                        // Detached per-connection thread; the wrap (the sealed
                        // handshake) runs HERE so a stalling peer cannot hold up
                        // other accepts. Ends when its socket ends. A spawn that fails
                        // (thread exhaustion) drops this socket and keeps accepting —
                        // `thread::spawn` would panic the acceptor.
                        let _ = thread::Builder::new().spawn(move || {
                            // Take a slot; the hard bound (the pre-check above races
                            // a burst). Beyond the cap the socket drops here.
                            if preauth.fetch_add(1, Ordering::AcqRel) >= MAX_PREAUTH_CONNS {
                                preauth.fetch_sub(1, Ordering::AcqRel);
                                return;
                            }
                            let wrapped = wrap(s);
                            preauth.fetch_sub(1, Ordering::AcqRel);
                            // Couldn't establish the (sealed) transport — the socket
                            // drops with the Err.
                            if let Ok(stream) = wrapped {
                                let _ = stream.set_read_timeout(None);
                                let _ = handle_conn(&sh, stream);
                            }
                        });
                    }
                    Err(ref e) if e.kind() == io::ErrorKind::WouldBlock => {
                        thread::sleep(ACCEPT_POLL);
                    }
                    Err(_) => thread::sleep(ACCEPT_POLL),
                }
            }
        })?;
        Ok(BrokerHandle {
            shared: self.shared.clone(),
            acceptor: Some(acceptor),
            writer: self.writer.lock().unwrap().take(),
            endpoint: Endpoint::Tcp(bound),
        })
    }
}

impl Drop for Broker {
    fn drop(&mut self) {
        // `serve` moves the writer into the handle, which then owns the lifecycle. If
        // it never did, this Broker IS the lifecycle: stop the writer (it would
        // otherwise poll forever, holding the log open and locked) and release the
        // log's lock.
        if let Some(w) = self.writer.lock().unwrap().take() {
            self.shared.running.store(false, Ordering::Relaxed);
            let _ = w.join();
            self.shared.log.lock().unwrap().unlock();
        }
    }
}

/// The broker's per-connection [`Stream`] behaviours for the sealed transport:
/// timeouts and shutdown act on the underlying socket (they never touch the
/// record bytes), and `try_clone` shares the AEAD record counters so the
/// read half and the ack-writer half stay one ordered record sequence.
#[cfg(feature = "aead")]
impl ConnShutdown for astream_aead::SealedStream<TcpStream> {
    fn shutdown_both(&self) {
        let _ = self.get_ref().shutdown(Shutdown::Both);
    }
    fn shutdown_write(&self) {
        let _ = self.get_ref().shutdown(Shutdown::Write);
    }
}

#[cfg(feature = "aead")]
impl Stream for astream_aead::SealedStream<TcpStream> {
    fn set_read_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        self.get_ref().set_read_timeout(d)
    }
    fn set_write_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        self.get_ref().set_write_timeout(d)
    }
    fn try_clone(&self) -> io::Result<Self> {
        astream_aead::SealedStream::try_clone(self)
    }
}

/// Owns the running acceptor; [`shutdown`](BrokerHandle::shutdown) stops it and
/// (for a Unix socket) unlinks it. Dropping the handle shuts down too.
pub struct BrokerHandle {
    shared: Arc<Shared>,
    acceptor: Option<JoinHandle<()>>,
    writer: Option<JoinHandle<()>>,
    endpoint: Endpoint,
}

impl BrokerHandle {
    /// The bound TCP address (useful when serving on port 0), or `None` for a Unix
    /// socket.
    pub fn tcp_addr(&self) -> Option<&str> {
        match &self.endpoint {
            Endpoint::Tcp(a) => Some(a),
            #[cfg(unix)]
            Endpoint::Unix(_) => None,
        }
    }

    /// Force-close every registered connection socket, so a thread parked in a
    /// blocking read_frame (a quiet producer) or a wedged socket write returns at
    /// once and is reaped — along with its ack-writer thread and cloned fd.
    fn force_close_conns(shared: &Shared) {
        for (_, c) in shared.conns.lock().unwrap().drain() {
            c.shutdown_both();
        }
    }

    /// Stop accepting, wake parked subscribers so they observe shutdown and exit,
    /// force-close every live connection (connection threads have no idle timeout —
    /// this is what reaps them), join the acceptor and the writer, release the log's
    /// file lock, and clean up the endpoint. Bounded even with a wedged follower or a
    /// silent client: nothing here waits on a peer.
    pub fn shutdown(&mut self) {
        self.shared.running.store(false, Ordering::Relaxed);
        // Wake parked subscriber threads so they observe shutdown and exit.
        self.shared.tail.notify_all();
        // Unblock the writer if it is parked on a follower that never answers.
        if let Some(rep) = &self.shared.replicator {
            rep.shutdown_links();
        }
        Self::force_close_conns(&self.shared);
        // The acceptor polls `running` (non-blocking accept), so it observes the flag
        // within ACCEPT_POLL and exits — no self-connect wakeup needed.
        if let Some(j) = self.acceptor.take() {
            let _ = j.join();
        }
        // A connection the acceptor handed off just before exiting registers itself on
        // its own thread — possibly after the drain above. Drain again now that no more
        // can arrive; handle_conn also leaves on its own if it sees `running` false
        // right after registering, so between the two no connection is missed.
        Self::force_close_conns(&self.shared);
        // The writer thread observes `running == false` on its next idle poll (or
        // after draining in-flight work) and exits; join it so its final batch is done.
        // Only the handle that owns the writer (the broker's first `serve*`) does this.
        if let Some(w) = self.writer.take() {
            let _ = w.join();
            // The writer — the only mutator — is gone: release the log's file lock
            // now, so a successor can open the log while connection threads that still
            // hold this log's `Arc` finish being reaped. A handle without the writer
            // must not: the writer may still be committing a batch.
            self.shared.log.lock().unwrap().unlock();
        }
        #[cfg(unix)]
        if let Endpoint::Unix(p) = &self.endpoint {
            let _ = std::fs::remove_file(p);
        }
    }
}

impl Drop for BrokerHandle {
    fn drop(&mut self) {
        if self.acceptor.is_some() || self.writer.is_some() {
            self.shutdown();
        }
    }
}

/// Serve one connection, then FIRE its registered will (if any) on ANY return — a
/// clean EOF, an I/O error, a shutdown force-close, or a panic-free early exit alike.
/// The connection thread does not wait for the ack: the will is already durable as a
/// hidden `/a/will` record, so the worst a lost firing costs is that the broker's next
/// open fires it instead.
fn handle_conn<S: Stream>(shared: &Arc<Shared>, stream: S) -> io::Result<()> {
    let mut will: Option<WillRecord> = None;
    let res = serve_conn(shared, stream, &mut will);
    if let Some(will) = will.take() {
        fire_will(shared, will);
    }
    res
}

/// Enqueue a durable mutation on the writer queue and WAIT for its ack — the shape a
/// request answered in the connection loop needs (an `Attach` that binds a producer id,
/// a `Will` that must be persisted before it is acknowledged), as opposed to the
/// pipelined path, whose acks a separate thread streams back.
///
/// The wait ends on the OP'S OWN FATE, never on a flag. An op queued just as the
/// writer thread exits must not park this thread for good — but `running == false` is
/// not that fact: `writer_loop` does not discard what is already queued, it drains and
/// commits it, so a wait that ended on the flag could answer "the will was not
/// persisted" for a `/a/will` record the log went on to hold (and which the next open
/// would then fire, for a producer that believes it registered nothing). The honest
/// signal is the writer DROPPING the op: when `writer_loop` returns it drops the
/// receiver, every queued `WriteOp` with it, and every ack `Sender` those held —
/// which is exactly `Disconnected` here.
fn submit_blocking(shared: &Arc<Shared>, kind: WriteKind) -> Result<(u64, bool), String> {
    let (tx, rx) = mpsc::channel();
    if shared.writes.send(WriteOp { kind, ack: tx }).is_err() {
        return Err("broker is stopping".to_string());
    }
    match rx.recv() {
        Ok(res) => res,
        // The writer is gone and took this op with it, unacked and uncommitted.
        Err(mpsc::RecvError) => Err("broker is stopping".to_string()),
    }
}

/// Enqueue one will as a fenced publish, discarding its ack. Fire-and-forget on
/// purpose: waiting could park a connection thread on a writer that a concurrent
/// shutdown has already stopped, and the `/a/will` record is the durable record of
/// intent either way.
fn fire_will(shared: &Arc<Shared>, will: WillRecord) {
    let (tx, _rx) = mpsc::channel();
    let _ = shared.writes.send(WriteOp {
        kind: WriteKind::WillFire { will },
        ack: tx,
    });
}

/// Let a client refused at the connection cap READ its refusal. Closing at once loses
/// it: a client whose first request lands after the close gets a broken pipe (Unix)
/// and one whose request is still unread when the socket closes gets a reset (TCP).
/// So the refused socket shuts only its write half (the client reads the error, then
/// EOF) and stays open for up to [`REFUSAL_LINGER`], reading and discarding input
/// until the client closes; at most [`MAX_LINGERING_REFUSALS`] do so at once, and past
/// that a refusal closes immediately.
fn linger_refused<S: Stream>(shared: &Shared, stream: &mut S) {
    if shared.refusing.fetch_add(1, Ordering::AcqRel) >= MAX_LINGERING_REFUSALS {
        shared.refusing.fetch_sub(1, Ordering::AcqRel);
        return;
    }
    // The refusal is all the client gets: a client still reading sees EOF right after
    // it, instead of waiting out the linger.
    stream.shutdown_write();
    let deadline = std::time::Instant::now() + REFUSAL_LINGER;
    let mut sink = [0u8; 4096];
    loop {
        let left = deadline.saturating_duration_since(std::time::Instant::now());
        if left.is_zero() || stream.set_read_timeout(Some(left)).is_err() {
            break;
        }
        match stream.read(&mut sink) {
            Ok(0) => break,
            Ok(_) => {}
            Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(_) => break,
        }
    }
    shared.refusing.fetch_sub(1, Ordering::AcqRel);
}

/// A connection's stream read against an absolute `deadline`: each read is bounded by
/// the time left, so a peer that sends frame after frame, or one frame a byte at a
/// time, cannot stretch the wait past it (a plain socket timeout re-arms on every
/// read). Used for the pre-authentication phase ([`FIRST_FRAME_TIMEOUT`]).
struct Deadlined<'a, S: Stream> {
    stream: &'a mut S,
    deadline: Instant,
}

impl<S: Stream> Read for Deadlined<'_, S> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let left = self.deadline.saturating_duration_since(Instant::now());
        if left.is_zero() {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "pre-authentication deadline passed",
            ));
        }
        self.stream.set_read_timeout(Some(left))?;
        self.stream.read(buf)
    }
}

fn serve_conn<S: Stream>(
    shared: &Arc<Shared>,
    mut stream: S,
    will: &mut Option<WillRecord>,
) -> io::Result<()> {
    // Register a shutdown handle so BrokerHandle::shutdown can force-close this socket
    // (both directions) and unblock a thread parked in read_frame / a socket write —
    // the connection thread (and any ack-writer it spawned) is then reaped promptly
    // instead of lingering until the client happens to send or disconnect. The
    // registry also enforces the connection cap.
    let conn_id = shared.conn_seq.fetch_add(1, Ordering::Relaxed);
    let max_conns = shared.max_conns.load(Ordering::Relaxed);
    {
        let mut conns = shared.conns.lock().unwrap();
        if conns.len() >= max_conns {
            drop(conns);
            let _ = stream.set_write_timeout(Some(ACK_WRITE_TIMEOUT));
            let _ = write_frame(
                &mut stream,
                &encode_response(&Response::Error {
                    code: 6,
                    msg: format!("too many connections (limit {max_conns})"),
                }),
            );
            linger_refused(shared, &mut stream);
            return Err(io::Error::new(
                io::ErrorKind::ConnectionRefused,
                "connection limit reached",
            ));
        }
        // No shutdown handle would mean no cap accounting and no force-close — under
        // fd exhaustion (exactly what the cap exists for) `try_clone` is what fails
        // first. Refuse rather than serve a connection the broker cannot bound or reap.
        conns.insert(conn_id, Box::new(stream.try_clone()?));
    }
    let _conn_guard = ConnGuard {
        shared,
        id: conn_id,
    };
    // Registered; if the broker began stopping meanwhile (this socket may have been
    // accepted after shutdown's first registry drain), leave now rather than park.
    if !shared.running.load(Ordering::Relaxed) {
        return Ok(());
    }
    // Nothing is known about the peer until its first frame — on a guarded broker,
    // until it has a capability accepted: bound that wait (see FIRST_FRAME_TIMEOUT).
    // `preauth` is that phase; `preauth_deadline` the instant a guarded connection
    // must end it by (`None` when the configured timeout is too far off to represent
    // as an instant, which leaves the socket timeout as the bound).
    let preauth_timeout =
        Duration::from_millis(shared.first_frame_timeout_ms.load(Ordering::Relaxed));
    let _ = stream.set_read_timeout(Some(preauth_timeout));
    let preauth_deadline = Instant::now().checked_add(preauth_timeout);
    let guarded = shared.cap_secret.is_some();
    let mut preauth = true;
    // And bound every RESPONSE write on this connection, for the whole of its life.
    // A peer that stops reading — SIGSTOPped, partitioned so its receive window shuts
    // and never reopens — otherwise parks this thread inside `write_all` forever, with
    // the fd and the `MAX_CONNS` slot still charged to it. It is set here, not only by
    // the pipelined ack-writer, because a connection that only ever READS (`Hello`,
    // `Attach`, `Last`, `Fetch`) never starts a `Pipeline`. Both halves take THIS
    // value: `SO_SNDTIMEO` is a property of the socket, not of the descriptor, so
    // whichever half sets it last sets it for both. A streaming verb raises it to
    // STREAM_WRITE_TIMEOUT when it takes the socket over — `tail_loop` for
    // subscriptions, the `ForkSubscribe` arm for a snapshot delivered on this thread.
    let _ = stream.set_write_timeout(Some(Duration::from_millis(
        shared.write_timeout_ms.load(Ordering::Relaxed),
    )));
    // Write ops (publish / commit / process_and_produce / replicate) and their
    // acks/errors flow through a lazily-started Pipeline: a second thread streams acks
    // back IN ORDER on a cloned write half while this thread keeps reading requests, so
    // ONE connection can have many writes in flight (they coalesce into the same
    // group-commit batch). A streaming verb (subscribe / fork) first FINISHes the
    // pipeline — flushing every pending ack and reclaiming the socket — before it
    // takes over for delivery.
    let mut pipe: Option<Pipeline> = None;
    // This connection's capability KEYRING: `Attach` APPENDS to it (a repeated grant
    // string replaces), and every request is authorized existentially over it, so one
    // connection can hold several narrow grants — read one subtree, commit under
    // another, publish as a bound principal in a third — instead of one wide one.
    #[cfg(feature = "cap")]
    let mut keyring: Vec<astream_cap::Capability> = Vec::new();
    // The nonce this connection's `Attach` proofs are computed over, once `Hello` has
    // handed one out. Kept on the DEFAULT build too, because `Hello` is answered by an
    // unguarded broker as well — one client works against either.
    let mut nonce: Option<[u8; 32]> = None;
    loop {
        // Guarded, the deadline is ABSOLUTE; unguarded, the socket timeout set above
        // bounds each read of the first frame.
        let read = match preauth_deadline {
            Some(deadline) if preauth && guarded => read_frame(&mut Deadlined {
                stream: &mut stream,
                deadline,
            }),
            _ => read_frame(&mut stream),
        };
        let payload = match read {
            Ok(Some(p)) => p,
            Ok(None) => break, // clean EOF: client closed
            Err(e) => {
                // A guarded connection out of time before it attached is told why
                // (best effort: it is closed either way).
                if preauth
                    && guarded
                    && matches!(
                        e.kind(),
                        io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut
                    )
                {
                    let _ = write_frame(
                        &mut stream,
                        &encode_response(&Response::Error {
                            code: 5,
                            msg: format!(
                                "unauthorized: no capability attached within {} ms of connecting",
                                preauth_timeout.as_millis()
                            ),
                        }),
                    );
                }
                finish_pipe(&mut pipe)?;
                return Err(e);
            }
        };
        // Unguarded, the first frame ends the pre-authentication phase: there is
        // nothing to authenticate. Guarded, only an accepted `Attach` ends it.
        if preauth && !guarded {
            preauth = false;
            let _ = stream.set_read_timeout(None);
        }
        let req = match decode_request(&payload) {
            Some(r) => r,
            None => {
                if !emit(&mut stream, &mut pipe, Err("malformed request".into()))? {
                    break;
                }
                continue;
            }
        };
        // Bounded names, before anything (the capability gate included) parses one.
        if let Some(err) = oversized_name(&req) {
            if !emit(&mut stream, &mut pipe, Err(err))? {
                break;
            }
            continue;
        }
        // `Hello` opens the capability handshake on EVERY build: it hands out this
        // connection's nonce and grants nothing, so an unguarded broker answers it too
        // and one client works against either kind. Answered in the request loop after
        // finish_pipe, like every other non-streaming verb.
        if matches!(req, Request::Hello) {
            finish_pipe(&mut pipe)?;
            let n = *nonce.insert(fresh_nonce());
            write_frame(
                &mut stream,
                &encode_response(&Response::Nonce { nonce: n.to_vec() }),
            )?;
            continue;
        }
        // Capability gate. `Attach` adds to the connection's keyring; every other
        // request is authorized against that ring when the broker is guarded. Off
        // entirely without the `cap` feature (no secret can be set), so the default
        // broker is unchanged. `until` is when the request's authority lapses: a
        // streaming verb, one request for the life of its stream, ends there.
        #[cfg(not(feature = "cap"))]
        let until = u64::MAX;
        #[cfg(feature = "cap")]
        let until = {
            if let Request::Attach { grant, proof } = &req {
                finish_pipe(&mut pipe)?;
                let res = match shared.cap_secret.as_deref() {
                    // Unguarded: acknowledge and enforce nothing (the ring is unused).
                    None => Ok(()),
                    Some(secret) => {
                        attach_grant(shared, secret, &mut keyring, nonce.as_ref(), grant, proof)
                    }
                };
                let resp = match res {
                    Ok(()) => {
                        // Authenticated: the pre-authentication deadline is lifted.
                        if preauth {
                            preauth = false;
                            let _ = stream.set_read_timeout(None);
                        }
                        let head = shared.head.load(Ordering::Relaxed);
                        Response::Mark {
                            next: head,
                            head,
                            resume: String::new(),
                        }
                    }
                    Err(msg) => Response::Error { code: 5, msg },
                };
                write_frame(&mut stream, &encode_response(&resp))?;
                continue;
            }
            match shared.cap_secret.as_deref() {
                None => u64::MAX,
                // THE INSTANT IS TAKEN PER REQUEST, not once per connection: a
                // capability that expires while a connection is open stops
                // authorizing its next request, and a stream it admitted ends at
                // the deadline (`until`).
                Some(secret) => match cap_authorized_until(secret, &keyring, &req, now_unix_ms()) {
                    Some(until) => until,
                    None => {
                        if !emit(
                            &mut stream,
                            &mut pipe,
                            Err(
                                "unauthorized: capability does not grant this subject/filter"
                                    .into(),
                            ),
                        )? {
                            break;
                        }
                        continue;
                    }
                },
            }
        };
        #[cfg(not(feature = "cap"))]
        {
            // Unguarded (no `cap` feature at all): accept an Attach and acknowledge it,
            // so a client's attach round trip completes against either broker.
            if matches!(req, Request::Attach { .. }) {
                finish_pipe(&mut pipe)?;
                let head = shared.head.load(Ordering::Relaxed);
                write_frame(
                    &mut stream,
                    &encode_response(&Response::Mark {
                        next: head,
                        head,
                        resume: String::new(),
                    }),
                )?;
                continue;
            }
        }
        match req {
            Request::Publish {
                producer_id,
                producer_seq,
                subject,
                body,
            } => {
                if let Some(err) = publish_subject_error(&subject) {
                    if !emit(&mut stream, &mut pipe, Err(err))? {
                        break;
                    }
                    continue;
                }
                if !emit_op(
                    shared,
                    &mut stream,
                    &mut pipe,
                    WriteKind::Publish {
                        producer_id,
                        producer_seq,
                        subject,
                        body,
                    },
                )? {
                    break;
                }
            }
            Request::Commit { group, upto } => {
                if !emit_op(
                    shared,
                    &mut stream,
                    &mut pipe,
                    WriteKind::Commit { group, upto },
                )? {
                    break;
                }
            }
            Request::ProcessAndProduce {
                producer_id,
                producer_seq,
                out_subject,
                out_body,
                group,
                upto,
            } => {
                if let Some(err) = publish_subject_error(&out_subject) {
                    if !emit(&mut stream, &mut pipe, Err(format!("output {err}")))? {
                        break;
                    }
                    continue;
                }
                if !emit_op(
                    shared,
                    &mut stream,
                    &mut pipe,
                    WriteKind::ProcessAndProduce {
                        producer_id,
                        producer_seq,
                        out_subject,
                        out_body,
                        group,
                        upto,
                    },
                )? {
                    break;
                }
            }
            Request::Replicate {
                seq,
                producer_id,
                producer_seq,
                subject,
                body,
                commit,
            } => {
                // The follower does not trust the wire. The subject must be valid,
                // and EVERY hidden subject is guarded:
                //
                // - `/a/commit` may carry ONLY the pure-commit shape (a leader's own
                //   commit record); anything else there would bypass dedup and never
                //   be delivered.
                // - `/a/will` and `/a/bind` are accepted ONLY on a log a leader is
                //   already shipping to (or one that is still EMPTY, which is what a
                //   fresh follower is). They must replicate — a follower's log is the
                //   leader's spine byte for byte, and a guarded leader's own first
                //   record is often a `/a/bind` — but on a broker that OWNS its log
                //   they are an injection, not a replication: an injected `/a/will` is
                //   an arbitrary publish, to an arbitrary subject, under an arbitrary
                //   producer id, executed by the broker itself at its next open and
                //   outside the capability matrix; an injected `/a/bind` locks a
                //   victim principal out of attaching for good.
                let pure_commit =
                    producer_id == 0 && producer_seq == 0 && body.is_empty() && commit.is_some();
                // Only a hidden subject asks the log whose it is — the common record
                // never takes the lock twice on the follower's ingest path.
                //
                // THIS IS AN EARLY REFUSAL, NOT THE RULE. It reads the promoted head
                // and drops the lock, while the record is appended later, in the
                // writer: this connection's own pipelined records are staged but not
                // promoted in between, so `head()` still reads 0 on a log that is about
                // to hold records of its own, and a hidden record admitted here on the
                // strength of "still empty" would land on a log the broker OWNS. The
                // rule itself is enforced by `stage_replica`, in the same critical
                // section that appends, from the same predicate that decides whether
                // the log is a replica. What this saves is a round trip through the
                // writer queue for the settled case, and it says the same sentence.
                let replica_shape = || {
                    let log = shared.log.lock().unwrap();
                    log.is_replica() || log.head().0 == 0
                };
                let err = if Subject::new(subject.as_str()).is_err() {
                    Some(format!("bad subject {subject:?}"))
                } else if subject == COMMIT_SUBJECT {
                    (!pure_commit).then(|| format!("reserved subject {COMMIT_SUBJECT}"))
                } else if is_hidden_subject(&subject) && !replica_shape() {
                    Some(replicated_reserved_msg(&subject))
                } else {
                    None
                };
                if let Some(err) = err {
                    if !emit(&mut stream, &mut pipe, Err(err))? {
                        break;
                    }
                    continue;
                }
                let rec = BrokerRecord {
                    seq: Offset(seq),
                    producer_id,
                    producer_seq,
                    subject,
                    body,
                    commit: commit.map(|(group, upto)| GroupCommit { group, upto }),
                };
                if !emit_op(shared, &mut stream, &mut pipe, WriteKind::Replicate { rec })? {
                    break;
                }
            }
            Request::Subscribe {
                from_offset,
                filter,
            } => {
                finish_pipe(&mut pipe)?; // flush pending acks, reclaim the socket
                let filt = match Filter::new(filter.as_str()) {
                    Ok(f) => f,
                    Err(_) => {
                        write_frame(
                            &mut stream,
                            &encode_response(&Response::Error {
                                code: 3,
                                msg: format!("bad filter {filter:?}"),
                            }),
                        )?;
                        return Ok(());
                    }
                };
                return tail_loop(shared, &mut stream, from_offset, filt, until);
            }
            Request::ForkSubscribe {
                fork_at,
                replacement_subject,
                replacement_body,
                filter,
            } => {
                finish_pipe(&mut pipe)?;
                if let Some(err) = publish_subject_error(&replacement_subject) {
                    write_frame(
                        &mut stream,
                        &encode_response(&Response::Error {
                            code: 2,
                            msg: format!("replacement {err}"),
                        }),
                    )?;
                    return Ok(());
                }
                let filt = match Filter::new(filter.as_str()) {
                    Ok(f) => f,
                    Err(_) => {
                        write_frame(
                            &mut stream,
                            &encode_response(&Response::Error {
                                code: 3,
                                msg: format!("bad filter {filter:?}"),
                            }),
                        )?;
                        return Ok(());
                    }
                };
                let replacement = BrokerRecord {
                    seq: Offset(fork_at),
                    producer_id: 0,
                    producer_seq: 0,
                    subject: replacement_subject,
                    body: replacement_body,
                    commit: None,
                };
                // A STREAMING VERB TAKING THE SOCKET OVER: raise the write bound the
                // way `tail_loop` does. The connection's own bound is sized for an ack
                // (10s by default), and this snapshot can be the whole history, read
                // by a client slower than the broker writes it.
                let _ = stream.set_write_timeout(Some(stream_write_timeout(shared)));
                // The counterfactual snapshot: every record below the VISIBLE head
                // (the quorum watermark in the Replicated tier), pinned on the first
                // read, with the one at `fork_at` replaced. It is read TAIL_CHUNK
                // records at a time under a SHORT lock — shared `Arc` handles, no
                // payload copy — and delivered outside it, so a fork of a long log
                // never holds the lock for a whole-log copy. Records below the pinned
                // head never change, so the chunks add up to the snapshot one read
                // would have taken (a fork is a frozen alternate history, so no live
                // tail); the live log and live subscribers are untouched. As on the
                // tail, records retention prunes mid-walk are skipped: the walk moves
                // up to the new base.
                let mut pinned: Option<u64> = None;
                let mut cursor = 0u64;
                let mut out = Vec::new();
                let visible = loop {
                    let (chunk, visible) = {
                        let log = shared.log.lock().unwrap();
                        let visible =
                            *pinned.get_or_insert_with(|| shared.head.load(Ordering::Relaxed));
                        (next_chunk(&log, &mut cursor, visible).0, visible)
                    };
                    if chunk.is_empty() {
                        break visible;
                    }
                    for rec in chunk {
                        if let Some(now) = lapsed(until) {
                            return end_lapsed(&mut stream, &mut out, until, now);
                        }
                        // Below the pinned head, so never the last offset there is.
                        cursor = rec.seq.0 + 1;
                        let rec: &BrokerRecord = if rec.seq.0 == fork_at {
                            &replacement
                        } else {
                            &rec
                        };
                        // Pure consumer-group commit records are internal bookkeeping;
                        // never deliver them (a wildcard filter like `/a/>` matches the
                        // reserved `/a/commit` subject — see tail_loop).
                        if is_hidden_subject(&rec.subject) {
                            continue;
                        }
                        if filt.matches_str(&rec.subject) {
                            queue_delivery(&mut stream, &mut out, rec)?;
                        }
                    }
                };
                flush_egress(&mut stream, &mut out)?;
                // THE END MARKER, written BEFORE the EOF: a bare EOF is also what a
                // connection torn down mid-snapshot gives, so "complete" is something
                // the client reads rather than infers. `recv` skips it; `recv_event`
                // is where a caller that cares looks.
                write_frame(
                    &mut stream,
                    &encode_response(&Response::Mark {
                        next: visible,
                        head: visible,
                        resume: String::new(),
                    }),
                )?;
                return Ok(()); // the snapshot is complete, and said so
            }
            Request::SubscribeGroup { group, filter } => {
                finish_pipe(&mut pipe)?;
                let filt = match Filter::new(filter.as_str()) {
                    Ok(f) => f,
                    Err(_) => {
                        write_frame(
                            &mut stream,
                            &encode_response(&Response::Error {
                                code: 3,
                                msg: format!("bad filter {filter:?}"),
                            }),
                        )?;
                        return Ok(());
                    }
                };
                // Resume from the group's DURABLE committed offset (broker-enforced).
                let start = {
                    let log = shared.log.lock().unwrap();
                    log.group_start(&group)
                };
                return tail_loop(shared, &mut stream, start.0, filt, until);
            }
            Request::Last { filter, after, max } => {
                // Answered IN THE REQUEST LOOP: the connection stays usable, so a
                // reader pairs its snapshot with a `Subscribe { from: mark.next }` on
                // the SAME connection. Pending pipelined acks are flushed and the
                // socket reclaimed first — the discipline every streaming verb follows.
                finish_pipe(&mut pipe)?;
                let filt = match Filter::new(filter.as_str()) {
                    Ok(f) => f,
                    Err(_) => {
                        if !emit(
                            &mut stream,
                            &mut pipe,
                            Err(format!("bad filter {filter:?}")),
                        )? {
                            break;
                        }
                        continue;
                    }
                };
                // BOTH bounds are the broker's. `max` is the client's ask, clamped to
                // LAST_PAGE_MAX; the index scan is cut off after LAST_SCAN_MAX entries
                // VISITED, so a sparse filter cannot walk the whole subject index with
                // the log lock held (`Fetch`'s bound, on the sibling verb). The
                // closing `Mark` carries the resume cursor, so a page
                // the scan bound cut short is continued rather than silently truncated.
                //
                // WHAT THIS PAGE MEANS. Every record below is its subject's newest
                // record STRICTLY BELOW the `head` in the closing `Mark`, whether the
                // walk took one scan round or sixty-four: `last_page` pins that head on
                // its first round and reads every round against it. The cost of the pin
                // is an omission, not a stale row — a subject whose newest record moves
                // to or above the pinned head while the walk is between rounds is left
                // out of this page, and reaches the reader on the `Subscribe { from:
                // mark.next }` that pairs with it. See `last_page` for the lock
                // discipline, for that trade in full, and for why the cursor it hands
                // back is never a subject this filter does not match.
                let want = max.min(LAST_PAGE_MAX) as usize;
                let (page, resume, head) = match last_page(shared, &filt, &after, want) {
                    Ok(v) => v,
                    Err(msg) => {
                        if !emit(&mut stream, &mut pipe, Err(msg))? {
                            break;
                        }
                        continue;
                    }
                };
                let mut out = Vec::new();
                for rec in page {
                    queue_delivery(&mut stream, &mut out, &rec)?;
                }
                append_frame(
                    &mut out,
                    &encode_response(&Response::Mark {
                        next: head,
                        head,
                        resume: resume.unwrap_or_default(),
                    }),
                )?;
                flush_egress(&mut stream, &mut out)?;
            }
            Request::Will {
                producer_id,
                producer_seq,
                subject,
                body,
            } => {
                // Answered in the request loop, like `Last`/`Fetch`: the connection
                // stays usable and the client learns the head from the `Mark`.
                finish_pipe(&mut pipe)?;
                if let Some(err) = publish_subject_error(&subject) {
                    write_frame(
                        &mut stream,
                        &encode_response(&Response::Error { code: 5, msg: err }),
                    )?;
                    continue;
                }
                // "ONE PER CONNECTION: a second Will replaces the first" is enforced
                // here, in memory — but the durable `/a/will` record of the will it
                // replaces stays on the log, and the re-firing at the next open keys by
                // PRODUCER, not by connection. A second Will under a DIFFERENT
                // producer id would leave two live entries, and the one this
                // connection retracted would still fire on the next open. Refusing it
                // makes the two rules one: on one connection, one producer id, and
                // replacement under it IS durable (the later `/a/will` record wins).
                if let Some(held) = will.as_ref().filter(|w| w.producer_id != producer_id) {
                    write_frame(
                        &mut stream,
                        &encode_response(&Response::Error {
                            code: 5,
                            msg: format!(
                                "this connection already holds a will for producer {}: a second \
                                 Will replaces the first, and replacement is durable only under \
                                 the SAME producer id (use another connection for producer {})",
                                held.producer_id, producer_id
                            ),
                        }),
                    )?;
                    continue;
                }
                let candidate = WillRecord {
                    producer_id,
                    producer_seq,
                    subject,
                    body,
                };
                // Persist FIRST, then remember it: a will acknowledged with a Mark is
                // one the log holds, so a broker that dies before the connection does
                // still fires it on its next open.
                //
                // THE INVARIANT: this in-memory will and the log's `/a/will` record
                // never disagree about whether the will exists. An error here must mean
                // the record is not on the log — nothing queued, or a batch rolled
                // back. It is not a place to report a follower's shortfall: a will the
                // log holds while the client is told it does not is one that fires at
                // the NEXT OPEN, for a producer that believes it registered nothing.
                // `process_batch` acks a `WillRegister` on its own local commit for
                // exactly that reason.
                if let Err(msg) = submit_blocking(
                    shared,
                    WriteKind::WillRegister {
                        will: candidate.clone(),
                    },
                ) {
                    write_frame(
                        &mut stream,
                        &encode_response(&Response::Error {
                            code: 5,
                            msg: format!("will was not persisted: {msg}"),
                        }),
                    )?;
                    continue;
                }
                *will = Some(candidate); // one per connection: a second replaces
                let head = shared.head.load(Ordering::Relaxed);
                write_frame(
                    &mut stream,
                    &encode_response(&Response::Mark {
                        next: head,
                        head,
                        resume: String::new(),
                    }),
                )?;
            }
            Request::Fetch {
                from_offset,
                filter,
                max,
            } => {
                // Answered in the request loop, like `Last`: flush pending acks (they
                // reach the client IN ORDER, before this page), reclaim the socket,
                // answer, and keep the connection.
                finish_pipe(&mut pipe)?;
                let filt = match Filter::new(filter.as_str()) {
                    Ok(f) => f,
                    Err(_) => {
                        if !emit(
                            &mut stream,
                            &mut pipe,
                            Err(format!("bad filter {filter:?}")),
                        )? {
                            break;
                        }
                        continue;
                    }
                };
                let (page, next, head) = {
                    let log = shared.log.lock().unwrap();
                    let head = shared.head.load(Ordering::Relaxed);
                    let (page, next) =
                        log.fetch(from_offset, &filt, max as usize, FETCH_SCAN_MAX, head);
                    (page, next, head)
                };
                let mut out = Vec::new();
                for rec in page {
                    queue_delivery(&mut stream, &mut out, &rec)?;
                }
                append_frame(
                    &mut out,
                    &encode_response(&Response::Mark {
                        next,
                        head,
                        resume: String::new(),
                    }),
                )?;
                flush_egress(&mut stream, &mut out)?;
            }
            // Both are fully handled by the capability gate above, which `continue`s.
            Request::Attach { .. } | Request::Hello => {}
        }
    }
    finish_pipe(&mut pipe)?;
    Ok(())
}

/// Why a client-chosen subject cannot be appended to: not a valid `Subject`, or the
/// broker-internal commit subject (a record there would bypass exactly-once dedup
/// and never be delivered — consumer-group commits go through `Commit` /
/// `ProcessAndProduce`).
fn publish_subject_error(subject: &str) -> Option<String> {
    if Subject::new(subject).is_err() {
        Some(format!("bad subject {subject:?}"))
    } else if is_hidden_subject(subject) {
        Some(reserved_msg(subject))
    } else {
        None
    }
}

/// Add one capability to a guarded connection's keyring, or say why not.
///
/// The §8.2 attach rules, in order: an `Attach` with no preceding `Hello` is refused
/// (there is no nonce to bind the proof to); the proof must verify as
/// `HMAC-SHA256(HMAC(secret, grant), nonce ‖ grant)`, which proves possession of the
/// tag without the tag ever crossing the wire and refuses a proof captured from
/// another connection; a grant that names a principal it may PUBLISH as binds that
/// principal's derived producer id in the durable binding table, and is refused if
/// that id is already bound to a DIFFERENT principal; and the ring is bounded, a
/// repeated grant string replacing rather than growing it.
///
/// The ring's bound is decided BEFORE the binding is appended, so an attach that will
/// be refused writes nothing: the durable mutation is the last thing that happens.
#[cfg(feature = "cap")]
fn attach_grant(
    shared: &Arc<Shared>,
    secret: &[u8],
    keyring: &mut Vec<astream_cap::Capability>,
    nonce: Option<&[u8; 32]>,
    grant: &str,
    proof: &[u8],
) -> Result<(), String> {
    let Some(nonce) = nonce else {
        return Err(
            "unauthorized: Attach without a preceding Hello (the proof of possession is \
             computed over this connection's nonce)"
                .to_string(),
        );
    };
    if !astream_cap::verify_attach(secret, grant, nonce, proof) {
        return Err("unauthorized: capability proof does not verify".to_string());
    }
    // EXPIRY IS ITS OWN REFUSAL, after possession is proved and before anything
    // is bound. A separate message because the two failures need separate
    // remedies: "does not verify" means the wrong secret or a tampered string,
    // "expired" means a correct capability whose time is up and which a mint can
    // reissue. Reporting both as one would send an operator to rotate a secret
    // that is fine. The authorization path re-checks this per request; this
    // check is here so an expired attach fails at the door rather than binding a
    // producer id and then authorizing nothing.
    let now_ms = now_unix_ms();
    if astream_cap::is_expired(grant, now_ms) {
        let exp = astream_cap::expires_at(grant).unwrap_or(0);
        return Err(format!(
            "unauthorized: capability expired at {exp} (now {now_ms}, unix ms)"
        ));
    }
    // Genuine under this broker's secret, so `parse` cannot fail (verify_attach parses
    // first) — but fail closed rather than unwrap on a library change.
    let parsed = astream_cap::Grant::parse(grant).map_err(|e| format!("unauthorized: {e}"))?;
    // DECIDE THE RING FIRST, MUTATE THE LOG SECOND. Minting and the ring's capacity are
    // pure, local checks; the producer-id binding below is a DURABLE append, so an
    // attach refused for a full ring must be refused before it, leaving the log
    // untouched.
    let cap = astream_cap::mint(secret, grant).map_err(|e| format!("unauthorized: {e}"))?;
    let slot = keyring.iter().position(|c| c.filter == cap.filter);
    if slot.is_none() && keyring.len() >= MAX_KEYRING {
        return Err(format!(
            "unauthorized: capability keyring is full ({MAX_KEYRING} grants)"
        ));
    }
    match (&parsed.mode, &parsed.principal) {
        // A grant that can PUBLISH under a named principal binds that principal's
        // derived producer id, durably, before it authorizes anything.
        (astream_cap::Mode::ReadWrite, Some(principal)) => {
            let producer_id = astream_cap::producer_id_of(principal);
            submit_blocking(
                shared,
                WriteKind::Bind {
                    producer_id,
                    principal: principal.clone(),
                },
            )
            .map_err(|msg| format!("unauthorized: {msg}"))?;
        }
        // An UNBOUND read-write grant may publish under any producer id — the god cap
        // the fleet root keeps. It is legal and it is a footgun, so say so once, on
        // stderr, where an operator can see which grant it was.
        (astream_cap::Mode::ReadWrite, None) => {
            eprintln!(
                "astream-broker: warn: attached an UNBOUND read-write grant {grant:?} — it may \
                 publish under ANY producer id (no principal binding); mint it as \
                 \"rw,p=<principal>:<filter>\" unless it is deliberately the fleet root"
            );
        }
        // A read-only grant publishes nothing, so it binds nothing: binding it would
        // let a read-only holder append a /a/bind record.
        (astream_cap::Mode::ReadOnly, _) => {}
    }
    match slot {
        Some(i) => keyring[i] = cap, // a repeated grant replaces, it does not grow the ring
        None => keyring.push(cap),
    }
    Ok(())
}

/// Whether `req` is authorized by this connection's capability KEYRING under the
/// broker's `secret` — the §8.2 matrix, EXISTENTIAL over the ring (one grant may
/// authorize the read half and another the write half of the same request).
///
/// A write (`Publish`, the output half of a `ProcessAndProduce`) needs a READ-WRITE
/// grant whose filter matches the subject AND — when that grant names a principal —
/// whose derived producer id is exactly the one the request carries: that binding is
/// what closes dedup-key poisoning, where a co-permitted publisher pre-takes a peer's
/// `(producer_id, producer_seq)` so the peer's genuine record silently dedups away.
/// Every request that advances a consumer group needs a read-write grant on the group
/// AS A SUBJECT. A read (`Subscribe`, `SubscribeGroup`'s filter, `ForkSubscribe`,
/// `Last`, `Fetch`) needs any grant, of either mode, that CONTAINS the filter.
///
/// `Replicate` is not an ordinary write and is not authorized like one: a follower
/// link is not a peer. It carries the ORIGINAL producer's id, never the link's own, so
/// no BOUND grant could ever cover it — and a link grant must therefore be minted
/// UNBOUND (a bare filter, or `rw:<filter>`), which is the god cap, named as such and
/// chosen once by the operator who stands the cluster up. So the verb takes a grant
/// that is genuine, read-write, filter-matching AND unbound, and a bound `rw` grant
/// cannot reach it at all.
///
/// Authorizing it by SUBJECT alone would hand every bound `rw` grant a write under
/// ANY producer id: dedup is keyed `(producer_id, producer_seq)` with no subject in
/// the key, so a holder permitted nowhere near a peer's subtree could burn that peer's
/// dedup keys from inside its own, and the peer's genuine publish would silently dedup
/// away at the attacker's offset, acked as landed.
/// An empty ring authorizes nothing.
///
/// The answer is `None` when `req` is not authorized at `now_ms`, else the unix-ms
/// instant its authority LAPSES. That instant matters to a streaming verb only — one
/// request for the life of its stream, which must end when the grants that admitted it
/// expire — so only a streaming verb computes it: each half of the request rests on
/// whichever authorizing grant lasts longest, and the request lapses with the first
/// half to go. Any other verb stops at the first grant that authorizes it and answers
/// `u64::MAX` ("authorized now"), which is also the answer for grants without an expiry.
#[cfg(feature = "cap")]
fn cap_authorized_until(
    secret: &[u8],
    keyring: &[astream_cap::Capability],
    req: &Request,
    now_ms: u64,
) -> Option<u64> {
    let streaming = matches!(
        req,
        Request::Subscribe { .. } | Request::SubscribeGroup { .. } | Request::ForkSubscribe { .. }
    );
    // Over the grants `ok` accepts now: the latest expiry (streaming), or whether any.
    let until = |ok: &dyn Fn(&astream_cap::Capability) -> bool| -> Option<u64> {
        if streaming {
            keyring
                .iter()
                .filter(|c| ok(c))
                .map(|c| astream_cap::expires_at(c.filter.as_str()).unwrap_or(u64::MAX))
                .max()
        } else {
            keyring.iter().any(ok).then_some(u64::MAX)
        }
    };
    // A write as a named producer: read-write, filter matches, producer id derived.
    let publish = |subject: &str, producer_id: u64| {
        until(&|c| astream_cap::grants_publish(secret, c, subject, producer_id, now_ms))
    };
    // A group advance: read-write on the group name as a subject.
    let commit = |group: &str| until(&|c| astream_cap::grants_commit(secret, c, group, now_ms));
    // A read: ANY grant (either mode) whose filter contains the requested one.
    let read = |filter: &str| until(&|c| astream_cap::grants_filter(secret, c, filter, now_ms));
    // A REPLICATED write: read-write and filter-matching, like any write — and
    // UNBOUND, because the record carries a producer id this connection's principal
    // does not derive and never could. `grants` has already proved the capability
    // genuine and its filter a match, so re-parsing the grant string for its principal
    // cannot fail here; treat a parse failure as "not a link grant" anyway.
    let replicate = |subject: &str| {
        until(&|c| {
            astream_cap::grants(secret, c, subject, now_ms)
                && astream_cap::Grant::parse(c.filter.as_str()).is_ok_and(|g| g.principal.is_none())
        })
    };
    // Both halves of a request: it lapses when the first does.
    let both = |a: Option<u64>, b: Option<u64>| Some(a?.min(b?));
    match req {
        // A `Will` is a publish the broker will make LATER on this connection's
        // behalf, so it is authorized now, exactly as a publish is — including the
        // producer binding.
        Request::Publish {
            subject,
            producer_id,
            ..
        }
        | Request::Will {
            subject,
            producer_id,
            ..
        } => publish(subject, *producer_id),
        // The commit HALF of a read-process-write also advances a consumer group,
        // so authorize BOTH the output subject AND the group (as a subject the ring
        // grants) — not the output subject alone.
        Request::ProcessAndProduce {
            out_subject,
            producer_id,
            group,
            ..
        } => both(publish(out_subject, *producer_id), commit(group)),
        // A replicated record needs a LINK grant on its subject — read-write,
        // filter-matching and unbound — plus, if it carries a commit, an advance of
        // that group. A bound `rw` grant does not reach this verb.
        Request::Replicate {
            subject, commit: c, ..
        } => match c {
            None => replicate(subject),
            Some((g, _)) => both(replicate(subject), commit(g)),
        },
        Request::Subscribe { filter, .. }
        | Request::ForkSubscribe { filter, .. }
        | Request::Last { filter, .. }
        | Request::Fetch { filter, .. } => read(filter),
        // A group subscription is authorized for BOTH what it reads (filter) and the
        // durable group it commits under (group-as-subject).
        Request::SubscribeGroup { group, filter } => both(read(filter), commit(group)),
        // Commit durably advances a consumer group. It MUST verify the capability and
        // be scoped to the group (the group is a subject the ring must grant), or any
        // connection could force another tenant's committed offset forward.
        Request::Commit { group, .. } => commit(group),
        // Both only ever ADD, and both are fully handled before this gate.
        Request::Attach { .. } | Request::Hello => Some(u64::MAX),
    }
}

/// The refusal for a request naming a subject, filter, group, cursor or grant longer
/// than [`MAX_NAME_LEN`], if it does. Checked before anything parses the name.
fn oversized_name(req: &Request) -> Option<String> {
    const NONE: (&str, &str) = ("", "");
    let names: [(&str, &str); 2] = match req {
        Request::Publish { subject, .. } | Request::Will { subject, .. } => {
            [("subject", subject), NONE]
        }
        Request::Subscribe { filter, .. } | Request::Fetch { filter, .. } => {
            [("filter", filter), NONE]
        }
        Request::ForkSubscribe {
            replacement_subject,
            filter,
            ..
        } => [("subject", replacement_subject), ("filter", filter)],
        Request::Commit { group, .. } => [("group", group), NONE],
        Request::ProcessAndProduce {
            out_subject, group, ..
        } => [("subject", out_subject), ("group", group)],
        Request::SubscribeGroup { group, filter } => [("group", group), ("filter", filter)],
        Request::Attach { grant, .. } => [("grant", grant), NONE],
        Request::Replicate {
            subject, commit, ..
        } => [
            ("subject", subject),
            commit.as_ref().map_or(NONE, |(g, _)| ("group", g)),
        ],
        Request::Last { filter, after, .. } => [("filter", filter), ("cursor", after)],
        Request::Hello => [NONE, NONE],
    };
    names
        .iter()
        .find(|(_, name)| name.len() > MAX_NAME_LEN)
        .map(|(what, name)| {
            format!(
                "{what} too long: {} bytes (limit {MAX_NAME_LEN})",
                name.len()
            )
        })
}

/// The pipelined ack path for one connection: an ordered, bounded queue of pending acks
/// feeding a dedicated thread that streams them back on a cloned write half. Lets a
/// connection keep many write ops in flight; back-pressures via the bounded queue.
struct Pipeline {
    /// Ordered queue of per-op ack receivers (bounded → flow control). `send` blocks
    /// when `PIPELINE_DEPTH` acks are outstanding.
    tx: mpsc::SyncSender<Receiver<AckResult>>,
    writer: Option<JoinHandle<io::Result<()>>>,
}

impl Pipeline {
    /// Start an ack-writer on a clone of `stream`'s write half, bounded by
    /// `write_timeout` — the CONNECTION's configured value, not a constant of this
    /// path's own. `set_write_timeout` is `setsockopt(SO_SNDTIMEO)`, a property of the
    /// socket rather than of the descriptor, and `try_clone` shares the file
    /// description: whatever the ack-writer sets here it also sets for the connection
    /// thread's own writes, for the rest of the connection's life, so anything but the
    /// configured [`Broker::set_write_timeout`] value would silently replace it.
    fn start<S: Stream>(stream: &S, write_timeout: Duration) -> io::Result<Pipeline> {
        let wr = stream.try_clone()?;
        let (tx, rx) = mpsc::sync_channel::<Receiver<AckResult>>(PIPELINE_DEPTH);
        // A failed spawn is this connection's error, not a panic that would unwind
        // past `handle_conn` and skip firing the connection's will.
        let writer =
            thread::Builder::new().spawn(move || ack_writer_loop(wr, rx, write_timeout))?;
        Ok(Pipeline {
            tx,
            writer: Some(writer),
        })
    }

    /// Submit a durable mutation: queue its ack slot in order, THEN enqueue the op to
    /// the global writer. Returns false if the ack-writer or the global writer has gone
    /// (the connection should close).
    ///
    /// Ordering matters for correctness: the ack slot is reserved FIRST. The bounded
    /// queue applies back-pressure here (blocks once PIPELINE_DEPTH acks are
    /// outstanding) BEFORE the op reaches the writer, so a record is never committed
    /// unless its ack is already queued to be delivered in order — closing the
    /// "committed durably but ack lost (client sees EOF)" window. If the writer has
    /// since exited, dropping the returned `WriteOp` closes `ack_tx`, so the ack-writer's
    /// blocked recv on the reserved slot returns cleanly instead of hanging.
    fn submit(&self, shared: &Arc<Shared>, kind: WriteKind) -> bool {
        let (ack_tx, ack_rx) = mpsc::channel();
        if self.tx.send(ack_rx).is_err() {
            return false; // ack-writer gone (its socket died); nothing committed
        }
        shared.writes.send(WriteOp { kind, ack: ack_tx }).is_ok()
    }

    /// Queue an already-resolved response (e.g. a validation error) in order.
    fn push_result(&self, res: AckResult) -> bool {
        let (tx, rx) = mpsc::channel();
        let _ = tx.send(res);
        self.tx.send(rx).is_ok()
    }

    /// Flush every queued ack and join the ack-writer (dropping `tx` makes its outer
    /// recv return `Disconnected` once drained), reclaiming the socket for streaming.
    fn finish(mut self) -> io::Result<()> {
        drop(self.tx);
        match self.writer.take() {
            Some(j) => j.join().unwrap_or(Ok(())),
            None => Ok(()),
        }
    }
}

/// Emit a pre-resolved response in order: through the active pipeline, or inline if no
/// write op has started one yet. Returns false when the ack path is gone (close).
fn emit<S: Stream>(
    stream: &mut S,
    pipe: &mut Option<Pipeline>,
    res: AckResult,
) -> io::Result<bool> {
    match pipe {
        Some(p) => Ok(p.push_result(res)),
        None => {
            write_ack(stream, res)?;
            Ok(true)
        }
    }
}

/// Submit a write op, lazily starting the connection's pipeline. Returns false when the
/// ack path is gone (close).
fn emit_op<S: Stream>(
    shared: &Arc<Shared>,
    stream: &mut S,
    pipe: &mut Option<Pipeline>,
    kind: WriteKind,
) -> io::Result<bool> {
    if pipe.is_none() {
        *pipe = Some(Pipeline::start(
            stream,
            Duration::from_millis(shared.write_timeout_ms.load(Ordering::Relaxed)),
        )?);
    }
    Ok(pipe.as_ref().unwrap().submit(shared, kind))
}

/// Finish the pipeline if one is active (flush acks, join the ack-writer).
fn finish_pipe(pipe: &mut Option<Pipeline>) -> io::Result<()> {
    match pipe.take() {
        Some(p) => p.finish(),
        None => Ok(()),
    }
}

/// The ack-writer half of a pipelined connection: stream each op's ack back in order.
///
/// Acks that are ALREADY resolved — a group-commit batch resolves a whole window at
/// once — are gathered and written together, one socket write (one sealed record)
/// for the lot instead of one each. What is gathered is written before this thread
/// blocks on anything, so no ack ever waits on a later one. A socket error tears the
/// connection down; an ack the global writer dropped (shutdown) ends the loop.
fn ack_writer_loop<S: Stream>(
    mut wr: S,
    rx: Receiver<Receiver<AckResult>>,
    write_timeout: Duration,
) -> io::Result<()> {
    use std::sync::mpsc::TryRecvError;
    let _ = wr.set_write_timeout(Some(write_timeout));
    let mut out = Vec::new();
    loop {
        let ack_rx = match rx.try_recv() {
            Ok(r) => r,
            Err(TryRecvError::Empty) => {
                flush_egress(&mut wr, &mut out)?;
                match rx.recv() {
                    Ok(r) => r,
                    Err(_) => return Ok(()),
                }
            }
            Err(TryRecvError::Disconnected) => return flush_egress(&mut wr, &mut out),
        };
        let ack = match ack_rx.try_recv() {
            Ok(a) => a,
            Err(TryRecvError::Empty) => {
                flush_egress(&mut wr, &mut out)?;
                match ack_rx.recv() {
                    Ok(a) => a,
                    Err(_) => return Ok(()),
                }
            }
            Err(TryRecvError::Disconnected) => return flush_egress(&mut wr, &mut out),
        };
        append_frame(&mut out, &encode_response(&ack_response(ack)))?;
        if out.len() >= EGRESS_CHUNK {
            flush_egress(&mut wr, &mut out)?;
        }
    }
}

/// A writer ack as its wire response.
fn ack_response(ack: AckResult) -> Response {
    match ack {
        Ok((offset, deduped)) => Response::PublishAck { offset, deduped },
        Err(msg) => Response::Error { code: 5, msg },
    }
}

/// Turn a writer ack into the wire response.
fn write_ack<S: Stream>(stream: &mut S, ack: AckResult) -> io::Result<()> {
    write_frame(stream, &encode_response(&ack_response(ack)))
}

/// The single writer thread: drain queued mutations into a batch and group-commit them
/// with ONE fsync. The batch self-tunes to load — everything that queued while the
/// previous fsync ran is drained at once — so throughput scales with offered
/// concurrency while each record keeps the Strict (fsync'd-before-ack) guarantee.
/// The only exits are `running == false` (observed on an idle poll) or the channel
/// closing.
fn writer_loop(shared: &Arc<Shared>, rx: Receiver<WriteOp>) {
    loop {
        // Block for the first op, waking periodically only to observe shutdown.
        let first = match rx.recv_timeout(WRITER_IDLE_POLL) {
            Ok(op) => op,
            Err(mpsc::RecvTimeoutError::Timeout) => {
                if shared.running.load(Ordering::Relaxed) {
                    continue;
                }
                return;
            }
            Err(mpsc::RecvTimeoutError::Disconnected) => return,
        };
        let mut batch = vec![first];
        while batch.len() < BATCH_MAX {
            match rx.try_recv() {
                Ok(op) => batch.push(op),
                Err(_) => break, // nothing more queued right now → commit what we have
            }
        }
        process_batch(shared, batch);
    }
}

/// Stage a whole batch under one lock, fsync once, then ack each op. A staged-record
/// I/O error poisons the batch (rolled back, all error); a too-large / reserved /
/// diverged record is an op-level error that does not abort the rest; an fsync error
/// fails the whole batch (none durable). Subscribers are woken once the batch is
/// visible. In the Replicated tier the batch is committed locally, then every
/// committed-but-unconfirmed record is shipped to the followers OUTSIDE the lock, and
/// each op is acked only if its offset is below the resulting quorum watermark.
fn process_batch(shared: &Arc<Shared>, batch: Vec<WriteOp>) {
    // Replicated tier: bring down follower links back first — network I/O, so never
    // under the log lock — so the re-ship base below counts exactly the followers
    // this batch can reach.
    if let Some(rep) = &shared.replicator {
        rep.redial(&shared.running);
    }
    let mut guard = shared.log.lock().unwrap();
    let mut acks: Vec<Sender<AckResult>> = Vec::with_capacity(batch.len());
    let mut results: Vec<AckResult> = Vec::with_capacity(batch.len());
    // Which ops are acked on the LOCAL commit alone, with no quorum gate. See the
    // `local_only` arm of the ack loop below: a `/a/will` registration is the broker's
    // own bookkeeping, never delivered to anyone, and its acknowledgement decides what
    // the CONNECTION does with the will — so it must answer for the record's own fate,
    // not for a follower's.
    let mut local_only: Vec<bool> = Vec::with_capacity(batch.len());
    let mut poisoned = false;
    for op in batch {
        acks.push(op.ack);
        local_only.push(matches!(op.kind, WriteKind::WillRegister { .. }));
        if poisoned {
            results.push(Err("batch aborted (prior append I/O error)".into()));
            continue;
        }
        let staged = match op.kind {
            WriteKind::Publish {
                producer_id,
                producer_seq,
                subject,
                body,
            } => guard.stage_publish(producer_id, producer_seq, subject, body),
            WriteKind::Commit { group, upto } => {
                guard.stage_commit(group, upto).map(|off| (off, false))
            }
            WriteKind::ProcessAndProduce {
                producer_id,
                producer_seq,
                out_subject,
                out_body,
                group,
                upto,
            } => guard.stage_process_and_produce(
                producer_id,
                producer_seq,
                out_subject,
                out_body,
                group,
                upto,
            ),
            WriteKind::Replicate { rec } => guard.stage_replica(rec),
            WriteKind::Bind {
                producer_id,
                principal,
            } => guard.stage_bind(producer_id, principal),
            WriteKind::WillRegister { will } => {
                guard.stage_will_register(&will).map(|off| (off, false))
            }
            WriteKind::WillFire { will } => guard.stage_will_fire(will),
        };
        match staged {
            Ok((off, deduped)) => results.push(Ok((off.0, deduped))),
            Err(StageErr::TooLarge) => results.push(Err("message too large".into())),
            Err(StageErr::Reserved(subject)) => results.push(Err(reserved_msg(&subject))),
            Err(StageErr::SubjectBound(msg)) => results.push(Err(msg)),
            Err(StageErr::Collision(msg)) => results.push(Err(msg)),
            // Not a failure: the fence did its job and the will appended nothing.
            Err(StageErr::Fenced(msg)) => results.push(Err(msg)),
            // Also not a failure: a replica appends nothing of its own making.
            Err(StageErr::Replica(msg)) => results.push(Err(msg)),
            Err(StageErr::Diverged(msg)) => results.push(Err(msg)),
            // Decided in here, under the lock that appends: a replicated hidden record
            // offered to a log this broker owns, and a will offered the reserved ack
            // half. Op-level, like every other refusal above — the file is untouched.
            Err(StageErr::ReservedReplica(msg)) => results.push(Err(msg)),
            Err(StageErr::SeqReserved(msg)) => results.push(Err(msg)),
            Err(StageErr::Io(e)) => {
                poisoned = true;
                results.push(Err(format!("append failed: {e}")));
            }
        }
    }
    // Commit the batch: one fsync for everyone (unless poisoned — then roll back).
    let commit_res = if poisoned {
        guard.abort_batch();
        Err("batch aborted before fsync".to_string())
    } else {
        guard
            .commit_batch()
            .map_err(|e| format!("commit failed: {e}"))
    };
    // Replicated tier: gather every committed-but-unconfirmed record — from the lowest
    // follower prefix to the head, cheap Arc clones — under the lock, to ship AFTER
    // releasing it: network I/O never holds the log lock (the delivery discipline).
    let to_ship = match &shared.replicator {
        Some(rep) if commit_res.is_ok() => {
            let base = rep.min_upto(guard.base().0, guard.head().0);
            Some(guard.read_from(Offset(base)))
        }
        _ => None,
    };
    if shared.replicator.is_none() {
        // Strict/Relaxed: the durable head IS the visible head. Publish it under the
        // lock (the tail's wait predicate reads it under this lock, so no wakeup is
        // lost between "caught up" and "wait").
        shared.head.store(guard.head().0, Ordering::Relaxed);
    }
    drop(guard);
    // Replicated tier: ship, then publish the quorum watermark as the visible head —
    // again under the log lock, for the same no-lost-wakeup reason — and wake.
    let watermark = match (&shared.replicator, to_ship) {
        (Some(rep), Some(records)) => {
            let wm = rep.replicate(&records, &shared.running);
            let g = shared.log.lock().unwrap();
            // MONOTONE: a record a quorum once held is not un-held because a follower
            // later restarted empty and its link reset to re-ship from 0 — the visible
            // head only ever advances (Kafka's high-watermark discipline).
            let hwm = shared.head.fetch_max(wm, Ordering::Relaxed).max(wm);
            drop(g);
            Some(hwm)
        }
        (Some(_), None) => Some(shared.head.load(Ordering::Relaxed)),
        (None, _) => None,
    };
    shared.tail.notify_all();
    // Ack each op: durable AND (if Replicated) below the quorum watermark, else error.
    // A deduped retry whose original record is still unconfirmed is an error too.
    //
    // WITH ONE EXCEPTION, `local_only`. The quorum gate answers "can a subscriber see
    // this record on a node that will survive me?" — the right question for a publish,
    // and the wrong one for a `/a/will` REGISTRATION, which no subscriber ever sees.
    // Its ack decides whether the connection keeps the will in memory, and the log
    // keeps the record whatever a follower did: answering a quorum shortfall with
    // "will was not persisted" would leave the connection with no will and the log
    // with the record, which the NEXT OPEN fires — a `gone` for a producer told it
    // registered nothing. The in-memory will and the `/a/will` record must never
    // disagree about whether the will exists, so the registration is acked on its own
    // commit. HONEST BOUNDARY: the will is then only
    // as durable as the leader's local log — if the leader is lost before a follower
    // takes the record, the goodbye is lost with it.
    for ((ack, res), local) in acks.into_iter().zip(results).zip(local_only) {
        let send = match (&commit_res, res) {
            // An op that failed on its own terms (too large / reserved / diverged / the
            // append or poisoned-log error that aborted the batch) keeps its own, more
            // specific message; the ops a batch failure took down with it get the batch's.
            (_, Err(msg)) => Err(msg),
            (Err(msg), Ok(_)) => Err(msg.clone()),
            (Ok(()), Ok((off, deduped))) => match watermark {
                Some(wm) if off >= wm && !local => Err("not replicated to quorum".into()),
                _ => Ok((off, deduped)),
            },
        };
        let _ = ack.send(send);
    }
}

/// One `Last` page: the rows, the cursor to resume from (`None` once the answer is
/// complete), and the subscriber-visible head they were read with.
///
/// THE WHOLE ANSWER IS READ AS OF ONE HEAD. `visible` is taken from `shared.head`
/// under the log lock on the FIRST round and PINNED for every round after it, and that
/// pinned value is the head the answer reports. So every row is its subject's newest
/// record STRICTLY BELOW the reported head — the one thing a last-value verb must not
/// get wrong.
///
/// Re-reading the head each round would get it wrong: round 1 collects `A@10` under
/// head H1; the lock is released between rounds, so a publisher writes `A@20`; round 3
/// finishes under H3 > 20 and the answer pairs `A@10` with H3, when A's last value
/// below H3 is 20. The cursor has already passed A, and the reader's paired
/// `Subscribe { from: mark.next }` starts at H3, so the stale row is never corrected.
///
/// WHAT THE PIN COSTS, DELIBERATELY. `last_matching` decides a subject from
/// `self.last` — its LATEST offset — and skips it entirely when that offset is not
/// below `visible`. So a subject whose newest record moves to or above the pinned head
/// mid-walk, and that the walk has not yet reached, is OMITTED from the page rather
/// than returned at its older value; reading it at its value as of the pin would need
/// a backward walk from `visible` that the store exposes no call for. This is the same
/// fail-closed direction the Replicated tier already takes for a record above the
/// quorum watermark, and here it loses nothing: the answer's `Mark.next` IS the pinned
/// head, so the record that displaced the omitted subject is delivered on the reader's
/// `Subscribe { from: mark.next }`. An omitted subject is filled in by the tail; a
/// stale row would not be.
///
/// THE PIN IS PER REQUEST. Client-driven paging (`Mark.resume` into the next `Last`)
/// pins a fresh head per page, so a paged reader still has to fold newest-wins across
/// its pages and tail from the FIRST page's `next`, exactly as `Client::last` says.
///
/// THE CURSOR NEVER NAMES A SUBJECT THE FILTER DOES NOT MATCH. `last_matching` walks
/// the ordered subject index from the filter's LITERAL PREFIX (`/f/F/in/*/*/n-1/*` ->
/// `/f/F/in/`) and reports the last entry it VISITED, matched or not. When the page is
/// cut by `max` that entry always matched, so it is inside whatever grant contained the
/// filter; when it is cut by the SCAN bound it is whatever the walk happened to stop
/// on, which under a literal prefix as broad as `/f/F/in/` is routinely another node's,
/// another session's, another human's inbox lane. Putting that on the wire would hand
/// a scoped reader one out-of-grant subject NAME per over-scanned page — and in this
/// fabric provenance is the address, so names are the roster.
///
/// So a page cut by the scan bound on a non-matching entry is CONTINUED here, from that
/// cursor, until the walk either finds enough matches or runs the prefix range out. The
/// lock is dropped between rounds, which is the property `LAST_SCAN_MAX` exists for —
/// no single acquisition visits more than `LAST_SCAN_MAX` entries, and ingest is never
/// stalled by a sparse filter. What a client can pay for is more CPU across rounds, and
/// [`LAST_RESUME_ROUNDS`] bounds that; past it the answer is an error rather than a
/// cursor it is not entitled to (blanking the cursor is not available: an empty
/// `Mark.resume` means "complete", which would be a silent truncation).
#[allow(clippy::type_complexity)]
fn last_page(
    shared: &Arc<Shared>,
    filt: &Filter,
    after: &str,
    want: usize,
) -> Result<(Vec<Arc<BrokerRecord>>, Option<String>, u64), String> {
    let mut out: Vec<Arc<BrokerRecord>> = Vec::new();
    let mut cursor = after.to_string();
    // The head every round reads against and the answer reports. Read under the log
    // lock on the first round (see below) and never re-read: that is what makes the
    // multi-round walk a snapshot rather than a splice of rounds taken at different
    // heads.
    let mut pinned: Option<u64> = None;
    for round in 0..LAST_RESUME_ROUNDS {
        // The FIRST round reads its head under the SAME lock as its page —
        // `shared.head` (the subscriber-visible head, the quorum watermark in the
        // Replicated tier), never `log.head()`. Under the lock: the seek, at most
        // LAST_SCAN_MAX index visits, and pointer clones — never the socket writes the
        // caller does, which happen with it released.
        let (page, resume, head) = {
            let log = shared.log.lock().unwrap();
            let head = *pinned.get_or_insert_with(|| shared.head.load(Ordering::Relaxed));
            let (page, resume) =
                log.last_matching(filt, &cursor, want - out.len(), LAST_SCAN_MAX, head);
            (page, resume, head)
        };
        out.extend(page);
        let covered = |s: &str| filt.matches_str(s) || out.len() >= want;
        match resume {
            // The prefix range ran out: the answer is complete.
            None => return Ok((out, None, head)),
            // Cut by `max`, or stopped on an entry the filter matches: either way the
            // cursor is a subject the caller's own filter covers.
            Some(s) if covered(&s) => return Ok((out, Some(s), head)),
            // Cut by the scan bound on a non-matching entry: keep walking.
            Some(s) => cursor = s,
        }
        // The round boundary, with the log lock released — the window a concurrent
        // publisher gets, and the one a test needs to occupy to prove the head above
        // does not move with it. Cloned out of the lock before the call so a hook is
        // free to touch the broker.
        let hook = shared.last_round_hook.lock().unwrap().clone();
        if let Some(hook) = hook {
            hook(round);
        }
    }
    Err(format!(
        "last: {LAST_RESUME_ROUNDS} scan rounds under {:?} reached no position this filter \
         covers; narrow the filter's literal prefix",
        filt.as_str()
    ))
}

/// Up to [`TAIL_CHUNK`] records from `*cursor` up to (not including) `head`, read
/// under the log lock the caller holds, and whether more remain below `head` after
/// them.
///
/// Records below the retention base are gone for good, so the cursor first moves up to
/// it. What is read is unchanged by that (`read_range` clamps there anyway), but the
/// tail parks on `head <= cursor`, and a cursor left below a base with nothing visible
/// above it would never park — it would spin on the lock.
fn next_chunk(log: &BrokerLog, cursor: &mut u64, head: u64) -> (Vec<Arc<BrokerRecord>>, bool) {
    *cursor = (*cursor).max(log.base().0);
    let behind = usize::try_from(head.saturating_sub(*cursor)).unwrap_or(usize::MAX);
    let chunk = log.read_range(Offset(*cursor), behind.min(TAIL_CHUNK));
    let more = behind > chunk.len();
    (chunk, more)
}

/// Stream every visible record matching `filter` from `cursor`, then tail live, until
/// the peer goes, the broker stops, or — on a guarded broker — the authority that
/// admitted the subscription lapses at `until` (unix ms; `u64::MAX`: never), which
/// ends the stream with an `unauthorized` error.
fn tail_loop<S: Stream>(
    shared: &Arc<Shared>,
    stream: &mut S,
    mut cursor: u64,
    filter: Filter,
    until: u64,
) -> io::Result<()> {
    // A short read timeout lets a parked subscriber probe for a vanished peer; a
    // generous write timeout means a wedged delivery to a stuck consumer errors out
    // (and resumes from its cursor) rather than hanging the thread forever.
    let _ = stream.set_read_timeout(Some(PEER_PROBE_TIMEOUT));
    let _ = stream.set_write_timeout(Some(stream_write_timeout(shared)));
    let mut out = Vec::new();
    // When the peer was last probed for having gone (see the end of the loop).
    let mut probed = Instant::now();
    loop {
        // Catch-up: copy the next records >= cursor that are VISIBLE (below `head` — in
        // the Replicated tier the quorum watermark, so nothing un-replicated is ever
        // delivered) under a SHORT lock, then release it. At most TAIL_CHUNK of them: a
        // cursor far behind the head catches up chunk by chunk, and a publisher waits
        // for one chunk's copy at most, never a whole-log one. `more`: the chunk was
        // cut short of the visible head.
        let (batch, more) = {
            let log = shared.log.lock().unwrap();
            let visible = shared.head.load(Ordering::Relaxed);
            next_chunk(&log, &mut cursor, visible)
        };
        if batch.is_empty() {
            if let Some(now) = lapsed(until) {
                return end_lapsed(stream, &mut out, until, now);
            }
            // Park until a new commit (head > cursor) or shutdown — releasing the
            // lock — but wake every LIVENESS_POLL to check whether the peer vanished,
            // and at the latest when this stream's authority lapses.
            let park = match until {
                u64::MAX => LIVENESS_POLL,
                t => LIVENESS_POLL.min(Duration::from_millis(t.saturating_sub(now_unix_ms()))),
            };
            {
                let guard = shared.log.lock().unwrap();
                let (guard, _timed_out) = shared
                    .tail
                    .wait_timeout_while(guard, park, |_log| {
                        shared.running.load(Ordering::Relaxed)
                            && shared.head.load(Ordering::Relaxed) <= cursor
                    })
                    .unwrap();
                drop(guard);
            }
            let head = shared.head.load(Ordering::Relaxed);
            if !shared.running.load(Ordering::Relaxed) && head <= cursor {
                return Ok(()); // shutdown, nothing more to deliver
            }
            if head <= cursor && peer_gone(stream) {
                return Ok(()); // consumer vanished — reap this thread + fd
            }
            continue;
        }
        // Deliver outside the lock; a slow consumer blocks only this thread.
        let mut wrote = false;
        for rec in batch {
            if let Some(now) = lapsed(until) {
                return end_lapsed(stream, &mut out, until, now);
            }
            // Checked, like the engine's offset spine: a u64::MAX seq ends the stream.
            cursor = match rec.seq.checked_next() {
                Some(o) => o.0,
                None => return flush_egress(stream, &mut out),
            };
            // Pure consumer-group commit records are internal bookkeeping — never
            // delivered to data subscribers. A wildcard filter (`/a/>`, `/a/*`)
            // matches the reserved `/a/commit` subject, so the skip must be explicit
            // and filter-independent; the record still consumes an offset (advanced
            // above), it is simply not sent.
            if is_hidden_subject(&rec.subject) {
                continue;
            }
            if filter.matches_str(&rec.subject) {
                // `rec` is a shared `Arc` (no deep copy out of the log), and its
                // frame is assembled in place from the borrowed subject/body.
                queue_delivery(stream, &mut out, &rec)?;
                wrote = true;
            }
        }
        flush_egress(stream, &mut out)?;
        // A subscriber whose filter matches nothing still drains the log without ever
        // writing, so the park branch (which probes for a vanished peer) is never
        // reached under continuous traffic. Probe here when a batch produced zero
        // writes, so a dead never-matching consumer's thread + fd are still reaped. A
        // probe blocks for PEER_PROBE_TIMEOUT, so a chunk with more right behind it
        // probes at most once per LIVENESS_POLL rather than once per chunk.
        if !wrote && (!more || probed.elapsed() >= LIVENESS_POLL) {
            probed = Instant::now();
            if peer_gone(stream) {
                return Ok(());
            }
        }
    }
}

/// Bytes of framed output a streaming verb gathers before it writes: one socket write
/// (and, sealed, one AEAD record per 64 KiB) per this much, not one per record.
const EGRESS_CHUNK: usize = 64 * 1024;

/// Gather `rec` as a framed `Delivery` in `out`, writing `out` to `stream` once it
/// holds [`EGRESS_CHUNK`] bytes. The caller ends its batch with [`flush_egress`].
fn queue_delivery<S: Write>(
    stream: &mut S,
    out: &mut Vec<u8>,
    rec: &BrokerRecord,
) -> io::Result<()> {
    append_delivery_frame(out, rec.seq.0, &rec.subject, &rec.body)?;
    if out.len() >= EGRESS_CHUNK {
        flush_egress(stream, out)?;
    }
    Ok(())
}

/// Write what `out` has gathered and empty it — handing back any capacity a large
/// record grew it to, so a long-lived subscription does not pin its biggest record.
fn flush_egress<S: Write>(stream: &mut S, out: &mut Vec<u8>) -> io::Result<()> {
    if !out.is_empty() {
        stream.write_all(out)?;
        out.clear();
    }
    out.shrink_to(2 * EGRESS_CHUNK);
    Ok(())
}

/// Whether the subscriber's peer has closed its end. After SUBSCRIBE the client
/// only reads, so a timed `read` returns EOF (`Ok(0)`) iff the peer closed; a hard
/// error (reset/pipe) is also gone; `WouldBlock`/`TimedOut` means still connected.
/// (`UnixStream::peek` would avoid consuming, but it is unstable on this toolchain;
/// any unexpected post-subscribe byte is simply ignored.)
fn peer_gone<S: Stream>(stream: &mut S) -> bool {
    let mut probe = [0u8; 1];
    match stream.read(&mut probe) {
        Ok(0) => true,
        Ok(_) => false,
        Err(e) => !matches!(
            e.kind(),
            io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A follower link at confirmed prefix `upto`; `live` gives it a connected socket
    /// (a loopback pair), otherwise it is down.
    fn link(upto: u64, fenced: Option<&str>, live: bool) -> FollowerLink {
        let stream = live.then(|| {
            let l = TcpListener::bind("127.0.0.1:0").unwrap();
            TcpStream::connect(l.local_addr().unwrap()).unwrap()
        });
        FollowerLink {
            addr: "127.0.0.1:0".to_string(),
            stream,
            upto,
            fenced: fenced.map(str::to_string),
            fresh: false,
        }
    }

    fn replicator(links: Vec<FollowerLink>) -> Replicator {
        Replicator {
            links: Mutex::new(links),
            kill: Mutex::new(Vec::new()),
            quorum: 1,
            io_timeout: Duration::from_secs(1),
        }
    }

    /// A FENCED follower does not hold the re-ship base down. `replicate` ships nothing
    /// to a fenced link, so its `upto` is frozen for the life of the leader; counting it
    /// would pin the base — the start of a slice the writer clones UNDER THE LOG LOCK
    /// on every batch — at that frozen offset.
    #[test]
    fn min_upto_ignores_fenced_links() {
        let r = replicator(vec![
            link(100, Some("replica diverged at offset 100"), true),
            link(500, None, true),
        ]);
        assert_eq!(
            r.min_upto(0, 500),
            500,
            "a diverged follower's frozen prefix became every later batch's base"
        );
        // Healthy links still set it, and the lowest of them wins.
        let r = replicator(vec![
            link(500, None, true),
            link(100, None, true),
            link(300, None, true),
        ]);
        assert_eq!(r.min_upto(0, 500), 100);
        // Every link fenced, or no links at all: nothing can be shipped, so the base is
        // the head and the slice is empty rather than the whole log.
        let r = replicator(vec![
            link(100, Some("diverged"), true),
            link(7, Some("unauthorized"), true),
        ]);
        assert_eq!(r.min_upto(0, 500), 500);
        assert_eq!(replicator(Vec::new()).min_upto(0, 500), 500);
    }

    /// A DOWN follower (its re-dial at the start of the batch failed) does not hold
    /// the re-ship base down either: nothing reaches it this batch, and counting it
    /// would clone its whole backlog under the log lock on every batch it stays down.
    #[test]
    fn min_upto_ignores_down_links() {
        let r = replicator(vec![link(100, None, false), link(500, None, true)]);
        assert_eq!(
            r.min_upto(0, 500),
            500,
            "a down follower's prefix became the batch's base"
        );
        let r = replicator(vec![link(100, None, false), link(300, None, false)]);
        assert_eq!(
            r.min_upto(0, 500),
            500,
            "no follower reachable: nothing to clone"
        );
    }

    /// A follower BEHIND the retention base (it answered a gap, its `upto` reset to 0,
    /// and the records it lacks were pruned) is never shipped to again, so it does not
    /// hold the re-ship base down to the base either — which would be a copy of the
    /// whole retained log under the log lock on every batch.
    #[test]
    fn min_upto_ignores_links_behind_the_base() {
        let r = replicator(vec![link(0, None, true), link(500, None, true)]);
        assert_eq!(
            r.min_upto(200, 500),
            500,
            "a follower behind the base became the batch's base"
        );
        // At or above the floor it counts as before.
        let r = replicator(vec![link(200, None, true), link(500, None, true)]);
        assert_eq!(r.min_upto(200, 500), 200);
        let r = replicator(vec![link(0, None, true)]);
        assert_eq!(r.min_upto(200, 500), 500, "nothing left to ship to");
    }

    /// Removes its files when dropped, so a test leaves nothing behind whether it
    /// passes or panics. Bound before the broker that uses them, so it drops after it.
    #[cfg(unix)]
    struct Cleanup(Vec<String>);

    #[cfg(unix)]
    impl Drop for Cleanup {
        fn drop(&mut self) {
            for path in &self.0 {
                let _ = std::fs::remove_file(path);
            }
        }
    }

    /// A served broker whose log holds `n` records (512-byte bodies on `/t/x`), and
    /// the guard that removes its files.
    #[cfg(unix)]
    fn filled(tag: &str, n: u64) -> (Cleanup, Broker, BrokerHandle, String) {
        static SEQ: AtomicU64 = AtomicU64::new(0);
        let k = SEQ.fetch_add(1, Ordering::Relaxed);
        let pid = std::process::id();
        let log = format!("/tmp/asb_unit_{tag}_{pid}_{k}.log");
        let sock = format!("/tmp/asb_unit_{tag}_{pid}_{k}.sock");
        let _ = std::fs::remove_file(&log);
        let tmp = Cleanup(vec![log.clone(), sock.clone()]);
        let b = Broker::open_with(&log, Durability::Relaxed).unwrap();
        {
            let mut l = b.shared.log.lock().unwrap();
            for seq in 0..n {
                l.publish(1, seq, "/t/x".to_string(), vec![0u8; 512])
                    .unwrap();
            }
            b.shared.head.store(l.head().0, Ordering::Relaxed);
        }
        let h = b.serve(&sock).unwrap();
        (tmp, b, h, sock)
    }

    /// Open a streaming verb with `req` on a connection that then never reads: the
    /// broker delivers until the socket buffers fill and blocks there, still holding
    /// whatever it copied out of the log and has not yet delivered.
    #[cfg(unix)]
    fn stalled_reader(sock: &str, req: &Request) -> UnixStream {
        let mut s = UnixStream::connect(sock).unwrap();
        write_frame(&mut s, &crate::proto::encode_request(req)).unwrap();
        s
    }

    /// How many of the log's records a reader holds copies of, once that number has
    /// stopped moving (the reader is blocked on the stalled socket).
    #[cfg(unix)]
    fn settled_copies(b: &Broker) -> usize {
        let t = Instant::now();
        let (mut last, mut same) = (usize::MAX, 0);
        loop {
            let n = b.shared.log.lock().unwrap().shared_records();
            same = if n == last && n > 0 { same + 1 } else { 0 };
            if same == 5 {
                return n;
            }
            last = n;
            assert!(
                t.elapsed() < Duration::from_secs(20),
                "the reader never settled (last count {n})"
            );
            thread::sleep(Duration::from_millis(40));
        }
    }

    /// A subscriber catching up from offset 0 copies the log out ONE CHUNK per lock
    /// hold, so the most it can hold at once is one chunk — never the whole suffix,
    /// which it would copy under the log lock while every publisher waits.
    #[cfg(unix)]
    #[test]
    fn a_tail_catching_up_copies_the_log_one_chunk_at_a_time() {
        let n = 3 * TAIL_CHUNK as u64;
        let (_tmp, b, mut h, sock) = filled("tailchunk", n);
        let _reader = stalled_reader(
            &sock,
            &Request::Subscribe {
                from_offset: 0,
                filter: "/t/>".to_string(),
            },
        );
        let held = settled_copies(&b);
        assert!(
            held <= TAIL_CHUNK,
            "a subscriber catching up from 0 held {held} of the log's {n} records at once \
             (one chunk is {TAIL_CHUNK})"
        );
        h.shutdown();
    }

    /// The same for a fork snapshot, which is delivered from the same kind of copy.
    #[cfg(unix)]
    #[test]
    fn a_fork_snapshot_copies_the_log_one_chunk_at_a_time() {
        let n = 3 * TAIL_CHUNK as u64;
        let (_tmp, b, mut h, sock) = filled("forkchunk", n);
        let _reader = stalled_reader(
            &sock,
            &Request::ForkSubscribe {
                fork_at: n - 1,
                replacement_subject: "/t/y".to_string(),
                replacement_body: b"r".to_vec(),
                filter: "/t/>".to_string(),
            },
        );
        let held = settled_copies(&b);
        assert!(
            held <= TAIL_CHUNK,
            "a fork of a {n}-record log held {held} of its records at once \
             (one chunk is {TAIL_CHUNK})"
        );
        h.shutdown();
    }
}
