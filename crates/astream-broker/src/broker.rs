//! The broker daemon: a thread-per-connection server over a Unix-domain socket or TCP
//! (plaintext; AEAD-sealed with the `aead` feature; capability-guarded with the `cap`
//! feature), one `Mutex<BrokerLog>` + `Condvar` for the single-writer log and live
//! tail, and a group-commit writer thread that every durable mutation funnels through.
//!
//! Lock discipline (the crux): the log `Mutex` is held ONLY for the memory half of a
//! batch — staging it and beginning its commit (the seal, the flush its tier owes), then
//! ending it (the promotion, the head) — or a short catch-up pointer copy (at most
//! [`TAIL_CHUNK`] records per hold) — NEVER across a socket write, a follower
//! round-trip, a `Condvar` wait, or the device. The writer RELEASES it for the batch's
//! `write` and fsync and takes it again to promote (`BrokerLog::commit_begin`, then
//! `BatchWrite::run`, then `BrokerLog::commit_end`), so a reader beside a busy Strict
//! writer never waits out an fsync. That is safe because nothing is promoted until the
//! end: while the lock is free the batch's records are only staged — the head has not
//! moved, so no reader can see them and no ack has gone — and a staged batch refuses
//! every other mutation of the log until it ends. The one caller that would rewrite the
//! file under it, retention, first takes the writer's BATCH lock (`Shared::batch`, held
//! by the writer from staging to promotion; lock order batch → log, and no reader takes
//! it), so it waits for the batch instead of being refused — for its begin and for its
//! finish; the bulk of its copy runs between them with neither lock held. So a slow/dead consumer (or
//! follower) blocks only its own thread, never other consumers, and a busy writer
//! blocks no reader for longer than it takes to stage or promote (and, on an
//! anti-rollback log, to advance its watermark sidecar). The tail wakes via
//! `Condvar` (no sleeps, no poll); the wait predicate reads the visible `head` under the
//! same lock the writer advances it under, so a commit landing between "caught up" and
//! "wait" is never missed. The writer wakes the tails only after a batch that made a
//! deliverable record visible: a parked tail sleeps through a batch that made nothing
//! visible or only hidden records, and reads past those offsets when it next wakes.
//!
//! The connection handshake reads nothing under the log lock. `Hello`'s log identity
//! (with the tier served and the lineage beside it) and the durable producer bindings
//! an `Attach` checks are copies kept beside the log, each behind its own short
//! `Mutex` (`Shared::hello`, `Shared::bindings`), which
//! the writer refreshes while it holds the log lock and every reader takes ALONE. So
//! the order is log → copy, never the reverse, and a guarded connect whose principals
//! are ALREADY bound does not queue behind another writer's fsync. A principal's FIRST
//! bind is still the writer's to append — as is a binding not yet visible, or a
//! different principal on a bound id, for the writer to refuse — so that attach waits
//! out whatever batch the writer is in, fsync included, once per connection.
//!
//! Lifecycle: the acceptor blocks in `accept()` — no poll, so a new connection is taken
//! the instant it arrives and an idle listener never wakes. Shutdown flips the
//! `running` flags, force-closes every registered connection socket (a thread parked in
//! a socket read/write returns at once), DIALS the listener until its acceptor reports
//! that it left (a Unix socket through `<socket>.wake`, a name the broker owns for the
//! same inode, so an embedder that unlinked the socket path first does not wedge it;
//! TCP through the bound address), joins the acceptor, queues the writer's stop behind
//! the work already queued and joins the writer — which sleeps on its queue with no
//! timer, so the stop wakes it at once — then releases the log's file lock. A dial
//! counts only when that listener's own acceptor answers it: after
//! `ACCEPT_WAKE_ATTEMPTS` unanswered rounds — no name left, or another listener taking
//! the dials — the acceptor is abandoned and counted, so shutdown always returns. A
//! listener that cannot get that name polls instead (`ACCEPT_POLL`,
//! [`BrokerHandle::blocks_in_accept`] `false`). A `Broker` dropped without ever serving
//! stops its own writer thread the same way.

use crate::brecord::{BrokerRecord, GroupCommit};
use crate::client::{kept_from_children, RecvBuf};
use crate::proto::{
    append_delivery_frame, append_delivery_frame_stamped, append_delivery_frame_with_crc,
    append_frame, compute_delivery_crc, decode_request_with_bt, decode_response,
    encode_protocol_refusal, encode_replicate_stamped, encode_response, read_frame, write_frame,
    AttachedProducerStats, FaceStats, Request, Response, WireStats, CAP_EXPIRED_PREFIX,
    ERR_BAD_FILTER, ERR_BAD_SUBJECT, ERR_ORIGIN_REFUSED, ERR_ORIGIN_UNKNOWN, ERR_RATE_LIMITED,
    ERR_RECORD_REFUSED, ERR_REFUSED, ERR_RELAY_NOT_READY, ERR_RETIRE_REFUSED, ERR_SUBJECT_BOUND,
    ERR_TOO_MANY_CONNS, ERR_UNAUTHORIZED, LOG_POISONED_PREFIX, PROTO_VERSION, RATE_LIMITED_PREFIX,
    RETAINED_FROM_PREFIX,
};
use crate::store::{
    is_hidden_subject, replicated_reserved_msg, reserved_msg, Begun, BrokerLog, Durability,
    FlushCounts, InjectedFaults, LogStats, OpenOptions, Prepared, RateLimit, StageErr, Told,
    WillRecord, COMMIT_SUBJECT, MAX_SUBJECTS_PER_PRODUCER, RETIRE_SUBJECT,
};
use astream_wire::{Filter, Offset, Subject};
use std::cell::Cell;
use std::collections::{BTreeMap, HashMap, HashSet};
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

/// A second handle to a connection's socket, held in [`Shared::conns`] so
/// [`BrokerHandle::shutdown`] can force-close the connection (both directions) and
/// unblock a thread parked in a socket read or write, letting it (and its ack-writer
/// thread and fds) be reaped promptly. For the sealed transport it is the TCP socket
/// beneath the records: shutdown never touches record bytes.
enum Sock {
    #[cfg(unix)]
    Unix(UnixStream),
    Tcp(TcpStream),
    #[cfg(feature = "handshake")]
    Roam(astream_aead::RoamCloser),
    /// An adopted stream ([`Broker::serve_stream`]), and the key its owner proved. Unlike a
    /// socket, it is ended as soon as that key is revoked ([`end_revoked_streams`]).
    #[cfg(feature = "stream")]
    Stream {
        link: crate::stream_link::LinkEnd,
        peer: [u8; 32],
    },
}

impl Sock {
    fn shutdown_both(&self) {
        match self {
            #[cfg(unix)]
            Sock::Unix(s) => {
                let _ = s.shutdown(Shutdown::Both);
            }
            Sock::Tcp(s) => {
                let _ = s.shutdown(Shutdown::Both);
            }
            #[cfg(feature = "handshake")]
            Sock::Roam(c) => c.shutdown_both(),
            #[cfg(feature = "stream")]
            Sock::Stream { link, .. } => {
                let _ = link.shutdown(Shutdown::Both);
            }
        }
    }
}

#[cfg(clean_islands)]
#[path = "broker_island.rs"]
mod broker_island;
#[cfg(not(clean_islands))]
pub use crate::twins::broker_batch_clamp;
#[cfg(clean_islands)]
pub use broker_island::broker_batch_clamp;

#[cfg(clean_islands)]
#[path = "tail_wake_island.rs"]
mod tail_wake_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{tail_skip_clamp, tail_wake_head_advance};
#[cfg(clean_islands)]
pub use tail_wake_island::{tail_skip_clamp, tail_wake_head_advance};

#[cfg(clean_islands)]
#[path = "rate_island.rs"]
mod rate_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{rate_clock_advance, rate_tokens_clamp};
#[cfg(clean_islands)]
pub use rate_island::{rate_clock_advance, rate_tokens_clamp};

contract_fn! {
    /// Verified check that a producer's refilled token balance covers `cost`
    /// (`cost <= tokens`), linked via `clean-kernel-defeq` to `rate_tokens_sufficient_isl`.
    #[must_use]
    pub const fn rate_tokens_sufficient(tokens: u64, cost: u64) -> bool
    clauses [ensures result == (cost <= tokens)]
    {
        cost <= tokens
    }
}

/// Hard cap on active per-producer / per-principal token buckets held in memory.
const MAX_RATE_BUCKETS: usize = 4096;

/// One bucket of a [`RateLimit`]: a principal's record and byte tokens in thousandths, and
/// the millisecond they were last refilled at, on whatever monotone clock its keeper reads.
///
/// [`RateBucket::step`] is the whole arithmetic the broker judges a publish with, in the
/// open so another program can judge its own writers by the same rule: nothing here reads a
/// clock, holds a lock or knows a producer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RateBucket {
    /// Record tokens, in thousandths of a record.
    pub rec_milli: u64,
    /// Byte tokens, in thousandths of a byte; 0 under a limit with no byte rate.
    pub byte_milli: u64,
    /// The millisecond the tokens were last refilled at.
    pub last_ms: u64,
}

/// Why [`RateBucket::step`] refused a record, and the milliseconds after which the same
/// record would pass were nothing else written meanwhile.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RateRefusal {
    /// Milliseconds to wait, at least 1.
    pub retry_ms: u64,
    /// Which bound refused.
    pub why: &'static str,
}

/// Milliseconds until `deficit` thousandths refill at `per_sec`, rounded up, at least 1.
const fn rate_retry_ms(deficit: u64, per_sec: u64) -> u64 {
    let ms = match deficit
        .saturating_add(per_sec.saturating_sub(1))
        .checked_div(per_sec)
    {
        Some(ms) => ms,
        None => 1,
    };
    if ms == 0 {
        1
    } else {
        ms
    }
}

/// A record's cost in bytes: its wire bytes, and 1 for an empty one.
const fn rate_wire_cost(wire_bytes: usize) -> u64 {
    if wire_bytes == 0 {
        1
    } else {
        wire_bytes as u64
    }
}

/// The refusal of a record of `cost` bytes that `limit`'s byte burst can never hold.
const fn rate_oversize(limit: &RateLimit, cost: u64) -> Option<RateRefusal> {
    if limit.bytes_per_sec > 0 && cost > limit.burst_bytes {
        let over = cost.saturating_sub(limit.burst_bytes).saturating_mul(1_000);
        Some(RateRefusal {
            retry_ms: rate_retry_ms(over, limit.bytes_per_sec),
            why: "record bytes exceed burst_bytes",
        })
    } else {
        None
    }
}

impl RateBucket {
    /// A bucket nothing has drawn from: `limit`'s whole burst, as of `now_ms`.
    #[must_use]
    pub const fn full(limit: &RateLimit, now_ms: u64) -> Self {
        Self {
            rec_milli: limit.burst_records.saturating_mul(1_000),
            byte_milli: limit.burst_bytes.saturating_mul(1_000),
            last_ms: now_ms,
        }
    }

    /// The tokens this bucket holds at `now_ms` under `limit`: what it held, refilled for
    /// the time since `last_ms` and clamped to the burst. No byte tokens without a byte rate.
    const fn refilled(&self, limit: &RateLimit, now_ms: u64) -> (u64, u64) {
        let elapsed_ms = now_ms.saturating_sub(self.last_ms);
        let rec = rate_tokens_clamp(
            self.rec_milli
                .saturating_add(elapsed_ms.saturating_mul(limit.records_per_sec)),
            limit.burst_records.saturating_mul(1_000),
        );
        let byte = if limit.bytes_per_sec > 0 {
            rate_tokens_clamp(
                self.byte_milli
                    .saturating_add(elapsed_ms.saturating_mul(limit.bytes_per_sec)),
                limit.burst_bytes.saturating_mul(1_000),
            )
        } else {
            0
        };
        (rec, byte)
    }

    /// Whether this bucket holds `limit`'s whole burst at `now_ms`: forgetting it then
    /// changes no later verdict, which is how a keeper of many buckets makes room.
    #[must_use]
    pub const fn is_full_at(&self, limit: &RateLimit, now_ms: u64) -> bool {
        let (rec, byte) = self.refilled(limit, now_ms);
        rec >= limit.burst_records.saturating_mul(1_000)
            && (limit.bytes_per_sec == 0 || byte >= limit.burst_bytes.saturating_mul(1_000))
    }

    /// This bucket once the limit changed to `limit` at `now_ms`: its tokens clamped to the
    /// new burst, and its time moved to `now_ms` with no refill for the time before it.
    #[must_use]
    pub const fn under(self, limit: &RateLimit, now_ms: u64) -> Self {
        Self {
            rec_milli: rate_tokens_clamp(self.rec_milli, limit.burst_records.saturating_mul(1_000)),
            byte_milli: rate_tokens_clamp(self.byte_milli, limit.burst_bytes.saturating_mul(1_000)),
            last_ms: rate_clock_advance(self.last_ms, now_ms),
        }
    }

    /// Judge one record of `wire_bytes` at `now_ms`: the bucket afterwards, and whether the
    /// record passes.
    ///
    /// A record larger than the byte burst can never pass and leaves the bucket as it was.
    /// Otherwise the bucket is refilled to `now_ms`; a record it cannot pay for is refused
    /// and draws nothing, and one it can pay for draws one record and its bytes. `now_ms`
    /// earlier than `last_ms` refills nothing and moves no time back, so a clock that steps
    /// back never pays the same interval twice.
    pub const fn step(
        self,
        limit: &RateLimit,
        now_ms: u64,
        wire_bytes: usize,
    ) -> (Self, Result<(), RateRefusal>) {
        let cost = rate_wire_cost(wire_bytes);
        if let Some(refusal) = rate_oversize(limit, cost) {
            return (self, Err(refusal));
        }
        let (rec_milli, byte_milli) = self.refilled(limit, now_ms);
        let refilled = Self {
            rec_milli,
            byte_milli,
            last_ms: rate_clock_advance(self.last_ms, now_ms),
        };
        if !rate_tokens_sufficient(rec_milli, 1_000) {
            let refusal = RateRefusal {
                retry_ms: rate_retry_ms(1_000u64.saturating_sub(rec_milli), limit.records_per_sec),
                why: "record rate exceeded",
            };
            return (refilled, Err(refusal));
        }
        let cost_milli = cost.saturating_mul(1_000);
        if limit.bytes_per_sec > 0 && !rate_tokens_sufficient(byte_milli, cost_milli) {
            let refusal = RateRefusal {
                retry_ms: rate_retry_ms(cost_milli.saturating_sub(byte_milli), limit.bytes_per_sec),
                why: "byte rate exceeded",
            };
            return (refilled, Err(refusal));
        }
        let drawn = Self {
            rec_milli: rec_milli.saturating_sub(1_000),
            byte_milli: if limit.bytes_per_sec > 0 {
                byte_milli.saturating_sub(cost_milli)
            } else {
                0
            },
            last_ms: refilled.last_ms,
        };
        (drawn, Ok(()))
    }
}

struct RateLimiterState {
    epoch: Instant,
    clock_ms: u64,
    limit: Option<RateLimit>,
    buckets: BTreeMap<u64, RateBucket>,
}

impl RateLimiterState {
    fn new() -> Self {
        Self {
            epoch: Instant::now(),
            clock_ms: 0,
            limit: None,
            buckets: BTreeMap::new(),
        }
    }

    fn advance_now(&mut self) -> u64 {
        let raw_ms = u64::try_from(self.epoch.elapsed().as_millis()).unwrap_or(u64::MAX);
        self.clock_ms = rate_clock_advance(self.clock_ms, raw_ms);
        self.clock_ms
    }

    fn set_limit(&mut self, limit: Option<RateLimit>) {
        let now_ms = self.advance_now();
        self.set_limit_at(now_ms, limit);
    }

    fn set_limit_at(&mut self, now_ms: u64, limit: Option<RateLimit>) {
        self.limit = limit;
        match limit {
            None => self.buckets.clear(),
            Some(lim) => {
                for bucket in self.buckets.values_mut() {
                    *bucket = bucket.under(&lim, now_ms);
                }
            }
        }
    }

    fn try_acquire(&mut self, producer_id: u64, wire_bytes: usize) -> Result<(), RateRefusal> {
        let now_ms = self.advance_now();
        self.try_acquire_at(now_ms, producer_id, wire_bytes)
    }

    /// [`RateBucket::step`] on `producer_id`'s bucket, a full one where it has none, with
    /// room made among [`MAX_RATE_BUCKETS`] by forgetting a bucket that is full again.
    fn try_acquire_at(
        &mut self,
        now_ms: u64,
        producer_id: u64,
        wire_bytes: usize,
    ) -> Result<(), RateRefusal> {
        let Some(lim) = self.limit else {
            return Ok(());
        };
        // Larger than the byte burst: refused before room or a bucket is made for it.
        if let Some(refusal) = rate_oversize(&lim, rate_wire_cost(wire_bytes)) {
            return Err(refusal);
        }
        let held = self.buckets.get(&producer_id).copied();
        if held.is_none() && self.buckets.len() >= MAX_RATE_BUCKETS {
            let full = self
                .buckets
                .iter()
                .find(|(_, bucket)| bucket.is_full_at(&lim, now_ms))
                .map(|(pid, _)| *pid);
            match full {
                Some(evict) => {
                    self.buckets.remove(&evict);
                }
                None => {
                    return Err(RateRefusal {
                        retry_ms: 50,
                        why: "active rate buckets at capacity",
                    });
                }
            }
        }
        let cur = held.unwrap_or(RateBucket::full(&lim, now_ms));
        let (next, verdict) = cur.step(&lim, now_ms, wire_bytes);
        self.buckets.insert(producer_id, next);
        verdict
    }
}

#[cfg(test)]
#[path = "rate_bucket_tests.rs"]
mod rate_bucket_tests;

contract_fn! {
    /// Verified check that unanswered acceptor wake rounds lie within the 10-attempt cap
    /// (`unanswered <= 10`), linked via `clean-kernel-defeq` to `broker_wake_attempts_within_cap_isl`.
    #[must_use]
    pub fn broker_wake_attempts_within_cap(unanswered: u32) -> bool
    clauses [ensures result == (unanswered <= 10)]
    {
        unanswered <= 10
    }
}

contract_fn! {
    /// Verified check that a selective subscriber tail's cursor has caught up to its
    /// highest matched visible head (`matched_head <= cursor`), linked via
    /// `clean-kernel-defeq` to `tail_wake_caught_up_isl`.
    #[must_use]
    pub fn tail_wake_is_caught_up(matched_head: u64, cursor: u64) -> bool
    clauses [ensures result == (matched_head <= cursor)]
    {
        matched_head <= cursor
    }
}

/// Per-subscriber wakeup state for [`Broker::set_selective_tail_wake`] (`cost study B4 step 2`).
struct TailParker {
    id: u64,
    filter: Filter,
    idle_marks: bool,
    cv: Condvar,
    needs_wake: AtomicBool,
    state: Mutex<TailParkerState>,
}

struct TailParkerState {
    safe_skip_to: u64,
    matched_head: u64,
    has_unread_match: bool,
}

enum WakePlan {
    None,
    Broadcast,
    Selective(Vec<Arc<TailParker>>),
}

/// One durable mutation queued to the single writer thread. The connection thread
/// blocks on `ack` until the writer's batch fsync makes the record durable (or fails).
struct WriteOp {
    kind: WriteKind,
    ack: AckSender,
    conn_id: Option<u64>,
}

/// Staging refuses and fences later fresh operations before their append. The
/// final ack path also latches commit, full-flush and quorum errors before the
/// single writer starts its next batch; it cannot undo an already staged suffix.
struct AckSender {
    sender: Sender<AckResult>,
    fresh: Option<Arc<AtomicBool>>,
}

impl From<Sender<AckResult>> for AckSender {
    fn from(sender: Sender<AckResult>) -> Self {
        Self {
            sender,
            fresh: None,
        }
    }
}

impl AckSender {
    fn send(&self, result: AckResult) -> Result<(), mpsc::SendError<AckResult>> {
        if result.is_err() {
            self.fence_fresh();
        }
        self.sender.send(result)
    }

    fn fence_fresh(&self) {
        if let Some(fence) = &self.fresh {
            fence.store(true, Ordering::Relaxed);
        }
    }
}

#[derive(Clone, Copy)]
struct StickyOpMeta {
    conn_id: u64,
    producer_id: u64,
    producer_seq: u64,
}

/// What the writer's queue carries: a durable mutation; a RUN of them, which one
/// connection's client sent together and the writer takes into one batch
/// ([`Pipeline::release`]); a connection-close fence removal ordered after every write
/// that connection decoded; or the STOP [`stop_writer`] queues behind every one already
/// queued, which is how the writer learns of shutdown at once ([`writer_loop`]).
enum Queued {
    Op(WriteOp),
    Run(Vec<WriteOp>),
    DropFences(u64),
    Stop,
}

/// `Ok((offset, deduped))` once durable, or `Err(refusal)` if the op or its batch
/// failed (e.g. the batch fsync errored — the record is then NOT durable).
type AckResult = Result<(u64, bool), Refusal>;

/// A refusal on its way to the wire: the `Response::Error` code (the
/// `proto::ERR_*` table: whether resending can ever land) and the message.
type Refusal = (u8, String);

/// The [`Refusal`] for `code` and `msg`.
fn refusal(code: u8, msg: impl Into<String>) -> Refusal {
    (code, msg.into())
}

enum WriteKind {
    /// Conditional append: any held key is a refusal, even for identical bytes.
    /// Its AckSender carries the mandatory connection-local fresh fence.
    FreshPublish {
        producer_id: u64,
        producer_seq: u64,
        subject: String,
        body: Vec<u8>,
    },
    Publish {
        producer_id: u64,
        producer_seq: u64,
        subject: String,
        body: Vec<u8>,
    },
    /// A [`Request::Relay`]: a publish of a record that originated elsewhere.
    Relay {
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
    /// (see [`Request::Replicate`]), with the leader's log identity when it sent one.
    /// `conn_diverged` latches on this connection if any `Replicate` conflicts with a
    /// record already held at `< next`, so later pipelined records in the same stream
    /// cannot append onto a divergent prefix before the link fences.
    Replicate {
        rec: BrokerRecord,
        leader: Option<crate::LogIdentity>,
        bt_ms: Option<u64>,
        conn_diverged: Arc<AtomicBool>,
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
        conn_id: Option<u64>,
        will: WillRecord,
    },
    /// Fire a registered will as an ordinary, FENCED publish — when its connection
    /// ends, or on broker open for every will the log still holds.
    WillFire {
        conn_id: Option<u64>,
        will: WillRecord,
    },
    /// Drop a closed connection's live will slot when its capability lapsed or its peer
    /// identity was revoked before firing.
    WillDrop {
        conn_id: u64,
    },
    /// Durably retire `target_subject` from `Last` and decrement `producer_id`'s
    /// distinct-subject count (a hidden `/a/retire` record).
    Retire {
        producer_id: u64,
        target_subject: String,
    },
    /// Conditional subject retirement (`Request::Retire`, `DESIGN-aterm-fabric` §5.2).
    RetireConditional {
        producer_id: u64,
        subject: String,
        offset: u64,
        log: crate::LogIdentity,
    },
    /// The retention tick's FORGETS (`retention.rs`, "Forgetting"): each subject, with the
    /// offset of the `Last` row the tick found, that a forgetting rule lets go, staged as a
    /// marked retire if every guard still holds against the batch
    /// ([`BrokerLog::stage_forgets`]). Answered on the local commit alone, with how many
    /// were staged in the offset's place.
    #[cfg(feature = "retention")]
    Forget {
        subjects: Vec<(String, Offset)>,
    },
    /// Flush the log in full ([`Broker::flush_durable`]): stages nothing; the writer
    /// issues the flush outside the log lock once this batch is committed (skipped when a
    /// full flush already covers the head) and answers with the durable head.
    Flush,
    /// Settle the log's device ([`Request::Settle`]): [`Flush`](Self::Flush), whose full flush
    /// the writer issues whatever already covers the head, so it is always one issued after
    /// the request was read.
    Settle,
    /// Un-fence every fenced follower link on the writer thread ([`Broker::rejoin_followers`]),
    /// resetting each un-fenced link's cursor to the leader's retention base, redialing,
    /// and catching up `[base..head)` in this batch. Answers with the number of un-fenced links.
    RejoinFollowers,
    /// Pre-writer refusal (e.g. capability expiry, subject error, or rate-limit throttle)
    /// routed in FIFO pipeline order to the writer thread when `sticky_batch_refusal` is
    /// enabled so `(conn_id, producer_id)` latches `fence_seq` in exact send order.
    PreRefused {
        producer_id: u64,
        producer_seq: u64,
        err: Refusal,
    },
}

/// The full flush a batch's `Flush` and `Settle` ops ask the writer for, beyond any its
/// commit owes (`process_batch`): ordered so that the strongest ask in a batch wins.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum FlushAsked {
    /// Neither rode the batch.
    No,
    /// A [`WriteKind::Flush`]: one, unless a full flush already covers the head (skipped,
    /// and counted so).
    Covering,
    /// A [`WriteKind::Settle`]: one whatever already covers the head, so the device is
    /// drained after the request was read.
    Always,
}

/// Upper bound on records folded into one group-commit fsync. The batch self-tunes to
/// offered concurrency (everything queued while the previous fsync ran is drained at
/// once); this only caps a single fsync's fan-in so one batch cannot grow unbounded.
const BATCH_MAX: usize = 4096;

/// How long a POLLING acceptor sleeps between non-blocking `accept()` calls, and how
/// long any acceptor backs off after an `accept()` error that is not one connection's
/// own (EMFILE/ENFILE: retried at once, they would spin).
///
/// Only the fallback polls. An acceptor normally BLOCKS in `accept()`: the poll it
/// replaced cost every new connection the rest of the sleep it landed in — 20 ms asked,
/// about 25 ms slept on macOS, so a connect + `Hello` took p50 24.4 ms back to back and
/// 12.1 ms at random arrivals against 0.03-0.07 ms blocking — and woke an idle broker
/// 42.75 times a second, forever. An aterm attach dials three or four connections in
/// series and paid it on each.
///
/// The blocking accept needs a wakeup at shutdown, and a ONE-SHOT self-connect races:
/// the acceptor could consume the wakeup while still observing a stale `running` and
/// re-block forever. [`BrokerHandle::shutdown`] therefore keeps dialing, one connection
/// per [`ACCEPT_WAKE_RETRY`], until the acceptor's exit signal fires — every `accept()`
/// return re-reads the flags, so each dial is another chance and none can be lost. The
/// dial needs a NAME for the listener, and an embedder may unlink the socket path
/// before it shuts down (astream's own `tests/suite/any_connection.rs` does): a Unix
/// listener gets a second name the broker owns, `<socket>.wake`, a hard link to the
/// same inode. A listener that cannot get one — `<socket>.wake` too long for a socket
/// address, a hard link the filesystem refuses, or a foreign file already at that name
/// (never removed) — polls at this interval, as every listener did before.
const ACCEPT_POLL: Duration = Duration::from_millis(20);

/// How long shutdown waits for a blocking acceptor's exit signal after each wakeup
/// dial before dialing again (and a TCP dial's connect timeout). The first dial
/// normally ends the wait within microseconds; another is needed only when the
/// acceptor was still busy (handing off a connection, draining a full backlog) or the
/// dial failed.
const ACCEPT_WAKE_RETRY: Duration = Duration::from_millis(100);

/// Consecutive wakeup rounds — one dial, then one [`ACCEPT_WAKE_RETRY`] wait — that the
/// acceptor never ANSWERS, after which shutdown stops waiting and abandons it (counted
/// in [`BrokerStats::acceptors_abandoned`]). A round is answered when this listener's
/// own acceptor returned from `accept()` during it; whether the dial connected does
/// not count. A connect proves only that SOME listener took it: on macOS/BSD a socket
/// bound to `127.0.0.1:P` beside this broker's `0.0.0.0:P` (a legal bind; std, OpenSSH
/// `-L` and most servers set `SO_REUSEADDR`) takes every loopback connection to P —
/// and loopback is what a wildcard bind is dialed through — while a `serve` that a
/// racing `serve` beat past its bind records the winner's inode and so dials the
/// winner. Counting connects as progress redialed such a stranger ten times a second,
/// forever, and the shutdown never returned.
///
/// So this bound covers every way the dials can miss: an embedder that removed both
/// the socket path and `<socket>.wake`, a TCP address no longer routable from this
/// host, or a name another listener answers. The parked thread keeps its listener fd
/// until a connection reaches it (none may, without a name) or the process exits.
/// Answered rounds cannot repeat without end: an `accept()` return after the flags are
/// cleared leaves the loop, so a round answered without the exit signal is one in which
/// the acceptor was already on its way out (the next round sees the signal) or read a
/// stale flag (the next dial gets it out).
const ACCEPT_WAKE_ATTEMPTS: u32 = 10;

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

/// How much a served connection's request buffer ([`RecvBuf`]) grows per read, and
/// what it returns to once empty: about one Unix socket's receive buffer (8 KiB on
/// macOS), so one read takes what a client's burst left there, while an idle
/// connection pins 8 KiB rather than a subscription's 64 KiB, at [`MAX_CONNS`] of them.
const CONN_READ_STEP: usize = 8 * 1024;

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
/// Lifted once the first frame is in (guarded: once a capability is accepted). From
/// then on an established, idle connection is read with no deadline — unless its
/// client KEEPS ALIVE ([`KEEPALIVE_DEADLINE`]); one that never does is reaped only by
/// shutdown's force-close. Tunable per broker via [`Broker::set_first_frame_timeout`].
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

/// Monotone floor for [`now_unix_ms`] (`REQUIREMENTS` R3): ensures the broker's
/// millisecond clock never steps backwards across NTP adjustments, so a capability
/// expiry or fabric deadline that has lapsed can never become un-expired.
static LAST_NOW_MS: AtomicU64 = AtomicU64::new(0);

/// Unix milliseconds, for the capability-expiry gate.
///
/// The wall clock is read HERE, at the connection boundary, and never inside
/// `astream-cap` — that crate is on the deterministic side of the effect seam,
/// where a clock read would make a replay depend on when it ran. A clock that
/// cannot be read at all yields the last monotone reading (or 0 if never read),
/// and `LAST_NOW_MS.fetch_max` guarantees strict non-decreasing monotonicity.
fn now_unix_ms() -> u64 {
    let raw = match std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH) {
        Ok(d) => d.as_millis() as u64,
        Err(_) => 0,
    };
    LAST_NOW_MS.fetch_max(raw, Ordering::AcqRel).max(raw)
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
            code: ERR_UNAUTHORIZED,
            msg: format!("{CAP_EXPIRED_PREFIX} at {until} (now {now}, unix ms)"),
        }),
    )?;
    flush_egress(stream, out)
}

/// Independent sources of an effective revocation. A file replacement changes only
/// the file source; an explicit public un-revoke clears both sources.
struct RevocationSet<T> {
    manual: HashSet<T>,
    file: HashSet<T>,
}

impl<T: Eq + std::hash::Hash> RevocationSet<T> {
    fn new() -> Self {
        Self {
            manual: HashSet::new(),
            file: HashSet::new(),
        }
    }

    fn contains(&self, value: &T) -> bool {
        self.manual.contains(value) || self.file.contains(value)
    }

    fn is_empty(&self) -> bool {
        self.manual.is_empty() && self.file.is_empty()
    }

    /// Record a manual source even when the file already revokes this value.
    /// Return whether the effective set gained it, matching the public API.
    fn insert(&mut self, value: T) -> bool {
        let added = !self.contains(&value);
        self.manual.insert(value);
        added
    }

    fn remove(&mut self, value: &T) -> bool {
        let manual = self.manual.remove(value);
        let file = self.file.remove(value);
        manual || file
    }

    fn replace_file(&mut self, file: HashSet<T>) {
        self.file = file;
    }
}

/// Return the public identity-added answer separately from any effective change:
/// the identity can already be revoked while its derived principal was cleared.
fn insert_identity_revocation(
    identities: &mut RevocationSet<[u8; 32]>,
    principals: &mut RevocationSet<String>,
    pubkey: [u8; 32],
) -> (bool, bool) {
    let added = identities.insert(pubkey);
    let principal_added = principals.insert(identity_principal(&pubkey));
    (added, added || principal_added)
}

/// State of the revocation file loaded via [`Broker::load_revocation_file`]. On
/// Apple targets it reloads when `SIGHUP` advances [`astream_sys::sighup_generation`].
struct RevocationFileState {
    path: std::path::PathBuf,
}

const REVOCATION_FILE_MAX: u64 = 1024 * 1024;

#[allow(clippy::type_complexity)]
fn parse_revocation_file(
    path: &Path,
) -> io::Result<(HashSet<[u8; 32]>, HashSet<String>, HashSet<u64>, usize)> {
    let mut bytes = Vec::new();
    std::fs::File::open(path)
        .and_then(|f| f.take(REVOCATION_FILE_MAX + 1).read_to_end(&mut bytes))?;
    if bytes.len() as u64 > REVOCATION_FILE_MAX {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "revocation file {}: larger than {REVOCATION_FILE_MAX} bytes",
                path.display()
            ),
        ));
    }
    let text = match core::str::from_utf8(&bytes) {
        Ok(t) => t,
        Err(e) => return Err(io::Error::new(io::ErrorKind::InvalidData, e)),
    };
    let mut identities = HashSet::new();
    let mut principals = HashSet::new();
    let mut serials = HashSet::new();
    let mut count = 0usize;
    for (idx, raw_line) in text.lines().enumerate() {
        let line = raw_line.split('#').next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        if let Some(serial_str) = line.strip_prefix("serial:") {
            let serial = match serial_str.parse::<u64>() {
                Ok(n) if n > 0 => n,
                _ => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!(
                            "revocation file {}:{} invalid serial entry {line:?}: expected serial:<u64> with serial > 0",
                            path.display(),
                            idx.saturating_add(1)
                        ),
                    ));
                }
            };
            serials.insert(serial);
            count = count.saturating_add(1);
            continue;
        }
        let mut is_hex64 = line.len() == 64;
        if is_hex64 {
            for &b in line.as_bytes() {
                if !b.is_ascii_hexdigit() {
                    is_hex64 = false;
                    break;
                }
            }
        }
        if is_hex64 {
            let mut pk = [0u8; 32];
            for (dst, [b0, b1]) in pk.iter_mut().zip(line.as_bytes().as_chunks::<2>().0) {
                *dst = pack_hex_byte(*b0, *b1);
            }
            identities.insert(pk);
            principals.insert(identity_principal(&pk));
            count = count.saturating_add(1);
            continue;
        }
        let mut is_principal = true;
        for &b in line.as_bytes() {
            if !(b.is_ascii_alphanumeric() || b == b'-') {
                is_principal = false;
                break;
            }
        }
        if is_principal {
            principals.insert(line.to_ascii_lowercase());
            count = count.saturating_add(1);
        } else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "revocation file {}:{} invalid entry {line:?}: expected 64-hex Ed25519 pubkey, principal, or serial:<u64>",
                    path.display(),
                    idx.saturating_add(1)
                ),
            ));
        }
    }
    Ok((identities, principals, serials, count))
}

fn apply_revocation_file(shared: &Shared, path: &Path) -> io::Result<usize> {
    #[cfg(target_vendor = "apple")]
    astream_sys::install_sighup_handler()?;
    let seen = astream_sys::sighup_generation();
    let (new_identities, new_principals, new_serials, count) = parse_revocation_file(path)?;
    {
        let mut file_state = shared
            .revocation_file
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        shared
            .revoked_identities
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .replace_file(new_identities);
        shared
            .revoked_principals
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .replace_file(new_principals);
        shared
            .revoked_cert_serials
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .replace_file(new_serials);
        *file_state = Some(RevocationFileState {
            path: path.to_path_buf(),
        });
    }
    shared.sighup_seen.store(seen, Ordering::Release);
    shared.has_revocation_file.store(true, Ordering::Release);
    shared.revocation_epoch.fetch_add(1, Ordering::AcqRel);
    notify_all_tails(shared);
    #[cfg(feature = "stream")]
    end_revoked_streams(shared);
    Ok(count)
}

/// End every adopted stream whose key or `n-` principal is now revoked. An identity TCP
/// connection learns of its revocation at its next request or delivery; an adopted stream is one
/// channel of its owner's live connection, and may sit idle for as long as that connection lasts,
/// so it is shut here and now. Runs after the revocation is in force, and a stream checks for it
/// after it registers ([`serve_conn`]), so one registering meanwhile is ended by one or the other.
#[cfg(feature = "stream")]
fn end_revoked_streams(shared: &Shared) {
    let identities = shared
        .revoked_identities
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let principals = shared
        .revoked_principals
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let conns = shared
        .conns
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    for sock in conns.values() {
        if let Sock::Stream { peer, .. } = sock {
            if identities.contains(peer) || principals.contains(&identity_principal(peer)) {
                sock.shutdown_both();
            }
        }
    }
}

fn maybe_reload_revocation_file(shared: &Shared) {
    if !shared.has_revocation_file.load(Ordering::Acquire) {
        return;
    }
    let cur = astream_sys::sighup_generation();
    if cur == shared.sighup_seen.load(Ordering::Acquire) {
        return;
    }
    let path = {
        let guard = shared
            .revocation_file
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        guard.as_ref().map(|st| st.path.clone())
    };
    let Some(path) = path else {
        shared.sighup_seen.store(cur, Ordering::Release);
        return;
    };
    if let Err(e) = apply_revocation_file(shared, &path) {
        shared.sighup_seen.store(cur, Ordering::Release);
        let _ = writeln!(
            io::stderr(),
            "astream-broker: warn: SIGHUP revocation reload of {} failed ({e}); keeping existing revocations",
            path.display()
        );
    }
}

/// Authenticated transport-layer peer identity (Rung 8 raw Ed25519 key, `serve_stream`
/// key, or Rung 9 CA-signed `ACRT` certificate), carried across the life of a served connection.
#[cfg_attr(
    not(any(feature = "identity", feature = "stream", feature = "relay")),
    allow(dead_code)
)]
#[derive(Debug, Clone, Default)]
struct PeerAuth {
    pubkey: Option<[u8; 32]>,
    cert_serial: Option<u64>,
    cert_valid_before_ms: Option<u64>,
    cert_principal: Option<String>,
    cert_principal_lower: Option<String>,
}

impl PeerAuth {
    const fn none() -> Self {
        Self {
            pubkey: None,
            cert_serial: None,
            cert_valid_before_ms: None,
            cert_principal: None,
            cert_principal_lower: None,
        }
    }

    #[cfg(any(feature = "identity", feature = "stream", feature = "relay"))]
    const fn from_identity(pubkey: [u8; 32]) -> Self {
        Self {
            pubkey: Some(pubkey),
            cert_serial: None,
            cert_valid_before_ms: None,
            cert_principal: None,
            cert_principal_lower: None,
        }
    }

    #[cfg(feature = "identity")]
    fn from_cert(v: astream_aead::VerifiedPeerCert) -> Self {
        let lower = v.principal.to_ascii_lowercase();
        Self {
            pubkey: Some(v.subject_pub),
            cert_serial: Some(v.serial),
            cert_valid_before_ms: Some(v.valid_before_ms),
            cert_principal: Some(v.principal),
            cert_principal_lower: Some(lower),
        }
    }
}

/// Whether `peer` has been revoked (by Ed25519 identity key, derived `n-` principal, certificate
/// serial, or certificate principal) without triggering file I/O — acquiring and dropping each
/// leaf lock one at a time so it is safe to call while holding `shared.log`.
fn peer_revocation_reason_raw(shared: &Shared, peer: &PeerAuth) -> Option<&'static str> {
    if let Some(ref pk) = peer.pubkey {
        if shared
            .revoked_identities
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .contains(pk)
        {
            return Some("unauthorized: peer identity key has been revoked");
        }
        let principals = shared
            .revoked_principals
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if !principals.is_empty() && principals.contains(&identity_principal(pk)) {
            return Some("unauthorized: peer identity key has been revoked");
        }
    }
    if let Some(ref serial) = peer.cert_serial {
        if shared
            .revoked_cert_serials
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .contains(serial)
        {
            return Some("unauthorized: peer certificate serial has been revoked");
        }
    }
    if let Some(ref lower) = peer.cert_principal_lower {
        if shared
            .revoked_principals
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .contains(lower)
        {
            return Some("unauthorized: peer certificate principal has been revoked");
        }
    }
    None
}

/// Reload the revocation file if `SIGHUP` fired, then check [`peer_revocation_reason_raw`].
fn peer_revocation_reason(shared: &Shared, peer: &PeerAuth) -> Option<&'static str> {
    maybe_reload_revocation_file(shared);
    peer_revocation_reason_raw(shared, peer)
}

/// Whether the capability principal bound to `producer_id` on a guarded broker has been
/// revoked (suppressing a disconnecting connection's pending last will).
fn is_will_principal_revoked(shared: &Shared, producer_id: u64) -> bool {
    maybe_reload_revocation_file(shared);
    if shared.cap_secret.is_none() {
        return false;
    }
    let principal = shared
        .bindings
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .get(&producer_id)
        .map(|(p, _)| p.to_ascii_lowercase());
    let Some(p) = principal else {
        return false;
    };
    shared
        .revoked_principals
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .contains(&p)
}

#[derive(Debug, PartialEq, Eq)]
enum StreamFailure {
    Revoked(&'static str),
    Expired { until: u64, now: u64 },
}

struct StreamCapCheck {
    #[cfg(feature = "cap")]
    keyring: Vec<astream_cap::Capability>,
    #[cfg(feature = "cap")]
    req: Option<Request>,
    // None forces an initial check even if revocation completed after the request
    // gate but before construction. No epoch value is reserved as a sentinel.
    seen_epoch: Option<u64>,
}

impl StreamCapCheck {
    #[cfg(feature = "cap")]
    fn new(
        shared: &Shared,
        keyring: &mut Vec<astream_cap::Capability>,
        req: Request,
    ) -> StreamCapCheck {
        if shared.cap_secret.is_some() {
            StreamCapCheck {
                keyring: std::mem::take(keyring),
                req: Some(req),
                seen_epoch: None,
            }
        } else {
            StreamCapCheck {
                keyring: Vec::new(),
                req: None,
                seen_epoch: None,
            }
        }
    }

    #[cfg(not(feature = "cap"))]
    fn new(_shared: &Shared) -> StreamCapCheck {
        StreamCapCheck { seen_epoch: None }
    }

    // The caller prunes revoked grants before a new epoch's validation. Captured
    // `now` makes the authority/deadline state transition independently testable.
    fn validate(
        &mut self,
        epoch: u64,
        now: u64,
        until: &mut u64,
        #[cfg(feature = "cap")] secret: Option<&[u8]>,
    ) -> Option<StreamFailure> {
        #[cfg(feature = "cap")]
        if let (Some(secret), Some(req)) = (secret, self.req.as_ref()) {
            if self.seen_epoch != Some(epoch) {
                match cap_authorized_until(secret, &self.keyring, req, now) {
                    Some(current_until) => *until = (*until).min(current_until),
                    None => {
                        // Time zero is diagnostic only. An expired grant must never
                        // authorize a delivery; preserve the typed expiry refusal.
                        if let Some(expired_until) =
                            cap_authorized_until(secret, &self.keyring, req, 0)
                        {
                            *until = (*until).min(expired_until);
                            return Some(StreamFailure::Expired { until: *until, now });
                        }
                        return Some(StreamFailure::Revoked(
                            "unauthorized: capability principal has been revoked",
                        ));
                    }
                }
            }
        }
        // Refresh accepted checks even without a capability guard, so an unrelated
        // epoch change cannot keep the tail's park predicate permanently awake.
        self.seen_epoch = Some(epoch);
        if *until != u64::MAX && now >= *until {
            return Some(StreamFailure::Expired { until: *until, now });
        }
        None
    }
}

fn stream_failure(
    shared: &Shared,
    peer: &PeerAuth,
    cap_check: &mut StreamCapCheck,
    until: &mut u64,
) -> Option<StreamFailure> {
    maybe_reload_revocation_file(shared);
    if let Some(reason) = peer_revocation_reason_raw(shared, peer) {
        return Some(StreamFailure::Revoked(reason));
    }
    // Read before pruning. A concurrent later epoch remains different from this
    // accepted snapshot and is rechecked, rather than being silently consumed.
    let epoch = shared.revocation_epoch.load(Ordering::Acquire);
    let needs_time = *until != u64::MAX;
    #[cfg(feature = "cap")]
    let needs_time = {
        let guarded = shared.cap_secret.is_some() && cap_check.req.is_some();
        let validate = guarded && cap_check.seen_epoch != Some(epoch);
        if validate {
            prune_revoked_capabilities(shared, &mut cap_check.keyring);
        }
        needs_time || validate
    };
    // Preserve the unguarded infinite-deadline fast path's lack of wall-clock reads.
    let now = if needs_time { now_unix_ms() } else { 0 };
    cap_check.validate(
        epoch,
        now,
        until,
        #[cfg(feature = "cap")]
        shared.cap_secret.as_deref(),
    )
}

fn end_stream_failure<S: Write>(
    stream: &mut S,
    out: &mut Vec<u8>,
    failure: StreamFailure,
) -> io::Result<()> {
    match failure {
        StreamFailure::Revoked(msg) => end_revoked(stream, out, msg),
        StreamFailure::Expired { until, now } => end_lapsed(stream, out, until, now),
    }
}

/// End a streaming verb whose peer identity key or capability principal was revoked:
/// flush what `out` already gathered, then emit the revocation error frame.
fn end_revoked<S: Write>(stream: &mut S, out: &mut Vec<u8>, msg: &str) -> io::Result<()> {
    append_frame(
        out,
        &encode_response(&Response::Error {
            code: ERR_UNAUTHORIZED,
            msg: msg.to_string(),
        }),
    )?;
    flush_egress(stream, out)
}

/// End a streaming verb when a retained cold record could not be read back from the log
/// file: flush any earlier deliveries in `out`, then emit an explicit `ERR_REFUSED`
/// naming the unreadable offset instead of silently truncating or spinning.
fn end_unreadable_cold_record<S: Write>(
    stream: &mut S,
    out: &mut Vec<u8>,
    bad_off: u64,
) -> io::Result<()> {
    append_frame(
        out,
        &encode_response(&Response::Error {
            code: ERR_REFUSED,
            msg: format!("cold record at offset {bad_off} could not be read back from the log"),
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
    let now = match std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH) {
        Ok(d) => d.as_nanos() as u64,
        Err(_) => 0,
    };
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

/// The connection the broker serves over: a local Unix socket (same machine),
/// plaintext TCP (multi-machine on a TRUSTED network), or, with the `aead` feature, an
/// XChaCha20-Poly1305 `SealedStream` over TCP (confidential and authenticated:
/// [`Broker::serve_tcp_sealed`]). The same Frame protocol rides all three; capability
/// enforcement (the `cap` feature, [`Broker::open_guarded`]) is orthogonal to the
/// transport.
///
/// A closed set named by one type, not a trait the connection code is generic over:
/// every call the serve path makes on a connection resolves to one transport's own
/// method, so the verified lane can follow it (a read through a type parameter is a
/// callee it cannot see, and it fails the whole path closed). Timeouts, non-blocking
/// mode and shutdown act on the socket, for the sealed transport the TCP socket
/// beneath the records; its `try_clone` shares the AEAD record counters, so the read
/// half and the ack-writer half stay one ordered record sequence.
enum Conn {
    #[cfg(unix)]
    Unix(UnixStream),
    Tcp(TcpStream),
    #[cfg(feature = "aead")]
    Sealed(astream_aead::SealedStream<TcpStream>),
    #[cfg(feature = "handshake")]
    Roam(astream_aead::RoamStream),
    /// A stream its owner authenticated ([`Broker::serve_stream`]), with the key it proved.
    #[cfg(feature = "stream")]
    Stream(crate::stream_link::LinkEnd, [u8; 32]),
}

impl Conn {
    fn set_read_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        match self {
            #[cfg(unix)]
            Conn::Unix(s) => s.set_read_timeout(d),
            Conn::Tcp(s) => s.set_read_timeout(d),
            #[cfg(feature = "aead")]
            Conn::Sealed(s) => s.get_ref().set_read_timeout(d),
            #[cfg(feature = "handshake")]
            Conn::Roam(s) => s.set_read_timeout(d),
            #[cfg(feature = "stream")]
            Conn::Stream(s, _) => s.set_read_timeout(d),
        }
    }

    fn set_write_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        match self {
            #[cfg(unix)]
            Conn::Unix(s) => s.set_write_timeout(d),
            Conn::Tcp(s) => s.set_write_timeout(d),
            #[cfg(feature = "aead")]
            Conn::Sealed(s) => s.get_ref().set_write_timeout(d),
            #[cfg(feature = "handshake")]
            Conn::Roam(s) => s.set_write_timeout(d),
            #[cfg(feature = "stream")]
            Conn::Stream(s, _) => s.set_write_timeout(d),
        }
    }

    /// Switch the socket's non-blocking mode (`O_NONBLOCK`, a property of the open
    /// socket that every handle to it shares): only for the liveness probe's one
    /// read, by the one thread using the socket (see `peer_gone`).
    fn set_nonblocking(&self, on: bool) -> io::Result<()> {
        match self {
            #[cfg(unix)]
            Conn::Unix(s) => s.set_nonblocking(on),
            Conn::Tcp(s) => s.set_nonblocking(on),
            #[cfg(feature = "aead")]
            Conn::Sealed(s) => s.get_ref().set_nonblocking(on),
            #[cfg(feature = "handshake")]
            Conn::Roam(s) => s.set_nonblocking(on),
            #[cfg(feature = "stream")]
            Conn::Stream(s, _) => s.set_nonblocking(on),
        }
    }

    /// A second handle to the same connection, so the read half (draining requests)
    /// and the ack-writer half (streaming acks back) run concurrently:
    /// single-connection pipelining. Read and write are independent directions on the
    /// same fd. Kept out of every child, as the first handle is
    /// (`astream_sys::close_on_fork`, a flag of the descriptor, so each duplicate
    /// carries its own).
    fn try_clone(&self) -> io::Result<Conn> {
        Ok(match self {
            #[cfg(unix)]
            Conn::Unix(s) => {
                let clone = s.try_clone()?;
                kept_from_children(&clone)?;
                Conn::Unix(clone)
            }
            Conn::Tcp(s) => {
                let clone = s.try_clone()?;
                kept_from_children(&clone)?;
                Conn::Tcp(clone)
            }
            #[cfg(feature = "aead")]
            Conn::Sealed(s) => {
                let clone = s.try_clone()?;
                kept_from_children(clone.get_ref())?;
                Conn::Sealed(clone)
            }
            #[cfg(feature = "handshake")]
            Conn::Roam(s) => {
                let clone = astream_aead::TryCloneable::try_clone(s)?;
                Conn::Roam(clone)
            }
            #[cfg(feature = "stream")]
            Conn::Stream(s, peer) => Conn::Stream(s.clone(), *peer),
        })
    }

    /// The handle [`Shared::conns`] keeps to force-close this connection's socket,
    /// kept out of every child as [`Conn::try_clone`]'s is.
    fn sock(&self) -> io::Result<Sock> {
        Ok(match self {
            #[cfg(unix)]
            Conn::Unix(s) => {
                let clone = s.try_clone()?;
                kept_from_children(&clone)?;
                Sock::Unix(clone)
            }
            Conn::Tcp(s) => {
                let clone = s.try_clone()?;
                kept_from_children(&clone)?;
                Sock::Tcp(clone)
            }
            #[cfg(feature = "aead")]
            Conn::Sealed(s) => {
                let clone = s.get_ref().try_clone()?;
                kept_from_children(&clone)?;
                Sock::Tcp(clone)
            }
            #[cfg(feature = "handshake")]
            Conn::Roam(s) => Sock::Roam(s.closer()),
            #[cfg(feature = "stream")]
            Conn::Stream(s, peer) => Sock::Stream {
                link: s.clone(),
                peer: *peer,
            },
        })
    }

    /// Shut only the write direction: the peer reads EOF, and may still write.
    fn shutdown_write(&self) {
        match self {
            #[cfg(unix)]
            Conn::Unix(s) => {
                let _ = s.shutdown(Shutdown::Write);
            }
            Conn::Tcp(s) => {
                let _ = s.shutdown(Shutdown::Write);
            }
            #[cfg(feature = "aead")]
            Conn::Sealed(s) => {
                let _ = s.get_ref().shutdown(Shutdown::Write);
            }
            #[cfg(feature = "handshake")]
            Conn::Roam(s) => s.shutdown_write(),
            #[cfg(feature = "stream")]
            Conn::Stream(s, _) => {
                let _ = s.shutdown(Shutdown::Write);
            }
        }
    }
}

impl Read for Conn {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        match self {
            #[cfg(unix)]
            Conn::Unix(s) => s.read(buf),
            Conn::Tcp(s) => s.read(buf),
            #[cfg(feature = "aead")]
            Conn::Sealed(s) => s.read(buf),
            #[cfg(feature = "handshake")]
            Conn::Roam(s) => s.read(buf),
            #[cfg(feature = "stream")]
            Conn::Stream(s, _) => s.read(buf),
        }
    }
}

impl Write for Conn {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        match self {
            #[cfg(unix)]
            Conn::Unix(s) => s.write(buf),
            Conn::Tcp(s) => s.write(buf),
            #[cfg(feature = "aead")]
            Conn::Sealed(s) => s.write(buf),
            #[cfg(feature = "handshake")]
            Conn::Roam(s) => s.write(buf),
            #[cfg(feature = "stream")]
            Conn::Stream(s, _) => s.write(buf),
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        match self {
            #[cfg(unix)]
            Conn::Unix(s) => s.flush(),
            Conn::Tcp(s) => s.flush(),
            #[cfg(feature = "aead")]
            Conn::Sealed(s) => s.flush(),
            #[cfg(feature = "handshake")]
            Conn::Roam(s) => s.flush(),
            #[cfg(feature = "stream")]
            Conn::Stream(s, _) => s.flush(),
        }
    }
}

/// Where the broker listens, so shutdown can wake a blocking acceptor (dial the
/// listener) and clean up the endpoint (unlink a Unix socket), and
/// [`BrokerHandle::tcp_addr`] can report a bound TCP address.
/// The Unix-socket endpoint is cfg(unix): std has no Unix-domain sockets on
/// Windows, where TCP ([`Broker::serve_tcp`]) is the only transport.
enum Endpoint {
    #[cfg(unix)]
    Unix {
        /// The socket path `serve` bound.
        path: PathBuf,
        /// The listener's inode, read right after the bind — `None` if that stat
        /// failed (the listener then polls, and shutdown unlinks `path` unchecked, as
        /// it always did). Shutdown dials and unlinks only names that still carry it:
        /// an embedder may have unlinked `path`, and another broker may since have
        /// bound its own socket there.
        node: Option<SocketNode>,
        /// `<path>.wake`, the hard link to the listener this broker created and owns
        /// (`None`: the listener polls).
        wake: Option<PathBuf>,
    },
    Tcp {
        /// The connectable form of the bound address ([`connectable_addr`]): what
        /// [`BrokerHandle::tcp_addr`] reports and what shutdown dials.
        dial: SocketAddr,
        /// `dial`, rendered once for [`BrokerHandle::tcp_addr`].
        shown: String,
    },
}

/// A filesystem object's identity, device and inode, and its birth where the
/// filesystem records one: what makes "this name still points at OUR listener"
/// checkable after an embedder or another broker may have replaced the name. The birth
/// tells apart a file given an inode number another one just freed (ext4 reissues one
/// at once).
#[cfg(unix)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct SocketNode {
    dev: u64,
    ino: u64,
    born: Option<std::time::SystemTime>,
}

#[cfg(unix)]
impl SocketNode {
    /// The identity of what one metadata read describes.
    fn of(m: &std::fs::Metadata) -> Self {
        use std::os::unix::fs::MetadataExt;
        Self {
            dev: m.dev(),
            ino: m.ino(),
            born: m.created().ok(),
        }
    }
}

/// The identity of whatever `path` names now, WITHOUT following a symlink (a symlink
/// planted at the name is not the listener).
#[cfg(unix)]
fn node_at(path: &Path) -> Option<SocketNode> {
    node_read(path).ok()
}

/// [`node_at`], with the read's error.
#[cfg(unix)]
fn node_read(path: &Path) -> io::Result<SocketNode> {
    std::fs::symlink_metadata(path).map(|m| SocketNode::of(&m))
}

/// Make `path` free for a broker's socket, or say why it is not: a file that is not a
/// socket is `AlreadyExists` and never removed, a socket a broker answers on or one
/// nothing shows stale is `AddrInUse`, and a stale socket (no socket is bound to it any
/// more: a crashed broker's) is removed, only while `path` still names it.
///
/// A stream connect is no liveness probe: a full listener backlog refuses it on
/// macOS and can wait indefinitely on Linux. A nonblocking datagram connect is
/// refused only when no socket at all is bound to the file; a bound stream socket
/// fails it by type (`EPROTOTYPE`), and a bound datagram takes it. Any other failure
/// (`EAGAIN`, `EINPROGRESS`, `EALREADY`, `EINTR`, `EACCES`, `EMFILE`) proves nothing
/// stale, so the socket stays. This probe never queues a stream connection.
#[cfg(unix)]
fn probe_socket_path(path: &Path) -> io::Result<()> {
    let probe = match std::os::unix::net::UnixDatagram::unbound() {
        Ok(probe) => probe,
        Err(e) => return Err(e),
    };
    if let Err(e) = kept_from_children(&probe) {
        return Err(e);
    }
    if let Err(e) = probe.set_nonblocking(true) {
        return Err(e);
    }
    probe.connect(path)
}

#[cfg(unix)]
fn socket_metadata_if_present(path: &Path) -> io::Result<Option<std::fs::Metadata>> {
    use std::os::unix::fs::FileTypeExt;
    let Ok(meta) = std::fs::symlink_metadata(path) else {
        return Ok(None);
    };
    if !meta.file_type().is_socket() {
        return Err(io::Error::new(
            io::ErrorKind::AlreadyExists,
            format!(
                "{}: exists and is not a socket; refusing to replace it",
                path.display()
            ),
        ));
    }
    Ok(Some(meta))
}

#[cfg(unix)]
fn finish_claim_socket_path(
    path: &Path,
    meta: &std::fs::Metadata,
    outcome: io::Result<()>,
) -> io::Result<()> {
    match outcome {
        Err(e) if e.kind() == io::ErrorKind::ConnectionRefused => {}
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
        outcome => {
            let why = match outcome {
                Ok(()) => "a live datagram socket accepted the probe".to_string(),
                Err(error) => error.to_string(),
            };
            return Err(io::Error::new(
                io::ErrorKind::AddrInUse,
                format!(
                    "{}: a socket nothing shows stale (the nonblocking probe: {why}); refusing \
                     to replace it",
                    path.display()
                ),
            ));
        }
    }
    #[cfg(test)]
    serve_hook(ServeAt::Judged);
    unlink_if_node(path, SocketNode::of(meta));
    Ok(())
}

#[cfg(unix)]
fn claim_socket_path(path: &Path) -> io::Result<()> {
    let meta = match socket_metadata_if_present(path) {
        Ok(Some(meta)) => meta,
        Ok(None) => return Ok(()),
        Err(e) => return Err(e),
    };
    finish_claim_socket_path(path, &meta, probe_socket_path(path))
}

#[cfg(all(test, unix))]
fn claim_socket_path_with(
    path: &Path,
    probe: impl FnOnce(&Path) -> io::Result<()>,
) -> io::Result<()> {
    let Some(meta) = socket_metadata_if_present(path)? else {
        return Ok(());
    };
    finish_claim_socket_path(path, &meta, probe(path))
}

/// The `n` the next private socket name takes ([`private_socket_name`]).
#[cfg(unix)]
static PRIVATE_SEQ: AtomicU64 = AtomicU64::new(0);

/// How many private names [`Broker::bind_unix`] tries before it binds the path itself.
#[cfg(unix)]
const PRIVATE_TRIES: usize = 4;

/// `<path>.<pid>.<n>`, the sibling name [`Broker::bind_unix`] binds under before `path`
/// names the listener; `None` when it is too long for a socket address (`SUN_LEN`).
#[cfg(unix)]
fn private_socket_name(path: &Path) -> Option<PathBuf> {
    let mut name = path.as_os_str().to_os_string();
    let n = PRIVATE_SEQ.fetch_add(1, Ordering::Relaxed);
    name.push(format!(".{}.{n}", std::process::id()));
    let name = PathBuf::from(name);
    std::os::unix::net::SocketAddr::from_pathname(&name)
        .is_ok()
        .then_some(name)
}

/// Whether `name` is a private socket name of `file`'s: `<file>.<digits>.<digits>`.
#[cfg(unix)]
fn is_private_name(file: &std::ffi::OsStr, name: &std::ffi::OsStr) -> bool {
    let Some(rest) = name
        .as_encoded_bytes()
        .strip_prefix(file.as_encoded_bytes())
        .and_then(|rest| rest.strip_prefix(b"."))
    else {
        return false;
    };
    let mut numbers = rest.split(|byte| *byte == b'.');
    let mut number = || {
        numbers
            .next()
            .is_some_and(|n| !n.is_empty() && n.iter().all(u8::is_ascii_digit))
    };
    number() && number() && numbers.next().is_none()
}

/// Remove the stale private names a broker killed inside [`Broker::bind_unix`] left
/// beside `path` (each through [`claim_socket_path`], so a live one, or a file that is
/// not a socket, stays): left, one would hold its name against a later process that
/// gets the same pid.
#[cfg(unix)]
fn clear_private_names(path: &Path) {
    let (Some(dir), Some(file)) = (path.parent(), path.file_name()) else {
        return;
    };
    let dir = if dir.as_os_str().is_empty() {
        Path::new(".")
    } else {
        dir
    };
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        if is_private_name(file, &entry.file_name()) {
            let _ = claim_socket_path(&entry.path());
        }
    }
}

/// A listener bound under a private name of `path`'s, and that name: the next name
/// when one is taken (a process with this pid in another pid namespace, sharing the
/// directory), up to [`PRIVATE_TRIES`]. `None` when no name fits a socket address or
/// one cannot be bound for another reason.
#[cfg(unix)]
fn bind_private(path: &Path) -> Option<(UnixListener, PathBuf)> {
    for _ in 0..PRIVATE_TRIES {
        let private = private_socket_name(path)?;
        match UnixListener::bind(&private) {
            Ok(listener) => return Some((listener, private)),
            Err(e) if e.kind() == io::ErrorKind::AddrInUse => {}
            Err(_) => return None,
        }
    }
    None
}

/// How many times [`link_into_place`] links before it gives up on a path that each
/// claim found free.
#[cfg(unix)]
const LINK_TRIES: usize = 3;

/// Give the listener bound at `private` the name `path` with `link(2)`, which never
/// replaces a name. A name already there goes through [`claim_socket_path`]: a live
/// socket or a file that is not a socket is refused, as when `serve` finds it first,
/// and a stale socket is removed and the link tried again. `None` when the filesystem
/// refuses the link for another reason: the caller binds `path` itself.
#[cfg(unix)]
fn link_into_place(private: &Path, path: &Path) -> Option<io::Result<()>> {
    for _ in 0..LINK_TRIES {
        match std::fs::hard_link(private, path) {
            Ok(()) => return Some(Ok(())),
            Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {}
            Err(_) => return None,
        }
        if let Err(e) = claim_socket_path(path) {
            return Some(Err(e));
        }
    }
    Some(Err(io::Error::new(
        io::ErrorKind::AddrInUse,
        format!(
            "{}: a stale socket was put at this path each time the broker linked its own",
            path.display()
        ),
    )))
}

/// Unlink `path` only while it still names `node`. Narrow, not atomic: a replacement
/// between the check and the unlink loses — the same window the unconditional unlink
/// it replaced held open.
#[cfg(unix)]
fn unlink_if_node(path: &Path, node: SocketNode) {
    if node_at(path) == Some(node) {
        let _ = crate::store::remove_file_path(path);
    }
}

/// Give the listener `from` names (identity `node`) a second name this broker owns,
/// `<socket>.wake`, so shutdown can dial the blocking acceptor out of `accept()` even
/// after the embedder unlinked `socket`. `from` is the listener's private name while it
/// has one, which no other process can replace, else `socket` itself. A hard link: the
/// same inode, so the same permissions — it lets in nobody the socket path does not (a
/// peer could reach it only through the same directory), except after an embedder
/// unlinks the path to hide a broker it means to keep running, which nothing in astream
/// or aterm does.
///
/// `None` — and the listener polls — when that name cannot be had safely:
/// - `<socket>.wake` is too long for a socket address (`SUN_LEN`), so it could never
///   be dialed;
/// - something that is not a socket is there (a user's file: never removed, exactly
///   as `serve` treats its own path);
/// - a LIVE socket, or one nothing shows stale, is there ([`claim_socket_path`]):
///   another broker's wake name (its embedder unlinked the socket path and this broker
///   bound a new one), which that broker's shutdown needs;
/// - the filesystem refuses the link, or the link does not land on `node` (`from`
///   changed between the bind and the link).
///
/// A STALE socket there (a broker that crashed or was killed) is removed, as `serve`
/// removes a stale socket at its own path.
#[cfg(unix)]
fn link_wake_name(from: &Path, socket: &Path, node: SocketNode) -> Option<PathBuf> {
    let mut wake = socket.to_path_buf();
    wake.as_mut_os_string().push(".wake");
    if std::os::unix::net::SocketAddr::from_pathname(&wake).is_err() {
        return None;
    }
    claim_socket_path(&wake).ok()?;
    if std::fs::hard_link(from, &wake).is_err() {
        return None;
    }
    if node_at(&wake) != Some(node) {
        // The link succeeded, so the name is ours — but not our listener's.
        let _ = crate::store::remove_file_path(&wake);
        return None;
    }
    Some(wake)
}

/// Map a bound socket address to one that can be *connected to*, for
/// [`BrokerHandle::tcp_addr`] and for shutdown's wakeup dial: an unspecified host
/// (`0.0.0.0` / `::`) becomes loopback, keeping the port, so a port-0 bind reports an
/// address a local client can dial. A concrete host is returned unchanged.
/// (`SocketAddr`'s `Display` brackets IPv6 for us.)
fn connectable_addr(addr: SocketAddr) -> SocketAddr {
    if addr.ip().is_unspecified() {
        let loopback = match addr.ip() {
            IpAddr::V4(_) => IpAddr::V4(Ipv4Addr::LOCALHOST),
            IpAddr::V6(_) => IpAddr::V6(Ipv6Addr::LOCALHOST),
        };
        SocketAddr::new(loopback, addr.port())
    } else {
        addr
    }
}

/// How [`BrokerHandle::shutdown`] gets a listener's acceptor out of `accept()`.
enum AcceptWake {
    /// The acceptor polls (the fallback, [`ACCEPT_POLL`]): it observes the cleared
    /// flags on its own within one poll, so shutdown just joins it. Unix only: a TCP
    /// address needs no name to stay dialable.
    #[cfg_attr(not(unix), allow(dead_code))]
    Polls,
    /// The acceptor blocks in `accept()`: shutdown dials the listener until `exited`
    /// disconnects — the acceptor thread holds the sender and drops it as it returns,
    /// panic included, so a disconnect means "left", never "still parked". Behind a
    /// `Mutex` only because a `Receiver` is not `Sync` and `BrokerHandle` must stay
    /// so (aterm shares one across threads); shutdown, which runs once, is its only
    /// locker, and takes no other lock while it holds it.
    ///
    /// `turns` counts this listener's `accept()` returns (the broker-wide
    /// [`BrokerStats::acceptor_wakeups`] cannot tell its listeners apart): it is how
    /// shutdown tells a dial THIS acceptor took from one some other listener answered
    /// ([`ACCEPT_WAKE_ATTEMPTS`]).
    Blocks {
        exited: Mutex<Receiver<()>>,
        turns: Arc<AtomicU64>,
    },
}

/// A wakeup dial's client socket, held until shutdown's wait for the exit signal is
/// over: the acceptor takes it off the backlog whatever its state, but holding it
/// keeps "the peer already closed" out of the question.
enum WakeDial {
    #[cfg(unix)]
    Unix(#[allow(dead_code)] UnixStream),
    Tcp(#[allow(dead_code)] TcpStream),
}

/// One listener's accept loop, Unix and TCP alike: take connections and hand each off
/// until shutdown clears `running` (the broker's) or `listening` (this listener's).
/// Every `accept()` return, connection or error, re-reads both flags, so a stopping
/// broker closes what the backlog hands it instead of spawning a handler shutdown
/// could miss — and each of shutdown's wakeup dials is a fresh chance to see the
/// flags, which is why a stale read cannot strand a blocking acceptor. The flags are
/// read only after an `accept()` returns, never before the first: an acceptor that
/// starts after shutdown began still parks in `accept()`, where shutdown's dials find
/// it (or, when none can, abandon it), instead of leaving by itself on a timing that
/// shutdown cannot see.
///
/// The loop itself is the listener's own (`Broker::serve`, `Broker::serve_tcp_with`):
/// it calls `accept()`, asks [`turn`](Self::turn) what that return means, hands a
/// connection off, and asks [`stopping`](Self::stopping) after the hand-off. A loop
/// written out at each listener, not one generic over closures for the accept and the
/// hand-off, so the verified lane resolves every call in it.
///
/// `polls`: the listener is non-blocking (no wake name, [`ACCEPT_POLL`]). Counted on
/// [`Shared`] for [`BrokerStats`]: every resumption of the thread from a blocking wait
/// (an `accept()` that returned in blocking mode, a sleep that ended), every sleep, and
/// every connection handed off. Counted on `turns`, this listener's own: every
/// `accept()` return, which is what shutdown reads to know its wakeup dial reached THIS
/// acceptor ([`AcceptWake::Blocks`]).
struct AcceptLoop<'a> {
    shared: &'a Shared,
    listening: &'a AtomicBool,
    turns: &'a AtomicU64,
    polls: bool,
}

impl AcceptLoop<'_> {
    /// Whether the broker or this listener is stopping.
    fn stopping(&self) -> bool {
        !self.shared.running.load(Ordering::Relaxed) || !self.listening.load(Ordering::Relaxed)
    }

    /// Count one `accept()` return and say whether the loop goes on: `failed` is the
    /// error it returned, `None` for a connection. For a connection, `true` is "hand it
    /// off" (the caller then asks [`stopping`](Self::stopping)) and `false` is "close
    /// it and leave"; for an error, `true` is "accept again".
    fn turn(&self, failed: Option<io::ErrorKind>) -> bool {
        self.turns.fetch_add(1, Ordering::Relaxed);
        if !self.polls {
            self.shared.acceptor_wakeups.fetch_add(1, Ordering::Relaxed);
        }
        let is_stopping = self.stopping();
        match failed {
            None => {
                // Stopping: close what the backlog handed us (a wakeup dial among them)
                // instead of spawning a handler shutdown could miss.
                if is_stopping {
                    return false;
                }
                self.shared.accepted.fetch_add(1, Ordering::Relaxed);
                return true;
            }
            Some(io::ErrorKind::WouldBlock) if self.polls => {
                if is_stopping {
                    return false;
                }
                self.back_off();
            }
            // ONE connection's failure (reset while it sat in the backlog): the next
            // connection is not to wait out a back-off for it. (A signal never gets
            // here: std's `accept()` retries EINTR itself.)
            Some(io::ErrorKind::ConnectionAborted) => {}
            // A transient accept() error (EMFILE/ENFILE) must NOT kill the listener —
            // back off briefly instead of spinning on it. Only shutdown stops it.
            Some(_) => {
                if is_stopping {
                    return false;
                }
                self.back_off();
            }
        }
        !self.stopping()
    }

    /// Sleep one [`ACCEPT_POLL`], counted.
    fn back_off(&self) {
        self.shared.acceptor_sleeps.fetch_add(1, Ordering::Relaxed);
        thread::sleep(ACCEPT_POLL);
        self.shared.acceptor_wakeups.fetch_add(1, Ordering::Relaxed);
    }
}

/// The error kind of an `accept()` return, `None` for a connection.
fn accept_failure<T>(got: &io::Result<T>) -> Option<io::ErrorKind> {
    match got {
        Ok(_) => None,
        Err(e) => Some(e.kind()),
    }
}

/// How often a parked subscriber wakes to probe whether its peer disconnected (a
/// never-matching subscriber never writes, so it would otherwise never notice a
/// dead client). This is a liveness heartbeat, NOT a delivery poll — a publish
/// still wakes the tail immediately via the `Condvar`. Overridable per broker with
/// [`Broker::set_liveness_poll`].
pub const LIVENESS_POLL: Duration = Duration::from_millis(200);

/// How long a CAUGHT-UP subscription (`Subscribe`, `SubscribeGroup`) that opted in
/// with [`Request::IdleMarks`] may go with
/// nothing written to it before the broker writes a `Mark { next, head }` — the
/// existing "resume from `next`; `head` is the visible head" frame, which
/// `Subscription::recv` skips — so a live idle subscription is never silent for
/// longer than this, and a subscriber that hears nothing for several of these is on
/// a dead link (`Subscription::recv_live` turns that into an error). The tail also
/// marks once the moment it first catches up. A wire FRAME, never a log record: it
/// costs the log nothing, and a write that fails reaps a vanished subscriber the
/// read probe alone could not. Overridable per broker with [`Broker::set_idle_mark`].
pub const IDLE_MARK: Duration = Duration::from_secs(10);

/// The read deadline a subscriber arms on the broker's idle marks
/// (`Subscription::recv_live`): three [`IDLE_MARK`]s, so a mark delayed by a loaded
/// broker is not a dead link, and a link that IS dead is an error inside half a
/// minute rather than never.
pub const IDLE_MARK_DEADLINE: Duration = Duration::from_secs(30);

/// How long a REQUEST/REPLY connection over TCP that keeps alive may go with nothing
/// read from it before the broker ends it — the request-side twin of
/// [`IDLE_MARK_DEADLINE`], and the only bound on a peer that vanished without a FIN.
///
/// The broker writes to a request/reply connection only to answer it, so a peer that
/// lost power, or whose path died while the link was idle (a NAT or Wi-Fi change, a
/// cable pull, a laptop asleep past its NAT mapping), leaves the connection thread
/// parked in a read that nothing ends: no OS timer runs on an idle socket with no
/// keepalive, and std offers none to set. Until the broker restarted, its will never
/// fired and its [`MAX_CONNS`] slot, thread and fd were never freed. A client that
/// sends [`Request::Keepalive`] asks to be held to this deadline instead: from its
/// first one, every read on the connection is bounded by it, and a connection silent
/// that long is ended exactly as a closed one is — `handle_conn` fires its will
/// (fenced as ever: a later incarnation's record still suppresses it) and its slot is
/// freed.
///
/// OPT-IN BY CONSTRUCTION. The deadline is armed by the client's first `Keepalive`,
/// so a client that never sends one — every client that predates the verb, idling
/// for hours on a quiet link — is never cut. A Unix-socket connection is never held
/// to it: its peer cannot vanish without its kernel closing the socket (a dead
/// process is an EOF, and a dead host took this broker with it), so a deadline there
/// could only ever cut a live peer that stalled.
///
/// Three [`KEEPALIVE_INTERVAL`]s, so a keepalive delayed by a loaded client is not a
/// dead link. Overridable per broker with [`Broker::set_keepalive_deadline`].
pub const KEEPALIVE_DEADLINE: Duration = Duration::from_secs(60);

/// How often a client that keeps a TCP connection alive sends a [`Request::Keepalive`]
/// when it has sent nothing else (`Client::keepalive_if_idle`): a third of
/// [`KEEPALIVE_DEADLINE`]. A wire frame, never a log record — it costs the log nothing
/// and reaches no subscriber, so it is not the heartbeat the fabric design rules out.
pub const KEEPALIVE_INTERVAL: Duration = Duration::from_secs(20);

/// How long ONE liveness probe may block reading the subscriber's socket should the
/// socket refuse to go non-blocking for it — the fallback bound, never the normal
/// path (see `peer_gone`). While a tail sits in a blocking probe a publish's `Condvar`
/// wakeup finds nobody waiting and the record waits out the probe instead, so keep it
/// the shortest the socket accepts.
const PEER_PROBE_TIMEOUT: Duration = Duration::from_millis(1);

#[derive(Clone, Copy)]
struct CachedDeliveryCrc {
    offset: u64,
    crc: u32,
}

/// What `Hello` reports from the log — its identity and the extension block beside it
/// — copied out of the log so the answer never takes the log lock (`Shared::hello`).
#[derive(Clone)]
struct HelloCopy {
    identity: crate::LogIdentity,
    ext: crate::proto::NonceExt,
}

impl HelloCopy {
    /// The log's own answer now: its identity, the tier this open serves, its lineage,
    /// the device its file is on, and the retention rules this open retains it by (never rules only read back from
    /// its held store, which compact nothing: `BrokerLog::retention_active`). Taken under
    /// the log lock (the caller holds the log); taken again when the rules are set.
    fn of(log: &BrokerLog) -> HelloCopy {
        #[cfg(feature = "retention")]
        let retention = match log.retention_active() {
            Some(r) => Some(r.encode()),
            None => None,
        };
        #[cfg(not(feature = "retention"))]
        let retention = None;
        HelloCopy {
            identity: log.identity(),
            ext: crate::proto::NonceExt {
                durability: Some(log.served()),
                lineage: Some(log.lineage().clone()),
                retention,
                requests: Some(
                    crate::proto::REQUEST_RETIRE
                        | crate::proto::REQUEST_GAP_NOTICES
                        | crate::proto::REQUEST_TOLD_FETCH
                        | crate::proto::REQUEST_BROKER_TIMES
                        | crate::proto::REQUEST_STATS
                        | crate::proto::REQUEST_BURST_MARKS
                        | crate::proto::REQUEST_RELAY
                        | crate::proto::REQUEST_SETTLE
                        | crate::proto::REQUEST_FRESH_PUBLISH,
                ),
                // Never copied: the answer reads it fresh from the vitals
                // (`hello_health`), since it moves with every batch's flush.
                health: None,
                device: log.device(),
            },
        }
    }
}

/// The `Hello` answer's health entry (its block's tag 0x04,
/// [`HelloHealth`](crate::HelloHealth)): the poison and the flush counts as they stand,
/// read from the vitals without the log lock.
fn hello_health(vitals: &crate::store::LogVitals) -> crate::proto::HelloHealth {
    crate::proto::HelloHealth {
        poisoned: match vitals.poisoned() {
            Some(why) => Some(why.to_string()),
            None => None,
        },
        flushes: vitals.flush_counts(),
    }
}

/// THE ANSWER TO `Hello` NOW, from `told` (the copy beside the log, [`Shared::hello`])
/// and the vitals: the health entry (tag 0x04), then the tier served (tag 0x01) with any
/// latch to Strict the vitals hold that the copy does not yet. In that order: the copy
/// is refreshed only when the writer publishes the batch's state, after the poison of a
/// failure that latched it — so the tier is read from the vitals AFTER the poison, and
/// an answer that names the poison names the tier the log serves with it
/// ([`LogVitals::served`](crate::store::LogVitals::served)). And whether the broker
/// gap-fences the writes of a connection that asks (`gap_fences`,
/// [`Broker::sticky_batch_refusal`], [`Request::FenceGaps`]), fixed when the broker opens:
/// the request set's [`REQUEST_GAP_FENCES`](crate::proto::REQUEST_GAP_FENCES) bit. A
/// connection that asked can rely on that guarantee for its entire lifetime.
fn hello_answer(told: HelloCopy, vitals: &crate::store::LogVitals, gap_fences: bool) -> HelloCopy {
    let HelloCopy { identity, mut ext } = told;
    ext.health = Some(hello_health(vitals));
    ext.durability = match ext.durability {
        Some(s) => Some(vitals.served(s)),
        None => None,
    };
    if gap_fences {
        ext.requests = Some(match ext.requests {
            Some(r) => r | crate::proto::REQUEST_GAP_FENCES,
            None => crate::proto::REQUEST_GAP_FENCES,
        });
    }
    HelloCopy { identity, ext }
}

#[cfg_attr(not(feature = "cap"), allow(dead_code))]
#[derive(Debug, Clone)]
struct AttachedConnInfo {
    principal: String,
    transport: &'static str,
    producer_id: u64,
    attached_at_ms: u64,
    grants: Vec<(Filter, Option<u64>)>,
    peer: PeerAuth,
}

struct Shared {
    log: Mutex<BrokerLog>,
    tail: Condvar,
    /// Monotone Unix-millisecond timestamp when this `Broker` opened (`REQUIREMENTS` R5).
    started_at_ms: u64,
    /// Active listener endpoints (`"<scheme>:<addr>"`), keyed by registration order.
    listeners: Mutex<std::collections::BTreeMap<u64, String>>,
    listener_seq: AtomicU64,
    /// Live attached producer entries per open connection (`conn_id`), cleaned up by
    /// [`ConnGuard::drop`] (`REQUIREMENTS` R5).
    attached_conns: Mutex<HashMap<u64, Vec<AttachedConnInfo>>>,
    /// The SUBSCRIBER-VISIBLE head: subscribers are delivered records below it, `Fetch`
    /// reads below it, `Last` pins it. In the Strict/Ordered/Relaxed tiers it is the
    /// log's head as each batch commits (advanced under the log lock) — HELD at the first
    /// escalated record of a batch until the full flush it owes has succeeded, so an
    /// escalated record is never visible before it is durable, and since every ack waits
    /// for visibility, never acked before either (the held head; see `process_batch`) —
    /// but a will registration's, whose hidden record no subscriber is ever delivered and
    /// whose ack answers for its commit alone. Nor does its effect leak: a group commit a
    /// held batch carries steers no group reader until then (`BrokerLog::group_start`).
    /// In the Replicated tier it is the QUORUM WATERMARK — the offset below which a
    /// quorum of followers holds every record — so a leader-side consumer never reads a
    /// record no follower has yet.
    head: AtomicU64,
    /// The DURABLE head ([`BrokerLog::durable_head`]): every record below it is on stable
    /// media by a full flush the writer saw succeed. Written under the log lock, beside
    /// `head`, wherever the log's moves (every Strict batch; a full flush on the weaker
    /// tiers), so [`Broker::durable_head`], every `Mark`'s `durable` and a sampler read it
    /// without the lock, and a tail parked on the lock's condition sees it move.
    durable: AtomicU64,
    /// Whether this open owes idle-marks subscribers DURABLE MARKS (`tail_loop`): the log
    /// served Ordered at its open. Fixed for the open, and so KEPT when the log latches
    /// to Strict. A Strict-from-open log sends none — its `durable` is the visible head
    /// after every batch, so a mark per delivery would tell nobody anything — and a
    /// Relaxed one's does not move between opens. But a tail that attached while the log
    /// served Ordered, like a connection whose `Hello` said Ordered, may hold back what it
    /// was delivered until a durable mark covers it (aterm's notifier pages only those),
    /// and nothing on its stream tells it the tier changed: cleared at the latch, it would
    /// wait for the idle mark an interval later, which a busy subscription never reaches.
    /// After a latch every batch is flushed in full, so each delivered batch costs such a
    /// tail one mark.
    durable_marks: bool,
    /// The Ordered horizon the writer keeps ([`Durability::Ordered`]), fixed at open:
    /// `None` on every other tier, and for `Ordered { horizon: None }`.
    horizon: Option<Duration>,
    running: AtomicBool,
    /// Producers enqueue durable mutations here; the single writer thread drains and
    /// group-commits them. Keeping all writes on one thread means dedup + the offset
    /// spine advance in order with no cross-thread append race. Shutdown queues the
    /// writer's stop here too ([`stop_writer`]).
    writes: Sender<Queued>,
    /// Live connection sockets (a clone per accepted connection), so shutdown can
    /// force-close any thread parked in a blocking socket read/write and reap it.
    conns: Mutex<HashMap<u64, Sock>>,
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
    /// [`IDLE_MARK`], in milliseconds ([`Broker::set_idle_mark`]).
    idle_mark_ms: AtomicU64,
    /// [`LIVENESS_POLL`], in milliseconds ([`Broker::set_liveness_poll`]).
    liveness_poll_ms: AtomicU64,
    /// [`KEEPALIVE_DEADLINE`], in milliseconds ([`Broker::set_keepalive_deadline`]).
    keepalive_deadline_ms: AtomicU64,
    /// Connections refused at the cap that are still lingering (`linger_refused`).
    refusing: AtomicUsize,
    /// Number of currently active [`BrokerHandle`] listeners serving this broker.
    /// Dropping or shutting down a single listener stops only its own acceptor;
    /// the shared writer thread and log lock are torn down when the LAST listener
    /// handle shuts down (or when an unserved `Broker` drops).
    active_listeners: AtomicUsize,
    /// The group-commit writer thread, shared across all [`BrokerHandle`]s on this
    /// broker and joined when the last listener shuts down.
    writer: Mutex<Option<JoinHandle<()>>>,
    /// [`BrokerStats::accepted`].
    accepted: AtomicU64,
    /// [`BrokerStats::acceptor_wakeups`].
    acceptor_wakeups: AtomicU64,
    /// [`BrokerStats::acceptor_sleeps`].
    acceptor_sleeps: AtomicU64,
    /// [`BrokerStats::acceptors_abandoned`].
    acceptors_abandoned: AtomicU64,
    /// Revoked Ed25519 peer identity public keys (`REQUIREMENTS` R6). Any new
    /// connection on [`Broker::serve_tcp_identity`] whose peer key is in this set is
    /// refused at the handshake, and any already-open connection is terminated with an
    /// `unauthorized` error on its next request or tail delivery.
    revoked_identities: Mutex<RevocationSet<[u8; 32]>>,
    /// Revoked capability principals (`p=<principal>`, including `n-<16 hex>` node
    /// principals derived from revoked Ed25519 keys via [`identity_principal`]).
    revoked_principals: Mutex<RevocationSet<String>>,
    /// Revoked `ACRT` certificate serial numbers (`serial:<u64>`, Rung 9).
    revoked_cert_serials: Mutex<RevocationSet<u64>>,
    /// Whose relayed records this broker takes: `identity_principal(key) -> key`.
    #[cfg(feature = "relay")]
    origin_keys: Mutex<std::collections::BTreeMap<String, [u8; 32]>>,
    /// Relayed records refused for what they are ([`ERR_ORIGIN_REFUSED`]).
    origin_refused: AtomicU64,
    /// Relayed records answered [`ERR_ORIGIN_UNKNOWN`]: each answer, so a record offered again
    /// counts again.
    origin_unknown: AtomicU64,
    /// Revocation file tracked for automatic Apple `SIGHUP` reload (`REQUIREMENTS` R6).
    revocation_file: Mutex<Option<RevocationFileState>>,
    /// Fast atomic flag set once [`Broker::load_revocation_file`] has been called.
    has_revocation_file: AtomicBool,
    /// Last [`astream_sys::sighup_generation`] observed by this broker.
    sighup_seen: AtomicU64,
    /// Monotone counter incremented whenever the live revocation set changes.
    revocation_epoch: AtomicU64,
    /// [`Broker::pause_last_scan_round`]: the test seam taken at one `last_page` round
    /// boundary. `None` — and one uncontended lock per boundary, never per record —
    /// unless a test installs one.
    ///
    /// A closed rendezvous, not a caller-supplied `dyn Fn`: a `dyn` callback stored here
    /// is an open principal for Trust's thread-spawn census (an out-of-sight caller
    /// could install a closure that spawns), which marked every indirect-call pool in
    /// the crate "may spawn" — `ConnGuard::drop` included.
    last_round_pause: Mutex<Option<RoundPause>>,
    /// TEST SEAM ([`TailPause`]): taken by the next tail to start. `None` unless a unit
    /// test installs one; not in a build that is not a test.
    #[cfg(test)]
    tail_pause: Mutex<Option<TailPause>>,
    /// Direct-mapped cache only for immutable live `Response::Delivery` payloads.
    /// Each slot keeps the full 64-bit offset and CRC under one short lock; a fork's
    /// counterfactual delivery never enters this cache. No offset bit is a valid flag.
    delivery_crc_cache: Box<[Mutex<Option<CachedDeliveryCrc>>; 4096]>,
    /// The log's [`LogIdentity`](crate::LogIdentity), and the extension block beside it
    /// (the tier served, the lineage: [`HelloCopy`]), as `Hello` reports them, kept
    /// beside the log so the answer never waits on the log lock — which the writer
    /// holds while it stages and promotes a batch (it held it across every batch's write
    /// and fsync too, before those left the lock). Without it a guarded connect beside
    /// one busy Strict publisher waited out most of an fsync before its very first
    /// reply (`Hello` p50 3.3-3.5 ms against 0.008 ms idle, cost study B2/B5).
    ///
    /// Set from the log at open. The identity changes in a running broker in exactly
    /// one place, a replica adopting its leader's in `process_batch` — which drops the
    /// replica's own lineage with it — and the writer copies both here right there,
    /// still under the log lock (lock order: log → copy). A `Hello` that reads it a
    /// moment before that copy reports what a `Hello` holding the log lock just before
    /// the batch would have: the adopting batch's records are not visible until the
    /// head moves, after the copy. The tier served changes only when the log latches to
    /// Strict: the writer copies it here when it publishes the batch's state, and every
    /// reader adds the latch from the log's vitals before that ([`hello_answer`]), so the
    /// poison of the failure that latched it is never told beside the tier before it.
    /// Anything else `Hello` comes to report from the log belongs here with it.
    hello: Mutex<HelloCopy>,
    /// The log's DURABLE producer bindings, `producer id → (principal, offset of its
    /// /a/bind record)`, kept beside the log so an `Attach` whose principal is already
    /// bound decides that without the log lock and without a writer round trip.
    ///
    /// Without it every read-write grant naming a principal queued a `Bind` to the
    /// writer, even for a principal bound long ago: the writer found the binding,
    /// appended nothing, and ran an empty batch anyway — behind whatever batch, fsync
    /// included, it was already in. aterm's ring carries four `rw,p=<node>` grants,
    /// so every guarded connection paid four serial writer round trips and four
    /// empty batches for nothing (`Hello` + attach p50 12.7-18.9 ms beside one busy
    /// Strict publisher, 0.107 ms idle; cost study B5, checker's numbers).
    ///
    /// WHY A COPY CAN BE TRUSTED. While this broker has the log open, a binding the log
    /// has promoted never stops being one: `/a/bind` records are appended and never
    /// rewritten, promotion keeps the FIRST binding of an id (`or_insert`), a running
    /// broker never cuts back its committed tail (a rollback cuts only the staged
    /// batch), and retention, which drops from the front, keeps every binding —
    /// `retain_before` refuses to drop a binding's record, `retain_before_carrying_state`
    /// carries it in `<log>.state`, and neither touches the in-memory table. So an
    /// entry copied here is the log's answer for as long as this copy lives, and the
    /// copy only ever has to GROW. It holds only what the log has promoted (durable at
    /// the log's tier), never the in-flight batch's.
    ///
    /// NOT ACROSS AN OPEN, and it need not be: the copy lives and dies with this
    /// `Broker`, and every open seeds a fresh one from what THAT open recovered. A
    /// Relaxed log that a power cut shortened (`broker.guarded-durability`), or one an
    /// explicit repair cut back to a corrupt record, can come back without a binding
    /// the last open held; the new copy simply lacks it, and the principal's next
    /// attach binds it again through the writer.
    ///
    /// Seeded from the log at open; the writer adds what each batch promoted, under
    /// the log lock (lock order: log → bindings), after publishing the head the batch
    /// reached. Readers take it alone. A MISS — an unbound id, a different principal,
    /// or a binding not yet below the visible head — is answered by the writer exactly
    /// as before, which is where a first bind is appended and a collision refused.
    /// Kept by a guarded broker only (an unguarded one checks no binding); empty
    /// otherwise.
    bindings: Mutex<HashMap<u64, (String, u64)>>,
    /// [`BrokerStats::writer_round_trips`].
    writer_round_trips: AtomicU64,
    /// [`BrokerStats::writer_batches`].
    writer_batches: AtomicU64,
    /// [`BrokerStats::writer_wakeups`].
    writer_wakeups: AtomicU64,
    /// [`BrokerStats::empty_batches`].
    empty_batches: AtomicU64,
    /// [`BrokerStats::binds_settled`].
    binds_settled: AtomicU64,
    /// [`BrokerStats::wills_settled`].
    wills_settled: AtomicU64,
    /// [`BrokerStats::tail_broadcasts`].
    tail_broadcasts: AtomicU64,
    /// [`BrokerStats::selective_tail_wakes`].
    selective_tail_wakes: AtomicU64,
    /// [`BrokerStats::tail_wakeups`].
    tail_wakeups: AtomicU64,
    /// [`Broker::selective_tail_wake`]: when `true`, the writer matches newly visible
    /// deliverable records against registered [`TailParker`] filters and wakes only
    /// matching tails (`cost study B4 step 2`).
    selective_tail_wake: AtomicBool,
    /// Bumped under `log` lock whenever `selective_tail_wake` is toggled so parked tails
    /// immediately wake and switch between `tail` and their per-subscriber `TailParker`.
    selective_mode_epoch: AtomicU64,
    /// Monotone id generator for [`TailParker`].
    next_parker_id: AtomicU64,
    /// Active subscriber tails registered for selective wakeups (pure leaf lock).
    tail_parkers: Mutex<Vec<Arc<TailParker>>>,
    /// Fast lock-free gate for [`Self::rate_limiter`] (`false` when unthrottled).
    has_rate_limit: AtomicBool,
    /// Per-principal / per-producer monotone token-bucket rate limiter (leaf lock).
    rate_limiter: Mutex<RateLimiterState>,
    /// [`BrokerStats::rate_limited`].
    rate_limited: AtomicU64,
    /// Fast lock-free gate for [`Self::sticky_fences`] (`false` by default).
    has_sticky_batch_refusal: bool,
    /// Per-`(conn_id, producer_id)` sticky sequence gap fences (pure leaf lock).
    sticky_fences: Mutex<crate::sticky_fence::StickyFenceTable>,
    /// [`BrokerStats::peer_probes`].
    peer_probes: AtomicU64,
    /// [`BrokerStats::parked_tails`].
    parked_tails: AtomicUsize,
    /// THE BATCH LOCK: held by the writer thread for a batch's whole life — staging, the
    /// write and flush it runs with the LOG lock released, the promotion — and taken by
    /// nothing else but retention, before the log lock (lock order: batch → log). So a
    /// `retain_before`, a tick or a `set_retention` that arrives while a batch is being
    /// written waits for that batch to commit or roll back, exactly as it waited on the log
    /// lock when the writer held that across the fsync, instead of meeting the batch staged
    /// and being refused ("a batch is being written"). No reader ever takes it, so it costs
    /// a reader nothing; the writer takes it uncontended once per batch.
    batch: Mutex<()>,
    /// [`BrokerStats::retention_waits`].
    retention_waits: AtomicU64,
    /// One compaction at a time: held by a retention call across its begin, its unlocked
    /// copy and its finish (lock order: compaction → batch → log). The copy writes the one
    /// `<log>.kept`, and the log is replaced by the finish of the compaction that copied
    /// it, so two may never overlap. [`Broker::set_retention`] takes it too, so no rules
    /// change lands inside a compaction: the job begun under the old rules writes its held
    /// frames where the store ended at its begin, which is where a rules frame would go,
    /// and its cut is where the new rules start to hold from.
    #[cfg(feature = "retention")]
    compaction: Mutex<()>,
    /// How many times a caller of [`lock_compaction`] found another's compaction under
    /// way and waited for it: what a test reads to know a call is waiting there.
    #[cfg(feature = "retention")]
    compaction_waits: AtomicU64,
    /// THE RETENTION TICK's wake and stop (`ticker_loop`): asked for by the writer when a
    /// batch takes some class of the rules past its bytes or the log past a cap, by
    /// [`Broker::set_retention`], and by nothing at all once a
    /// [retention interval](Broker::set_retention_interval) passes; stopped at shutdown,
    /// before the writer. `tick_cv` wakes the ticker, `tick_done` whoever waits on a tick.
    #[cfg(feature = "retention")]
    tick: Mutex<TickState>,
    #[cfg(feature = "retention")]
    tick_cv: Condvar,
    #[cfg(feature = "retention")]
    tick_done: Condvar,
    /// The retention tick's thread: started by the first rules or cap set, joined at
    /// shutdown before the writer. `None` on a broker nothing retains, which never ticks.
    #[cfg(feature = "retention")]
    ticker: Mutex<Option<JoinHandle<()>>>,
    /// [`RETENTION_INTERVAL`], in milliseconds ([`Broker::set_retention_interval`]).
    #[cfg(feature = "retention")]
    retention_interval_ms: AtomicU64,
    /// The log's bytes on disk (`BrokerLog::durable_len`), published with its head so the
    /// writer can tell, with no lock, that a batch took the log past what retention allows.
    #[cfg(feature = "retention")]
    log_bytes: AtomicU64,
    /// [`BrokerLog::retention_due`]: set, a batch asks for a tick at once. Published under
    /// the log lock with every batch's state and after every planning.
    #[cfg(feature = "retention")]
    retain_due: AtomicBool,
    /// [`Broker::pause_next_batch`] and [`Broker::pause_next_acks`]: the test seam
    /// taken at one point of one batch. Empty unless a test arms it;
    /// `batch_pause_armed` keeps an unarmed broker's writer from taking even this lock
    /// per batch.
    batch_pause: Mutex<BatchPauseSeam>,
    batch_pause_armed: AtomicBool,
    /// [`Broker::arm_unclean_stop`]: the test seam under which this broker's stop skips
    /// the clean close ([`stop_log`]). False unless a test arms it.
    unclean_stop: AtomicBool,
    /// The log's poison and flush counts, shared with the log that writes them
    /// ([`LogVitals`](crate::store::LogVitals)): what [`Broker::poisoned`],
    /// [`Broker::flush_counts`], [`Broker::wait_poisoned`], every `Hello` answer (its
    /// block's tag 0x04) and the health sidecar read WITHOUT the log lock — which the
    /// writer holds across a rollback's truncate and the identity I/O of a failed flush,
    /// the slow I/O of exactly the failure they report.
    vitals: Arc<crate::store::LogVitals>,
    /// The path the log was opened from: the stem `<log>.health` is named from.
    log_path: std::path::PathBuf,
    /// `<log>.health` once this broker keeps it ([`Broker::write_health`],
    /// [`Broker::keep_health`]): the file it last published, held under its lock until
    /// the log closes ([`stop_health`]). Taken alone, never under the log lock.
    health: Mutex<Option<crate::health::HealthFile>>,
    /// The thread that rewrites `<log>.health` every period ([`Broker::keep_health`]),
    /// joined when the log closes.
    health_thread: Mutex<Option<JoinHandle<()>>>,
    /// The log's retention base (`BrokerLog::base`), updated under the log lock
    /// whenever retention advances it so [`Broker::base`] can read it without locking
    /// `shared.log`.
    base: AtomicU64,
    /// The log's committed head (`BrokerLog::head`), updated under the log lock
    /// whenever a batch commits so [`Broker::head`] and `serve_replicate`'s hidden-subject
    /// pre-check can read it without locking `shared.log`.
    log_head: AtomicU64,
    /// Whether the log is a replica (`BrokerLog::is_replica`), updated under the log
    /// lock so `serve_replicate` can check it without locking `shared.log`.
    is_replica: AtomicBool,
    /// Automatic state-carrying compaction record cap (`0` = unlimited, default `0`).
    #[cfg_attr(not(feature = "retention"), allow(dead_code))]
    max_retained_records: AtomicUsize,
    /// Automatic state-carrying compaction byte cap (`0` = unlimited, default `0`).
    #[cfg_attr(not(feature = "retention"), allow(dead_code))]
    max_retained_bytes: AtomicUsize,
}

/// How often the retention tick runs when nothing asks for it sooner: once a minute
/// ([`Broker::set_retention_interval`]). The writer asks for one at once when a batch takes
/// the log past what the rules' bytes or the caps allow, so the interval is what an age
/// rule waits for, not what bounds the log.
#[cfg(feature = "retention")]
pub const RETENTION_INTERVAL: Duration = Duration::from_secs(60);

/// The retention tick's wake (`Shared::tick`).
#[cfg(feature = "retention")]
#[derive(Default)]
struct TickState {
    /// A tick is asked for now.
    due: bool,
    /// The broker is shutting down: the ticker returns.
    stop: bool,
    /// Ticks run, by the ticker or [`Broker::retention_tick_at`]
    /// ([`BrokerStats::retention_ticks`]).
    ticks: u64,
    /// The ticker's ticks skipped, a compaction being under way
    /// ([`BrokerStats::retention_skips`]).
    skips: u64,
}

/// Where in a batch a [`BatchPauseSlot`] parks the writer.
#[derive(Clone, Copy, PartialEq, Eq)]
enum BatchPoint {
    /// Staged, the log lock HELD, nothing written yet: [`Broker::pause_next_batch`].
    Staged,
    /// Begun — sealed, its flush chosen, its bytes taken — the log lock RELEASED,
    /// nothing written or flushed yet: [`Broker::pause_next_write`].
    Writing,
    /// Committed, its head published and its bindings copied, the log lock released,
    /// no ack sent yet: [`Broker::pause_next_acks`].
    BeforeAcks,
    /// A batch that owes a full flush (the held head): every op it does not keep back
    /// answered, the log lock released, the flush not yet issued:
    /// [`Broker::pause_next_flush`].
    BeforeFlush,
}

/// The broker side of the batch-pause seam.
#[derive(Default)]
struct BatchPauseSeam {
    /// The armed rendezvous, if any.
    slot: Option<BatchPauseSlot>,
    /// Set, under this lock, as the writer thread exits. After that no batch reaches a
    /// pause point again, so the armed slot is dropped — its `reached` sender with it,
    /// which is what lets [`BatchPause::wait`] answer `false` instead of blocking for
    /// as long as the `Broker` lives — and a pause armed later is never stored. Under
    /// the one lock, an arm racing the exit lands on one side of it or the other.
    writer_stopped: bool,
}

/// The broker side of a batch-pause rendezvous.
struct BatchPauseSlot {
    /// The point of the batch that takes the pause.
    at: BatchPoint,
    /// Signalled when the writer is there.
    reached: Sender<()>,
    /// The batch goes on when this yields (or its sender is gone).
    resume: Receiver<()>,
}

/// The test side of [`Broker::pause_next_batch`] and [`Broker::pause_next_acks`]: wait
/// for the writer to reach the point in a batch, act in that window, then
/// [`resume`](Self::resume) it. Dropping the handle also resumes the batch, so a
/// panicking test never wedges the broker.
pub struct BatchPause {
    reached: Receiver<()>,
    resume: Sender<()>,
}

impl BatchPause {
    /// Block until the writer is paused at the point. `false` once no batch can reach
    /// it any more: the writer thread stopped (the broker shut down) first, or the
    /// pause was armed after it had.
    pub fn wait(&self) -> bool {
        self.reached.recv().is_ok()
    }

    /// [`wait`](Self::wait), giving up after `limit` (`false`): a test's HANG DETECTOR
    /// for a point a batch must reach — never a latency budget.
    pub fn wait_at_most(&self, limit: Duration) -> bool {
        self.reached.recv_timeout(limit).is_ok()
    }

    /// Let the paused batch go on.
    pub fn resume(self) {
        let _ = self.resume.send(());
    }
}

/// Run on the writer thread as it exits, by returning or by unwinding: see
/// [`BatchPauseSeam::writer_stopped`].
struct WriterExit<'a>(&'a Shared);

impl Drop for WriterExit<'_> {
    fn drop(&mut self) {
        // Never a second panic while unwinding: nothing that holds this lock panics,
        // and if something ever did, a pause left armed is a test's hang detector away.
        if let Ok(mut seam) = self.0.batch_pause.lock() {
            seam.writer_stopped = true;
            seam.slot = None;
            self.0.batch_pause_armed.store(false, Ordering::Release);
        }
    }
}

/// TEST SEAM: the next tail to start reads at most `chunk` records per hold of the log
/// lock, and stops once, `at` the point it names, its cursor sent on `reached`, until
/// `resume` yields (or its sender is gone): the window in which a test lands a retention
/// while the tail reads, or while it is about to park.
#[cfg(test)]
pub(crate) struct TailPause {
    pub(crate) chunk: usize,
    pub(crate) at: PauseAt,
    pub(crate) reached: Sender<u64>,
    pub(crate) resume: Receiver<()>,
}

/// Where a [`TailPause`] stops its tail.
#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PauseAt {
    /// Once it has delivered its first chunk.
    FirstChunk,
    /// Caught up, its idle mark written, before it takes the log lock to park: records
    /// that land then, and a retention that gives them up, are what its park wakes to.
    Park,
}

/// Stop the tail at `at` if its [`TailPause`] names it, until the test resumes it.
#[cfg(test)]
fn tail_pause_at(pause: &mut Option<TailPause>, at: PauseAt, cursor: u64) {
    if pause.as_ref().is_some_and(|p| p.at == at) {
        if let Some(p) = pause.take() {
            if p.reached.send(cursor).is_ok() {
                let _ = p.resume.recv();
            }
        }
    }
}

/// TEST SEAM: a moment inside `serve` at which another process could change what its
/// socket path names, where a hook a unit test armed on this thread runs
/// ([`SERVE_HOOKS`]).
#[cfg(all(test, unix))]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ServeAt {
    /// [`claim_socket_path`] judged the socket at a path stale, before removing it.
    Judged,
    /// The listener is bound (under its private name, or at the path itself), before
    /// its identity is read and before the path names it.
    Bound,
    /// The path names the listener and its wake name is made, before `serve` goes on.
    Linked,
}

/// TEST SEAM: what a unit test runs at a [`ServeAt`].
#[cfg(all(test, unix))]
pub(crate) type ServeHook = Box<dyn FnOnce()>;

#[cfg(all(test, unix))]
thread_local! {
    /// TEST SEAM: the hooks a unit test armed for the `serve` it calls on this thread, each
    /// run once, in order, at the first [`ServeAt`] it names. Each runs on `serve`'s own
    /// thread with no lock held, so a hook that panics fails its test and never hangs it.
    pub(crate) static SERVE_HOOKS: std::cell::RefCell<Vec<(ServeAt, ServeHook)>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// Run the first hook armed at `at` on this thread, if there is one.
#[cfg(all(test, unix))]
fn serve_hook(at: ServeAt) {
    let hook = SERVE_HOOKS.with(|hooks| {
        let mut hooks = hooks.borrow_mut();
        let first = hooks.iter().position(|(when, _)| *when == at)?;
        Some(hooks.remove(first).1)
    });
    if let Some(hook) = hook {
        hook();
    }
}

/// What a connection asked of its next tail or read before it ran: catch-up and idle
/// marks ([`Request::IdleMarks`]), gap notices ([`Request::GapNotices`]), and monotone
/// broker-stamped wall times ([`Request::BrokerTimes`]).
#[derive(Debug, Clone, Copy, Default)]
struct TailAsks {
    idle_marks: bool,
    gaps: bool,
    broker_times: bool,
    burst_marks: bool,
    origin_stamps: bool,
}

/// The broker side of a [`Broker::pause_last_scan_round`] rendezvous.
struct RoundPause {
    /// The round whose trailing boundary pauses.
    round: usize,
    /// Signalled when the walk reaches that boundary.
    reached: Sender<()>,
    /// The walk resumes when this yields (or its sender is gone).
    resume: Receiver<()>,
}

/// The test side of [`Broker::pause_last_scan_round`]: wait for the `Last` walk to reach
/// the round boundary, act in the window, then [`resume`](Self::resume) it. Dropping the
/// handle also resumes the walk, so a panicking test never wedges the broker.
pub struct LastRoundPause {
    reached: Receiver<()>,
    resume: Sender<()>,
}

impl LastRoundPause {
    /// Block until a `Last` walk is paused at the boundary. `false` if the broker went
    /// away without ever reaching it.
    pub fn wait(&self) -> bool {
        self.reached.recv().is_ok()
    }

    /// Let the paused walk continue.
    pub fn resume(self) {
        let _ = self.resume.send(());
    }
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

/// Wire transport used by a `Replicated` leader to dial its follower brokers.
///
/// By default ([`Broker::open_replicated`]), follower links are plaintext TCP
/// (`Plain`, suitable only on a trusted network). Across untrusted LAN/WAN links,
/// [`Broker::open_replicated_transport`] and `Broker::open_replicated_guarded_transport`
/// (under `feature = "cap"`) wrap every follower socket — at initial open and on every
/// reconnect — in one of `astream-aead`'s authenticated, encrypted transports.
#[allow(clippy::large_enum_variant)]
#[derive(Clone)]
pub enum FollowerTransport {
    /// Plaintext TCP (`Broker::serve_tcp`).
    Plain,
    /// XChaCha20-Poly1305 sealed stream under a 32-byte PSK (`Broker::serve_tcp_sealed`).
    #[cfg(feature = "aead")]
    Sealed([u8; astream_aead::KEY_LEN]),
    /// Forward-secret ephemeral X25519 authenticated by a 32-byte PSK (`Broker::serve_tcp_handshake`).
    #[cfg(feature = "handshake")]
    Handshake([u8; astream_aead::KEY_LEN]),
    /// Mutual Ed25519 signed-DH (`Broker::serve_tcp_identity`) with per-follower pinned host keys.
    #[cfg(feature = "identity")]
    Identity {
        /// Leader's Ed25519 identity keypair presented to every follower.
        identity: Arc<astream_aead::IdentityKeypair>,
        /// Expected Ed25519 public key for each follower in `follower_addrs` (`1:1` by index).
        expected_followers: Vec<[u8; astream_aead::ID_PUB_LEN]>,
    },
    /// Mutual CA-certified SIGMA (`Broker::serve_tcp_certified`) with a live-reloadable
    /// CA trust store and an `IdentitySigner` (`Local` or `SshAgent`, Rung 9).
    #[cfg(feature = "identity")]
    Certified {
        /// Leader's Ed25519 signer (`IdentityKeypair` or `SshAgentSigner`).
        signer: astream_aead::IdentitySigner,
        /// Leader's CA-signed `CertRole::Client` certificate.
        cert: astream_aead::IdentityCertificate,
        /// Shared CA trust store verifying each follower's `CertRole::Host` certificate.
        trust: astream_aead::SharedCertTrust,
        /// Expected host principal per follower (`1:1` with `follower_addrs`, or empty to
        /// accept any CA-valid `CertRole::Host` principal).
        expected_principals: Vec<Option<String>>,
    },
}

impl std::fmt::Debug for FollowerTransport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FollowerTransport::Plain => f.write_str("FollowerTransport::Plain"),
            #[cfg(feature = "aead")]
            FollowerTransport::Sealed(_) => f.write_str("FollowerTransport::Sealed(<secret>)"),
            #[cfg(feature = "handshake")]
            FollowerTransport::Handshake(_) => {
                f.write_str("FollowerTransport::Handshake(<secret>)")
            }
            #[cfg(feature = "identity")]
            FollowerTransport::Identity {
                expected_followers, ..
            } => f
                .debug_struct("FollowerTransport::Identity")
                .field("followers", &expected_followers.len())
                .finish(),
            #[cfg(feature = "identity")]
            FollowerTransport::Certified {
                cert,
                expected_principals,
                ..
            } => f
                .debug_struct("FollowerTransport::Certified")
                .field("principal", &cert.principal())
                .field("serial", &cert.serial())
                .field("followers", &expected_principals.len())
                .finish(),
        }
    }
}

#[derive(Clone)]
enum LinkTransport {
    Plain,
    #[cfg(feature = "aead")]
    Sealed([u8; astream_aead::KEY_LEN]),
    #[cfg(feature = "handshake")]
    Handshake([u8; astream_aead::KEY_LEN]),
    #[cfg(feature = "identity")]
    Identity {
        identity: Arc<astream_aead::IdentityKeypair>,
        expected_server: [u8; astream_aead::ID_PUB_LEN],
    },
    #[cfg(feature = "identity")]
    Certified {
        signer: Arc<astream_aead::IdentitySigner>,
        cert: Arc<astream_aead::IdentityCertificate>,
        trust: astream_aead::SharedCertTrust,
        expected_principal: Option<String>,
    },
}

impl FollowerTransport {
    fn links_for(&self, count: usize) -> io::Result<Vec<LinkTransport>> {
        const MAX_REPLICATED_FOLLOWERS: usize = 4096;
        if count > MAX_REPLICATED_FOLLOWERS {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!(
                    "Replicated tier: follower count ({count}) exceeds MAX_REPLICATED_FOLLOWERS ({MAX_REPLICATED_FOLLOWERS})"
                ),
            ));
        }
        match self {
            FollowerTransport::Plain => {
                let mut out = Vec::with_capacity(count);
                for _ in 0..count {
                    out.push(LinkTransport::Plain);
                }
                Ok(out)
            }
            #[cfg(feature = "aead")]
            FollowerTransport::Sealed(key) => {
                let mut out = Vec::with_capacity(count);
                for _ in 0..count {
                    out.push(LinkTransport::Sealed(*key));
                }
                Ok(out)
            }
            #[cfg(feature = "handshake")]
            FollowerTransport::Handshake(psk) => {
                let mut out = Vec::with_capacity(count);
                for _ in 0..count {
                    out.push(LinkTransport::Handshake(*psk));
                }
                Ok(out)
            }
            #[cfg(feature = "identity")]
            FollowerTransport::Identity {
                identity,
                expected_followers,
            } => {
                if expected_followers.len() != count {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!(
                            "FollowerTransport::Identity expected_followers length ({}) must match follower_addrs length ({count})",
                            expected_followers.len()
                        ),
                    ));
                }
                let mut out = Vec::with_capacity(count);
                for pk in expected_followers {
                    out.push(LinkTransport::Identity {
                        identity: identity.clone(),
                        expected_server: *pk,
                    });
                }
                Ok(out)
            }
            #[cfg(feature = "identity")]
            FollowerTransport::Certified {
                signer,
                cert,
                trust,
                expected_principals,
            } => {
                if !expected_principals.is_empty() && expected_principals.len() != count {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!(
                            "FollowerTransport::Certified expected_principals length ({}) must be empty or match follower_addrs length ({count})",
                            expected_principals.len()
                        ),
                    ));
                }
                let signer_arc = Arc::new(signer.clone());
                let cert_arc = Arc::new(cert.clone());
                let mut out = if count <= 1024 {
                    Vec::with_capacity(count)
                } else {
                    Vec::new()
                };
                for idx in 0..count {
                    let expected_principal = expected_principals.get(idx).cloned().flatten();
                    out.push(LinkTransport::Certified {
                        signer: Arc::clone(&signer_arc),
                        cert: Arc::clone(&cert_arc),
                        trust: trust.clone(),
                        expected_principal,
                    });
                }
                Ok(out)
            }
        }
    }
}

/// Concrete follower byte stream (plaintext TCP or AEAD-sealed TCP) so the verified lane
/// resolves every replication read/write without open trait-object or generic dispatch.
enum FollowerStream {
    Plain(TcpStream),
    #[cfg(feature = "aead")]
    Sealed(astream_aead::SealedStream<TcpStream>),
}

impl FollowerStream {
    fn tcp_ref(&self) -> &TcpStream {
        match self {
            FollowerStream::Plain(s) => s,
            #[cfg(feature = "aead")]
            FollowerStream::Sealed(s) => s.get_ref(),
        }
    }

    #[cfg(any(feature = "cap", feature = "handshake"))]
    fn set_read_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        self.tcp_ref().set_read_timeout(d)
    }

    #[cfg(any(feature = "cap", feature = "handshake"))]
    fn set_write_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        self.tcp_ref().set_write_timeout(d)
    }

    fn try_clone_tcp(&self) -> io::Result<TcpStream> {
        let clone = self.tcp_ref().try_clone()?;
        kept_from_children(&clone)?;
        Ok(clone)
    }

    fn shutdown(&self, how: Shutdown) -> io::Result<()> {
        self.tcp_ref().shutdown(how)
    }
}

impl Read for FollowerStream {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        match self {
            FollowerStream::Plain(s) => s.read(buf),
            #[cfg(feature = "aead")]
            FollowerStream::Sealed(s) => s.read(buf),
        }
    }
}

impl Write for FollowerStream {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        match self {
            FollowerStream::Plain(s) => s.write(buf),
            #[cfg(feature = "aead")]
            FollowerStream::Sealed(s) => s.write(buf),
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        match self {
            FollowerStream::Plain(s) => s.flush(),
            #[cfg(feature = "aead")]
            FollowerStream::Sealed(s) => s.flush(),
        }
    }
}

/// One follower's replication link, driven only by the writer thread.
struct FollowerLink {
    /// The leader's own [`LogIdentity`](crate::LogIdentity), sent beside every record
    /// so the follower — a replica of exactly these offsets — reports it too. Fixed
    /// for the leader's life: a log a broker owns changes identity only at an open.
    leader: crate::LogIdentity,
    addr: String,
    transport: LinkTransport,
    /// `None` while the link is down (dropped after an I/O error / timeout); it is
    /// re-established on the next batch. A per-record REFUSAL from the follower (a
    /// `Response::Error`) does not drop the link — the stream stays in sync.
    stream: Option<FollowerStream>,
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
    /// Consecutive timed-out redial attempts on a blackholed/unresponsive follower,
    /// used to compute exponential redial backoff so a dead WAN host does not stall
    /// the leader's writer thread for `io_timeout` on every batch.
    timeout_failures: u32,
    /// Earliest instant at which a timed-out follower link should be redialed.
    /// Immediate `ConnectionRefused` (local process restart) leaves this `None` so
    /// fast-restarting followers catch up on the very next batch.
    next_dial_at: Option<Instant>,
    /// Optional replication capability attached (`Hello` -> `Nonce` -> `Attach` -> `Mark`)
    /// on initial dial and on every reconnect when replicating to guarded followers.
    #[cfg(feature = "cap")]
    cap: Option<astream_cap::Capability>,
}

#[cfg(feature = "handshake")]
fn confirm_follower_hello(stream: &mut FollowerStream, timeout: Duration) -> io::Result<()> {
    let deadline = Instant::now().checked_add(timeout).ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "follower handshake deadline is too far away",
        )
    })?;
    let mut bounded = Deadlined {
        stream: DeadlineOn::Follower(stream),
        deadline,
    };
    write_frame(&mut bounded, &crate::proto::encode_request(&Request::Hello))?;
    let Some(hello_reply) = read_frame(&mut bounded)? else {
        return Err(io::Error::new(
            io::ErrorKind::UnexpectedEof,
            "follower closed before Hello confirmation",
        ));
    };
    match decode_response(&hello_reply) {
        Some(Response::Nonce { .. }) => {
            bounded.stream.set_read_timeout(Some(timeout))?;
            bounded.stream.set_write_timeout(Some(timeout))?;
            Ok(())
        }
        Some(Response::Error { code, msg }) => Err(io::Error::new(
            if code == ERR_UNAUTHORIZED || msg.starts_with("unauthorized") {
                io::ErrorKind::PermissionDenied
            } else {
                io::ErrorKind::Other
            },
            msg,
        )),
        _ => Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "unexpected follower Hello response",
        )),
    }
}

#[cfg(feature = "cap")]
fn attach_follower_cap(
    stream: &mut FollowerStream,
    cap: &astream_cap::Capability,
    timeout: Duration,
) -> Result<(), (bool, io::Error)> {
    let deadline = Instant::now().checked_add(timeout).ok_or_else(|| {
        (
            false,
            io::Error::new(
                io::ErrorKind::InvalidInput,
                "follower handshake deadline is too far away",
            ),
        )
    })?;
    // One deadline covers the complete Hello/Attach exchange, not each socket read.
    let mut bounded = Deadlined {
        stream: DeadlineOn::Follower(stream),
        deadline,
    };
    write_frame(&mut bounded, &crate::proto::encode_request(&Request::Hello))
        .map_err(|e| (false, e))?;
    let Some(hello_reply) = read_frame(&mut bounded).map_err(|e| (false, e))? else {
        return Err((
            false,
            io::Error::new(io::ErrorKind::UnexpectedEof, "follower closed before Nonce"),
        ));
    };
    let Some(Response::Nonce { nonce, .. }) = decode_response(&hello_reply) else {
        return Err((
            false,
            io::Error::new(
                io::ErrorKind::InvalidData,
                "unexpected follower Hello response",
            ),
        ));
    };
    let proof = astream_cap::attach_proof(&cap.tag, &nonce, &cap.filter);
    let req = Request::Attach {
        grant: cap.filter.clone(),
        proof: proof.to_vec(),
    };
    write_frame(&mut bounded, &crate::proto::encode_request(&req)).map_err(|e| (false, e))?;
    let Some(attach_reply) = read_frame(&mut bounded).map_err(|e| (false, e))? else {
        return Err((
            false,
            io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "follower closed before Attach Mark",
            ),
        ));
    };
    match decode_response(&attach_reply) {
        Some(Response::Mark { .. }) => {
            // Restore the ordinary per-record I/O timeout after the bounded handshake.
            bounded
                .stream
                .set_read_timeout(Some(timeout))
                .map_err(|e| (false, e))?;
            bounded
                .stream
                .set_write_timeout(Some(timeout))
                .map_err(|e| (false, e))?;
            Ok(())
        }
        Some(Response::Error { code, msg }) => {
            let is_unauth = code == ERR_UNAUTHORIZED || msg.starts_with("unauthorized");
            Err((
                is_unauth,
                io::Error::new(
                    if is_unauth {
                        io::ErrorKind::PermissionDenied
                    } else {
                        io::ErrorKind::Other
                    },
                    msg,
                ),
            ))
        }
        _ => Err((
            false,
            io::Error::new(
                io::ErrorKind::InvalidData,
                "unexpected follower Attach response",
            ),
        )),
    }
}

fn encode_replica_record(
    r: &BrokerRecord,
    bt_ms: Option<u64>,
    leader: &crate::LogIdentity,
) -> Vec<u8> {
    let commit = match &r.commit {
        Some(c) => Some((c.group.as_str(), c.upto)),
        None if r.is_marked_retire() => Some((crate::proto::REPLICATE_RETIRE_GROUP, 0)),
        None => None,
    };
    encode_replicate_stamped(
        r.seq.0,
        r.producer_id,
        r.producer_seq,
        &r.subject,
        &r.body,
        commit,
        Some(leader),
        bt_ms,
    )
}

/// Dial a follower TCP socket with the replication timeouts applied.
fn dial_follower_tcp(addr: &str, timeout: Duration) -> io::Result<TcpStream> {
    let mut last = io::Error::new(
        io::ErrorKind::NotFound,
        format!("follower {addr}: no address"),
    );
    for sa in addr.to_socket_addrs()? {
        match TcpStream::connect_timeout(&sa, timeout) {
            Ok(s) => {
                let _ = kept_from_children(&s);
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

#[cfg_attr(not(feature = "handshake"), allow(unused_variables))]
fn upgrade_follower_stream(
    raw: TcpStream,
    transport: &LinkTransport,
    has_cap: bool,
    timeout: Duration,
) -> io::Result<FollowerStream> {
    match transport {
        LinkTransport::Plain => Ok(FollowerStream::Plain(raw)),
        #[cfg(feature = "aead")]
        LinkTransport::Sealed(key) => {
            let sealed = astream_aead::SealedStream::handshake_client(raw, *key)?;
            sealed.get_ref().set_read_timeout(Some(timeout))?;
            sealed.get_ref().set_write_timeout(Some(timeout))?;
            Ok(FollowerStream::Sealed(sealed))
        }
        #[cfg(feature = "handshake")]
        LinkTransport::Handshake(psk) => {
            let sealed = astream_aead::client_handshake(raw, psk)?;
            sealed.get_ref().set_read_timeout(Some(timeout))?;
            sealed.get_ref().set_write_timeout(Some(timeout))?;
            let mut fs = FollowerStream::Sealed(sealed);
            if !has_cap {
                confirm_follower_hello(&mut fs, timeout)?;
            }
            Ok(fs)
        }
        #[cfg(feature = "identity")]
        LinkTransport::Identity {
            identity,
            expected_server,
        } => {
            let sealed = astream_aead::client_identity_handshake(raw, identity, expected_server)?;
            sealed.get_ref().set_read_timeout(Some(timeout))?;
            sealed.get_ref().set_write_timeout(Some(timeout))?;
            let mut fs = FollowerStream::Sealed(sealed);
            if !has_cap {
                confirm_follower_hello(&mut fs, timeout)?;
            }
            Ok(fs)
        }
        #[cfg(feature = "identity")]
        LinkTransport::Certified {
            signer,
            cert,
            trust,
            expected_principal,
        } => {
            let store = trust.snapshot();
            let (sealed, _) = astream_aead::client_cert_handshake(
                raw,
                signer,
                cert,
                &store,
                expected_principal.as_deref(),
                now_unix_ms(),
            )?;
            sealed.get_ref().set_read_timeout(Some(timeout))?;
            sealed.get_ref().set_write_timeout(Some(timeout))?;
            let mut fs = FollowerStream::Sealed(sealed);
            if !has_cap {
                confirm_follower_hello(&mut fs, timeout)?;
            }
            Ok(fs)
        }
    }
}

impl FollowerLink {
    /// Write one window of `records` (at most [`REPLICA_WINDOW`] `Replicate` frames)
    /// into `stream`, flushing in [`EGRESS_CHUNK`] slices.
    fn write_window_frames(
        leader: &crate::LogIdentity,
        stream: &mut FollowerStream,
        window: &[(Arc<BrokerRecord>, Option<u64>)],
    ) -> io::Result<()> {
        let mut out = Vec::new();
        for (r, bt_ms) in window {
            let payload = encode_replica_record(r, *bt_ms, leader);
            append_frame(&mut out, &payload)?;
            if out.len() >= EGRESS_CHUNK {
                flush_egress(stream, &mut out)?;
            }
        }
        flush_egress(stream, &mut out)
    }

    /// Read the acks for `window` in order, advancing `self.upto` past each record the
    /// follower confirms in order. Returns the number of records confirmed (`confirmed == window.len()`
    /// means the full window was confirmed; `< window.len()` means a record was refused
    /// or acked out of order, with the remaining acks in the window drained so `stream`
    /// stays in sync).
    fn read_window_acks(
        &mut self,
        stream: &mut FollowerStream,
        window: &[(Arc<BrokerRecord>, Option<u64>)],
    ) -> io::Result<usize> {
        let mut confirmed = 0usize;
        let mut stopped = false;
        for (r, _) in window {
            let Some(payload) = read_frame(stream)? else {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "follower closed",
                ));
            };
            if stopped {
                continue; // drain, so the stream stays in sync for the next batch
            }
            self.apply_replica_ack(&payload, r.seq.0, &mut confirmed, &mut stopped)?;
        }
        Ok(confirmed)
    }

    fn clear_kill_slot(i: usize, kill: &Mutex<Vec<Option<TcpStream>>>) {
        if let Some(slot) = kill
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .get_mut(i)
        {
            *slot = None;
        }
    }

    /// Pass 1 of pipelined multi-follower replication: write `window` to this
    /// follower's socket without waiting for its acks yet. If a stale link fails on
    /// write, re-dial once and retry writing `window`. Returns `true` if `window` is
    /// now in flight on `self.stream`.
    fn write_window_with_retry(
        &mut self,
        i: usize,
        window: &[(Arc<BrokerRecord>, Option<u64>)],
        fresh_flags: &mut [bool],
        timeout: Duration,
        running: &AtomicBool,
        kill: &Mutex<Vec<Option<TcpStream>>>,
    ) -> bool {
        if !running.load(Ordering::Relaxed) {
            return false;
        }
        let Some(mut stream) = self.stream.take() else {
            return false;
        };
        if Self::write_window_frames(&self.leader, &mut stream, window).is_ok() {
            self.stream = Some(stream);
            return true;
        }
        Self::clear_kill_slot(i, kill);
        drop(stream);
        let was_fresh = fresh_flags.get(i).copied().unwrap_or(true);
        if was_fresh {
            return false;
        }
        if let Some(slot) = fresh_flags.get_mut(i) {
            *slot = true;
        }
        let Some(mut retry_stream) = self.reconnect(i, timeout, running, kill) else {
            return false;
        };
        if Self::write_window_frames(&self.leader, &mut retry_stream, window).is_ok() {
            self.stream = Some(retry_stream);
            true
        } else {
            Self::clear_kill_slot(i, kill);
            drop(retry_stream);
            false
        }
    }

    /// Pass 2 of pipelined multi-follower replication: read the acks for the `window`
    /// written in Pass 1. If a stale link fails mid-read, re-dial once so the next
    /// round resumes from the confirmed `self.upto`. Returns `true` if this follower
    /// can continue to the next window in this batch.
    fn read_window_with_retry(
        &mut self,
        i: usize,
        window: &[(Arc<BrokerRecord>, Option<u64>)],
        fresh_flags: &mut [bool],
        timeout: Duration,
        running: &AtomicBool,
        kill: &Mutex<Vec<Option<TcpStream>>>,
    ) -> bool {
        let Some(mut stream) = self.stream.take() else {
            return false;
        };
        match self.read_window_acks(&mut stream, window) {
            Ok(confirmed) => {
                self.stream = Some(stream);
                confirmed == window.len()
            }
            Err(_) => {
                Self::clear_kill_slot(i, kill);
                drop(stream);
                let was_fresh = fresh_flags.get(i).copied().unwrap_or(true);
                if was_fresh {
                    return false;
                }
                if let Some(slot) = fresh_flags.get_mut(i) {
                    *slot = true;
                }
                match self.reconnect(i, timeout, running, kill) {
                    Some(s) => {
                        self.stream = Some(s);
                        true
                    }
                    None => false,
                }
            }
        }
    }

    fn apply_replica_ack(
        &mut self,
        payload: &[u8],
        seq: u64,
        confirmed: &mut usize,
        stopped: &mut bool,
    ) -> io::Result<()> {
        let Some(resp) = decode_response(payload) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "unexpected follower response",
            ));
        };
        match resp {
            Response::PublishAck { offset, .. } => {
                if offset == seq && self.upto == seq {
                    self.upto =
                        crate::proto::replica_ack_monotone(self.upto, seq.saturating_add(1));
                    *confirmed = confirmed.saturating_add(1);
                } else {
                    // Acked out of order: the confirmed prefix ends here. The rest of the
                    // window is still drained below, so the stream stays in sync and is
                    // reused on the next batch.
                    *stopped = true;
                }
                Ok(())
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
            Response::Error { msg, .. } => {
                if msg.starts_with("replica gap") {
                    self.upto = 0;
                } else if msg.starts_with("replica diverged")
                    || msg.starts_with("replica fenced")
                    || msg.starts_with("unauthorized")
                {
                    self.fenced = Some(msg);
                }
                *stopped = true;
                Ok(())
            }
            _ => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "unexpected follower response",
            )),
        }
    }

    fn note_dial_error(&mut self, e: &io::Error) {
        if matches!(
            e.kind(),
            io::ErrorKind::TimedOut | io::ErrorKind::WouldBlock
        ) {
            let backoff = Duration::from_millis(follower_backoff_ms(self.timeout_failures));
            self.timeout_failures = self.timeout_failures.saturating_add(1);
            self.next_dial_at = Some(Instant::now() + backoff);
        } else {
            self.timeout_failures = 0;
            self.next_dial_at = None;
        }
    }

    fn reconnect(
        &mut self,
        i: usize,
        timeout: Duration,
        running: &AtomicBool,
        kill: &Mutex<Vec<Option<TcpStream>>>,
    ) -> Option<FollowerStream> {
        if !running.load(Ordering::Relaxed) {
            return None;
        }
        match dial_follower_tcp(&self.addr, timeout) {
            Ok(raw) => {
                let Ok(shutdown) = raw.try_clone() else {
                    return None;
                };
                let _ = kept_from_children(&shutdown);
                {
                    let mut slots = kill
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner);
                    if !running.load(Ordering::Relaxed) {
                        let _ = raw.shutdown(Shutdown::Both);
                        return None;
                    }
                    let Some(slot) = slots.get_mut(i) else {
                        let _ = raw.shutdown(Shutdown::Both);
                        return None;
                    };
                    *slot = Some(shutdown);
                }
                #[cfg(feature = "cap")]
                let has_cap = self.cap.is_some();
                #[cfg(not(feature = "cap"))]
                let has_cap = false;
                #[allow(unused_mut)]
                let mut s = match upgrade_follower_stream(raw, &self.transport, has_cap, timeout) {
                    Ok(fs) => fs,
                    Err(e) => {
                        Self::clear_kill_slot(i, kill);
                        self.note_dial_error(&e);
                        return None;
                    }
                };
                #[cfg(feature = "cap")]
                if let Some(ref cap) = self.cap {
                    if let Err((is_unauth, e)) = attach_follower_cap(&mut s, cap, timeout) {
                        Self::clear_kill_slot(i, kill);
                        if is_unauth {
                            self.fenced = Some(e.to_string());
                            self.timeout_failures = 0;
                            self.next_dial_at = None;
                        } else {
                            self.note_dial_error(&e);
                        }
                        return None;
                    }
                }
                self.timeout_failures = 0;
                self.next_dial_at = None;
                if !running.load(Ordering::Relaxed) {
                    Self::clear_kill_slot(i, kill);
                    let _ = s.shutdown(Shutdown::Both);
                    return None;
                }
                Some(s)
            }
            Err(e) => {
                self.note_dial_error(&e);
                None
            }
        }
    }
}

impl Replicator {
    /// Un-fence every fenced follower link on the writer thread, closing any open socket,
    /// clearing redial backoff, and resetting `upto` to `floor` (the leader's retention
    /// base) so the immediately following `redial` + `replicate` catches the follower up
    /// across `[floor..head)` and restores its adopted leader `LogIdentity`.
    fn rejoin(&self, floor: u64) -> usize {
        let mut links = self
            .links
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let mut rejoined = 0usize;
        for (i, link) in links.iter_mut().enumerate() {
            if link.fenced.take().is_some() {
                if let Some(s) = link.stream.take() {
                    let _ = s.shutdown(Shutdown::Both);
                }
                FollowerLink::clear_kill_slot(i, &self.kill);
                link.fresh = false;
                link.timeout_failures = 0;
                link.next_dial_at = None;
                link.upto = floor;
                rejoined = rejoined.saturating_add(1);
            }
        }
        rejoined
    }

    /// Re-dial every follower whose link is down (and not fenced) — at the start of a
    /// batch, before it reads the log for them. One that answers is caught up in this
    /// same batch; one still down is left out of the re-ship base (`min_upto`).
    ///
    /// A follower whose prior redial timed out (blackholed host) is skipped until its
    /// exponential backoff window elapses, preventing per-batch `io_timeout` stalls on
    /// the writer thread.
    fn redial(&self, running: &AtomicBool) {
        let mut links = self
            .links
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let now = Instant::now();
        for (i, link) in links.iter_mut().enumerate() {
            link.fresh = false; // fresh only for the batch that dialed it
            let dial_ready = match link.next_dial_at {
                Some(t) => now >= t,
                None => true,
            };
            if link.fenced.is_none() && link.stream.is_none() && dial_ready {
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
        let links = self
            .links
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let mut min_val: Option<u64> = None;
        for l in links.iter() {
            if l.fenced.is_none() && l.stream.is_some() && l.upto >= floor {
                min_val = Some(match min_val {
                    Some(m) => m.min(l.upto),
                    None => l.upto,
                });
            }
        }
        min_val.unwrap_or(fallback)
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
    fn replicate(&self, records: &[(Arc<BrokerRecord>, Option<u64>)], running: &AtomicBool) -> u64 {
        let mut links = self
            .links
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let Some((first, _)) = records.first() else {
            return Self::watermark(&links, self.quorum);
        };
        let base = first.seq.0;
        let mut fresh_flags: Vec<bool> = Vec::new();
        let mut done: Vec<bool> = Vec::new();
        for link in links.iter_mut() {
            let is_done = link.fenced.is_some() || link.stream.is_none() || link.upto < base;
            fresh_flags.push(std::mem::take(&mut link.fresh));
            done.push(is_done);
        }
        // Two-phase pipelined shipping across all followers in lockstep windows:
        // Pass 1 writes up to REPLICA_WINDOW frames to every active follower's TCP
        // socket before Pass 2 blocks reading any follower's acks, overlapping network
        // RTT and follower processing across all replicas in parallel.
        let mut in_flight: Vec<Option<(usize, usize)>> = Vec::new();
        while running.load(Ordering::Relaxed) {
            in_flight.clear();
            let mut any_sent = false;
            for (i, link) in links.iter_mut().enumerate() {
                if done.get(i).copied().unwrap_or(true) || link.fenced.is_some() {
                    in_flight.push(None);
                    continue;
                }
                let Some(skip) = link.upto.checked_sub(base) else {
                    if let Some(d) = done.get_mut(i) {
                        *d = true;
                    }
                    in_flight.push(None);
                    continue;
                };
                let pos = usize::try_from(skip)
                    .unwrap_or(usize::MAX)
                    .min(records.len());
                let rem = records.len().saturating_sub(pos);
                if rem == 0 {
                    if let Some(d) = done.get_mut(i) {
                        *d = true;
                    }
                    in_flight.push(None);
                    continue;
                }
                let want = rem.min(REPLICA_WINDOW);
                let Some(window) = records.get(pos..pos.saturating_add(want)) else {
                    if let Some(d) = done.get_mut(i) {
                        *d = true;
                    }
                    in_flight.push(None);
                    continue;
                };
                if link.write_window_with_retry(
                    i,
                    window,
                    &mut fresh_flags,
                    self.io_timeout,
                    running,
                    &self.kill,
                ) {
                    any_sent = true;
                    in_flight.push(Some((pos, want)));
                } else {
                    if let Some(d) = done.get_mut(i) {
                        *d = true;
                    }
                    in_flight.push(None);
                }
            }
            if !any_sent {
                break;
            }
            for (i, link) in links.iter_mut().enumerate() {
                let Some((pos, want)) = in_flight.get(i).copied().flatten() else {
                    continue;
                };
                let Some(window) = records.get(pos..pos.saturating_add(want)) else {
                    if let Some(d) = done.get_mut(i) {
                        *d = true;
                    }
                    continue;
                };
                if !link.read_window_with_retry(
                    i,
                    window,
                    &mut fresh_flags,
                    self.io_timeout,
                    running,
                    &self.kill,
                ) {
                    if let Some(d) = done.get_mut(i) {
                        *d = true;
                    }
                }
            }
        }
        Self::watermark(&links, self.quorum)
    }

    fn watermark(links: &[FollowerLink], quorum: usize) -> u64 {
        let mut uptos: Vec<u64> = Vec::new();
        for l in links {
            uptos.push(l.upto);
        }
        uptos.sort_unstable();
        uptos.reverse();
        uptos.get(quorum.saturating_sub(1)).copied().unwrap_or(0)
    }

    /// Force-close every live follower socket so a writer parked on a follower that
    /// never answers returns immediately (shutdown must not wait out the I/O timeout).
    fn shutdown_links(&self) {
        for k in self
            .kill
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .iter_mut()
        {
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
    fences_gaps: Cell<bool>,
}
impl Drop for ConnGuard<'_> {
    fn drop(&mut self) {
        self.shared
            .conns
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .remove(&self.id);
        self.shared
            .attached_conns
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .remove(&self.id);
        if self.fences_gaps.get() {
            // The pipeline is declared after this guard, so its held run reaches this same
            // queue first on every return from `serve_conn`. Clear the connection's fences
            // only once the writer has judged those writes: clearing here lets a clean close
            // race an already-decoded successor and admit it after its predecessor failed.
            let _ = self.shared.writes.send(Queued::DropFences(self.id));
        }
    }
}

/// Operational snapshot of a running [`Broker`] (`REQUIREMENTS` R5).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BrokerStats {
    /// Relayed records refused for what they are ([`ERR_ORIGIN_REFUSED`]): a bad signature, or a
    /// record that is not its origin's.
    pub origin_refused: u64,
    /// Answers that a relayed record's origin is not one this broker takes now
    /// ([`ERR_ORIGIN_UNKNOWN`]): no key, or a revoked one. Each answer counts, so a record its
    /// carrier holds and offers again counts each time.
    pub origin_unknown: u64,
    /// Snapshot of the underlying durable [`BrokerLog`].
    pub log: LogStats,
    /// Subscriber-visible head offset (the durable head in Strict/Relaxed, or the
    /// quorum watermark in Replicated).
    pub visible_head: u64,
    /// Number of currently open client connections.
    pub active_conns: usize,
    /// Number of currently active [`BrokerHandle`] listeners.
    pub active_listeners: usize,
    /// Connections this broker's acceptors have handed to a connection thread, over
    /// the broker's life and every listener.
    pub accepted: u64,
    /// Times an acceptor thread resumed from a blocking wait: an `accept()` that
    /// returned, in the normal blocking mode, or a poll sleep that ended. A blocking
    /// acceptor wakes once per connection and never while idle (shutdown's wakeup dial
    /// is one more), so this tracks [`accepted`](Self::accepted); a polling one
    /// ([`BrokerHandle::blocks_in_accept`] `false`) wakes per sleep.
    pub acceptor_wakeups: u64,
    /// Times an acceptor slept: a polling listener's sleep between `accept()` calls,
    /// or any listener's back-off after an `accept()` error such as fd exhaustion.
    /// Zero for blocking listeners that met no such error — no connection waits out a
    /// sleep.
    pub acceptor_sleeps: u64,
    /// Blocking acceptors that shutdown could not dial out of `accept()` and left
    /// parked: no name reached the listener any more (an embedder removed both the
    /// socket path and `<socket>.wake`), its TCP address no longer connects, or some
    /// OTHER listener answered every dial (on macOS a socket bound to `127.0.0.1:P`
    /// beside a `0.0.0.0:P` broker; the winner of a `serve` that raced this one past its
    /// bind). Zero in any embedding that leaves the broker's names and port alone.
    pub acceptors_abandoned: u64,
    /// Durable mutations a connection thread queued to the writer and then WAITED on
    /// before answering its request: a principal's first `Bind` at attach, and a
    /// `Will` registration. (Pipelined publishes are not counted: their acks stream
    /// back without the connection thread waiting on each.) Each one queues behind
    /// whatever batch the writer is in, fsync included. An attach whose principal is
    /// already durably bound adds nothing here (see
    /// [`binds_settled`](Self::binds_settled)).
    pub writer_round_trips: u64,
    /// Batches the writer thread has processed, committed or refused, empty or not.
    pub writer_batches: u64,
    /// Times the writer thread resumed from its wait with nothing queued: only the
    /// Ordered horizon falling due, which owes a full flush
    /// ([`Durability::Ordered`]). Otherwise an idle writer sleeps until work, or the
    /// stop shutdown queues, arrives, so on every other tier this stays 0 for the
    /// broker's life, its shutdown included: shutdown never waits out a timer.
    pub writer_wakeups: u64,
    /// Writer batches that appended no record: every op in them deduplicated, was
    /// refused, or (an attach re-binding a principal the writer found bound) had
    /// nothing to append. In the Strict and Relaxed tiers none wakes a subscriber tail.
    /// In the Replicated tier one can: appending nothing is not shipping nothing, and
    /// an empty batch still ships whatever its followers lack, so a batch that only
    /// re-sends a publish refused for want of a quorum, and confirms it, makes that
    /// record visible and wakes the tails (see
    /// [`tail_broadcasts`](Self::tail_broadcasts)).
    pub empty_batches: u64,
    /// Read-write grants naming a principal whose attach found that principal already
    /// durably bound to its producer id, below the visible head, and so made no writer
    /// round trip: the second and later `rw,p=` grants of one principal on a
    /// connection, and every one of them on a later connection or a later open.
    pub binds_settled: u64,
    /// Wills the writer has SETTLED. A connection that ends holding a registered will
    /// queues the will's firing (or, when the capability behind it lapsed or its peer's
    /// identity was revoked, its drop), and an open queues a firing for each will the
    /// log holds. Each is counted here once the batch that staged it has ended and
    /// published its head, whatever the firing came to: the goodbye appended, deduped
    /// against a record already under its key, fenced by a later record of its
    /// producer, refused on a replica, or rolled back with a failed batch (the next open
    /// fires it again).
    ///
    /// A will that comes to NOTHING leaves no record to wait for, so this is how a
    /// reader knows it has come to nothing. The writer takes its queue in order: once
    /// this reads N, the first N wills queued have been staged, whatever they appended
    /// is in the log, and a write queued afterwards lands above it.
    /// [`active_conns`](Self::active_conns) cannot say the same: a connection leaves
    /// that set when its requests end, BEFORE it queues its will.
    pub wills_settled: u64,
    /// Times the writer woke every parked subscriber tail at once (one `notify_all` on
    /// the log's `Condvar`) after a batch: only after a batch that made a record some
    /// subscriber could be delivered visible. A batch that made nothing visible or only
    /// hidden records (a group commit, a will registration, a binding, a retirement)
    /// wakes nobody, so `writer_batches - tail_broadcasts` counts those. What a batch
    /// makes visible depends on the tier. In Strict and Relaxed it is the batch's own
    /// appends, so an empty batch ([`empty_batches`](Self::empty_batches)) never
    /// broadcasts. In Replicated it is what the quorum watermark the batch publishes
    /// newly passed, whichever batch appended it: an empty or hidden-only batch whose
    /// ship confirms an earlier publish broadcasts for it, and a batch whose own
    /// publish no quorum confirmed does not. Revocation and shutdown wake the tails
    /// too, and are not counted here.
    pub tail_broadcasts: u64,
    /// Per-subscriber `notify_one` wakeups emitted by the writer when
    /// [`Broker::selective_tail_wake`] is active (`cost study B4 step 2`).
    pub selective_tail_wakes: u64,
    /// `Publish` and `ProcessAndProduce` requests refused with [`ERR_RATE_LIMITED`] by
    /// [`Broker::set_rate_limit`] (`DESIGN-aterm-fabric` T9 & T17).
    pub rate_limited: u64,
    /// Times a parked subscriber tail resumed from its wait: woken by a writer
    /// broadcast, a revocation or shutdown, or at the end of its liveness poll
    /// ([`Broker::set_liveness_poll`]). A broadcast resumes every tail parked at that
    /// moment, whatever its filter, so with S parked tails each broadcast adds S.
    pub tail_wakeups: u64,
    /// Liveness probes subscriber tails made: a one-byte read of the subscriber's own
    /// socket that answers whether its peer has gone. A tail that writes nothing — its
    /// filter matched nothing it read — has no other way to learn its subscriber left.
    pub peer_probes: u64,
    /// Subscriber tails parked right now, waiting for the visible head to pass their
    /// cursor. Each is counted under the log lock as it goes to wait — the lock the
    /// writer publishes the head under — so a batch whose head is published after a
    /// read of N here finds those N tails waiting.
    pub parked_tails: usize,
    /// Retention calls (`Broker::retain_before`, `Broker::retain_before_carrying_state`,
    /// `Broker::set_retention` and a retention tick, the `retention` feature's) that found
    /// the writer's batch lock (`Shared::batch`) taken and waited for it, at the
    /// compaction's begin or at its finish, or before the rules are written — counted once
    /// per call, not once per wait. The writer writes and flushes a batch with the log lock
    /// released, so retention, which rewrites the file, waits on that lock instead — for
    /// the batch the writer is in to commit or roll back. Two retention calls made at once queue on a lock of their own
    /// (`Shared::compaction`), which this does not count, so what it counts is retention
    /// that waited for a batch.
    pub retention_waits: u64,
    /// Retention ticks run (`Broker::set_retention`): by the tick's thread, asked for by
    /// a batch or the interval, and by `Broker::retention_tick_at`. `0` on a broker
    /// nothing retains, which never ticks.
    pub retention_ticks: u64,
    /// The retention tick's thread's ticks SKIPPED because a compaction (a retention call's,
    /// or an explicit `Broker::retention_tick_at`) was under way: the next batch over a
    /// bound, or the next interval, asks again.
    pub retention_skips: u64,
}

const fn follower_backoff_ms(timeout_failures: u32) -> u64 {
    let shift = if timeout_failures < 5 {
        timeout_failures
    } else {
        5
    };
    100u64 << shift
}

const fn hex_byte_chars(b: u8) -> (char, char) {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    (
        HEX[(b >> 4) as usize] as char,
        HEX[(b & 0x0f) as usize] as char,
    )
}

const fn hex_nibble_digit(b: u8) -> u8 {
    match b {
        b'0' => 0,
        b'1' => 1,
        b'2' => 2,
        b'3' => 3,
        b'4' => 4,
        b'5' => 5,
        b'6' => 6,
        b'7' => 7,
        b'8' => 8,
        b'9' => 9,
        b'a' | b'A' => 10,
        b'b' | b'B' => 11,
        b'c' | b'C' => 12,
        b'd' | b'D' => 13,
        b'e' | b'E' => 14,
        b'f' | b'F' => 15,
        _ => 0,
    }
}

const fn pack_hex_byte(b0: u8, b1: u8) -> u8 {
    let hi = (hex_nibble_digit(b0) & 0x0f) << 4;
    let lo = hex_nibble_digit(b1) & 0x0f;
    hi | lo
}

/// Derive the canonical node principal name (`n-<16 lowercase hex chars>`) from a
/// 32-byte Ed25519 identity public key (`REQUIREMENTS` R6).
///
/// When a client connects over `Broker::serve_tcp_identity`, its transport-layer
/// Ed25519 public key is cryptographically verified by the SIGMA handshake. Any
/// capability grant attached on that connection whose principal has the node-identity
/// shape (`n-` followed by 16 hex digits) MUST match `identity_principal(&peer_pubkey)`
/// or `Attach` is refused — preventing a compromised host from attaching a capability
/// minted for another node's principal.
#[must_use]
pub fn identity_principal(pubkey: &[u8; 32]) -> String {
    let mut out = String::with_capacity(18);
    out.push_str("n-");
    for &b in &pubkey[..8] {
        let (hi, lo) = hex_byte_chars(b);
        out.push(hi);
        out.push(lo);
    }
    out
}

/// Whether `principal` has the node-identity principal shape (`n-` + 16 hex digits).
#[cfg(feature = "cap")]
fn is_identity_shaped_principal(principal: &str) -> bool {
    let Some(hex_part) = principal.strip_prefix("n-") else {
        return false;
    };
    if hex_part.len() != 16 {
        return false;
    }
    for &b in hex_part.as_bytes() {
        if !b.is_ascii_hexdigit() {
            return false;
        }
    }
    true
}

/// The refusal of an empty capability secret: an HMAC under an empty key is computable
/// by anyone, so it would admit any capability anyone cares to mint.
fn empty_secret() -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidInput,
        "open_guarded: the capability secret is empty, so anyone could mint a \
         capability it accepts",
    )
}

/// A broker over one durable [`BrokerLog`].
pub struct Broker {
    shared: Arc<Shared>,
}

impl Broker {
    /// Open (creating if absent) a broker backed by the Strict durable log at `log_path`.
    pub fn open(log_path: impl AsRef<Path>) -> io::Result<Broker> {
        Broker::open_with(log_path, Durability::Strict)
    }

    /// Open a broker at the given [`Durability`] tier (Strict fsyncs every batch;
    /// Ordered acks on an ordering barrier — a power loss leaves a prefix of whole
    /// batches, the newest possibly lost and announced; Relaxed acks on page-cache write
    /// — lower latency, survives process crash but not power loss). No escalation table
    /// (that is [`open_opts`](Self::open_opts)'s). The log is exclusively locked while
    /// open (a second broker on the same log fails `AlreadyExists`), and refuses to open
    /// a corrupt log — see [`BrokerLog::open_with`].
    pub fn open_with(log_path: impl AsRef<Path>, durability: Durability) -> io::Result<Broker> {
        let log = BrokerLog::open_with(log_path, durability)?;
        Ok(Self::start(log, None, None, false))
    }

    /// Open at `durability`, preparing embedder sidecars under the log's own lock.
    ///
    /// `prepare` runs once after the file is opened, exclusively locked where
    /// advisory locks are supported, and its directory synced. It runs before
    /// recovery or identity sidecar reads. The same file remains owned through
    /// recovery and by the returned broker; no writer starts before preparation
    /// and recovery both succeed. A busy log refuses before calling `prepare`.
    ///
    /// The callback must not remove, replace, truncate, or otherwise change the
    /// log file itself. It may prepare its own sidecars, and must make those
    /// changes crash safe: a callback error or later recovery error does not roll
    /// them back. A newly created log may remain after an error. Callback errors
    /// propagate unchanged, releasing the file lock on return or unwind.
    pub fn open_with_prepare(
        log_path: impl AsRef<Path>,
        durability: Durability,
        prepare: impl FnOnce() -> io::Result<()>,
    ) -> io::Result<Broker> {
        let log = BrokerLog::open_with_prepare(log_path, durability, prepare)?;
        Ok(Self::start(log, None, None, false))
    }

    /// Open a broker as `opts` say — the open the other constructors are shorthands
    /// for: [`BrokerLog::open_opts`] (the tier, the escalation table, the boot and volume
    /// the identity rules read, the embedder's `prepare` and its [`Prepared`] verdict),
    /// plus, with the `cap`
    /// feature, `opts.guard`: `Some(secret)` enforces capabilities as
    /// `open_guarded` does, an empty secret refused before the log
    /// is opened or `prepare` runs; and `opts.health_every`: `Some(period)` keeps the
    /// health sidecar `<log>.health` from the open on ([`keep_health`](Self::keep_health)).
    pub fn open_opts(
        log_path: impl AsRef<Path>,
        opts: OpenOptions,
        prepare: impl FnOnce() -> io::Result<Prepared>,
    ) -> io::Result<Broker> {
        Self::open_opts_on(opts, |opts| BrokerLog::open_opts(log_path, opts, prepare))
    }

    /// [`open_opts`](Self::open_opts) on a SIMULATED DEVICE ([`SimDevice`](crate::SimDevice))
    /// in place of a file, with nothing to prepare ([`BrokerLog::open_sim`]): the whole
    /// broker — its writer, its flushes, its clean close — over a device a test can take
    /// every power-loss image of once the broker is stopped. Retention's rewrite refuses
    /// on it, and `opts.health_every` is refused here: the health sidecar is a file.
    ///
    /// # Errors
    ///
    /// Whatever [`open_opts`](Self::open_opts) and [`BrokerLog::open_sim`] refuse, and
    /// `InvalidInput` for `opts.health_every`.
    #[cfg(any(test, debug_assertions))]
    pub fn open_sim(device: &crate::SimDevice, opts: OpenOptions) -> io::Result<Broker> {
        if opts.health_every.is_some() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "a simulated log keeps no health sidecar",
            ));
        }
        Self::open_opts_on(opts, |opts| BrokerLog::open_sim(device, opts))
    }

    /// [`open_opts`](Self::open_opts) with the log opened by `open`: what is refused before
    /// the log is opened, the open, and what the broker sets up after it.
    fn open_opts_on(
        opts: OpenOptions,
        open: impl FnOnce(OpenOptions) -> io::Result<BrokerLog>,
    ) -> io::Result<Broker> {
        // The writer acks each batch at its publish: a log recorded as acked only at a full
        // flush would hide the loss of those acks after an unclean stop.
        if opts.acks != crate::store::Acks::Publish {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "a broker acks at its writer's publish: Acks::FullFlush is for a BrokerLog \
                 used directly",
            ));
        }
        #[cfg(feature = "cap")]
        let guard = opts.guard.clone();
        #[cfg(not(feature = "cap"))]
        let guard: Option<Vec<u8>> = None;
        if let Some(g) = &guard {
            if g.is_empty() {
                return Err(empty_secret());
            }
        }
        let rate_limit = match opts.rate_limit {
            None => None,
            Some(lim) => match lim.validate() {
                Ok(valid) => Some(valid),
                Err(msg) => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("invalid rate_limit: {msg}"),
                    ));
                }
            },
        };
        let health_every = opts.health_every;
        let selective_tail_wake = opts.selective_tail_wake;
        let sticky_batch_refusal = opts.sticky_batch_refusal;
        let log = open(opts)?;
        let broker = Self::start(log, None, guard, sticky_batch_refusal);
        if selective_tail_wake {
            broker.set_selective_tail_wake(true);
        }
        if let Some(lim) = rate_limit {
            broker.set_rate_limit(Some(lim))?;
        }
        if let Some(every) = health_every {
            // The open has happened (and fired the wills the log held): a sidecar it
            // cannot write is said, not a refused open — the thread tries again every
            // period, and `write_health` answers an embedder that must know.
            if let Err(e) = broker.keep_health(every) {
                eprintln!(
                    "astream-broker: {}: could not write its health sidecar ({e}); trying \
                     again every {} ms",
                    broker.shared.log_path.display(),
                    every.as_millis()
                );
            }
        }
        Ok(broker)
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
        Ok(Self::start(log, None, None, false))
    }

    /// [`open_replica`](Self::open_replica) with capability enforcement on the accept
    /// path (see [`open_guarded`](Self::open_guarded)). Every connection to this
    /// follower — including the leader's replication link — must `Attach` a capability
    /// signed under `secret` before its requests are served; an unbound read-write
    /// capability is required for `Request::Replicate`. Strict durability by default.
    #[cfg(feature = "cap")]
    pub fn open_replica_guarded(log_path: impl AsRef<Path>, secret: Vec<u8>) -> io::Result<Broker> {
        Self::open_replica_guarded_with(log_path, secret, Durability::Strict)
    }

    /// [`open_replica_guarded`](Self::open_replica_guarded) at an explicit
    /// [`Durability`] tier.
    #[cfg(feature = "cap")]
    pub fn open_replica_guarded_with(
        log_path: impl AsRef<Path>,
        secret: Vec<u8>,
        durability: Durability,
    ) -> io::Result<Broker> {
        if secret.is_empty() {
            return Err(empty_secret());
        }
        let mut log = BrokerLog::open_with(log_path, durability)?;
        log.declare_replica()?;
        Ok(Self::start(log, None, Some(secret), false))
    }

    /// Open a broker whose durable log is ENCRYPTED AT REST: every record's payload
    /// is sealed on disk under `key` (XChaCha20-Poly1305, bound to `<log>.seal` on v2
    /// logs), so the forensic value of the log — a verbatim recording of every keystroke
    /// and screen frame — is gone to anyone without the key. The wire protocol and all
    /// in-memory behaviour are unchanged; recovery decrypts, and refuses (rather than
    /// discards) on a wrong key, cross-log splice, or tampered log. Off by default (the
    /// `at-rest` feature). Strict.
    #[cfg(feature = "at-rest")]
    pub fn open_encrypted(log_path: impl AsRef<Path>, key: [u8; 32]) -> io::Result<Broker> {
        let log = BrokerLog::open_encrypted(log_path, key)?;
        Ok(Self::start(log, None, None, false))
    }

    /// [`open_encrypted`](Self::open_encrypted) at a chosen [`Durability`].
    #[cfg(feature = "at-rest")]
    pub fn open_encrypted_with(
        log_path: impl AsRef<Path>,
        durability: Durability,
        key: [u8; 32],
    ) -> io::Result<Broker> {
        let log = BrokerLog::open_encrypted_with(log_path, durability, key)?;
        Ok(Self::start(log, None, None, false))
    }

    /// Like [`open_encrypted`](Self::open_encrypted), additionally refusing legacy v1
    /// unbound encrypted logs that lack `<log>.seal` (`Astream.Broker.TlaAtRestLogBinding`).
    #[cfg(feature = "at-rest")]
    pub fn open_encrypted_bound(log_path: impl AsRef<Path>, key: [u8; 32]) -> io::Result<Broker> {
        let log = BrokerLog::open_encrypted_bound(log_path, key)?;
        Ok(Self::start(log, None, None, false))
    }

    /// [`open_encrypted_bound`](Self::open_encrypted_bound) at a chosen [`Durability`].
    #[cfg(feature = "at-rest")]
    pub fn open_encrypted_bound_with(
        log_path: impl AsRef<Path>,
        durability: Durability,
        key: [u8; 32],
    ) -> io::Result<Broker> {
        let log = BrokerLog::open_encrypted_bound_with(log_path, durability, key)?;
        Ok(Self::start(log, None, None, false))
    }

    /// Open a broker combining CAPABILITY ENFORCEMENT (`secret`, as
    /// [`open_guarded`](Self::open_guarded)) with ENCRYPT-AT-REST (`key`, as
    /// [`open_encrypted`](Self::open_encrypted)). Strict durability.
    #[cfg(all(feature = "cap", feature = "at-rest"))]
    pub fn open_guarded_encrypted(
        log_path: impl AsRef<Path>,
        secret: Vec<u8>,
        key: [u8; 32],
    ) -> io::Result<Broker> {
        Self::open_guarded_encrypted_with(log_path, secret, Durability::Strict, key)
    }

    /// [`open_guarded_encrypted`](Self::open_guarded_encrypted) at a chosen [`Durability`].
    #[cfg(all(feature = "cap", feature = "at-rest"))]
    pub fn open_guarded_encrypted_with(
        log_path: impl AsRef<Path>,
        secret: Vec<u8>,
        durability: Durability,
        key: [u8; 32],
    ) -> io::Result<Broker> {
        let mut opts = OpenOptions::new(durability);
        opts.guard = Some(secret);
        opts.at_rest_key = Some(key);
        Self::open_opts(log_path, opts, || Ok(Prepared::Nothing))
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
        Ok(Self::start(log, None, None, false))
    }

    /// Bootstrap [`open_encrypted_verified`](Self::open_encrypted_verified): establish
    /// the head watermark at the current head (first adoption of anti-rollback).
    #[cfg(feature = "anti-rollback")]
    pub fn open_encrypted_verified_init(
        log_path: impl AsRef<Path>,
        key: [u8; 32],
    ) -> io::Result<Broker> {
        let log = BrokerLog::open_encrypted_verified_init(log_path, key)?;
        Ok(Self::start(log, None, None, false))
    }

    /// Open a broker combining CAPABILITY ENFORCEMENT (`secret`), ENCRYPT-AT-REST (`key`),
    /// and ANTI-ROLLBACK verification (`<log>.hw`). Strict durability.
    #[cfg(all(feature = "cap", feature = "anti-rollback"))]
    pub fn open_guarded_encrypted_verified(
        log_path: impl AsRef<Path>,
        secret: Vec<u8>,
        key: [u8; 32],
    ) -> io::Result<Broker> {
        let mut opts = OpenOptions::new(Durability::Strict);
        opts.guard = Some(secret);
        opts.at_rest_key = Some(key);
        opts.anti_rollback = crate::AntiRollback::Verify;
        Self::open_opts(log_path, opts, || Ok(Prepared::Nothing))
    }

    /// Bootstrap [`open_guarded_encrypted_verified`](Self::open_guarded_encrypted_verified):
    /// establish `<log>.hw` at the current head while enforcing capabilities under `secret`.
    #[cfg(all(feature = "cap", feature = "anti-rollback"))]
    pub fn open_guarded_encrypted_verified_init(
        log_path: impl AsRef<Path>,
        secret: Vec<u8>,
        key: [u8; 32],
    ) -> io::Result<Broker> {
        let mut opts = OpenOptions::new(Durability::Strict);
        opts.guard = Some(secret);
        opts.at_rest_key = Some(key);
        opts.anti_rollback = crate::AntiRollback::Init;
        Self::open_opts(log_path, opts, || Ok(Prepared::Nothing))
    }

    /// The 128-bit per-log cryptographic at-rest binding (`<log>.seal`), or `None` when
    /// unencrypted or opened on a legacy v1 unbound log.
    #[cfg(feature = "at-rest")]
    #[must_use]
    pub fn at_rest_seal_id(&self) -> Option<[u8; 16]> {
        self.shared
            .log
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .at_rest_seal_id()
    }

    /// RETENTION: compact the durable log, dropping records with offset `< min_offset`
    /// (kept records keep their absolute offsets). A consumer below the new base
    /// catches up from the earliest retained. Returns the number of records dropped. Off
    /// by default (the `retention` feature).
    ///
    /// OFF THE ACK PATH. The compaction begins between batches — it waits for a batch the
    /// writer is in the middle of, its write and flush included
    /// ([`BrokerStats::retention_waits`]) — and settles its floor there. Then it copies
    /// the kept suffix to the durable length it began at with NEITHER the log lock NOR
    /// the writer's batch lock held: those bytes are durable and nothing rewrites them, so
    /// the writer commits and acks batches meanwhile. Only the bytes appended since the
    /// begin are copied under both locks, before the switch. Crash-safe: an open after a
    /// crash anywhere in it finishes or discards it ([`BrokerLog::retain_before`]).
    /// Compactions run one at a time.
    ///
    /// REFUSED (`InvalidInput`) for a `min_offset` above the subscriber-visible head:
    /// records at or above it are committed but not yet shown — a batch held for the full
    /// flush its escalated record owes, or (Replicated) records no quorum holds yet — and
    /// pruning them would drop records no reader could ever have been delivered.
    #[cfg(feature = "retention")]
    pub fn retain_before(&self, min_offset: u64) -> io::Result<u64> {
        self.compact(min_offset, false)
    }

    /// THE BROKER'S COMPACTION, off the ack path (see [`retain_before`](Self::retain_before)):
    /// begin between batches, copy with no lock held, finish between batches.
    #[cfg(feature = "retention")]
    fn compact(&self, min_offset: u64, carry_state: bool) -> io::Result<u64> {
        // Count a wait, but recover a poisoned compaction gate: it guards no data.
        let _one = match self.shared.compaction.try_lock() {
            Ok(held) => held,
            Err(std::sync::TryLockError::Poisoned(poisoned)) => poisoned.into_inner(),
            Err(std::sync::TryLockError::WouldBlock) => {
                self.shared.compaction_waits.fetch_add(1, Ordering::Relaxed);
                self.shared
                    .compaction
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner)
            }
        };
        let mut waited = false;
        let begun = {
            // A poisoned try-lock already owns its guard. Panic with that guard;
            // taking the lock again here would wait on this same thread forever.
            let _batch = match self.shared.batch.try_lock() {
                Ok(held) => held,
                Err(std::sync::TryLockError::WouldBlock) => {
                    record_retention_wait(&self.shared, &mut waited);
                    self.shared
                        .batch
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner)
                }
                Err(std::sync::TryLockError::Poisoned(poisoned)) => {
                    panic!("retention: the writer panicked inside a batch ({poisoned})")
                }
            };
            let mut log = self
                .shared
                .log
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            self.refuse_above_visible(min_offset.min(log.head().0))?;
            let begun = log.compact_begin(Offset(min_offset), carry_state);
            // A log its rules retain planned at that floor: the writer asks by it.
            publish_retention(&self.shared, &log);
            begun?
        };
        let Some(mut c) = begun else {
            return Ok(0);
        };
        // The bulk of the copy: no lock held, so no publish's ack waits for it.
        if let Err(e) = c.copy() {
            self.shared
                .log
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .compact_abandon(c);
            return Err(e);
        }
        let _batch = match self.shared.batch.try_lock() {
            Ok(held) => held,
            Err(std::sync::TryLockError::WouldBlock) => {
                record_retention_wait(&self.shared, &mut waited);
                self.shared
                    .batch
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner)
            }
            Err(std::sync::TryLockError::Poisoned(poisoned)) => {
                panic!("retention: the writer panicked inside a batch ({poisoned})")
            }
        };
        let mut log = self
            .shared
            .log
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let dropped = log.compact_finish(c);
        publish_retention(&self.shared, &log);
        dropped
    }

    /// The guard both retention calls take, with the log lock held (the visible head is
    /// published under it). `min_offset` is what retention would take: clamped to the
    /// head, as `retain_before` itself clamps it, so a call that asks for "everything" is
    /// refused only while some committed record is not yet visible.
    #[cfg(feature = "retention")]
    fn refuse_above_visible(&self, min_offset: u64) -> io::Result<()> {
        let visible = self.shared.head.load(Ordering::Relaxed);
        if min_offset > visible {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!(
                    "retention to offset {min_offset} would prune records above the \
                     subscriber-visible head {visible}, which no reader has been shown yet"
                ),
            ));
        }
        Ok(())
    }

    /// STATE-CARRYING RETENTION: compact the durable log to `min_offset`, persisting
    /// any producer bindings (`/a/bind`), active pending wills (`/a/will`), producer
    /// sequence fences, and consumer-group commit watermarks from the dropped prefix
    /// into the `<log>.state` sidecar so compaction succeeds past early bindings and
    /// wills (`ROADMAP.md`, `AUDIT-2026-09.md`).
    ///
    /// Off the ack path, crash-safe, waits for a batch in flight, and is refused above the
    /// subscriber-visible head, as [`retain_before`](Self::retain_before) does and is.
    #[cfg(feature = "retention")]
    pub fn retain_before_carrying_state(&self, min_offset: u64) -> io::Result<u64> {
        self.compact(min_offset, true)
    }

    /// Configure automatic state-carrying compaction whenever the log's retained record
    /// count exceeds `max` (`0` = unlimited, the default).
    ///
    /// When a batch takes the log over the cap, the writer asks the RETENTION TICK for a
    /// tick ([`set_retention`](Self::set_retention)), which compacts at least the oldest
    /// half of the safe visible prefix, and enough to keep half the cap, as
    /// [`Self::retain_before_carrying_state`] does — off the ack path, its copy under no
    /// lock — preserving all producer bindings, pending wills, producer sequence fences,
    /// consumer-group commits, and the latest record of every quiet subject (`Last`) in
    /// `<log>.state`. The base moves when that tick finishes, not before the next batch.
    /// The tick skips while a retention call compacts (one compaction at a time), and the
    /// next batch over the cap asks again. With rules set, the cut is the higher of theirs
    /// and the cap's, and what the rules hold below it is carried.
    #[cfg(feature = "retention")]
    pub fn set_max_retained_records(&self, max: usize) {
        self.shared
            .max_retained_records
            .store(max, Ordering::Relaxed);
        if max > 0 {
            // Asked before the thread starts, so a thread started here takes this ask as
            // its first tick and none after it (`ensure_ticker`).
            ask_tick(&self.shared);
            ensure_ticker(&self.shared);
        }
    }

    /// The configured automatic compaction record threshold (`0` = unlimited).
    #[cfg(feature = "retention")]
    #[must_use]
    pub fn max_retained_records(&self) -> usize {
        self.shared.max_retained_records.load(Ordering::Relaxed)
    }

    /// Bound the decoded records this broker's log keeps resident in memory to about
    /// `budget` bytes of subject and body (the newest record always stays;
    /// [`BrokerLog::set_resident_budget`]).
    pub fn set_resident_budget(&self, budget: usize) {
        self.shared
            .log
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .set_resident_budget(budget);
    }

    /// `(resident records, resident bytes, retained records)` currently held in memory
    /// by this broker's log ([`BrokerLog::residency`]).
    #[must_use]
    pub fn residency(&self) -> (usize, usize, usize) {
        self.shared
            .log
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .residency()
    }

    /// The records this broker's log has read back from its file because the residency budget
    /// left them cold, since the open ([`BrokerLog::cold_reads`]): what the budget costs its
    /// readers. 0 with no budget.
    #[must_use]
    pub fn cold_reads(&self) -> u64 {
        self.shared
            .log
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .cold_reads()
    }

    /// What this broker's log's residency tier did since the open
    /// ([`BrokerLog::tier_tally`]): read around a piece of work, how much of the tier's code
    /// it ran. A test or debug build only.
    #[cfg(any(test, debug_assertions))]
    #[must_use]
    pub fn tier_tally(&self) -> crate::TierTally {
        self.shared
            .log
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .tier_tally()
    }

    #[cfg(all(test, unix))]
    pub(crate) fn reset_cold_reads(&self) {
        self.shared
            .log
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .reset_cold_reads();
    }

    #[cfg(all(test, unix))]
    pub(crate) fn shared_log_frame_at_for_test(&self, idx: usize) -> Option<u64> {
        self.shared
            .log
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .frame_at_for_test(idx)
    }

    /// Configure automatic state-carrying compaction whenever the log's retained byte
    /// size exceeds `max` (`0` = unlimited, the default), through the retention tick as
    /// [`set_max_retained_records`](Self::set_max_retained_records) does.
    #[cfg(feature = "retention")]
    pub fn set_max_retained_bytes(&self, max: usize) {
        self.shared.max_retained_bytes.store(max, Ordering::Relaxed);
        if max > 0 {
            // Asked before the thread starts, so a thread started here takes this ask as
            // its first tick and none after it (`ensure_ticker`).
            ask_tick(&self.shared);
            ensure_ticker(&self.shared);
        }
    }

    /// RETAIN BY RULES (`REQUIREMENTS` R4; [`Retention`](crate::Retention)): from here the
    /// broker's RETENTION TICK takes the cut the prefix rule says, carries below it what
    /// the hold rules still want into the held store `<log>.held`, and gives up what they
    /// no longer want — off the ack path, as [`retain_before`](Self::retain_before) runs.
    /// It ticks when a batch takes some class past its bytes (counted by the class of each
    /// record, so a class at its bytes asks for nothing while other classes' records
    /// arrive), and at least every [`RETENTION_INTERVAL`]
    /// ([`set_retention_interval`](Self::set_retention_interval)), by the wall clock; the
    /// first tick is asked for at once. A class past its bytes gives up at least a quarter
    /// of them ([`SLACK_DIV`](crate::retention::SLACK_DIV)), so its own records ask for a
    /// cut, which copies the log it keeps, at most once a quarter of its bytes. Reads answer by the rules
    /// at once, and every `Hello` answered from here advertises them (its extension
    /// block's retention entry). The rules are durable in the held store before this
    /// returns; a broker never given rules never compacts by itself, and behaves exactly
    /// as before.
    ///
    /// PER OPEN: a broker retains by the rules set on it since its open, and advertises
    /// only those. Reopened, a log answers reads by the rules its held store was last held
    /// under ([`BrokerLog::retention`]), and compacts by none, nor advertises any, until
    /// they are set again — as `asb serve --retain-file` does at every start.
    ///
    /// Refused on a simulated log (no held store), and on a poisoned one. Waits for a
    /// compaction under way, a tick's or a retention call's, to finish first: the rules
    /// change between compactions, never inside one. Waits, too, for a batch the writer
    /// is in the middle of, its write and flush included
    /// ([`BrokerStats::retention_waits`]), as a compaction's begin does: the held store's
    /// rules frame is written between batches, never beside one. So the rules may be set
    /// the moment a broker opens — while the writer still commits the wills the open
    /// fired, as `asb serve --retain-file` sets them — with no flush first.
    #[cfg(feature = "retention")]
    pub fn set_retention(&self, rules: crate::Retention) -> io::Result<()> {
        {
            // Lock order: compaction → batch → log, a compaction's own. A job begun under
            // the old rules appends its held frames where the store ended at its begin;
            // the rules frame set here goes after them, and its cut is the base the new
            // rules hold from.
            let _one = match self.shared.compaction.try_lock() {
                Ok(held) => held,
                Err(std::sync::TryLockError::Poisoned(poisoned)) => poisoned.into_inner(),
                Err(std::sync::TryLockError::WouldBlock) => {
                    self.shared.compaction_waits.fetch_add(1, Ordering::Relaxed);
                    self.shared
                        .compaction
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner)
                }
            };
            // The writer's batch lock, taken as a compaction's begin takes it: a batch in
            // its write window is waited out (the log, met there, refuses every mutation:
            // "a batch is being written outside the log lock"). A poisoned try-lock
            // already owns its guard; panic with it rather than lock again.
            let mut waited = false;
            let _batch = match self.shared.batch.try_lock() {
                Ok(held) => held,
                Err(std::sync::TryLockError::WouldBlock) => {
                    record_retention_wait(&self.shared, &mut waited);
                    self.shared
                        .batch
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner)
                }
                Err(std::sync::TryLockError::Poisoned(poisoned)) => {
                    panic!("retention: the writer panicked inside a batch ({poisoned})")
                }
            };
            let mut log = self
                .shared
                .log
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            log.set_retention(rules)?;
            publish_retention(&self.shared, &log);
            // Hello advertises them from here (lock order: log → copy).
            *self
                .shared
                .hello
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner) = HelloCopy::of(&log);
        }
        // Asked before the thread starts, so a thread started here takes this ask as its
        // first tick and none after it (`ensure_ticker`).
        ask_tick(&self.shared);
        ensure_ticker(&self.shared);
        Ok(())
    }

    /// The rules this broker retains its log by: the ones [`set_retention`](Self::set_retention)
    /// set since its open, which every `Hello` advertises; `None` before. A reopened log's
    /// held store may keep the rules it was last held under, which its reads answer by
    /// ([`BrokerLog::retention`]) but which compact nothing, so are not these, until they
    /// are set again.
    #[cfg(feature = "retention")]
    #[must_use]
    pub fn retention(&self) -> Option<crate::Retention> {
        self.shared
            .log
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .retention_active()
            .cloned()
    }

    /// Override how often the retention tick runs when no batch asks for it sooner
    /// (default [`RETENTION_INTERVAL`], a minute; at least a millisecond). Asks for a tick
    /// now, after which the new interval runs.
    #[cfg(feature = "retention")]
    pub fn set_retention_interval(&self, every: Duration) {
        self.shared.retention_interval_ms.store(
            every.as_millis().clamp(1, u64::MAX as u128) as u64,
            Ordering::Relaxed,
        );
        ask_tick(&self.shared);
    }

    /// The retention tick's interval ([`set_retention_interval`](Self::set_retention_interval)).
    #[cfg(feature = "retention")]
    #[must_use]
    pub fn retention_interval(&self) -> Duration {
        Duration::from_millis(self.shared.retention_interval_ms.load(Ordering::Relaxed))
    }

    /// ONE RETENTION TICK NOW, on this thread, at `now_ms` (unix ms: the caller's clock, a
    /// test's hand clock): exactly what the tick's thread runs, off the ack path — begin
    /// between batches, the held store's frames and the copy with no lock held, finish
    /// between batches — and one compaction at a time with it and every retention call.
    /// Says what it did. Nothing without rules or a cap over.
    #[cfg(feature = "retention")]
    pub fn retention_tick_at(&self, now_ms: u64) -> io::Result<crate::RetentionTick> {
        match retention_tick(&self.shared, now_ms, true)? {
            Some(tick) => Ok(tick),
            None => Err(io::Error::other(
                "retention: a waiting tick was skipped, which cannot happen",
            )),
        }
    }

    /// THE OLDEST offset of `filter` ([`BrokerLog::oldest`]), at and above which the filter
    /// is complete: the base, or, for what a hold rule keeps records of, the greatest floor
    /// over the subjects it matches (records some subject still holds can lie below it).
    #[must_use]
    pub fn oldest(&self, filter: &Filter) -> u64 {
        self.shared
            .log
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .oldest(filter)
            .0
    }

    /// The configured automatic compaction byte threshold (`0` = unlimited).
    #[cfg(feature = "retention")]
    #[must_use]
    pub fn max_retained_bytes(&self) -> usize {
        self.shared.max_retained_bytes.load(Ordering::Relaxed)
    }

    /// Enable or disable filter-indexed selective subscriber tail wakeups
    /// (`cost study B4 step 2`).
    ///
    /// When `false` (the default), every batch with newly visible deliverable records
    /// broadcasts once on the shared condvar (`tail_broadcasts`). When `true`, the
    /// writer evaluates newly visible deliverable records against registered subscriber
    /// [`Filter`]s under the log lock and calls `notify_one` only on matching tails
    /// (`selective_tail_wakes`), eliminating `O(S)` wakeup storms across disjoint
    /// subscribers. Toggling this live wakes all currently parked tails so they switch
    /// cleanly with zero lost wakeups.
    pub fn set_selective_tail_wake(&self, on: bool) {
        {
            let _log = self
                .shared
                .log
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            let vis = self.shared.head.load(Ordering::Relaxed);
            self.shared.selective_tail_wake.store(on, Ordering::Release);
            self.shared
                .selective_mode_epoch
                .fetch_add(1, Ordering::AcqRel);
            let parkers = self
                .shared
                .tail_parkers
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            for p in parkers.iter() {
                let mut st = p
                    .state
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
                st.matched_head = tail_wake_head_advance(st.matched_head, vis);
                st.has_unread_match = true;
                p.needs_wake.store(true, Ordering::Release);
            }
        }
        notify_all_tails(&self.shared);
    }

    /// Whether filter-indexed selective subscriber tail wakeups are currently active.
    #[must_use]
    pub fn selective_tail_wake(&self) -> bool {
        self.shared.selective_tail_wake.load(Ordering::Acquire)
    }

    /// Install, update, or clear (`None`) the broker's per-principal / per-producer
    /// monotone token-bucket rate limit (`DESIGN-aterm-fabric` T9 & T17).
    ///
    /// Returns `InvalidInput` if `limit` specifies a zero or out-of-range rate/burst.
    pub fn set_rate_limit(&self, limit: Option<RateLimit>) -> io::Result<()> {
        let validated = match limit {
            None => None,
            Some(lim) => match lim.validate() {
                Ok(v) => Some(v),
                Err(msg) => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("invalid rate_limit: {msg}"),
                    ));
                }
            },
        };
        let mut st = match self.shared.rate_limiter.lock() {
            Ok(g) => g,
            Err(p) => p.into_inner(),
        };
        st.set_limit(validated);
        self.shared
            .has_rate_limit
            .store(validated.is_some(), Ordering::Release);
        Ok(())
    }

    /// Whether this broker was opened with sticky producer gap fencing.
    /// Fixed for its lifetime so a producer can rely on the guarantee advertised by Hello.
    #[must_use]
    pub fn sticky_batch_refusal(&self) -> bool {
        self.shared.has_sticky_batch_refusal
    }

    /// Currently active per-principal / per-producer rate limit, if any.
    #[must_use]
    pub fn rate_limit(&self) -> Option<RateLimit> {
        if !self.shared.has_rate_limit.load(Ordering::Acquire) {
            return None;
        }
        let st = match self.shared.rate_limiter.lock() {
            Ok(g) => g,
            Err(p) => p.into_inner(),
        };
        st.limit
    }

    /// Operational snapshot of this broker's log, subscriber-visible head, active
    /// connections, and active listeners (`REQUIREMENTS` R5).
    pub fn stats(&self) -> BrokerStats {
        stats_of(&self.shared)
    }

    /// The broker's monotone millisecond clock (`REQUIREMENTS` R3): never regresses even
    /// if the OS wall clock steps backwards, so a capability expiry or fabric deadline
    /// (`bt=`) that has lapsed can never become un-expired.
    #[must_use]
    pub fn now_ms(&self) -> u64 {
        now_unix_ms()
    }

    /// Say which producers continue others' sequences, `successor -> predecessors`, replacing what
    /// the last call said: a produce under `(successor, seq)` that a predecessor's record already
    /// holds at `(predecessor, seq)` is answered from that record, as a resend, and appends
    /// nothing. An embedder says it whenever a producer it admits takes a new id for an old
    /// sequence, before it admits the new id's writes: a federation mirror whose source's key
    /// rotated pushes its source's offsets under the new key's producer, and a burst the old one
    /// landed here but never committed at the source is not appended twice
    /// ([`BrokerLog::set_producer_lineage`](crate::store::BrokerLog::set_producer_lineage)).
    pub fn set_producer_lineage(&self, lineage: impl IntoIterator<Item = (u64, Vec<u64>)>) {
        self.shared
            .log
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .set_producer_lineage(lineage);
    }

    /// Say whose relayed records this broker takes: exactly these Ed25519 keys, replacing the set
    /// the last call gave. An embedder calls it whenever its membership changes. A relayed record
    /// must name `identity_principal(key)` as its subject's owner, carry that principal's derived
    /// producer id and be signed by the key ([`origin`](crate::origin)), so a neighbour can
    /// neither forge another node's record nor race one in ahead of the real one. A broker that
    /// was given no keys takes no relayed record. A key also stands refused while it is revoked
    /// ([`revoke_identity`](Self::revoke_identity), [`revoke_principal`](Self::revoke_principal)).
    #[cfg(feature = "relay")]
    pub fn set_origin_keys(&self, keys: impl IntoIterator<Item = [u8; 32]>) {
        let keys: std::collections::BTreeMap<String, [u8; 32]> = keys
            .into_iter()
            .map(|key| (identity_principal(&key), key))
            .collect();
        let ids: Vec<u64> = keys
            .keys()
            .map(|principal| astream_cap::producer_id_of(principal))
            .collect();
        *self
            .shared
            .origin_keys
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = keys;
        self.shared
            .log
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .add_relay_origin_ids(ids);
    }

    /// Revoke an Ed25519 peer identity public key (`REQUIREMENTS` R6).
    ///
    /// Any future connection attempt presenting `pubkey` on `Self::serve_tcp_identity`
    /// is refused during the handshake, any capability bound to `identity_principal(&pubkey)`
    /// (`n-<16 hex>`) is revoked, and any already-open connection authenticated under
    /// `pubkey` is terminated with an `unauthorized` error on its next request or
    /// subscription delivery (with any pending last will suppressed), and any stream adopted
    /// under `pubkey` (`Self::serve_stream`, the `stream` feature's) is shut at once. Returns
    /// `true` if `pubkey` was newly added to the revocation set.
    pub fn revoke_identity(&self, pubkey: [u8; 32]) -> bool {
        let (added, changed) = insert_identity_revocation(
            &mut self
                .shared
                .revoked_identities
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner),
            &mut self
                .shared
                .revoked_principals
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner),
            pubkey,
        );
        if changed {
            self.shared.revocation_epoch.fetch_add(1, Ordering::AcqRel);
            notify_all_tails(&self.shared);
            #[cfg(feature = "stream")]
            end_revoked_streams(&self.shared);
        }
        added
    }

    /// Remove `pubkey` (and its derived `n-<16 hex>` principal) from the live identity
    /// revocation set. Returns `true` if `pubkey` was present.
    pub fn unrevoke_identity(&self, pubkey: &[u8; 32]) -> bool {
        let _file_state = self
            .shared
            .revocation_file
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let removed = self
            .shared
            .revoked_identities
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .remove(pubkey);
        let derived = identity_principal(pubkey);
        let principal_removed = self
            .shared
            .revoked_principals
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .remove(&derived);
        if removed || principal_removed {
            self.shared.revocation_epoch.fetch_add(1, Ordering::AcqRel);
            notify_all_tails(&self.shared);
        }
        removed
    }

    /// Revoke `pubkey` alone: every connection and stream under that key is refused and ended as
    /// [`revoke_identity`](Self::revoke_identity) does, but its derived `n-<16 hex>` principal is
    /// left as it stands, so grants bound to that principal keep their standing. For an embedder
    /// that knows another key derives the same principal (a 64-bit prefix holds no more) and
    /// decides that principal's revocation itself ([`revoke_principal`](Self::revoke_principal)).
    /// Returns `true` if `pubkey` was newly added to the revocation set.
    pub fn revoke_key(&self, pubkey: [u8; 32]) -> bool {
        let added = self
            .shared
            .revoked_identities
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .insert(pubkey);
        if added {
            self.shared.revocation_epoch.fetch_add(1, Ordering::AcqRel);
            notify_all_tails(&self.shared);
            #[cfg(feature = "stream")]
            end_revoked_streams(&self.shared);
        }
        added
    }

    /// Remove `pubkey` alone from the live identity revocation set, leaving its derived principal
    /// as it stands ([`revoke_key`](Self::revoke_key)). Returns `true` if `pubkey` was present.
    pub fn unrevoke_key(&self, pubkey: &[u8; 32]) -> bool {
        let _file_state = self
            .shared
            .revocation_file
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let removed = self
            .shared
            .revoked_identities
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .remove(pubkey);
        if removed {
            self.shared.revocation_epoch.fetch_add(1, Ordering::AcqRel);
            notify_all_tails(&self.shared);
        }
        removed
    }

    /// Whether `pubkey` is currently in the live identity revocation set.
    pub fn is_identity_revoked(&self, pubkey: &[u8; 32]) -> bool {
        maybe_reload_revocation_file(&self.shared);
        self.shared
            .revoked_identities
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .contains(pubkey)
    }

    /// Revoke a capability principal (`p=<principal>`, e.g. `n-<16 hex>` or `s-<id>`).
    /// Any future `Attach` or request using a grant bound to `principal` is refused,
    /// any open subscription authorized solely by `principal` is terminated, and any
    /// pending last will registered under `principal` is suppressed.
    pub fn revoke_principal(&self, principal: &str) -> bool {
        let added = self
            .shared
            .revoked_principals
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .insert(principal.to_ascii_lowercase());
        if added {
            self.shared.revocation_epoch.fetch_add(1, Ordering::AcqRel);
            notify_all_tails(&self.shared);
            #[cfg(feature = "stream")]
            end_revoked_streams(&self.shared);
        }
        added
    }

    /// Remove `principal` from the revoked-principal set.
    pub fn unrevoke_principal(&self, principal: &str) -> bool {
        let lower = principal.to_ascii_lowercase();
        let _file_state = self
            .shared
            .revocation_file
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let removed = self
            .shared
            .revoked_principals
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .remove(&lower);
        if removed {
            self.shared.revocation_epoch.fetch_add(1, Ordering::AcqRel);
            notify_all_tails(&self.shared);
        }
        removed
    }

    /// Whether `principal` is currently revoked.
    pub fn is_principal_revoked(&self, principal: &str) -> bool {
        maybe_reload_revocation_file(&self.shared);
        self.shared
            .revoked_principals
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .contains(&principal.to_ascii_lowercase())
    }

    /// Revoke an `ACRT` certificate `serial` (`serial > 0`, Rung 9).
    ///
    /// Any future connection presenting `serial` on `Self::serve_tcp_certified` is
    /// refused during the handshake, and any already-open connection authenticated with
    /// `serial` is terminated with `ERR_UNAUTHORIZED` on its next request or tail
    /// delivery (suppressing any pending last will). Returns `true` if `serial` was
    /// newly added.
    pub fn revoke_cert_serial(&self, serial: u64) -> bool {
        if serial == 0 {
            return false;
        }
        let added = self
            .shared
            .revoked_cert_serials
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .insert(serial);
        if added {
            self.shared.revocation_epoch.fetch_add(1, Ordering::AcqRel);
            notify_all_tails(&self.shared);
        }
        added
    }

    /// Remove `serial` from the live certificate-serial revocation set. Returns `true`
    /// if `serial` was present.
    pub fn unrevoke_cert_serial(&self, serial: u64) -> bool {
        let _file_state = self
            .shared
            .revocation_file
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let removed = self
            .shared
            .revoked_cert_serials
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .remove(&serial);
        if removed {
            self.shared.revocation_epoch.fetch_add(1, Ordering::AcqRel);
            notify_all_tails(&self.shared);
        }
        removed
    }

    /// Whether certificate `serial` is currently revoked on this broker.
    pub fn is_cert_serial_revoked(&self, serial: u64) -> bool {
        maybe_reload_revocation_file(&self.shared);
        self.shared
            .revoked_cert_serials
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .contains(&serial)
    }

    /// Load a revocation file (`REQUIREMENTS` R6). On Apple targets, also register its
    /// path for automatic `SIGHUP` reload; elsewhere call this method again to reload:
    /// each non-empty, non-`#`-comment line is either a 64-hex-character
    /// Ed25519 public key (revoking both the transport key and its derived `n-<16 hex>`
    /// principal) or a principal string (`n-...`, `s-...`, `a-...`, `h-...`).
    ///
    /// Parsed atomically and fail-closed: if the file cannot be read or contains any
    /// malformed line, this call (or a later `SIGHUP` reload) returns an error and
    /// leaves all existing revocations untouched. An Apple handler-installation failure
    /// also returns an error before changing revocations. File replacement preserves
    /// manual revocations; explicit un-revokes clear both sources until a later reload.
    /// Returns the number of entries loaded.
    pub fn load_revocation_file(&self, path: impl AsRef<Path>) -> io::Result<usize> {
        apply_revocation_file(&self.shared, path.as_ref())
    }

    /// Spawn the writer over an opened log.
    fn start(
        mut log: BrokerLog,
        replicator: Option<Replicator>,
        cap_secret: Option<Vec<u8>>,
        sticky_batch_refusal: bool,
    ) -> Broker {
        // Strict/Relaxed: everything durable is visible. Replicated: only what a quorum
        // already confirmed (the caller caught the followers up before handing us
        // the replicator, so the watermark is the current one).
        let head = match &replicator {
            Some(rep) => Replicator::watermark(
                &rep.links
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner),
                rep.quorum,
            ),
            None => log.head().0,
        };
        log.start_last_visible(head);
        let durable = log.durable_head().0;
        let base = log.base().0;
        #[cfg(feature = "retention")]
        let (log_bytes, retain_due) = (log.durable_len(), log.retention_due());
        let log_head = log.head().0;
        let is_replica = log.is_replica();
        let durable_marks = log.served().served == crate::proto::Tier::Ordered;
        let horizon = log.horizon();
        let (writes, rx) = mpsc::channel::<Queued>();
        // The copies the handshake reads instead of the log (see their fields): taken
        // here, before any connection or the writer can run. Only a guarded broker
        // checks bindings at attach, so only it keeps their copy.
        let hello = HelloCopy::of(&log);
        let vitals = log.vitals();
        let log_path = log.path().to_path_buf();
        let mut bindings = HashMap::new();
        if cap_secret.is_some() {
            for (id, principal, off) in log.durable_bindings() {
                bindings.insert(id, (principal.to_string(), off.0));
            }
        }
        let shared = Arc::new(Shared {
            log: Mutex::new(log),
            tail: Condvar::new(),
            started_at_ms: now_unix_ms(),
            listeners: Mutex::new(std::collections::BTreeMap::new()),
            listener_seq: AtomicU64::new(0),
            attached_conns: Mutex::new(HashMap::new()),
            head: AtomicU64::new(head),
            durable: AtomicU64::new(durable),
            durable_marks,
            horizon,
            running: AtomicBool::new(true),
            writes,
            conns: Mutex::new(HashMap::new()),
            conn_seq: AtomicU64::new(0),
            replicator,
            cap_secret,
            first_frame_timeout_ms: AtomicU64::new(FIRST_FRAME_TIMEOUT.as_millis() as u64),
            write_timeout_ms: AtomicU64::new(ACK_WRITE_TIMEOUT.as_millis() as u64),
            max_conns: AtomicUsize::new(MAX_CONNS),
            idle_mark_ms: AtomicU64::new(IDLE_MARK.as_millis() as u64),
            liveness_poll_ms: AtomicU64::new(LIVENESS_POLL.as_millis() as u64),
            keepalive_deadline_ms: AtomicU64::new(KEEPALIVE_DEADLINE.as_millis() as u64),
            refusing: AtomicUsize::new(0),
            active_listeners: AtomicUsize::new(0),
            writer: Mutex::new(None),
            accepted: AtomicU64::new(0),
            acceptor_wakeups: AtomicU64::new(0),
            acceptor_sleeps: AtomicU64::new(0),
            acceptors_abandoned: AtomicU64::new(0),
            revoked_identities: Mutex::new(RevocationSet::new()),
            revoked_principals: Mutex::new(RevocationSet::new()),
            revoked_cert_serials: Mutex::new(RevocationSet::new()),
            #[cfg(feature = "relay")]
            origin_keys: Mutex::new(std::collections::BTreeMap::new()),
            origin_refused: AtomicU64::new(0),
            origin_unknown: AtomicU64::new(0),
            revocation_file: Mutex::new(None),
            has_revocation_file: AtomicBool::new(false),
            sighup_seen: AtomicU64::new(0),
            revocation_epoch: AtomicU64::new(0),
            last_round_pause: Mutex::new(None),
            #[cfg(test)]
            tail_pause: Mutex::new(None),
            delivery_crc_cache: Box::new(std::array::from_fn(|_| Mutex::new(None))),
            hello: Mutex::new(hello),
            bindings: Mutex::new(bindings),
            writer_round_trips: AtomicU64::new(0),
            writer_batches: AtomicU64::new(0),
            writer_wakeups: AtomicU64::new(0),
            empty_batches: AtomicU64::new(0),
            binds_settled: AtomicU64::new(0),
            wills_settled: AtomicU64::new(0),
            tail_broadcasts: AtomicU64::new(0),
            selective_tail_wakes: AtomicU64::new(0),
            tail_wakeups: AtomicU64::new(0),
            selective_tail_wake: AtomicBool::new(false),
            selective_mode_epoch: AtomicU64::new(0),
            next_parker_id: AtomicU64::new(1),
            tail_parkers: Mutex::new(Vec::new()),
            has_rate_limit: AtomicBool::new(false),
            rate_limiter: Mutex::new(RateLimiterState::new()),
            rate_limited: AtomicU64::new(0),
            has_sticky_batch_refusal: sticky_batch_refusal,
            sticky_fences: Mutex::new(crate::sticky_fence::StickyFenceTable::new()),
            peer_probes: AtomicU64::new(0),
            parked_tails: AtomicUsize::new(0),
            batch: Mutex::new(()),
            retention_waits: AtomicU64::new(0),
            #[cfg(feature = "retention")]
            compaction: Mutex::new(()),
            #[cfg(feature = "retention")]
            compaction_waits: AtomicU64::new(0),
            #[cfg(feature = "retention")]
            tick: Mutex::new(TickState::default()),
            #[cfg(feature = "retention")]
            tick_cv: Condvar::new(),
            #[cfg(feature = "retention")]
            tick_done: Condvar::new(),
            #[cfg(feature = "retention")]
            ticker: Mutex::new(None),
            #[cfg(feature = "retention")]
            retention_interval_ms: AtomicU64::new(RETENTION_INTERVAL.as_millis() as u64),
            #[cfg(feature = "retention")]
            log_bytes: AtomicU64::new(log_bytes),
            #[cfg(feature = "retention")]
            retain_due: AtomicBool::new(retain_due),
            batch_pause: Mutex::new(BatchPauseSeam::default()),
            batch_pause_armed: AtomicBool::new(false),
            unclean_stop: AtomicBool::new(false),
            vitals,
            log_path,
            health: Mutex::new(None),
            health_thread: Mutex::new(None),
            base: AtomicU64::new(base),
            log_head: AtomicU64::new(log_head),
            is_replica: AtomicBool::new(is_replica),
            max_retained_records: AtomicUsize::new(0),
            max_retained_bytes: AtomicUsize::new(0),
        });
        let w_shared = shared.clone();
        let writer = thread::spawn(move || {
            let _exit = WriterExit(&w_shared);
            writer_loop(&w_shared, rx);
        });
        *shared
            .writer
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = Some(writer);
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
            let log = shared
                .log
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if log.is_replica() {
                Vec::new()
            } else {
                log.pending_wills()
            }
        };
        for will in pending {
            fire_will(&shared, will);
        }
        Broker { shared }
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
    ///
    /// Strict: [`open_guarded_with`](Self::open_guarded_with) at
    /// [`Durability::Strict`], as [`open`](Self::open) is
    /// [`open_with`](Self::open_with)'s.
    #[cfg(feature = "cap")]
    pub fn open_guarded(log_path: impl AsRef<Path>, secret: Vec<u8>) -> io::Result<Broker> {
        Self::open_guarded_with(log_path, secret, Durability::Strict)
    }

    /// [`open_guarded`](Self::open_guarded) at an explicit [`Durability`] tier. The
    /// guard and the tier are ORTHOGONAL: the guard decides which requests a
    /// connection may make, the tier what an `ack` to an authorized one promises, and
    /// neither reads the other. So a Relaxed guarded broker enforces exactly what a
    /// Strict one does — the same capability checks on the same accept path, the same
    /// refusal of an empty `secret` — and acks after the batch's page-cache write
    /// instead of its fsync, which is [`Durability::Relaxed`]'s whole difference.
    ///
    /// WHAT RELAXED COSTS A CLIENT THAT KEEPS OFFSETS. A Relaxed ack survives a process
    /// crash, not a power loss. A power loss is ANNOUNCED: the first open after the
    /// reboot finds the run did not stop cleanly in that boot, keeps the longest intact
    /// prefix above the durable floor, and moves the log's
    /// [`identity`](Self::log_identity) generation with lineage — so a client compares
    /// the identity it kept offsets under, and resumes at
    /// [`LogIdentity::continues`](crate::LogIdentity::continues) (or forgets, against a
    /// broker or a log that cannot say where it continues). The embedder does not move
    /// the identity itself; one with its own unclean verdict hands it to the open
    /// ([`Prepared::Unclean`](crate::Prepared), through
    /// [`open_opts`](Self::open_opts)), and the generation moves once. A stop through
    /// [`BrokerHandle::shutdown`] closes the log cleanly and moves nothing at the next
    /// boot.
    ///
    /// [`Durability::Ordered`] costs the same kind of announced loss, bounded: at most
    /// the batches acked since the last full flush (the horizon's). Through this
    /// shorthand its escalation table is EMPTY, so every record rides the horizon; a
    /// broker whose records a person would miss names them in
    /// [`OpenOptions::escalation`] through [`open_opts`](Self::open_opts), with the
    /// guard in [`OpenOptions::guard`] — a guard is what binds producers to principals,
    /// the `PrincipalPrefix` rule's whole input.
    #[cfg(feature = "cap")]
    pub fn open_guarded_with(
        log_path: impl AsRef<Path>,
        secret: Vec<u8>,
        durability: Durability,
    ) -> io::Result<Broker> {
        if secret.is_empty() {
            return Err(empty_secret());
        }
        let log = BrokerLog::open_with(log_path, durability)?;
        Ok(Self::start(log, None, Some(secret), false))
    }

    /// [`open_guarded_with`](Self::open_guarded_with) with sidecar preparation
    /// under the log's own lock, as in [`open_with_prepare`](Self::open_with_prepare).
    /// An empty capability secret is refused before opening the log or calling
    /// `prepare`; capability enforcement and durability otherwise stay unchanged.
    #[cfg(feature = "cap")]
    pub fn open_guarded_with_prepare(
        log_path: impl AsRef<Path>,
        secret: Vec<u8>,
        durability: Durability,
        prepare: impl FnOnce() -> io::Result<()>,
    ) -> io::Result<Broker> {
        if secret.is_empty() {
            return Err(empty_secret());
        }
        let log = BrokerLog::open_with_prepare(log_path, durability, prepare)?;
        Ok(Self::start(log, None, Some(secret), false))
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
        Self::open_replicated_transport_with(
            log_path,
            follower_addrs,
            FollowerTransport::Plain,
            quorum,
            replica_timeout,
        )
    }

    /// [`open_replicated`](Self::open_replicated) over an authenticated/encrypted
    /// [`FollowerTransport`] (`Sealed`, `Handshake`, or `Identity`) for cross-host
    /// LAN/WAN replication.
    pub fn open_replicated_transport(
        log_path: impl AsRef<Path>,
        follower_addrs: &[String],
        transport: FollowerTransport,
        quorum: usize,
    ) -> io::Result<Broker> {
        Self::open_replicated_transport_with(
            log_path,
            follower_addrs,
            transport,
            quorum,
            REPLICA_IO_TIMEOUT,
        )
    }

    /// [`open_replicated_transport`](Self::open_replicated_transport) with an explicit
    /// follower I/O timeout.
    pub fn open_replicated_transport_with(
        log_path: impl AsRef<Path>,
        follower_addrs: &[String],
        transport: FollowerTransport,
        quorum: usize,
        replica_timeout: Duration,
    ) -> io::Result<Broker> {
        Self::open_replicated_inner(
            log_path,
            None,
            follower_addrs,
            transport,
            #[cfg(feature = "cap")]
            None,
            quorum,
            replica_timeout,
        )
    }

    /// [`open_replicated`](Self::open_replicated) with capability enforcement on the
    /// leader's accept path (`secret`) AND capability attachment (`follower_cap`) on
    /// every follower replication link (at initial dial and on every reconnect).
    ///
    /// `follower_cap` must be an unbound read-write capability accepted by the
    /// followers (e.g. minted with `"rw:/>"` under the followers' secret); a follower
    /// that refuses `Attach` or `Replicate` with `ERR_UNAUTHORIZED` is fenced. An
    /// empty `secret` is refused (`InvalidInput`) before opening the log or dialing
    /// any follower.
    #[cfg(feature = "cap")]
    pub fn open_replicated_guarded(
        log_path: impl AsRef<Path>,
        secret: Vec<u8>,
        follower_addrs: &[String],
        follower_cap: astream_cap::Capability,
        quorum: usize,
    ) -> io::Result<Broker> {
        Self::open_replicated_guarded_with(
            log_path,
            secret,
            follower_addrs,
            follower_cap,
            quorum,
            REPLICA_IO_TIMEOUT,
        )
    }

    /// [`open_replicated_guarded`](Self::open_replicated_guarded) with an explicit
    /// follower I/O timeout.
    #[cfg(feature = "cap")]
    pub fn open_replicated_guarded_with(
        log_path: impl AsRef<Path>,
        secret: Vec<u8>,
        follower_addrs: &[String],
        follower_cap: astream_cap::Capability,
        quorum: usize,
        replica_timeout: Duration,
    ) -> io::Result<Broker> {
        Self::open_replicated_guarded_transport_with(
            log_path,
            secret,
            follower_addrs,
            FollowerTransport::Plain,
            follower_cap,
            quorum,
            replica_timeout,
        )
    }

    /// [`open_replicated_guarded`](Self::open_replicated_guarded) over an
    /// authenticated/encrypted [`FollowerTransport`].
    #[cfg(feature = "cap")]
    pub fn open_replicated_guarded_transport(
        log_path: impl AsRef<Path>,
        secret: Vec<u8>,
        follower_addrs: &[String],
        transport: FollowerTransport,
        follower_cap: astream_cap::Capability,
        quorum: usize,
    ) -> io::Result<Broker> {
        Self::open_replicated_guarded_transport_with(
            log_path,
            secret,
            follower_addrs,
            transport,
            follower_cap,
            quorum,
            REPLICA_IO_TIMEOUT,
        )
    }

    /// [`open_replicated_guarded_transport`](Self::open_replicated_guarded_transport)
    /// with an explicit follower I/O timeout.
    #[cfg(feature = "cap")]
    pub fn open_replicated_guarded_transport_with(
        log_path: impl AsRef<Path>,
        secret: Vec<u8>,
        follower_addrs: &[String],
        transport: FollowerTransport,
        follower_cap: astream_cap::Capability,
        quorum: usize,
        replica_timeout: Duration,
    ) -> io::Result<Broker> {
        if secret.is_empty() {
            return Err(empty_secret());
        }
        match astream_cap::Grant::parse(follower_cap.filter.as_str()) {
            Ok(g)
                if g.mode == astream_cap::Mode::ReadWrite && g.principal.is_none() && !g.relay => {}
            Ok(_) => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!(
                        "follower capability {:?} must be an unbound read-write grant (e.g. \"rw:/>\"); \
                         a bound or read-only grant cannot authorize Request::Replicate",
                        follower_cap.filter
                    ),
                ));
            }
            Err(e) => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("invalid follower capability {:?}: {e}", follower_cap.filter),
                ));
            }
        }
        Self::open_replicated_inner(
            log_path,
            Some(secret),
            follower_addrs,
            transport,
            Some(follower_cap),
            quorum,
            replica_timeout,
        )
    }

    fn open_replicated_inner(
        log_path: impl AsRef<Path>,
        secret: Option<Vec<u8>>,
        follower_addrs: &[String],
        transport: FollowerTransport,
        #[cfg(feature = "cap")] follower_cap: Option<astream_cap::Capability>,
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
        let link_transports = transport.links_for(follower_addrs.len())?;
        let mut log = BrokerLog::open_with(log_path, Durability::Relaxed)?;
        // Every link's confirmed prefix starts at the log's retention BASE: records
        // below it were pruned, so there is nothing below it to ship or confirm.
        let base = log.base().0;
        let quorum = quorum.clamp(1, follower_addrs.len());
        let mut links = Vec::new();
        let mut kill = Vec::new();
        let mut live = 0usize;
        let mut last_err: Option<io::Error> = None;
        #[cfg(feature = "cap")]
        let has_cap = follower_cap.is_some();
        #[cfg(not(feature = "cap"))]
        let has_cap = false;
        for (addr, link_transport) in follower_addrs.iter().zip(link_transports) {
            // A follower that cannot be dialed now is a DOWN link (re-dialed on every
            // batch, then caught up), not a fatal error — unless so many are down that
            // the quorum could never be met, which is a configuration error to fail
            // fast on rather than a broker that refuses every ack.
            #[allow(unused_mut)]
            let mut init_fenced: Option<String> = None;
            let stream = match dial_follower_tcp(addr, replica_timeout).and_then(|raw| {
                upgrade_follower_stream(raw, &link_transport, has_cap, replica_timeout)
            }) {
                #[allow(unused_mut)]
                Ok(mut s) => {
                    #[cfg(feature = "cap")]
                    let auth_res = match follower_cap.as_ref() {
                        Some(cap) => attach_follower_cap(&mut s, cap, replica_timeout),
                        None => Ok(()),
                    };
                    #[cfg(not(feature = "cap"))]
                    let auth_res: Result<(), (bool, io::Error)> = Ok(());
                    match auth_res {
                        Ok(()) => {
                            live = live.saturating_add(1);
                            kill.push(match s.try_clone_tcp() {
                                Ok(c) => Some(c),
                                Err(_) => None,
                            });
                            Some(s)
                        }
                        Err((is_unauth, e)) => {
                            if is_unauth {
                                init_fenced = Some(e.to_string());
                            }
                            last_err = Some(e);
                            kill.push(None);
                            None
                        }
                    }
                }
                Err(e) => {
                    last_err = Some(e);
                    kill.push(None);
                    None
                }
            };
            links.push(FollowerLink {
                leader: log.identity(),
                addr: addr.clone(),
                transport: link_transport,
                stream,
                upto: base,
                fenced: init_fenced,
                fresh: false,
                timeout_failures: 0,
                next_dial_at: None,
                #[cfg(feature = "cap")]
                cap: follower_cap.clone(),
            });
        }
        if live < quorum {
            let e = match last_err {
                Some(e) => e,
                None => io::Error::other("no follower reachable"),
            };
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
        let backlog = log.read_from_stamped(Offset(base));
        let wm = rep.replicate(&backlog, &AtomicBool::new(true));
        let committed_wm = log.record_replica_ack(Offset(wm)).0;
        if committed_wm < head {
            return Err(io::Error::other(format!(
                "Replicated tier: a quorum confirmed only {committed_wm} of the {head} local records \
                 at open (a follower refused, diverged, or timed out)"
            )));
        }
        Ok(Self::start(log, Some(rep), secret, false))
    }

    /// Override the wall-clock source sampled when stamping broker time (`bt=`) on
    /// newly appended records (`REQUIREMENTS` R3).
    ///
    /// Even when overridden, the stamped `bt=` remains strictly monotone via the
    /// Clean-origin `broker_bt_advance` state machine (a backward jump in `clock`
    /// clamps at the previous record's `bt=`). Passing `None` restores the process
    /// monotone clock (`now_unix_ms()`).
    pub fn set_clock_override(&self, clock: Option<Arc<AtomicU64>>) {
        self.shared
            .log
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .set_clock_override(clock);
    }

    /// The durable head of the log (its record count; the offset the next commit
    /// takes), read without waiting on the log lock.
    pub fn head(&self) -> u64 {
        self.shared.log_head.load(Ordering::Acquire)
    }

    /// The lowest offset still retained in the log (records below it were pruned by
    /// retention), read without waiting on the log lock.
    pub fn base(&self) -> u64 {
        self.shared.base.load(Ordering::Acquire)
    }

    /// The [`LogIdentity`](crate::LogIdentity) of the log this broker serves — what
    /// it tells every client in the answer to `Hello` (on a replica, its leader's once
    /// a replicated batch carrying it has committed and reached its newest record).
    /// Read from the same copy `Hello` answers from, so the two never disagree, and
    /// like `Hello` it does not wait on the log lock.
    pub fn log_identity(&self) -> crate::LogIdentity {
        self.shared
            .hello
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .identity
    }

    /// The SUBSCRIBER-VISIBLE head. Equal to [`head`](Self::head) in the Strict tier,
    /// and in the Ordered and Relaxed tiers but for one window: a batch holding a record
    /// the escalation table names ([`OpenOptions::escalation`]) is HELD here, at that
    /// record, from its commit until the full flush it owes has succeeded — so the record
    /// is durable before anyone can see it or be acked for it; if that flush fails, for
    /// the rest of the open, which the failure poisons. In the Replicated tier it
    /// is the quorum watermark — records at or above it are committed locally but not yet
    /// held by a quorum of followers, so they are neither acked nor delivered.
    pub fn visible_head(&self) -> u64 {
        self.shared.head.load(Ordering::Relaxed)
    }

    /// The DURABLE head ([`BrokerLog::durable_head`]): every record below this offset is
    /// on stable media by a full flush this broker saw succeed. Strict: the head, after
    /// every batch. Ordered and Relaxed: it moves at the open, at each full flush (an
    /// escalated record's, the Ordered horizon's, [`flush_durable`](Self::flush_durable))
    /// and at the clean close — never at an Ordered batch's barrier. Read without the log
    /// lock (a sampler can poll it), and the value every `Mark` carries.
    pub fn durable_head(&self) -> u64 {
        self.shared.durable.load(Ordering::Acquire)
    }

    /// Where consumer group `group` RESUMES: one past the offset it last committed
    /// through, `0` if it never committed — the offset a `SubscribeGroup` for it starts
    /// at, read from the same place ([`BrokerLog::group_start`]), so a commit a held
    /// batch carries counts only once the full flush that releases it has succeeded.
    /// Read under the log lock, which the writer holds from a batch's promotion until
    /// its heads are published (and lets go only around the write and the flush, while
    /// readers see the log as it stood before the batch): a commit counted here came
    /// with its batch's [`visible_head`](Self::visible_head), in every tier but
    /// Replicated, where it counts once the leader has committed it and the visible
    /// head is the quorum watermark. An embedder serving its own broker reads a
    /// group's progress here without a connection (aterm's fabric bench waits on its
    /// inbox group's before each next post); like [`stats`](Self::stats), it waits out a
    /// batch's staging and promotion, so it is no sampler's poll. Outside Replicated a
    /// waiter polls the lock-free visible head and reads this only when that has moved,
    /// as aterm's bench does: a commit counts here with the head's move.
    pub fn group_start(&self, group: &str) -> u64 {
        self.shared
            .log
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .group_start(group)
            .0
    }

    /// The tier this broker serves, with the one it was asked for and why they differ
    /// ([`ServedInfo`](crate::ServedInfo)) — exactly what the answer to `Hello` tells a
    /// client (`Client::served_durability`), read from the same copy, without the log
    /// lock. It changes in a running broker only when the log latches to Strict, which
    /// it reports from the moment the log latches (read from the log's vitals, beside
    /// the poison): once [`poisoned`](Self::poisoned) has named a failure that latched
    /// the log, this names the latch too.
    pub fn served_durability(&self) -> crate::ServedInfo {
        // The copy's lock is released before the log's could be taken (the writer
        // takes them in the other order).
        let told = self
            .shared
            .hello
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .ext
            .durability;
        match told {
            Some(s) => self.shared.vitals.served(s),
            None => self
                .shared
                .log
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .served(),
        }
    }

    /// How many flushes the log has issued since it opened, by kind ([`FlushCounts`]):
    /// barriers, full flushes, full flushes skipped because one already covered the
    /// head, and flushes that failed. Read WITHOUT the log lock (each count is exact;
    /// the four are not one instant) — the same counts every `Hello` answer carries
    /// ([`HelloHealth`](crate::HelloHealth)).
    pub fn flush_counts(&self) -> FlushCounts {
        self.shared.vitals.flush_counts()
    }

    /// `Some(reason)` once the log is POISONED ([`BrokerLog::poisoned`]): it refuses
    /// every write until it is reopened, and no resend to this broker lands. The cure is
    /// the embedder's: drop this broker and open the log again — in a supervised
    /// process, exit and let the supervisor start it — which moves the generation when
    /// the failure may have lost acked records (the run is recorded `Lossy`). Every write
    /// refused meanwhile carries the reason too, in a refusal that starts
    /// [`LOG_POISONED_PREFIX`]
    /// ([`BrokerRefusal::is_poisoned`](crate::BrokerRefusal::is_poisoned)), and so does
    /// the answer to every `Hello` ([`HelloHealth`](crate::HelloHealth)).
    ///
    /// [`stats`](Self::stats)' `log.poisoned` says the same as a flag; this names why, so
    /// an embedder's exit line can say what astream decided. The first reason stands: the
    /// poison is set once.
    ///
    /// LOCK-FREE: one atomic load, never the log lock. The writer holds that lock across
    /// a rollback's truncate and across the `<log>.id` write a failed flush records
    /// `Lossy` in — filesystem I/O that a failing disk makes slow, at exactly the moment
    /// this is asked — so a look that took it could wait out the very failure it was
    /// looking for (`broker.poisoned-refusal`). [`wait_poisoned`](Self::wait_poisoned)
    /// sleeps on it instead of polling.
    pub fn poisoned(&self) -> Option<String> {
        match self.shared.vitals.poisoned() {
            Some(s) => Some(s.to_string()),
            None => None,
        }
    }

    /// Sleep until the log is POISONED ([`poisoned`](Self::poisoned)) and return why, or
    /// return `None` once `timeout` has passed or the broker has stopped serving its log
    /// (its last listener shut down, or an unserved broker dropped), whichever is first.
    /// For an embedder that exits on the poison, so its supervisor reopens the log: a
    /// thread parked here wakes at the poison itself, with no poll and without the log
    /// lock.
    pub fn wait_poisoned(&self, timeout: Duration) -> Option<String> {
        let deadline = Instant::now().checked_add(timeout);
        self.shared
            .vitals
            .wait(deadline, &self.shared.running, true);
        self.poisoned()
    }

    /// The broker's health now (`REQUIREMENTS` R5): what the log holds, who is attached
    /// and parked, what its flushes did, whether it is poisoned — the snapshot
    /// `<log>.health` carries ([`BrokerHealth`](crate::BrokerHealth)), stamped with this
    /// process's pid and [`now_ms`](Self::now_ms). Takes the log lock, as
    /// [`stats`](Self::stats) does.
    pub fn health(&self) -> crate::health::BrokerHealth {
        health_of(&self.shared)
    }

    /// Write `<log>.health` now ([`health`](Self::health)'s snapshot), replacing the one
    /// there, and hold it: until the log closes, [`read_health`](crate::read_health)
    /// tells a reader in another process that this broker still serves the log. For an
    /// embedder that writes it on its own schedule; [`keep_health`](Self::keep_health)
    /// writes it on a period.
    ///
    /// # Errors
    ///
    /// The sidecar could not be written (the one published before, if any, stays, and
    /// stays held), or the broker has stopped serving its log — a broker that has
    /// closed its log publishes nothing a reader would take for a serving one.
    pub fn write_health(&self) -> io::Result<()> {
        write_health_of(&self.shared).1
    }

    /// Keep `<log>.health` from now on: write it now, then again every `every` — and at
    /// once when the log is poisoned — until the log closes, when the last one is
    /// written, after the log's clean close, and let go
    /// ([`read_health`](crate::read_health) then reads its writer
    /// [`Gone`](crate::HealthWriter::Gone)). [`OpenOptions::health_every`] asks for the
    /// same at the open. A second call writes now and keeps the first call's period.
    ///
    /// "At once" is the period's thread waking at the poison, which nothing orders
    /// before a [`wait_poisoned`](Self::wait_poisoned) that wakes at it too: an embedder
    /// that exits on the poison and wants the file to name it calls
    /// [`write_health`](Self::write_health) first, or stops the broker (drops it, or
    /// shuts its last listener down), whose last word names it.
    ///
    /// A write the period's thread cannot make is said once on stderr and tried again
    /// next period; the file published before it stays.
    ///
    /// # Errors
    ///
    /// The first write failed (the thread still starts and keeps trying), or the broker
    /// has stopped serving its log.
    pub fn keep_health(&self, every: Duration) -> io::Result<()> {
        let (named, first) = write_health_of(&self.shared);
        if !self.shared.running.load(Ordering::Acquire) {
            return first;
        }
        let mut slot = self
            .shared
            .health_thread
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if slot.is_none() {
            let shared = Arc::clone(&self.shared);
            *slot = Some(thread::spawn(move || health_loop(&shared, every, named)));
        }
        first
    }

    /// FLUSH THE LOG IN FULL, through the writer: the op stages nothing, rides the next
    /// batch, and is answered once a full flush covers everything committed before it —
    /// issued outside the log lock, after that batch's other acks, and skipped (counted
    /// so) when one already covers the head. Returns the durable head after it.
    ///
    /// For an embedder that must know a moment's records are on stable media (a clean
    /// hand-off, a checkpoint), and for tests: `Durability::Ordered { horizon: None }`
    /// plus this makes durability deterministic. On Strict it is always skipped.
    ///
    /// # Errors
    /// The flush failed (the run is then recorded `Lossy` and the log refuses every write
    /// until it is reopened; see [`InjectedFaults::sync`]), or the broker is stopping.
    pub fn flush_durable(&self) -> io::Result<u64> {
        match submit_blocking(&self.shared, WriteKind::Flush) {
            Ok((durable, _)) => Ok(durable),
            Err((code, msg)) => Err(crate::client::BrokerRefusal { code, msg }.into()),
        }
    }

    /// Operator-invoked tail truncation on a running REPLICA broker (`is_replica == true`)
    /// to `target_head` (`base <= target_head <= head`), discarding any divergent suffix
    /// `[target_head..head)` between writer batches so this follower can catch up from its
    /// leader and rejoin the replication quorum (paired with [`Broker::rejoin_followers`]
    /// on the leader).
    ///
    /// Preserves canonical lock ordering (`compaction -> batch -> log`), mints a fresh
    /// replica [`LogIdentity`](crate::LogIdentity) until the leader's catch-up batch
    /// re-adopts the leader's identity, refreshes `Hello` and producer bindings, and
    /// returns the number of truncated records (`old_head - target_head`).
    pub fn truncate_replica_to(&self, target_head: u64) -> io::Result<u64> {
        #[cfg(feature = "retention")]
        let _one = self
            .shared
            .compaction
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let _batch = match self.shared.batch.try_lock() {
            Ok(held) => held,
            Err(std::sync::TryLockError::WouldBlock) => self
                .shared
                .batch
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner),
            Err(std::sync::TryLockError::Poisoned(poisoned)) => {
                panic!("truncate_replica_to: writer panicked inside a batch ({poisoned})")
            }
        };
        let (dropped, old_retire) = {
            let mut log = self
                .shared
                .log
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            let (dropped, old_retire) = log.truncate_replica_to_detaching(Offset(target_head))?;
            if dropped > 0 {
                self.shared
                    .is_replica
                    .store(log.is_replica(), Ordering::Release);
                self.shared.log_head.store(log.head().0, Ordering::Release);
                #[cfg(feature = "retention")]
                {
                    self.shared
                        .log_bytes
                        .store(log.durable_len(), Ordering::Relaxed);
                    self.shared
                        .retain_due
                        .store(log.retention_due(), Ordering::Relaxed);
                }
                publish_floor(&self.shared, &log);
                self.shared
                    .durable
                    .store(log.durable_head().0, Ordering::Release);
                if self.shared.replicator.is_none() {
                    self.shared
                        .head
                        .store(log.visible_head().0, Ordering::Release);
                }
                reset_tail_parkers_to(&self.shared, log.visible_head().0);
                *self
                    .shared
                    .hello
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner) = HelloCopy::of(&log);
                if self.shared.cap_secret.is_some() {
                    let mut bindings = self
                        .shared
                        .bindings
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner);
                    bindings.clear();
                    for (id, principal, off) in log.durable_bindings() {
                        bindings.insert(id, (principal.to_string(), off.0));
                    }
                }
            }
            (dropped, old_retire)
        };
        drop(old_retire);
        if dropped > 0 {
            notify_all_tails(&self.shared);
        }
        Ok(dropped)
    }

    /// Un-fence every fenced follower link on a `Replicated` leader (after an operator has
    /// truncated a diverged follower via [`Broker::truncate_replica_to`] or rotated an
    /// unauthorized capability), immediately redialing on the writer thread and catching
    /// up `[base..head)` so quorum watermark and adopted `LogIdentity` recover in one step.
    ///
    /// Returns the number of follower links that were un-fenced (`0` on a non-replicated
    /// broker or when no follower link was fenced).
    pub fn rejoin_followers(&self) -> io::Result<usize> {
        match submit_blocking(&self.shared, WriteKind::RejoinFollowers) {
            Ok((rejoined, _)) => Ok(usize::try_from(rejoined).unwrap_or(usize::MAX)),
            Err((code, msg)) => Err(crate::client::BrokerRefusal { code, msg }.into()),
        }
    }

    pub(crate) fn is_diverged(&self) -> bool {
        match self.shared.log.lock() {
            Ok(g) => g.is_diverged(),
            Err(p) => p.into_inner().is_diverged(),
        }
    }

    /// [`BrokerStats::writer_round_trips`] alone, read WITHOUT the log lock — what
    /// [`visible_head`](Self::visible_head) is to [`head`](Self::head).
    /// [`stats`](Self::stats) snapshots the log under its lock, so it waits out the
    /// writer's staging and promotion of a batch — and a writer parked at
    /// [`pause_next_batch`](Self::pause_next_batch), which holds the lock — though not
    /// the batch's write and flush, which run with the lock released (there it answers
    /// at once with the head before the batch, so it neither waits for a write nor
    /// blocks behind one); this takes no lock at all. The counter is bumped by
    /// the connection thread BEFORE it hands the op to the writer, so a test that has
    /// parked the writer ([`pause_next_batch`](Self::pause_next_batch)) reads here that
    /// a round trip is now queued behind the parked batch.
    pub fn writer_round_trips(&self) -> u64 {
        self.shared.writer_round_trips.load(Ordering::Relaxed)
    }

    /// Arm (or clear) the log's documented fault-injection seam — see
    /// [`InjectedFaults`]. A test hook; inert unless called.
    pub fn inject_faults(&self, faults: InjectedFaults) {
        self.shared
            .log
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .inject_faults(faults);
    }

    /// Arm the UNCLEAN-STOP seam: when this broker stops — its last listener's
    /// [`shutdown`](BrokerHandle::shutdown) (or that handle's drop), or the drop of a
    /// broker never served — it stops WITHOUT the clean close. Everything else about the
    /// stop is unchanged: the writer commits what was queued and is joined, the
    /// connections close, the log is latched shut — this broker writes nothing to it
    /// again, a retention call on the `Broker` value kept after the stop refused as after
    /// a clean close — and the log's lock is released, so the next open (in this process
    /// too) proceeds. But the log is not flushed in full, and `<log>.id` is left as this
    /// run last wrote it: the record its open wrote (`Open`, the floor at the open's
    /// head), unless the run itself rewrote it since (a full flush that failed records
    /// `Lossy`; a replica records the identity it adopted). That is what a killed process
    /// leaves, and what a power loss leaves minus the page cache, so the next open judges
    /// the log by the unclean-stop rules (the [`LogIdentity`](crate::LogIdentity) module
    /// docs). In ANOTHER boot a run that SERVED Ordered or Relaxed moves the generation
    /// once, with lineage at the head the open recovers, and a run served Strict moves
    /// nothing, its acks having been on stable media. In the SAME boot nothing moves
    /// only where the open can trust the page cache: the boot named (`Boot::Known`, or
    /// `Boot::Detect` on a host that names it) and the log on the boot volume
    /// (`Volume::Boot`, or `Volume::Detect` finding it there; see [`Boot`](crate::Boot)
    /// and [`Volume`](crate::Volume)). Under `Boot::Unknown`, or off the boot volume — a
    /// Linux tmpfs `/tmp` is, to `Volume::Detect` — every unclean stop of a run that
    /// served a weak tier moves the generation, a same-boot reopen included, exactly as a
    /// kill does there: a test that stands in "a process crash" names the boot and the
    /// volume.
    ///
    /// A test seam; inert unless called, and nothing in astream calls it. It exists so a
    /// test of a reader that keeps offsets outside the log (an embedder's bridge, its
    /// notifier, a cursor file) can stand in a crash or a reboot of a broker it serves in
    /// process. Without it such a test saved `<log>.id` after the open and wrote it back
    /// after the stop: it forged a file whose format, and the moments it is written at,
    /// are astream's own. It grants nothing a process cannot do to itself by dying, and
    /// its misuse costs the safe direction: a reboot after the stop moves a weak run's
    /// generation, and readers re-read. Armed, it stays armed for the broker's one stop;
    /// there is nothing to clear. The health sidecar (`<log>.health`) still gets its last
    /// word, which reports this process and which no open reads. A [`BrokerLog`] used
    /// directly needs no seam: dropped without [`close_clean`](BrokerLog::close_clean),
    /// it stops this way.
    pub fn arm_unclean_stop(&self) {
        self.shared.unclean_stop.store(true, Ordering::Release);
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

    /// Override how long an opted-in caught-up subscription goes with nothing written before
    /// the broker marks it (default [`IDLE_MARK`], 10 s). A parked tail looks at the
    /// clock once per liveness poll (200 ms, [`set_liveness_poll`](Self::set_liveness_poll)),
    /// so that is the finest interval served.
    /// Applies to subscriptions opened after the call.
    pub fn set_idle_mark(&self, interval: Duration) {
        self.shared.idle_mark_ms.store(
            interval.as_millis().clamp(1, u64::MAX as u128) as u64,
            Ordering::Relaxed,
        );
    }

    /// Override how often a subscriber tail checks that its subscriber is still there
    /// (default [`LIVENESS_POLL`], 200 ms): a parked tail wakes this often to probe its
    /// peer, look at the clock and mark an idle stream, and a tail that writes nothing
    /// probes at most this often. It bounds how long the thread and descriptor of a
    /// subscriber that left without a word outlive it, and is the finest interval
    /// [`set_idle_mark`](Self::set_idle_mark) can serve. It never delays a delivery: a
    /// commit wakes a parked tail through the `Condvar`, not this poll. Applies to
    /// subscriptions opened after the call.
    pub fn set_liveness_poll(&self, interval: Duration) {
        self.shared.liveness_poll_ms.store(
            interval.as_millis().clamp(1, u64::MAX as u128) as u64,
            Ordering::Relaxed,
        );
    }

    /// Override how long a TCP connection that keeps alive may go with nothing read
    /// from it before the broker ends it, firing its will (default
    /// [`KEEPALIVE_DEADLINE`], 60 s). Keep it a few times the interval clients keep
    /// alive at ([`KEEPALIVE_INTERVAL`]): shorter than that cuts live clients. Applies
    /// to connections whose first [`Request::Keepalive`] arrives after the call.
    pub fn set_keepalive_deadline(&self, deadline: Duration) {
        self.shared.keepalive_deadline_ms.store(
            deadline.as_millis().clamp(1, u64::MAX as u128) as u64,
            Ordering::Relaxed,
        );
    }

    /// Pause the next `Last` walk at the SCAN-ROUND BOUNDARY after round `round`:
    /// after that round has added its rows, before the next round re-takes the log
    /// lock — the exact window a concurrent publisher gets. One-shot: the first walk
    /// to reach that boundary takes the pause.
    ///
    /// A test seam; inert unless called. It exists so a test can OCCUPY that window
    /// instead of racing for it — the walk's connection thread stops there with the log
    /// lock released, so another thread may [`wait`](LastRoundPause::wait) for it,
    /// publish through a second connection and block on the ack, and the walk does not
    /// resume until that thread [`resume`](LastRoundPause::resume)s it (or drops the
    /// handle).
    pub fn pause_last_scan_round(&self, round: usize) -> LastRoundPause {
        let (reached_tx, reached_rx) = mpsc::channel();
        let (resume_tx, resume_rx) = mpsc::channel();
        *self
            .shared
            .last_round_pause
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = Some(RoundPause {
            round,
            reached: reached_tx,
            resume: resume_rx,
        });
        LastRoundPause {
            reached: reached_rx,
            resume: resume_tx,
        }
    }

    /// Pause the writer inside its NEXT batch: after it has taken the log lock and
    /// staged the batch, before it begins the commit — the part of a batch that still
    /// holds the log lock (staging, the seal, then the promotion; the write and the
    /// flush run without it, see [`pause_next_write`](Self::pause_next_write)). One-shot:
    /// the first batch to reach that point after this call takes the pause.
    ///
    /// A test seam; inert unless called. It exists so a test can OCCUPY the writer's
    /// lock hold instead of racing a real batch for it: the writer stops there with
    /// the log lock HELD, so another thread may [`wait`](BatchPause::wait) for it and
    /// then show that something completes without the log lock (it would hang
    /// otherwise), and the batch does not commit until that thread
    /// [`resume`](BatchPause::resume)s it (or drops the handle). Anything that needs the
    /// log lock — [`stats`](Self::stats) included — waits for the resume.
    ///
    /// Arming replaces any pause still armed (its [`wait`](BatchPause::wait) answers
    /// `false`); on a broker whose writer has stopped, `wait` answers `false` at once.
    pub fn pause_next_batch(&self) -> BatchPause {
        self.arm_batch_pause(BatchPoint::Staged)
    }

    /// Pause the writer inside its NEXT non-empty batch at the start of its WRITE: the
    /// batch staged, sealed, its flush chosen and its bytes taken, the log lock
    /// RELEASED, and not one byte of it written or flushed. One-shot, like
    /// [`pause_next_batch`](Self::pause_next_batch), and replaced or answered `false`
    /// the same way. A batch with nothing to write (every op deduplicated or refused)
    /// never lets the lock go and does not take this pause.
    ///
    /// A test seam; inert unless called. It exists so a test can stand where a reader
    /// stands beside a busy writer's write and fsync, and show what holds there: the log
    /// lock is free ([`stats`](Self::stats), `Fetch`, `Last` and a tail's catch-up all
    /// answer), the batch's records are invisible (the head has not moved), and
    /// retention waits for the batch rather than run beside it. Nothing is written until
    /// the test [`resume`](BatchPause::resume)s it (or drops the handle).
    pub fn pause_next_write(&self) -> BatchPause {
        self.arm_batch_pause(BatchPoint::Writing)
    }

    /// Pause the writer just before it ANSWERS its next batch: the batch is committed,
    /// its head published and the bindings it promoted copied for the attach path
    /// (`Shared::bindings`), the log lock released — and not one of its acks sent.
    /// One-shot, like [`pause_next_batch`](Self::pause_next_batch), and replaced or
    /// answered `false` the same way.
    ///
    /// A test seam; inert unless called. It exists so a test can show what a batch's
    /// acks may RELY on: anything a connection does on the strength of its ack happens
    /// after this point, so whatever a test finds already true here — a principal the
    /// batch bound attaching settled on another connection, with no round trip — is
    /// true for every ack the batch sends. The log lock is free in the window, so
    /// [`stats`](Self::stats) answers in it.
    pub fn pause_next_acks(&self) -> BatchPause {
        self.arm_batch_pause(BatchPoint::BeforeAcks)
    }

    /// Pause the writer inside the next batch that OWES A FULL FLUSH (the held head: an
    /// escalated record, a resend of one no full flush covers, a `flush_durable`), between
    /// the acks it sends at once and the flush: every op the held head does not keep back
    /// has been answered and the tails woken, the log lock is released, and the flush has
    /// not been issued. Batches that owe none pass the point by. One-shot, like
    /// [`pause_next_batch`](Self::pause_next_batch), and replaced or answered `false` the
    /// same way.
    ///
    /// A test seam; inert unless called. It exists so a test can hold the window the held
    /// head is FOR instead of racing a real flush through it: in it an escalated record
    /// must be unseen ([`visible_head`](Self::visible_head) at it, the durable head below
    /// it) and its op unanswered — an assertion that, made after the ack arrives, a broker
    /// that acked first and flushed a moment later passes whenever the test thread is
    /// slower than the flush.
    pub fn pause_next_flush(&self) -> BatchPause {
        self.arm_batch_pause(BatchPoint::BeforeFlush)
    }

    /// Arm the batch-pause seam at `at` (see [`BatchPauseSeam`]).
    fn arm_batch_pause(&self, at: BatchPoint) -> BatchPause {
        let (reached_tx, reached_rx) = mpsc::channel();
        let (resume_tx, resume_rx) = mpsc::channel();
        let mut seam = self
            .shared
            .batch_pause
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        // A stopped writer reaches no batch: the slot is not stored, its `reached`
        // sender drops here, and `wait` answers `false` instead of blocking.
        if !seam.writer_stopped {
            seam.slot = Some(BatchPauseSlot {
                at,
                reached: reached_tx,
                resume: resume_rx,
            });
            self.shared.batch_pause_armed.store(true, Ordering::Release);
        }
        BatchPause {
            reached: reached_rx,
            resume: resume_tx,
        }
    }

    /// Bind the Unix socket at `socket_path` and start accepting clients. Returns a
    /// [`BrokerHandle`] that shuts the broker down and unlinks the socket on demand.
    /// A leftover socket file is unlinked only if no socket is bound to it any more
    /// (stale, from a crashed broker); a LIVE broker there, or a socket nothing shows
    /// stale, is `AddrInUse`, never silently displaced, and a path that is not a socket
    /// at all is `AlreadyExists`, never removed. That holds for one put there while
    /// `serve` binds, too: the listener is bound under a private sibling name and then
    /// linked into place, which replaces nothing. Only where that name cannot be had
    /// (too long for a socket address, or a filesystem without hard links) does `serve`
    /// bind the path itself, and then a socket renamed over the path just after that
    /// bind is taken as its own, and a path removed just after it is `NotFound`.
    /// cfg(unix): std has no Unix-domain sockets on Windows — use
    /// [`serve_tcp`](Self::serve_tcp) there.
    #[cfg(unix)]
    pub fn serve(&self, socket_path: impl AsRef<Path>) -> io::Result<BrokerHandle> {
        let socket_path = socket_path.as_ref().to_path_buf();
        claim_socket_path(&socket_path)?;
        let (listener, node, wake) = Self::bind_unix(&socket_path)?;
        let polls = wake.is_none();
        if let Err(e) = listener.set_nonblocking(polls) {
            if let Some(w) = &wake {
                let _ = crate::store::remove_file_path(w);
            }
            return Err(e);
        }
        let shared = self.shared.clone();
        let listener_running = Arc::new(AtomicBool::new(true));
        let acc_running = Arc::clone(&listener_running);
        let (exited_tx, exited) = mpsc::channel::<()>();
        let turns = Arc::new(AtomicU64::new(0));
        let acc_turns = Arc::clone(&turns);
        let spawned = thread::Builder::new().spawn(move || {
            // Dropped as this thread returns: shutdown's signal that it left.
            let _exited = exited_tx;
            let acc = AcceptLoop {
                shared: &shared,
                listening: &acc_running,
                turns: &acc_turns,
                polls,
            };
            loop {
                let got = listener.accept();
                if !acc.turn(accept_failure(&got)) {
                    break;
                }
                let Ok((s, _)) = got else {
                    continue;
                };
                // Accepted sockets MUST be blocking (the frame reader uses
                // read_exact); a polling listener's non-blocking mode may be
                // inherited (BSD accept), so clear it.
                if polls {
                    let _ = s.set_nonblocking(false);
                }
                // Out of every child, as the listener is (`astream_sys::close_on_fork`).
                let _ = kept_from_children(&s);
                let sh = shared.clone();
                // Detached per-connection thread; ends when its socket ends.
                // A spawn that fails (thread exhaustion) drops this socket and
                // keeps accepting — `thread::spawn` would panic the acceptor.
                // Its client reads only a close, so the reason is said here.
                if let Err(e) = thread::Builder::new().spawn(move || {
                    let _ = handle_conn(&sh, Conn::Unix(s), Wire::Unix);
                }) {
                    let _ = writeln!(
                        io::stderr(),
                        "astream-broker: warn: closed an accepted connection: its thread did not start ({e})"
                    );
                }
                if acc.stopping() {
                    break;
                }
            }
        });
        let acceptor = match spawned {
            Ok(j) => j,
            Err(e) => {
                if let Some(w) = &wake {
                    let _ = crate::store::remove_file_path(w);
                }
                return Err(e);
            }
        };
        let listener_id = self.shared.listener_seq.fetch_add(1, Ordering::Relaxed);
        self.shared
            .listeners
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .insert(listener_id, format!("unix:{}", socket_path.display()));
        self.shared.active_listeners.fetch_add(1, Ordering::AcqRel);
        Ok(BrokerHandle {
            shared: self.shared.clone(),
            listener_id,
            listener_running,
            acceptor: Some(acceptor),
            wake: if polls {
                AcceptWake::Polls
            } else {
                AcceptWake::Blocks {
                    exited: Mutex::new(exited),
                    turns,
                }
            },
            endpoint: Endpoint::Unix {
                path: socket_path,
                node,
                wake,
            },
        })
    }

    /// Bind the listener [`serve`](Self::serve) publishes at `path`, with its identity,
    /// read before `path` names it, and its wake name ([`link_wake_name`]). Bound under
    /// a private sibling name, `<path>.<pid>.<n>`, which no other process knows, so the
    /// identity read there is the listener's own; then given `path` by
    /// [`link_into_place`], which never replaces a socket put there meanwhile, and its
    /// wake name from the private name; then the private name is removed. A stale one a
    /// killed broker left beside `path` is removed first ([`clear_private_names`]).
    ///
    /// Bound at `path` itself, its identity read there after the bind, when no private
    /// name fits a socket address (`SUN_LEN`), none can be bound, or it cannot be
    /// linked for another reason than a name already at `path`. A socket renamed over
    /// `path` between that bind and that read is taken as the listener's own; a path
    /// removed in between is `NotFound`, since no client could reach the listener.
    ///
    /// Either way the listener is kept from every child this process spawns before
    /// `path` names it: a child's exec-time close of its copy, under a descriptor scan,
    /// drains the listener and every connection it accepts.
    #[cfg(unix)]
    fn bind_unix(path: &Path) -> io::Result<(UnixListener, Option<SocketNode>, Option<PathBuf>)> {
        clear_private_names(path);
        if let Some((listener, private)) = bind_private(path) {
            #[cfg(test)]
            serve_hook(ServeAt::Bound);
            let node = node_at(&private);
            let placed = match kept_from_children(&listener) {
                Ok(()) => link_into_place(&private, path),
                Err(e) => Some(Err(e)),
            };
            let wake = match (&placed, node) {
                (Some(Ok(())), Some(n)) => link_wake_name(&private, path, n),
                _ => None,
            };
            let _ = crate::store::remove_file_path(&private);
            if let Some(placed) = placed {
                placed?;
                #[cfg(test)]
                serve_hook(ServeAt::Linked);
                return Ok((listener, node, wake));
            }
        }
        let listener = UnixListener::bind(path)?;
        #[cfg(test)]
        serve_hook(ServeAt::Bound);
        let node = match node_read(path) {
            Ok(n) => Some(n),
            Err(e)
                if matches!(
                    e.kind(),
                    io::ErrorKind::NotFound | io::ErrorKind::NotADirectory
                ) =>
            {
                return Err(io::Error::new(
                    io::ErrorKind::NotFound,
                    format!(
                        "{}: removed as the broker bound it, so no client can reach its listener",
                        path.display()
                    ),
                ));
            }
            Err(_) => None,
        };
        if let Err(e) = kept_from_children(&listener) {
            if let Some(n) = node {
                unlink_if_node(path, n);
            }
            return Err(e);
        }
        let wake = node.and_then(|n| link_wake_name(path, path, n));
        #[cfg(test)]
        serve_hook(ServeAt::Linked);
        Ok((listener, node, wake))
    }

    /// Serve one connection over `link`, a stream the embedder ALREADY authenticated as the
    /// holder of `peer_pubkey`: no listener, no handshake and no second identity. The peer is
    /// `identity_principal(&peer_pubkey)`, exactly as on [`serve_tcp_identity`](Self::serve_tcp_identity):
    /// a grant naming any other `n-` principal is refused at `Attach`, and a revoked key is
    /// refused here, ends this connection at once ([`revoke_identity`](Self::revoke_identity)),
    /// and drops its last will.
    ///
    /// The connection runs on a thread of its own, which the returned handle joins; it counts
    /// against the connection cap and shuts `link` as it ends. Dropping the handle detaches it.
    ///
    /// # Errors
    /// `PermissionDenied` for a revoked key or principal (`link` is shut); the thread's spawn.
    #[cfg(feature = "stream")]
    pub fn serve_stream(
        &self,
        link: Arc<dyn crate::stream_link::StreamLink>,
        peer_pubkey: [u8; 32],
    ) -> io::Result<JoinHandle<io::Result<()>>> {
        let end = crate::stream_link::LinkEnd::new(link);
        let stream_peer = PeerAuth::from_identity(peer_pubkey);
        if let Some(reason) = peer_revocation_reason(&self.shared, &stream_peer) {
            let _ = end.shutdown(Shutdown::Both);
            return Err(io::Error::new(io::ErrorKind::PermissionDenied, reason));
        }
        let shared = self.shared.clone();
        thread::Builder::new().spawn(move || {
            let conn = Conn::Stream(end.clone(), peer_pubkey);
            let res = handle_conn_with_peer(&shared, conn, Wire::Tcp, "stream", stream_peer);
            let _ = end.shutdown(Shutdown::Both);
            res
        })
    }

    /// Like [`serve`](Self::serve) but over TCP — multi-machine, PLAINTEXT and
    /// unauthenticated, so for a TRUSTED network only (the sealed transport is
    /// `serve_tcp_sealed`, with the `aead` feature). Binds `addr` (use `127.0.0.1:0`
    /// for an ephemeral port) and serves the SAME Frame protocol. Returns the handle;
    /// read the bound address from it if you bound port 0.
    pub fn serve_tcp(&self, addr: impl std::net::ToSocketAddrs) -> io::Result<BrokerHandle> {
        // Identity wrap: the raw TcpStream IS the connection stream.
        self.serve_tcp_with(addr, TcpWrap::Plain)
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
        self.serve_tcp_with(addr, TcpWrap::Sealed(key))
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
        self.serve_tcp_with(addr, TcpWrap::Handshake(psk))
    }

    /// Serve this broker over **zero-gap AEAD-over-UDP connection migration** (`AROM` v1;
    /// `docs/ROADMAP.md` §1) authenticated by `psk` with per-session ephemeral X25519
    /// forward secrecy, stateless HMAC `PKT_RETRY` source-address cookies, immutable 8-byte
    /// Connection IDs, and RFC 9000 §8.2 `PATH_CHALLENGE` / `PATH_RESPONSE` + 3x
    /// anti-amplification path validation.
    ///
    /// Clients connect with [`crate::client::Client::connect_udp_roaming`] and can migrate
    /// across new local [`std::net::UdpSocket`]s without dropping live subscriptions,
    /// pipelined publishes, attached capabilities, or falsely firing Last Wills.
    #[cfg(feature = "handshake")]
    pub fn serve_udp_roaming(
        &self,
        addr: impl std::net::ToSocketAddrs,
        psk: [u8; astream_aead::KEY_LEN],
    ) -> io::Result<BrokerHandle> {
        let sock = std::net::UdpSocket::bind(addr)?;
        kept_from_children(&sock)?;
        let dial = connectable_addr(sock.local_addr()?);
        let listener = astream_aead::RoamListener::from_socket(sock, psk)?;
        let shared = self.shared.clone();
        let listener_running = Arc::new(AtomicBool::new(true));
        let acc_running = Arc::clone(&listener_running);
        let acceptor = thread::Builder::new().spawn(move || {
            let mut listener = listener;
            loop {
                if !shared.running.load(Ordering::Relaxed) || !acc_running.load(Ordering::Relaxed) {
                    break;
                }
                match listener.accept_timeout(ACCEPT_POLL) {
                    Ok(Some(roam_stream)) => {
                        if !shared.running.load(Ordering::Relaxed)
                            || !acc_running.load(Ordering::Relaxed)
                        {
                            break;
                        }
                        shared.accepted.fetch_add(1, Ordering::Relaxed);
                        let sh = shared.clone();
                        let _ = thread::Builder::new().spawn(move || {
                            let _ = handle_conn_with_peer(
                                &sh,
                                Conn::Roam(roam_stream),
                                Wire::Tcp,
                                "roam",
                                PeerAuth::none(),
                            );
                        });
                    }
                    Ok(None) => {}
                    Err(_) => break,
                }
            }
            listener.shutdown();
        })?;
        let listener_id = self.shared.listener_seq.fetch_add(1, Ordering::Relaxed);
        self.shared
            .listeners
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .insert(listener_id, format!("roam:{dial}"));
        self.shared.active_listeners.fetch_add(1, Ordering::AcqRel);
        Ok(BrokerHandle {
            shared: self.shared.clone(),
            listener_id,
            listener_running,
            acceptor: Some(acceptor),
            wake: AcceptWake::Polls,
            endpoint: Endpoint::Tcp {
                dial,
                shown: dial.to_string(),
            },
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
        self.serve_tcp_with(
            addr,
            TcpWrap::Identity {
                identity: Box::new(identity),
                authorized_clients,
            },
        )
    }

    /// Like [`serve_tcp_identity`](Self::serve_tcp_identity) but bound to an **external
    /// identity authority** (Rung 9): each connection runs a mutual certificate-authenticated
    /// SIGMA handshake using `host_rotator` (supporting live overlapping host-key/certificate
    /// rotation and out-of-process `SSH_AUTH_SOCK` signing via [`astream_aead::SshAgentSigner`])
    /// and verifies client `ACRT` certificates against `client_trust` (multi-root CA rollover
    /// plus monotonic KRL revocation). Session keys derive solely from ephemeral X25519.
    ///
    /// On a guarded broker, any capability naming a principal (`p=<principal>`) must match
    /// the authenticated client certificate's principal, and open connections/subscriptions
    /// automatically terminate when the peer certificate expires or its serial/principal/key
    /// is revoked. Clients connect with [`crate::client::Client::connect_tcp_certified`].
    #[cfg(feature = "identity")]
    pub fn serve_tcp_certified(
        &self,
        addr: impl std::net::ToSocketAddrs,
        host_rotator: astream_aead::HostCertRotator,
        client_trust: astream_aead::SharedCertTrust,
    ) -> io::Result<BrokerHandle> {
        self.serve_tcp_with(
            addr,
            TcpWrap::Certified {
                host_rotator,
                client_trust,
            },
        )
    }

    /// Shared TCP accept loop, given how each accepted [`TcpStream`] is wrapped into
    /// the per-connection [`Conn`] ([`TcpWrap`]: as it is for plaintext, the sealed
    /// handshake for the AEAD transports). The wrap runs on the connection's own
    /// thread, never on the acceptor, under pre-authentication bounds — a deadline
    /// and a cap on how many connections may be inside their wrap at once — so a
    /// peer that cannot authenticate can hold up neither other accepts nor a
    /// thread for long (the sealed handshake itself bounds memory: it allocates
    /// nothing an unkeyed peer can size). The cap counts connections INSIDE the
    /// wrap, so the instant plaintext wrap never holds a slot and a burst of
    /// plaintext accepts is never refused by it. A connection that fails to wrap
    /// is dropped.
    fn serve_tcp_with(
        &self,
        addr: impl std::net::ToSocketAddrs,
        wrap: TcpWrap,
    ) -> io::Result<BrokerHandle> {
        // How long a connection may take to complete its wrap (the sealed handshake):
        // the socket read timeout until the wrap returns, lifted once it has — the
        // protocol above sets its own timeouts.
        const PREAUTH_TIMEOUT: Duration = Duration::from_secs(5);
        // How many connections may sit inside the wrap at once; an accept beyond
        // it is dropped at once rather than given a thread.
        const MAX_PREAUTH_CONNS: usize = 64;

        let listener = TcpListener::bind(addr)?;
        // Out of every child, as a Unix listener is (`astream_sys::close_on_fork`).
        kept_from_children(&listener)?;
        // Report a *connectable* address: a wildcard bind (0.0.0.0 / ::) is not a valid
        // destination for a client, so map an unspecified host to loopback (keeping
        // the port) for `tcp_addr`. It is also what shutdown dials to get the
        // blocking acceptor out of `accept()` — an address cannot be unlinked, so TCP
        // needs no wake name and never polls.
        let dial = connectable_addr(listener.local_addr()?);
        let transport = wrap.transport_name();
        let shared = self.shared.clone();
        let listener_running = Arc::new(AtomicBool::new(true));
        let acc_running = Arc::clone(&listener_running);
        let wrap = Arc::new(wrap);
        let (exited_tx, exited) = mpsc::channel::<()>();
        let turns = Arc::new(AtomicU64::new(0));
        let acc_turns = Arc::clone(&turns);
        let acceptor = thread::Builder::new().spawn(move || {
            // Dropped as this thread returns: shutdown's signal that it left.
            let _exited = exited_tx;
            // Connections currently INSIDE their wrap (the sealed handshake): the
            // pre-authentication population. Counted on the connection thread
            // around the wrap itself — so an instant wrap (plaintext) holds a slot
            // for no measurable time — and pre-checked here so a peer beyond the
            // cap is dropped without being given a thread.
            let preauth = Arc::new(std::sync::atomic::AtomicUsize::new(0));
            let acc = AcceptLoop {
                shared: &shared,
                listening: &acc_running,
                turns: &acc_turns,
                polls: false,
            };
            loop {
                let got = listener.accept();
                if !acc.turn(accept_failure(&got)) {
                    break;
                }
                let Ok((s, _)) = got else {
                    continue;
                };
                let _ = s.set_nodelay(true);
                let _ = kept_from_children(&s);
                // Beyond the pre-authentication cap the socket is dropped here.
                if preauth.load(Ordering::Acquire) < MAX_PREAUTH_CONNS {
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
                        let wrapped = wrap.wrap(&sh, s);
                        preauth.fetch_sub(1, Ordering::AcqRel);
                        // Couldn't establish the (sealed) transport — the socket
                        // drops with the Err.
                        if let Ok((stream, peer)) = wrapped {
                            let _ = stream.set_read_timeout(None);
                            let _ = handle_conn_with_peer(&sh, stream, Wire::Tcp, transport, peer);
                        }
                    });
                }
                if acc.stopping() {
                    break;
                }
            }
        })?;
        let listener_id = self.shared.listener_seq.fetch_add(1, Ordering::Relaxed);
        self.shared
            .listeners
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .insert(listener_id, format!("{transport}:{dial}"));
        self.shared.active_listeners.fetch_add(1, Ordering::AcqRel);
        Ok(BrokerHandle {
            shared: self.shared.clone(),
            listener_id,
            listener_running,
            acceptor: Some(acceptor),
            wake: AcceptWake::Blocks {
                exited: Mutex::new(exited),
                turns,
            },
            endpoint: Endpoint::Tcp {
                dial,
                shown: dial.to_string(),
            },
        })
    }
}

/// How [`Broker::serve_tcp_with`] makes each accepted [`TcpStream`] the [`Conn`] it
/// serves: as it is (plaintext), or through one of the sealed handshakes. It runs on
/// the connection's own thread, under the pre-authentication bounds.
enum TcpWrap {
    /// [`Broker::serve_tcp`]: the raw stream IS the connection stream.
    Plain,
    /// [`Broker::serve_tcp_sealed`]: the sealed handshake under the pre-shared key.
    #[cfg(feature = "aead")]
    Sealed([u8; astream_aead::KEY_LEN]),
    /// [`Broker::serve_tcp_handshake`]: the forward-secret key agreement,
    /// authenticated by the pre-shared key.
    #[cfg(feature = "handshake")]
    Handshake([u8; astream_aead::KEY_LEN]),
    /// [`Broker::serve_tcp_identity`]: the mutual signed-DH handshake, against the
    /// authorized client keys. The keypair is boxed: it is most of the enum's size, and
    /// one listener holds one.
    #[cfg(feature = "identity")]
    Identity {
        identity: Box<astream_aead::IdentityKeypair>,
        authorized_clients: Vec<[u8; astream_aead::ID_PUB_LEN]>,
    },
    /// [`Broker::serve_tcp_certified`]: mutual CA-certified SIGMA with overlapping
    /// host-key rotation and external `ssh-agent` signing support.
    #[cfg(feature = "identity")]
    Certified {
        host_rotator: astream_aead::HostCertRotator,
        client_trust: astream_aead::SharedCertTrust,
    },
}

impl TcpWrap {
    const fn transport_name(&self) -> &'static str {
        match self {
            TcpWrap::Plain => "tcp",
            #[cfg(feature = "aead")]
            TcpWrap::Sealed(_) => "sealed",
            #[cfg(feature = "handshake")]
            TcpWrap::Handshake(_) => "handshake",
            #[cfg(feature = "identity")]
            TcpWrap::Identity { .. } => "identity",
            #[cfg(feature = "identity")]
            TcpWrap::Certified { .. } => "certified",
        }
    }
    /// The connection `s` becomes, and the [`PeerAuth`] identity/certificate it proved.
    /// `shared` is read for the live revocation sets.
    #[cfg_attr(not(feature = "identity"), allow(unused_variables))]
    fn wrap(&self, shared: &Shared, s: TcpStream) -> io::Result<(Conn, PeerAuth)> {
        match self {
            TcpWrap::Plain => Ok((Conn::Tcp(s), PeerAuth::none())),
            #[cfg(feature = "aead")]
            TcpWrap::Sealed(key) => {
                let sealed = astream_aead::SealedStream::handshake_server(s, *key)?;
                Ok((Conn::Sealed(sealed), PeerAuth::none()))
            }
            #[cfg(feature = "handshake")]
            TcpWrap::Handshake(psk) => {
                // Bound the handshake I/O: a peer that connects then stalls (sends
                // nothing, or a partial message) must not park this thread + fd
                // forever — nothing gates the pre-handshake read, so an unauthenticated
                // slowloris would otherwise exhaust threads unbounded. Reset to blocking
                // once the handshake completes; the request loop and tail_loop then set
                // their own timeouts.
                s.set_read_timeout(Some(HANDSHAKE_TIMEOUT))?;
                s.set_write_timeout(Some(HANDSHAKE_TIMEOUT))?;
                let sealed = astream_aead::server_handshake(s, psk)?;
                sealed.get_ref().set_read_timeout(None)?;
                sealed.get_ref().set_write_timeout(None)?;
                Ok((Conn::Sealed(sealed), PeerAuth::none()))
            }
            #[cfg(feature = "identity")]
            TcpWrap::Identity {
                identity,
                authorized_clients,
            } => {
                s.set_read_timeout(Some(HANDSHAKE_TIMEOUT))?;
                s.set_write_timeout(Some(HANDSHAKE_TIMEOUT))?;
                let (sealed, client_id) =
                    astream_aead::server_identity_handshake(s, identity, authorized_clients)?;
                let peer = PeerAuth::from_identity(client_id);
                if let Some(reason) = peer_revocation_reason(shared, &peer) {
                    return Err(io::Error::new(io::ErrorKind::PermissionDenied, reason));
                }
                sealed.get_ref().set_read_timeout(None)?;
                sealed.get_ref().set_write_timeout(None)?;
                Ok((Conn::Sealed(sealed), peer))
            }
            #[cfg(feature = "identity")]
            TcpWrap::Certified {
                host_rotator,
                client_trust,
            } => {
                s.set_read_timeout(Some(HANDSHAKE_TIMEOUT))?;
                s.set_write_timeout(Some(HANDSHAKE_TIMEOUT))?;
                let now_ms = now_unix_ms();
                let trust_snap = client_trust.snapshot();
                let (sealed, verified) =
                    astream_aead::server_cert_handshake(s, host_rotator, &trust_snap, now_ms)?;
                let peer = PeerAuth::from_cert(verified);
                if let Some(reason) = peer_revocation_reason(shared, &peer) {
                    return Err(io::Error::new(io::ErrorKind::PermissionDenied, reason));
                }
                sealed.get_ref().set_read_timeout(None)?;
                sealed.get_ref().set_write_timeout(None)?;
                Ok((Conn::Sealed(sealed), peer))
            }
        }
    }
}

/// [`Broker::stats`]: the log's snapshot under its lock, and the counters beside it.
fn stats_of(shared: &Shared) -> BrokerStats {
    let log = shared
        .log
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .stats();
    let visible_head = shared.head.load(Ordering::Acquire);
    let active_conns = shared
        .conns
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .len();
    let active_listeners = shared.active_listeners.load(Ordering::Acquire);
    // Read once, the guard dropped here: a second lock of it inside the literal below
    // would wait on the first's temporary.
    #[cfg(feature = "retention")]
    let (retention_ticks, retention_skips) = {
        let t = shared
            .tick
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        (t.ticks, t.skips)
    };
    #[cfg(not(feature = "retention"))]
    let (retention_ticks, retention_skips) = (0, 0);
    BrokerStats {
        origin_refused: shared.origin_refused.load(Ordering::Relaxed),
        origin_unknown: shared.origin_unknown.load(Ordering::Relaxed),
        log,
        visible_head,
        active_conns,
        active_listeners,
        accepted: shared.accepted.load(Ordering::Relaxed),
        acceptor_wakeups: shared.acceptor_wakeups.load(Ordering::Relaxed),
        acceptor_sleeps: shared.acceptor_sleeps.load(Ordering::Relaxed),
        acceptors_abandoned: shared.acceptors_abandoned.load(Ordering::Relaxed),
        writer_round_trips: shared.writer_round_trips.load(Ordering::Relaxed),
        writer_batches: shared.writer_batches.load(Ordering::Relaxed),
        writer_wakeups: shared.writer_wakeups.load(Ordering::Relaxed),
        empty_batches: shared.empty_batches.load(Ordering::Relaxed),
        binds_settled: shared.binds_settled.load(Ordering::Relaxed),
        wills_settled: shared.wills_settled.load(Ordering::Relaxed),
        tail_broadcasts: shared.tail_broadcasts.load(Ordering::Relaxed),
        selective_tail_wakes: shared.selective_tail_wakes.load(Ordering::Relaxed),
        rate_limited: shared.rate_limited.load(Ordering::Relaxed),
        tail_wakeups: shared.tail_wakeups.load(Ordering::Relaxed),
        peer_probes: shared.peer_probes.load(Ordering::Relaxed),
        parked_tails: shared.parked_tails.load(Ordering::Relaxed),
        retention_waits: shared.retention_waits.load(Ordering::Relaxed),
        retention_ticks,
        retention_skips,
    }
}

/// `n` as a count in the health snapshot (a `usize` never exceeds a `u64` here; the
/// saturation is for the type, not a case).
fn count64(n: usize) -> u64 {
    u64::try_from(n).unwrap_or(u64::MAX)
}

/// [`Broker::health`]: [`stats_of`] (the log lock), then the heads and the identity from
/// the copies beside the log, and the poison, the tier served (with the latch the copy
/// may not carry yet) and the flush counts as the `Hello` answer reads them
/// ([`hello_answer`]) — read last, so a poison the snapshot's other facts were taken
/// under is in it, and so is the latch that came with it.
fn health_of(shared: &Shared) -> crate::health::BrokerHealth {
    let stats = stats_of(shared);
    let told = shared
        .hello
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .clone();
    let HelloCopy { identity, ext } =
        hello_answer(told, &shared.vitals, shared.has_sticky_batch_refusal);
    let served = match ext.durability {
        Some(s) => s,
        None => shared
            .log
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .served(),
    };
    let (poisoned, flushes) = match ext.health {
        Some(h) => (h.poisoned, h.flushes),
        None => (None, shared.vitals.flush_counts()),
    };
    crate::health::BrokerHealth {
        pid: std::process::id(),
        written_at_ms: now_unix_ms(),
        identity,
        served,
        base: stats.log.base.0,
        head: stats.log.head.0,
        visible_head: stats.visible_head,
        durable_head: shared.durable.load(Ordering::Acquire),
        retained_records: count64(stats.log.retained_records),
        retained_bytes: count64(stats.log.retained_bytes),
        distinct_subjects: count64(stats.log.distinct_subjects),
        bound_producers: count64(stats.log.bound_producers),
        pending_wills: count64(stats.log.pending_wills),
        group_commits: count64(stats.log.group_commits),
        replica: stats.log.is_replica,
        active_conns: count64(stats.active_conns),
        parked_tails: count64(stats.parked_tails),
        flushes,
        process_flushes: Some(astream_sys::flush_tally()),
        process_flush_times: Some(astream_sys::flush_times()),
        resident: Some(crate::health::Residency {
            records: count64(stats.log.resident_records),
            bytes: count64(stats.log.resident_bytes),
        }),
        poisoned,
    }
}

/// [`Broker::write_health`]. `running` is read under the health mutex, which
/// [`stop_health`] takes after clearing it: a write either lands before the stop lets
/// the file go, or is refused — never a held file for a log that has closed.
///
/// Says, beside the write's outcome, whether the snapshot it took NAMES THE POISON: what
/// the period's thread waits on next ([`health_loop`]).
fn write_health_of(shared: &Shared) -> (bool, io::Result<()>) {
    let snapshot = health_of(shared);
    let named = snapshot.poisoned.is_some();
    let mut slot = shared
        .health
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    if !shared.running.load(Ordering::Acquire) {
        return (
            named,
            Err(io::Error::other(
                "the broker has stopped serving its log; it publishes no health",
            )),
        );
    }
    let file = match slot.as_mut() {
        Some(f) => f,
        None => slot.insert(crate::health::HealthFile::new(&shared.log_path)),
    };
    (named, file.write(&snapshot))
}

/// [`Broker::keep_health`]'s thread: sleep a period — or, while the last snapshot it
/// tried to write did not name the poison, until the log is poisoned — then write;
/// until the broker stops. `named` is what [`keep_health`](Broker::keep_health)'s own
/// first write said. A failed write is said on stderr once per distinct error, then
/// tried again next period.
///
/// WHY THE SNAPSHOT, and not a look at the poison before each wait. A poison that lands
/// after a write's snapshot is taken but before that look — while the file is created,
/// locked, written and renamed, which is slow on exactly the failing disk that poisons a
/// log — is in no file, yet the look finds it set, and its wake was spent while nobody
/// waited: the thread would sleep a whole period while the sidecar said `poisoned=no`
/// of a log that refuses every write. Waiting on what the file says closes that: a
/// snapshot that did not name the poison is followed at once by one that does. And one
/// that named it but could not be written waits the period, as any failed write does,
/// rather than spinning on a disk that fails.
fn health_loop(shared: &Shared, every: Duration, mut named: bool) {
    let mut said: Option<String> = None;
    loop {
        let deadline = Instant::now().checked_add(every);
        shared.vitals.wait(deadline, &shared.running, !named);
        if !shared.running.load(Ordering::Acquire) {
            return;
        }
        let (now_named, res) = write_health_of(shared);
        named = now_named;
        match res {
            Ok(()) => said = None,
            Err(e) => {
                let msg = e.to_string();
                if said.as_deref() != Some(msg.as_str()) {
                    eprintln!(
                        "astream-broker: {}: could not write its health sidecar ({msg}); \
                         trying again every {} ms",
                        shared.log_path.display(),
                        every.as_millis()
                    );
                    said = Some(msg);
                }
            }
        }
    }
}

/// THE LOG'S STOP, once the writer is joined (`running` is already cleared and the
/// waiters woken): close the log cleanly — a full flush, then `Closed` in its sidecar —
/// so a reboot after this stop keeps the identity at any tier; then the health
/// sidecar's last word ([`stop_health`]); then the log's file lock, released last. The
/// release latches the log shut (`BrokerLog::unlock`), whether the clean close ran,
/// failed or was skipped under the unclean-stop seam: from then on a successor may serve
/// the file, and nothing this broker still holds — the `Broker` value, a retention call
/// on it — may write to it.
///
/// The close comes BEFORE the last word, which is what makes that word the log's final
/// state: the clean close moves the durable head to the head, and a snapshot taken
/// before it told a stopped Relaxed or Ordered broker's records as never durable when
/// the close had flushed them all. The durable head the close reached is published to
/// the copy the snapshot reads ([`Shared::durable`]); a close that failed leaves it
/// where it was, so the last word says what is not known durable. The log's guard is
/// let go for the snapshot, which takes it ([`stats_of`]): the writer is joined, so
/// nothing appends in between.
fn stop_log(shared: &Shared) {
    {
        let mut log = shared
            .log
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        // Under the unclean-stop seam (`Broker::arm_unclean_stop`) the log is left as a
        // killed process leaves it: no full flush, `<log>.id` as the run last wrote it.
        // The unlock below still latches it shut, as a kill leaves no writer behind.
        if !shared.unclean_stop.load(Ordering::Acquire) {
            log.close_clean_at_shutdown();
        }
        shared
            .durable
            .store(log.durable_head().0, Ordering::Release);
    }
    stop_health(shared);
    shared
        .log
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .unlock();
}

/// Stop keeping `<log>.health`: join the period's thread, write the last snapshot — the
/// writer is joined and the log closed ([`stop_log`]), so it is the log's final state —
/// and let the file go. Called BEFORE the log's own lock is released, so no reader is
/// told a broker serves a log it has closed; a reader in between reads the writer
/// `Gone` a moment early, the safe direction.
fn stop_health(shared: &Shared) {
    let thread = shared
        .health_thread
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .take();
    if let Some(t) = thread {
        let _ = t.join();
    }
    let snapshot = health_of(shared);
    let mut slot = shared
        .health
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    if let Some(file) = slot.as_mut() {
        if let Err(e) = file.write(&snapshot) {
            eprintln!(
                "astream-broker: {}: could not write its last health snapshot ({e}); the \
                 one before it stays",
                shared.log_path.display()
            );
        }
        file.release();
    }
    *slot = None;
}

impl Drop for Broker {
    fn drop(&mut self) {
        // When `serve*` has been called, the active `BrokerHandle`(s) own the writer
        // lifecycle and shut it down when the last listener stops. If `serve*` was
        // never called (`active_listeners == 0`), this `Broker` IS the lifecycle: stop
        // the writer and release the log's file lock.
        if self.shared.active_listeners.load(Ordering::Acquire) == 0 {
            // A broker that only ever adopted streams has no handle to end them.
            #[cfg(feature = "stream")]
            {
                self.shared.running.store(false, Ordering::Relaxed);
                notify_all_tails(&self.shared);
                BrokerHandle::force_close_conns(&self.shared);
            }
            stop_writer(&self.shared);
        }
    }
}

impl Broker {
    /// Stop serving connections, finish queued writes, flush the log and mark its run closed.
    /// This also closes a broker served only through adopted streams, without waiting for its
    /// owner to drop. Listener handles should be shut down first to remove their endpoints.
    /// Repeated calls after shutdown has completed do nothing.
    pub fn shutdown(&self) {
        self.shared.running.store(false, Ordering::Relaxed);
        notify_all_tails(&self.shared);
        self.shared.vitals.wake();
        if let Some(rep) = &self.shared.replicator {
            rep.shutdown_links();
        }
        BrokerHandle::force_close_conns(&self.shared);
        stop_writer(&self.shared);
    }
}

/// Stop the shared writer thread and release the log: the last step of the last
/// listener's [`BrokerHandle::shutdown`], and all of dropping a [`Broker`] never
/// served. Clears `running`, queues the writer's STOP behind every op already queued,
/// and joins the writer once it has committed them and whatever else was queued when
/// it got there ([`writer_loop`]) — so its final batch is done. Nothing more is
/// appended then, so the log is closed cleanly before its lock is released to a
/// successor ([`stop_log`]), and a reboot after this stop keeps the identity at any
/// tier — unless [`Broker::arm_unclean_stop`] armed the seam that skips the clean
/// close. The join waits on that final batch and nothing
/// else: the writer sleeps on its queue, and the stop wakes it at once. A no-op once
/// the writer was taken.
fn stop_writer(shared: &Shared) {
    // The retention tick first: it finishes the tick it is in, so none meets the log
    // closed below. Idempotent, as the rest is.
    stop_ticker(shared);
    let Some(w) = shared
        .writer
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .take()
    else {
        return;
    };
    shared.running.store(false, Ordering::Relaxed);
    // A `wait_poisoned` and the health thread sleep on the vitals: wake them to read
    // `running`.
    shared.vitals.wake();
    // The writer holds the queue's receiver until it returns, so this lands; it fails
    // only when the writer is gone already (it panicked), and the join answers at once.
    let _ = shared.writes.send(Queued::Stop);
    let _ = w.join();
    // The writer is joined, so nothing more is appended: close the log cleanly, then
    // the health sidecar's last word, then the log's lock.
    stop_log(shared);
}

/// Owns a running listener acceptor; [`shutdown`](BrokerHandle::shutdown) stops this
/// listener and (for a Unix socket) unlinks it. When the LAST active `BrokerHandle`
/// on a [`Broker`] shuts down, it also stops the shared writer thread, closes all live
/// connections, and releases the log's file lock. Dropping the handle shuts down too.
pub struct BrokerHandle {
    shared: Arc<Shared>,
    listener_id: u64,
    listener_running: Arc<AtomicBool>,
    acceptor: Option<JoinHandle<()>>,
    wake: AcceptWake,
    endpoint: Endpoint,
}

impl BrokerHandle {
    /// The bound TCP address (useful when serving on port 0), or `None` for a Unix
    /// socket.
    pub fn tcp_addr(&self) -> Option<&str> {
        match &self.endpoint {
            Endpoint::Tcp { shown, .. } => Some(shown),
            #[cfg(unix)]
            Endpoint::Unix { .. } => None,
        }
    }

    /// Whether the socket path `serve` bound names this listener now, by the identity
    /// `serve` read before the path named it: `Some(false)` once the path was unlinked,
    /// or another socket (or anything else) is there. A symlink there is followed, as a
    /// client's connect follows it: one to this listener's own socket names it. `None`
    /// when that cannot be told: TCP, a Unix listener whose identity `serve` could not
    /// read, or a read of the path that failed otherwise than by its absence.
    pub fn names_listener(&self) -> Option<bool> {
        match &self.endpoint {
            Endpoint::Tcp { .. } => None,
            #[cfg(unix)]
            Endpoint::Unix { path, node, .. } => {
                let node = (*node)?;
                match std::fs::metadata(path) {
                    Ok(now) => Some(SocketNode::of(&now) == node),
                    Err(e)
                        if matches!(
                            e.kind(),
                            io::ErrorKind::NotFound | io::ErrorKind::NotADirectory
                        ) =>
                    {
                        Some(false)
                    }
                    Err(_) => None,
                }
            }
        }
    }

    /// Whether this listener's acceptor blocks in `accept()` — a new connection is
    /// taken the instant it arrives and an idle listener never wakes. Always `true` for
    /// TCP. `false` for a Unix socket that could not get its `<socket>.wake` name — too
    /// long for a socket address, a hard link the filesystem refuses, or a foreign file
    /// or another broker's live socket already there: that acceptor polls (every 20 ms),
    /// and a connection waits out up to one poll.
    pub fn blocks_in_accept(&self) -> bool {
        matches!(self.wake, AcceptWake::Blocks { .. })
    }

    /// Dial this listener once to wake a blocking acceptor: through `<socket>.wake`,
    /// else the socket path, each only while it still names the listener (a name
    /// someone replaced would wake a stranger); for TCP, the bound address. `None` when
    /// no dial connected. A dial that connects may still have reached another listener
    /// (a loopback-specific bind beside a wildcard one; a recorded inode that was
    /// never ours): [`Self::wake_acceptor`] trusts only this acceptor's own answer.
    fn dial_listener(&self) -> Option<WakeDial> {
        match &self.endpoint {
            Endpoint::Tcp { dial, .. } => {
                match TcpStream::connect_timeout(dial, ACCEPT_WAKE_RETRY) {
                    Ok(s) => Some(WakeDial::Tcp(s)),
                    Err(_) => None,
                }
            }
            #[cfg(unix)]
            Endpoint::Unix { path, node, wake } => {
                let node = (*node)?;
                if let Some(wake_path) = wake {
                    if node_at(wake_path) == Some(node) {
                        if let Ok(s) = UnixStream::connect(wake_path) {
                            return Some(WakeDial::Unix(s));
                        }
                    }
                }
                if node_at(path) == Some(node) {
                    if let Ok(s) = UnixStream::connect(path) {
                        return Some(WakeDial::Unix(s));
                    }
                }
                None
            }
        }
    }

    /// Get this listener's acceptor out of `accept()` once the flags are cleared:
    /// `true` when it has left (join it), `false` when it is ABANDONED.
    ///
    /// A polling acceptor leaves by itself within [`ACCEPT_POLL`]. A blocking one is
    /// dialed, and its exit signal awaited for [`ACCEPT_WAKE_RETRY`], again and again
    /// until the signal fires: one dial is enough unless the acceptor read a stale flag
    /// or was busy, and a repeat costs one more queued connection the closing listener
    /// discards. [`ACCEPT_WAKE_ATTEMPTS`] rounds in a row that THIS acceptor never
    /// answers — its own `accept()` did not return, whether or not the dial connected
    /// somewhere — give up: no name reaches it, or another listener answers in its
    /// place, and waiting would turn shutdown's bound into a hang (see
    /// [`BrokerStats::acceptors_abandoned`]). A busy acceptor answers as soon as it is
    /// back in `accept()`, since the dial is queued on its listener.
    fn wake_acceptor(&self) -> bool {
        let AcceptWake::Blocks { exited, turns } = &self.wake else {
            return true;
        };
        let exited = exited
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let mut unanswered: u32 = 0;
        loop {
            if !matches!(exited.try_recv(), Err(mpsc::TryRecvError::Empty)) {
                return true;
            }
            let before = turns.load(Ordering::Relaxed);
            let dial = self.dial_listener();
            if !matches!(
                exited.recv_timeout(ACCEPT_WAKE_RETRY),
                Err(mpsc::RecvTimeoutError::Timeout)
            ) {
                return true;
            }
            drop(dial);
            if turns.load(Ordering::Relaxed) != before {
                unanswered = 0;
            } else {
                unanswered = unanswered.saturating_add(1);
                if unanswered >= ACCEPT_WAKE_ATTEMPTS {
                    return false;
                }
            }
        }
    }

    /// Force-close every registered connection socket, so a thread parked in a
    /// blocking read_frame (a quiet producer) or a wedged socket write returns at
    /// once and is reaped — along with its ack-writer thread and cloned fd.
    fn force_close_conns(shared: &Shared) {
        for (_, c) in shared
            .conns
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .drain()
        {
            c.shutdown_both();
        }
    }

    /// Stop this handle's acceptor and clean up its endpoint. When this is the last
    /// active listener on the [`Broker`], also wake parked subscribers, force-close
    /// every live connection (a connection thread has no idle timeout unless its client
    /// keeps alive, [`KEEPALIVE_DEADLINE`] — this is what reaps the rest), join the
    /// shared writer thread, and release the log's file lock. Follower shutdown
    /// handles include sockets authenticating a capability. Name resolution, dialing
    /// each address and platform calls are not a hard wall-clock bound.
    pub fn shutdown(&mut self) {
        let Some(j) = self.acceptor.take() else {
            return;
        };
        self.shared
            .listeners
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .remove(&self.listener_id);
        self.listener_running.store(false, Ordering::Relaxed);
        let prev = self.shared.active_listeners.fetch_sub(1, Ordering::AcqRel);
        let is_last = prev <= 1;
        if is_last {
            self.shared.running.store(false, Ordering::Relaxed);
            // Wake parked subscriber threads so they observe shutdown and exit.
            notify_all_tails(&self.shared);
            // And a `wait_poisoned` and the health thread, asleep on the vitals.
            self.shared.vitals.wake();
            // Unblock the writer if it is parked on a follower that never answers.
            if let Some(rep) = &self.shared.replicator {
                rep.shutdown_links();
            }
            Self::force_close_conns(&self.shared);
        }
        // A blocking acceptor is dialed out of `accept()` (a polling one observes the
        // flags within ACCEPT_POLL), then joined. One no dial reaches any more — no name
        // left, or another listener answering in its place — is left parked rather
        // than waited on forever: it holds only its listener and an `Arc` of the shared
        // state, and if a connection ever reaches it, it sees the cleared flags and
        // returns.
        let reached = self.wake_acceptor();
        if reached {
            let _ = j.join();
        } else {
            self.shared
                .acceptors_abandoned
                .fetch_add(1, Ordering::Relaxed);
            drop(j);
        }
        if is_last {
            // A connection the acceptor handed off just before exiting registers itself on
            // its own thread — possibly after the drain above. Drain again now that no more
            // can arrive; handle_conn also leaves on its own if it sees `running` false
            // right after registering, so between the two no connection is missed.
            Self::force_close_conns(&self.shared);
            // Stop the writer behind whatever is queued — its final batch done, never an
            // idle poll waited out — then close the log cleanly before its lock is
            // released to a successor.
            stop_writer(&self.shared);
        }
        // Unlink the socket path and the wake name — each only while it still names
        // THIS listener: the embedder may have unlinked the path, and another broker
        // may since have bound its own socket there. An ABANDONED acceptor leaves the
        // socket path alone: no dial through it reached this acceptor, so a path that
        // still carries `node` names some other socket — one renamed over the path
        // between this listener's bind there and its identity read (`bind_unix`'s
        // fallback), whose inode this one recorded. The wake name is this broker's own
        // (it made the link) whatever it names. A listener whose identity `serve` could
        // not read removes nothing: it cannot tell its own socket at the path from
        // another's, and its own, left stale, is removed by the next `serve`.
        #[cfg(unix)]
        if let Endpoint::Unix {
            path,
            node: Some(node),
            wake,
        } = &self.endpoint
        {
            if reached {
                unlink_if_node(path, *node);
            }
            if let Some(w) = wake {
                unlink_if_node(w, *node);
            }
        }
    }
}

impl Drop for BrokerHandle {
    fn drop(&mut self) {
        if self.acceptor.is_some() {
            self.shutdown();
        }
    }
}

/// Which listener accepted a connection: what decides whether a [`Request::Keepalive`]
/// holds it to [`KEEPALIVE_DEADLINE`] (TCP, sealed or not) or to nothing (a Unix
/// socket, whose peer cannot vanish without its kernel closing it).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Wire {
    #[cfg_attr(not(unix), allow(dead_code))]
    Unix,
    Tcp,
}

/// Serve one connection, then FIRE its registered will (if any) on ANY return — a
/// clean EOF, an I/O error (a keepalive deadline passing among them), a shutdown
/// force-close, or a panic-free early exit alike — provided the capability that
/// authorized the will has not lapsed and the peer's identity has not been revoked.
/// cfg(unix): its one caller is the Unix-socket acceptor; a TCP connection, the only
/// kind Windows has, goes straight to `handle_conn_with_peer`.
#[cfg(unix)]
fn handle_conn(shared: &Arc<Shared>, stream: Conn, wire: Wire) -> io::Result<()> {
    handle_conn_with_peer(shared, stream, wire, "unix", PeerAuth::none())
}

fn handle_conn_with_peer(
    shared: &Arc<Shared>,
    stream: Conn,
    wire: Wire,
    transport: &'static str,
    peer: PeerAuth,
) -> io::Result<()> {
    let conn_id = shared.conn_seq.fetch_add(1, Ordering::Relaxed);
    let mut will: Vec<(WillRecord, u64)> = Vec::new();
    let mut had_will = false;
    let res = serve_conn(
        shared,
        stream,
        wire,
        transport,
        conn_id,
        &mut will,
        &mut had_will,
        &peer,
    );
    finish_disconnected_will(shared, conn_id, &mut will, had_will, &peer, now_unix_ms);
    res
}

/// Dispose of the last registered will, sampling each authorization deadline at
/// its original point. In particular, a certificate is checked after revocation
/// reloading, which can take time. Nonexpiring capability authority reads no clock.
/// Firing and cleanup remain fire-and-forget writes; the caller never waits on a
/// possibly stopped writer. The private clock effect makes these boundaries testable.
fn finish_disconnected_will(
    shared: &Arc<Shared>,
    conn_id: u64,
    will: &mut Vec<(WillRecord, u64)>,
    had_will: bool,
    peer: &PeerAuth,
    mut now: impl FnMut() -> u64,
) {
    if let Some((will, until)) = will.pop() {
        if (until == u64::MAX || now() < until)
            && peer_revocation_reason(shared, peer).is_none()
            && peer.cert_valid_before_ms.is_none_or(|exp| now() < exp)
            && !is_will_principal_revoked(shared, will.producer_id)
        {
            fire_will_for_conn(shared, Some(conn_id), will);
        } else {
            drop_will_for_conn(shared, conn_id);
        }
    } else if had_will {
        drop_will_for_conn(shared, conn_id);
    }
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
/// The words a request that WAITED on the writer ([`submit_blocking`]) answers a refusal
/// of the writer's with: `<what>: <the writer's words>` — except a POISONED log's
/// refusal, which keeps its words FIRST (`<the writer's words> — <what>`), because a
/// producer tells that refusal by how it begins ([`LOG_POISONED_PREFIX`],
/// [`BrokerRefusal::is_poisoned`](crate::BrokerRefusal::is_poisoned)): an attach's
/// binding or a will on a poisoned log is as worthless to resend on this connection as a
/// publish is, and the producer must be able to read that off either.
fn waited_refusal(code: u8, msg: &str, what: &str) -> String {
    if code == ERR_REFUSED && msg.starts_with(LOG_POISONED_PREFIX) {
        format!("{msg} — {what}")
    } else {
        format!("{what}: {msg}")
    }
}

fn submit_blocking(shared: &Arc<Shared>, kind: WriteKind) -> AckResult {
    shared.writer_round_trips.fetch_add(1, Ordering::Relaxed);
    let (tx, rx) = mpsc::channel();
    if shared
        .writes
        .send(Queued::Op(WriteOp {
            kind,
            ack: tx.into(),
            conn_id: None,
        }))
        .is_err()
    {
        return Err(refusal(ERR_REFUSED, "broker is stopping"));
    }
    match rx.recv() {
        Ok(res) => res,
        // The writer is gone and took this op with it, unacked and uncommitted.
        Err(mpsc::RecvError) => Err(refusal(ERR_REFUSED, "broker is stopping")),
    }
}

/// Whether `producer_id` is DURABLY bound to exactly `principal` at an offset below
/// the subscriber-visible head — the case in which the writer's own `Bind` would find
/// the binding, append nothing and ack it — read from `Shared::bindings` without the
/// log lock.
///
/// Below the visible head, because that is the rule the writer's ack of a re-bind
/// applies: in the Replicated tier a binding held locally but not yet by a quorum is
/// refused "not replicated to quorum", and this answers it no differently by falling
/// through to the writer. In Strict and Relaxed every copied binding is already below
/// the head (the writer publishes the head before it copies), so the check never
/// declines one there. The head is read AFTER the copy, and the copy's mutex orders it:
/// the writer stores the head before it locks the copy to add an entry, so a reader
/// that saw the entry sees that head or a later one.
#[cfg(feature = "cap")]
fn binding_settled(shared: &Shared, producer_id: u64, principal: &str) -> bool {
    let at = match shared
        .bindings
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .get(&producer_id)
    {
        Some((held, at)) if held == principal => *at,
        _ => return false,
    };
    crate::proto::offset_is_committed(shared.head.load(Ordering::Relaxed), at)
}

/// Copy into `Shared::bindings` whatever bindings the log has promoted that the copy
/// lacks. Called by the writer with the log lock held, after the batch is committed
/// and its head published. The log's table only grows and never changes an entry, so
/// equal sizes mean equal tables and the common batch (no new binding) costs one
/// comparison; a batch that added one visits the table once.
fn copy_new_bindings(shared: &Shared, log: &BrokerLog) {
    let mut copy = shared
        .bindings
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    if copy.len() == log.durable_binding_count() {
        return;
    }
    for (id, principal, off) in log.durable_bindings() {
        if !copy.contains_key(&id) {
            copy.insert(id, (principal.to_string(), off.0));
        }
    }
}

/// Enqueue one will as a fenced publish, discarding its ack. Fire-and-forget on
/// purpose: waiting could park a connection thread on a writer that a concurrent
/// shutdown has already stopped, and the `/a/will` record is the durable record of
/// intent either way.
fn fire_will(shared: &Arc<Shared>, will: WillRecord) {
    fire_will_for_conn(shared, None, will);
}

fn fire_will_for_conn(shared: &Arc<Shared>, conn_id: Option<u64>, will: WillRecord) {
    let (tx, _rx) = mpsc::channel();
    let _ = shared.writes.send(Queued::Op(WriteOp {
        kind: WriteKind::WillFire { conn_id, will },
        ack: tx.into(),
        conn_id: None,
    }));
}

fn drop_will_for_conn(shared: &Arc<Shared>, conn_id: u64) {
    let (tx, _rx) = mpsc::channel();
    let _ = shared.writes.send(Queued::Op(WriteOp {
        kind: WriteKind::WillDrop { conn_id },
        ack: tx.into(),
        conn_id: None,
    }));
}

/// Let a client refused at the connection cap — or for speaking another protocol —
/// READ its refusal. Closing at once loses it: a client whose first request lands after
/// the close gets a broken pipe (Unix) and one whose request is still unread when the
/// socket closes gets a reset (TCP).
/// So the refused socket shuts only its write half (the client reads the error, then
/// EOF) and stays open for up to [`REFUSAL_LINGER`], reading and discarding input
/// until the client closes; at most [`MAX_LINGERING_REFUSALS`] do so at once, and past
/// that a refusal closes immediately.
fn linger_refused(shared: &Shared, stream: &mut Conn) {
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
/// read). Used for the pre-authentication phase ([`FIRST_FRAME_TIMEOUT`]), and by a
/// leader attaching its capability to a guarded follower.
struct Deadlined<'a> {
    stream: DeadlineOn<'a>,
    deadline: Instant,
}

/// The stream a [`Deadlined`] bounds: a served connection, or the link a leader dialed
/// to a follower.
enum DeadlineOn<'a> {
    Conn(&'a mut Conn),
    #[cfg(any(feature = "cap", feature = "handshake"))]
    Follower(&'a mut FollowerStream),
}

impl DeadlineOn<'_> {
    fn set_read_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        match self {
            DeadlineOn::Conn(s) => s.set_read_timeout(d),
            #[cfg(any(feature = "cap", feature = "handshake"))]
            DeadlineOn::Follower(s) => s.set_read_timeout(d),
        }
    }

    fn set_write_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        match self {
            DeadlineOn::Conn(s) => s.set_write_timeout(d),
            #[cfg(any(feature = "cap", feature = "handshake"))]
            DeadlineOn::Follower(s) => s.set_write_timeout(d),
        }
    }
}

impl Deadlined<'_> {
    /// The time left before the deadline, refused once none is.
    fn left(&self) -> io::Result<Duration> {
        let left = self.deadline.saturating_duration_since(Instant::now());
        if left.is_zero() {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "pre-authentication deadline passed",
            ));
        }
        Ok(left)
    }

    /// Bound the next write by the time left.
    fn arm_write(&mut self) -> io::Result<()> {
        let left = self.left()?;
        self.stream.set_write_timeout(Some(left))
    }
}

impl Read for Deadlined<'_> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let left = self.left()?;
        self.stream.set_read_timeout(Some(left))?;
        match &mut self.stream {
            DeadlineOn::Conn(s) => s.read(buf),
            #[cfg(any(feature = "cap", feature = "handshake"))]
            DeadlineOn::Follower(s) => s.read(buf),
        }
    }
}

impl Write for Deadlined<'_> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.arm_write()?;
        match &mut self.stream {
            DeadlineOn::Conn(s) => s.write(buf),
            #[cfg(any(feature = "cap", feature = "handshake"))]
            DeadlineOn::Follower(s) => s.write(buf),
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        self.arm_write()?;
        match &mut self.stream {
            DeadlineOn::Conn(s) => s.flush(),
            #[cfg(any(feature = "cap", feature = "handshake"))]
            DeadlineOn::Follower(s) => s.flush(),
        }
    }
}

#[cfg(feature = "cap")]
fn record_attached_conn(
    shared: &Shared,
    conn_id: u64,
    transport: &'static str,
    peer: &PeerAuth,
    grant: &str,
) {
    let Ok(parsed) = astream_cap::Grant::parse(grant) else {
        return;
    };
    let (astream_cap::Mode::ReadWrite, Some(principal)) = (parsed.mode, parsed.principal) else {
        return;
    };
    let Ok(grant_filter) = Filter::new(&parsed.filter) else {
        return;
    };
    let producer_id = astream_cap::producer_id_of(&principal);
    let expires_at_ms = astream_cap::expires_at(grant);
    let now_ms = now_unix_ms();
    let mut held = shared
        .attached_conns
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let list = held.entry(conn_id).or_default();
    for existing in list.iter_mut() {
        if existing.principal == principal {
            existing.grants.push((grant_filter, expires_at_ms));
            return;
        }
    }
    list.push(AttachedConnInfo {
        principal,
        transport,
        producer_id,
        attached_at_ms: now_ms,
        grants: vec![(grant_filter, expires_at_ms)],
        peer: peer.clone(),
    });
}

#[allow(clippy::too_many_arguments)]
fn serve_conn(
    shared: &Arc<Shared>,
    mut stream: Conn,
    wire: Wire,
    #[cfg_attr(not(feature = "cap"), allow(unused_variables))] transport: &'static str,
    conn_id: u64,
    will: &mut Vec<(WillRecord, u64)>,
    had_will: &mut bool,
    peer: &PeerAuth,
) -> io::Result<()> {
    // Register a shutdown handle so BrokerHandle::shutdown can force-close this socket
    // (both directions) and unblock a thread parked in read_frame / a socket write —
    // the connection thread (and any ack-writer it spawned) is then reaped promptly
    // instead of lingering until the client happens to send or disconnect. The
    // registry also enforces the connection cap.
    let max_conns = shared.max_conns.load(Ordering::Relaxed);
    {
        let mut conns = shared
            .conns
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if conns.len() >= max_conns {
            drop(conns);
            let _ = stream.set_write_timeout(Some(ACK_WRITE_TIMEOUT));
            let _ = write_frame(
                &mut stream,
                &encode_response(&Response::Error {
                    code: ERR_TOO_MANY_CONNS,
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
        let handle = match stream.sock() {
            Ok(handle) => handle,
            Err(e) => {
                drop(conns);
                let _ = writeln!(
                    io::stderr(),
                    "astream-broker: warn: closed an accepted connection: no shutdown handle for it ({e})"
                );
                return Err(e);
            }
        };
        conns.insert(conn_id, handle);
    }
    let _conn_guard = ConnGuard {
        shared,
        id: conn_id,
        fences_gaps: Cell::new(false),
    };
    // Registered; if the broker began stopping meanwhile (this socket may have been
    // accepted after shutdown's first registry drain), leave now rather than park.
    if !shared.running.load(Ordering::Relaxed) {
        return Ok(());
    }
    // A revocation that ran before this connection registered found nothing to end.
    #[cfg(feature = "stream")]
    if let Conn::Stream(_, stream_pk) = &stream {
        let stream_auth = PeerAuth::from_identity(*stream_pk);
        if let Some(reason) = peer_revocation_reason(shared, &stream_auth) {
            return Err(io::Error::new(io::ErrorKind::PermissionDenied, reason));
        }
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
    // What the connection asked of its tail. Legacy clients never ask: their recv skips
    // marks, which would reset the socket timeout an old take/drain uses to stop on idle,
    // and they would read a gap notice as a reply of the wrong kind.
    let mut asks = TailAsks::default();
    // Whether the connection asked to have its producers' writes GAP-FENCED
    // ([`Request::FenceGaps`]), on a broker that offers it: until it does, a refused write
    // latches no fence, and a write it pipelined behind one lands as on an unfenced broker,
    // so a client that predates the verb is served as it always was.
    let replicate_diverged = Arc::new(AtomicBool::new(false));
    let fresh_fenced = Arc::new(AtomicBool::new(false));
    // The requests read off the socket and not yet served: one read takes every frame
    // that has arrived, and the loop asks it whether the next request is already here
    // whole before it lets the writes it holds go ([`Held`]). Bytes left in it when a
    // streaming verb takes the socket over are dropped, as the tail would discard them
    // (`peer_gone`): nothing is read on a stream after a subscribe.
    let mut rx = RecvBuf::with_step(CONN_READ_STEP);
    loop {
        // Nothing more already here: the writes this connection's client sent together
        // go to the writer as one run, before the read below can block.
        if !rx.holds_frame() && pipe.as_mut().is_some_and(|p| !p.release()) {
            break;
        }
        // Guarded, the deadline is ABSOLUTE; unguarded, the socket timeout set above
        // bounds each read of the first frame.
        let read = match preauth_deadline {
            Some(deadline) if preauth && guarded => rx.next_frame(&mut Deadlined {
                stream: DeadlineOn::Conn(&mut stream),
                deadline,
            }),
            _ => rx.next_frame(&mut stream),
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
                            code: ERR_UNAUTHORIZED,
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
        let (req, req_bt_ms) = match decode_request_with_bt(&payload) {
            Some(pair) => pair,
            // ANOTHER PROTOCOL: say so in the one layout every version reads, stamped
            // with the peer's own version byte (`encode_protocol_refusal`), and close.
            // A "malformed request" here would be stamped with OURS, which the peer's
            // decoder refuses at its first byte — a broker that answered and was read
            // as a garbled stream. Nothing more the peer sends is decodable, so the
            // connection ends; the linger lets the refusal be read rather than reset
            // away by frames the peer pipelined behind it.
            None if matches!(payload.first(), Some(&v) if v != PROTO_VERSION) => {
                finish_pipe(&mut pipe)?;
                let ver = payload.first().copied().unwrap_or(0);
                let _ = write_frame(&mut stream, &encode_protocol_refusal(ver));
                linger_refused(shared, &mut stream);
                return Ok(());
            }
            None => {
                let err = refusal(ERR_REFUSED, "malformed request");
                let kept = if crate::proto::is_fresh_request(&payload) {
                    emit_fresh_refusal(shared, &mut stream, &mut pipe, &fresh_fenced, err)?
                } else {
                    emit(&mut stream, &mut pipe, Err(err))?
                };
                if !kept {
                    break;
                }
                continue;
            }
        };
        // Bounded names, before anything (the capability gate included) parses one.
        if let Some(err) = oversized_name(&req) {
            let err = refusal(ERR_RECORD_REFUSED, err);
            let kept = if matches!(req, Request::FreshPublish { .. }) {
                emit_fresh_refusal(shared, &mut stream, &mut pipe, &fresh_fenced, err)?
            } else {
                emit(&mut stream, &mut pipe, Err(err))?
            };
            if !kept {
                break;
            }
            continue;
        }
        if let Some(reason) = peer_revocation_reason(shared, peer) {
            will.clear();
            let _ = emit(
                &mut stream,
                &mut pipe,
                Err(refusal(ERR_UNAUTHORIZED, reason)),
            );
            break;
        }
        if let Some(cert_exp) = peer.cert_valid_before_ms {
            let now = now_unix_ms();
            if now >= cert_exp {
                will.clear();
                let _ = emit(
                    &mut stream,
                    &mut pipe,
                    Err(refusal(
                        ERR_UNAUTHORIZED,
                        format!("unauthorized: peer certificate expired at {cert_exp} (now {now}, unix ms)"),
                    )),
                );
                break;
            }
        }
        // `Hello` opens the capability handshake on EVERY build: it hands out this
        // connection's nonce and grants nothing, so an unguarded broker answers it too
        // and one client works against either kind. Answered in the request loop after
        // finish_pipe, like every other non-streaming verb.
        if matches!(req, Request::Hello) {
            finish_pipe(&mut pipe)?;
            let n = *nonce.insert(fresh_nonce());
            // The log's identity rides the answer every client already asks for, so a
            // client that kept offsets can check them before it uses one. Read now,
            // not at open: a replica adopts its leader's. Beside it, the extension
            // block: the tier this broker serves (read from the broker itself, never
            // inferred from how it was started) and where the log's generations agree,
            // so a reader that kept offsets under an earlier generation resumes
            // instead of forgetting. Both from the copy the writer keeps beside the log
            // (`Shared::hello`), never under the log lock: the first reply of every
            // connection must not wait out a writer's fsync. And the log's health —
            // poisoned or not, and its flushes — read from the vitals as it is now,
            // lock-free too (the block's tag 0x04), with the latch the copy may not
            // carry yet (`hello_answer`).
            let told = shared
                .hello
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .clone();
            let HelloCopy { identity, ext } =
                hello_answer(told, &shared.vitals, shared.has_sticky_batch_refusal);
            let log = Some(identity);
            write_frame(
                &mut stream,
                &encode_response(&Response::Nonce {
                    nonce: n.to_vec(),
                    log,
                    ext,
                }),
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
                    Some(secret) => attach_grant(
                        shared,
                        secret,
                        &mut keyring,
                        nonce.as_ref(),
                        peer,
                        grant,
                        proof,
                    ),
                };
                let resp = match res {
                    Ok(()) => {
                        // Authenticated: the pre-authentication deadline is lifted.
                        if preauth {
                            preauth = false;
                            let _ = stream.set_read_timeout(None);
                        }
                        record_attached_conn(shared, conn_id, transport, peer, grant);
                        mark_at_head(shared)
                    }
                    Err((code, msg)) => {
                        let _ = writeln!(
                            io::stderr(),
                            "astream-broker: warn: refused Attach for grant {grant:?}: {msg}"
                        );
                        Response::Error { code, msg }
                    }
                };
                write_frame(&mut stream, &encode_response(&resp))?;
                continue;
            }
            match shared.cap_secret.as_deref() {
                None => u64::MAX,
                // THE INSTANT IS TAKEN PER REQUEST, not once per connection: a
                // capability that expires while a connection is open stops
                // authorizing its next request, and a stream it admitted ends at
                // the deadline (`until`). Any capability whose bound principal was
                // revoked since `Attach` is pruned before authorization.
                Some(secret) => {
                    prune_revoked_capabilities(shared, &mut keyring);
                    if will
                        .last()
                        .is_some_and(|(w, _)| is_will_principal_revoked(shared, w.producer_id))
                    {
                        will.clear();
                    }
                    let now = now_unix_ms();
                    match cap_authorized_until(secret, &keyring, &req, now) {
                        Some(until) => until,
                        None => {
                            let why = ungranted(secret, &keyring, &req, now);
                            let err = refusal(ERR_UNAUTHORIZED, why);
                            let keep_open = match &req {
                                Request::FreshPublish { .. } => emit_fresh_refusal(
                                    shared,
                                    &mut stream,
                                    &mut pipe,
                                    &fresh_fenced,
                                    err,
                                )?,
                                Request::Relay {
                                    producer_id,
                                    producer_seq,
                                    ..
                                } => emit_producer_refusal(
                                    shared,
                                    &mut stream,
                                    &mut pipe,
                                    _conn_guard.fences_gaps.get().then_some(conn_id),
                                    *producer_id,
                                    *producer_seq,
                                    err,
                                )?,
                                Request::Publish {
                                    producer_id,
                                    producer_seq,
                                    subject,
                                    ..
                                } if subject != RETIRE_SUBJECT => emit_producer_refusal(
                                    shared,
                                    &mut stream,
                                    &mut pipe,
                                    _conn_guard.fences_gaps.get().then_some(conn_id),
                                    *producer_id,
                                    *producer_seq,
                                    err,
                                )?,
                                Request::ProcessAndProduce {
                                    producer_id,
                                    producer_seq,
                                    ..
                                } => emit_producer_refusal(
                                    shared,
                                    &mut stream,
                                    &mut pipe,
                                    _conn_guard.fences_gaps.get().then_some(conn_id),
                                    *producer_id,
                                    *producer_seq,
                                    err,
                                )?,
                                _ => emit(&mut stream, &mut pipe, Err(err))?,
                            };
                            if !keep_open {
                                break;
                            }
                            continue;
                        }
                    }
                }
            }
        };
        #[cfg(not(feature = "cap"))]
        {
            // Unguarded (no `cap` feature at all): accept an Attach and acknowledge it,
            // so a client's attach round trip completes against either broker.
            if matches!(req, Request::Attach { .. }) {
                finish_pipe(&mut pipe)?;
                write_frame(&mut stream, &encode_response(&mark_at_head(shared)))?;
                continue;
            }
        }
        let until = match peer.cert_valid_before_ms {
            Some(cert_exp) => until.min(cert_exp),
            None => until,
        };
        if !dispatch_request(
            shared,
            &mut stream,
            wire,
            conn_id,
            &mut pipe,
            will,
            had_will,
            &mut asks,
            &_conn_guard.fences_gaps,
            &replicate_diverged,
            &fresh_fenced,
            until,
            peer,
            #[cfg(feature = "cap")]
            &mut keyring,
            req,
            req_bt_ms,
        )? {
            break;
        }
    }
    finish_pipe(&mut pipe)?;
    Ok(())
}

#[cfg(feature = "cap")]
fn prune_revoked_capabilities(shared: &Shared, keyring: &mut Vec<astream_cap::Capability>) {
    maybe_reload_revocation_file(shared);
    let revoked = shared
        .revoked_principals
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    prune_capability_keyring(&revoked, keyring);
}

#[cfg(feature = "cap")]
fn prune_capability_keyring(
    revoked: &RevocationSet<String>,
    keyring: &mut Vec<astream_cap::Capability>,
) {
    if !revoked.is_empty() {
        let mut kept = Vec::new();
        for c in std::mem::take(keyring) {
            let is_revoked = match astream_cap::Grant::parse(&c.filter) {
                Ok(astream_cap::Grant {
                    principal: Some(p), ..
                }) => revoked.contains(&p.to_ascii_lowercase()),
                _ => false,
            };
            if !is_revoked {
                kept.push(c);
            }
        }
        *keyring = kept;
    }
}

#[allow(clippy::too_many_arguments)]
fn dispatch_request(
    shared: &Arc<Shared>,
    stream: &mut Conn,
    wire: Wire,
    conn_id: u64,
    pipe: &mut Option<Pipeline>,
    will: &mut Vec<(WillRecord, u64)>,
    had_will: &mut bool,
    asks: &mut TailAsks,
    fences_gaps: &Cell<bool>,
    replicate_diverged: &Arc<AtomicBool>,
    fresh_fenced: &Arc<AtomicBool>,
    until: u64,
    peer: &PeerAuth,
    #[cfg(feature = "cap")] keyring: &mut Vec<astream_cap::Capability>,
    req: Request,
    req_bt_ms: Option<u64>,
) -> io::Result<bool> {
    // The connection a refused write fences, once it asked ([`Request::FenceGaps`]).
    let fence = fences_gaps.get().then_some(conn_id);
    match req {
        Request::FreshPublish {
            producer_id,
            producer_seq,
            subject,
            body,
        } => serve_fresh_publish(
            shared,
            stream,
            pipe,
            fresh_fenced,
            producer_id,
            producer_seq,
            subject,
            body,
        ),
        Request::Publish {
            producer_id,
            producer_seq,
            subject,
            body,
        } => serve_publish(
            shared,
            stream,
            fence,
            pipe,
            producer_id,
            producer_seq,
            subject,
            body,
        ),
        Request::Commit { group, upto } => {
            emit_op(shared, stream, pipe, WriteKind::Commit { group, upto })
        }
        Request::ProcessAndProduce {
            producer_id,
            producer_seq,
            out_subject,
            out_body,
            group,
            upto,
        } => {
            if let Some((code, err)) = publish_subject_error(&out_subject) {
                return emit_producer_refusal(
                    shared,
                    stream,
                    pipe,
                    fence,
                    producer_id,
                    producer_seq,
                    (code, format!("output {err}")),
                );
            }
            if let Err(err) = check_publish_rate_limit(
                shared,
                producer_id,
                out_subject.len().saturating_add(out_body.len()),
            ) {
                return emit_producer_refusal(
                    shared,
                    stream,
                    pipe,
                    fence,
                    producer_id,
                    producer_seq,
                    err,
                );
            }
            emit_conn_op(
                shared,
                stream,
                pipe,
                fence,
                WriteKind::ProcessAndProduce {
                    producer_id,
                    producer_seq,
                    out_subject,
                    out_body,
                    group,
                    upto,
                },
            )
        }
        Request::Replicate {
            seq,
            producer_id,
            producer_seq,
            subject,
            body,
            commit,
            leader,
        } => serve_replicate(
            shared,
            stream,
            pipe,
            replicate_diverged,
            seq,
            producer_id,
            producer_seq,
            subject,
            body,
            commit,
            leader,
            req_bt_ms,
        ),
        Request::Subscribe {
            from_offset,
            filter,
        } => {
            finish_pipe(pipe)?; // flush pending acks, reclaim the socket
            let filt = match Filter::new(filter.as_str()) {
                Ok(f) => f,
                Err(_) => {
                    write_frame(
                        stream,
                        &encode_response(&Response::Error {
                            code: ERR_BAD_FILTER,
                            msg: format!("bad filter {filter:?}"),
                        }),
                    )?;
                    return Ok(false);
                }
            };
            #[cfg(feature = "cap")]
            let cap_check = StreamCapCheck::new(
                shared,
                keyring,
                Request::Subscribe {
                    from_offset,
                    filter,
                },
            );
            #[cfg(not(feature = "cap"))]
            let cap_check = StreamCapCheck::new(shared);
            tail_loop(
                shared,
                stream,
                from_offset,
                filt,
                until,
                *asks,
                peer,
                cap_check,
            )?;
            Ok(false)
        }
        Request::ForkSubscribe {
            fork_at,
            replacement_subject,
            replacement_body,
            filter,
        } => {
            finish_pipe(pipe)?;
            #[cfg(feature = "cap")]
            let cap_check = StreamCapCheck::new(
                shared,
                keyring,
                Request::ForkSubscribe {
                    fork_at,
                    replacement_subject: replacement_subject.clone(),
                    replacement_body: Vec::new(),
                    filter: filter.clone(),
                },
            );
            #[cfg(not(feature = "cap"))]
            let cap_check = StreamCapCheck::new(shared);
            serve_fork_subscribe(
                shared,
                stream,
                fork_at,
                replacement_subject,
                replacement_body,
                filter,
                until,
                peer,
                cap_check,
            )?;
            Ok(false)
        }
        Request::SubscribeGroup { group, filter } => {
            finish_pipe(pipe)?;
            let filt = match Filter::new(filter.as_str()) {
                Ok(f) => f,
                Err(_) => {
                    write_frame(
                        stream,
                        &encode_response(&Response::Error {
                            code: ERR_BAD_FILTER,
                            msg: format!("bad filter {filter:?}"),
                        }),
                    )?;
                    return Ok(false);
                }
            };
            // Resume from the group's committed offset (broker-enforced): never from a
            // commit a held batch carries, which is neither visible nor durable yet
            // (`BrokerLog::group_start`) — a second reader of a person's inbox must not
            // skip mail on the strength of a read mark that may still be refused or lost.
            let start = {
                let log = shared
                    .log
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
                log.group_start(&group)
            };
            #[cfg(feature = "cap")]
            let cap_check =
                StreamCapCheck::new(shared, keyring, Request::SubscribeGroup { group, filter });
            #[cfg(not(feature = "cap"))]
            let cap_check = StreamCapCheck::new(shared);
            tail_loop(shared, stream, start.0, filt, until, *asks, peer, cap_check)?;
            Ok(false)
        }
        Request::Last { filter, after, max } => {
            serve_last(shared, stream, pipe, *asks, filter, after, max)
        }
        Request::Will {
            producer_id,
            producer_seq,
            subject,
            body,
        } => {
            serve_will(
                shared,
                stream,
                conn_id,
                pipe,
                will,
                had_will,
                producer_id,
                producer_seq,
                subject,
                body,
                until,
            )?;
            Ok(true)
        }
        Request::Keepalive => {
            // Answered in the request loop, like `Will`, after the pending acks.
            // From here on every read on a TCP connection is bounded by the
            // keepalive deadline — SO_RCVTIMEO is per read, so each frame that
            // arrives re-arms it — and a read that runs it out returns from this
            // function like any I/O error: the will fires and the slot is freed
            // (KEEPALIVE_DEADLINE). Nothing is written first: a peer silent past
            // its own promise is presumed gone, and a write could only park.
            finish_pipe(pipe)?;
            if wire == Wire::Tcp {
                let deadline =
                    Duration::from_millis(shared.keepalive_deadline_ms.load(Ordering::Relaxed));
                let _ = stream.set_read_timeout(Some(deadline));
            }
            write_frame(stream, &encode_response(&mark_at_head(shared)))?;
            Ok(true)
        }
        Request::IdleMarks => {
            finish_pipe(pipe)?;
            asks.idle_marks = true;
            write_frame(stream, &encode_response(&mark_at_head(shared)))?;
            Ok(true)
        }
        Request::GapNotices => {
            finish_pipe(pipe)?;
            asks.gaps = true;
            write_frame(stream, &encode_response(&mark_at_head(shared)))?;
            Ok(true)
        }
        Request::BrokerTimes => {
            finish_pipe(pipe)?;
            asks.broker_times = true;
            write_frame(stream, &encode_response(&mark_at_head(shared)))?;
            Ok(true)
        }
        Request::BurstMarks => {
            finish_pipe(pipe)?;
            asks.burst_marks = true;
            write_frame(stream, &encode_response(&mark_at_head(shared)))?;
            Ok(true)
        }
        Request::OriginStamps => {
            finish_pipe(pipe)?;
            asks.origin_stamps = true;
            write_frame(stream, &encode_response(&mark_at_head(shared)))?;
            Ok(true)
        }
        Request::Relay {
            producer_id,
            producer_seq,
            subject,
            body,
        } => {
            if let Some(err) = publish_subject_error(&subject) {
                return emit_producer_refusal(
                    shared,
                    stream,
                    pipe,
                    fence,
                    producer_id,
                    producer_seq,
                    err,
                );
            }
            if let Some(err) = origin_refusal(shared, producer_id, producer_seq, &subject, &body) {
                if err.0 == ERR_ORIGIN_REFUSED {
                    shared.origin_refused.fetch_add(1, Ordering::Relaxed);
                } else if err.0 == ERR_ORIGIN_UNKNOWN {
                    shared.origin_unknown.fetch_add(1, Ordering::Relaxed);
                }
                return emit_producer_refusal(
                    shared,
                    stream,
                    pipe,
                    fence,
                    producer_id,
                    producer_seq,
                    err,
                );
            }
            // No rate limit: the bucket is the origin's, and a carrier replaying one genuine
            // record would spend it under the origin's id. The origin's own broker charged the
            // record when it was published.
            emit_conn_op(
                shared,
                stream,
                pipe,
                fence,
                WriteKind::Relay {
                    producer_id,
                    producer_seq,
                    subject,
                    body,
                },
            )
        }
        Request::FenceGaps => {
            // Answered in the request loop after the pending acks, so every write this
            // connection sent before the request was judged unfenced, as it was sent, and
            // every write it sends after the answer is fenced. A broker opened without the
            // option keeps none: it refuses the ask, and the producer keeps its order by
            // keeping one write in flight (`ERR_REFUSED`, the code a broker that predates the
            // verb answers it with).
            finish_pipe(pipe)?;
            if !shared.has_sticky_batch_refusal {
                return emit(
                    stream,
                    pipe,
                    Err(refusal(
                        ERR_REFUSED,
                        "gap fences not kept: the broker was opened without sticky_batch_refusal",
                    )),
                );
            }
            fences_gaps.set(true);
            write_frame(stream, &encode_response(&mark_at_head(shared)))?;
            Ok(true)
        }
        // Through the writer, in send order behind this connection's writes, and answered in
        // the ack stream with the durable head after a full flush the writer issues once it
        // took the request, whatever already covers the head (`FlushAsked::Always`).
        Request::Settle => emit_op(shared, stream, pipe, WriteKind::Settle),
        Request::ClearGapFences => {
            // Answered in the request loop after the pending acks: every write this
            // connection sent before the request has been judged by then, each refused
            // one's latch set before its ack went (`record_sticky_ack_refusal`), so the
            // drop lifts the fences of writes already answered and none of a write still
            // in flight. The same drop a close makes (`ConnGuard`'s `Drop`).
            finish_pipe(pipe)?;
            if shared.has_sticky_batch_refusal {
                shared
                    .sticky_fences
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner)
                    .drop_conn(conn_id);
            }
            write_frame(stream, &encode_response(&mark_at_head(shared)))?;
            Ok(true)
        }
        Request::Stats { filter } => serve_stats(shared, stream, pipe, filter),
        Request::Budget { producer_id } => {
            // Answered in the request loop after the pending acks, so a count read
            // right after this connection's own publishes includes them. Read under
            // the log lock, where the writer promotes a whole batch in one hold (its
            // write and flush run with the lock released, but nothing is promoted
            // then), so the count is never one a half-promoted batch is still moving.
            finish_pipe(pipe)?;
            let (subjects, reserved) = {
                let log = shared
                    .log
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
                (
                    log.subjects_per_producer(producer_id),
                    log.will_reserved_subjects(producer_id),
                )
            };
            write_frame(
                stream,
                &encode_response(&Response::Budget {
                    subjects: subjects as u64,
                    reserved: reserved as u64,
                    max: MAX_SUBJECTS_PER_PRODUCER as u64,
                }),
            )?;
            Ok(true)
        }
        Request::Fetch {
            from_offset,
            filter,
            max,
        } => serve_fetch(shared, stream, pipe, *asks, from_offset, filter, max),
        Request::Retire {
            producer_id,
            subject,
            offset,
            log,
        } => serve_retire(shared, stream, pipe, producer_id, subject, offset, log),
        // Both are fully handled by the capability gate above, which `continue`s.
        Request::Attach { .. } | Request::Hello => Ok(true),
    }
}

fn serve_retire(
    shared: &Arc<Shared>,
    stream: &mut Conn,
    pipe: &mut Option<Pipeline>,
    producer_id: u64,
    subject: String,
    offset: u64,
    log: crate::LogIdentity,
) -> io::Result<bool> {
    let retire_err = if is_hidden_subject(&subject) || subject.starts_with("/a/") || subject == "/a"
    {
        Some(refusal(ERR_RECORD_REFUSED, reserved_msg(&subject)))
    } else if Subject::new(&subject).is_err() {
        Some(refusal(ERR_BAD_SUBJECT, format!("bad subject {subject:?}")))
    } else {
        None
    };
    if let Some(err) = retire_err {
        return emit(stream, pipe, Err(err));
    }
    emit_op(
        shared,
        stream,
        pipe,
        WriteKind::RetireConditional {
            producer_id,
            subject,
            offset,
            log,
        },
    )
}

#[allow(clippy::too_many_arguments)]
fn serve_fresh_publish(
    shared: &Arc<Shared>,
    stream: &mut Conn,
    pipe: &mut Option<Pipeline>,
    fresh: &Arc<AtomicBool>,
    producer_id: u64,
    producer_seq: u64,
    subject: String,
    body: Vec<u8>,
) -> io::Result<bool> {
    // Fresh is a data append only; it never uses Publish's legacy retire command.
    if let Some(err) = publish_subject_error(&subject) {
        return emit_fresh_refusal(shared, stream, pipe, fresh, err);
    }
    if let Err(err) = check_publish_rate_limit(
        shared,
        producer_id,
        subject.len().saturating_add(body.len()),
    ) {
        return emit_fresh_refusal(shared, stream, pipe, fresh, err);
    }
    emit_fresh_op(
        shared,
        stream,
        pipe,
        fresh,
        WriteKind::FreshPublish {
            producer_id,
            producer_seq,
            subject,
            body,
        },
    )
}

#[allow(clippy::too_many_arguments)]
fn serve_publish(
    shared: &Arc<Shared>,
    stream: &mut Conn,
    fence: Option<u64>,
    pipe: &mut Option<Pipeline>,
    producer_id: u64,
    producer_seq: u64,
    subject: String,
    body: Vec<u8>,
) -> io::Result<bool> {
    if subject == RETIRE_SUBJECT {
        let target_subject = match std::str::from_utf8(&body) {
            Ok(s) => s.to_owned(),
            Err(_) => {
                return emit(
                    stream,
                    pipe,
                    Err(refusal(
                        ERR_RECORD_REFUSED,
                        "retire body must be a valid UTF-8 subject",
                    )),
                );
            }
        };
        if target_subject.len() > MAX_NAME_LEN {
            return emit(
                stream,
                pipe,
                Err(refusal(
                    ERR_RECORD_REFUSED,
                    format!(
                        "subject too long: {} bytes (limit {MAX_NAME_LEN})",
                        target_subject.len()
                    ),
                )),
            );
        }
        let retire_err = if is_hidden_subject(&target_subject)
            || target_subject.starts_with("/a/")
            || target_subject == "/a"
        {
            Some(refusal(ERR_RECORD_REFUSED, reserved_msg(&target_subject)))
        } else if Subject::new(&target_subject).is_err() {
            Some(refusal(
                ERR_BAD_SUBJECT,
                format!("bad subject {target_subject:?}"),
            ))
        } else {
            None
        };
        if let Some(err) = retire_err {
            return emit(stream, pipe, Err(err));
        }
        return emit_op(
            shared,
            stream,
            pipe,
            WriteKind::Retire {
                producer_id,
                target_subject,
            },
        );
    }
    if let Some(err) = publish_subject_error(&subject) {
        return emit_producer_refusal(shared, stream, pipe, fence, producer_id, producer_seq, err);
    }
    if let Err(err) = check_publish_rate_limit(
        shared,
        producer_id,
        subject.len().saturating_add(body.len()),
    ) {
        return emit_producer_refusal(shared, stream, pipe, fence, producer_id, producer_seq, err);
    }
    emit_conn_op(
        shared,
        stream,
        pipe,
        fence,
        WriteKind::Publish {
            producer_id,
            producer_seq,
            subject,
            body,
        },
    )
}

fn check_publish_rate_limit(
    shared: &Shared,
    producer_id: u64,
    wire_bytes: usize,
) -> Result<(), Refusal> {
    if !shared.has_rate_limit.load(Ordering::Acquire) {
        return Ok(());
    }
    let res = {
        let mut limiter = match shared.rate_limiter.lock() {
            Ok(g) => g,
            Err(p) => p.into_inner(),
        };
        limiter.try_acquire(producer_id, wire_bytes)
    };
    match res {
        Ok(()) => Ok(()),
        Err(RateRefusal { retry_ms, why }) => {
            shared.rate_limited.fetch_add(1, Ordering::Relaxed);
            Err(refusal(
                ERR_RATE_LIMITED,
                format!("{RATE_LIMITED_PREFIX}{retry_ms} ({why})"),
            ))
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn serve_replicate(
    shared: &Arc<Shared>,
    stream: &mut Conn,
    pipe: &mut Option<Pipeline>,
    replicate_diverged: &Arc<AtomicBool>,
    seq: u64,
    producer_id: u64,
    producer_seq: u64,
    subject: String,
    body: Vec<u8>,
    commit: Option<(String, u64)>,
    leader: Option<crate::LogIdentity>,
    bt_ms: Option<u64>,
) -> io::Result<bool> {
    let is_retire_marker =
        commit.as_ref().map(|(g, _)| g.as_str()) == Some(crate::proto::REPLICATE_RETIRE_GROUP);
    let pure_commit = !is_retire_marker
        && producer_id == 0
        && producer_seq == 0
        && body.is_empty()
        && commit.is_some();
    let rec = BrokerRecord {
        seq: Offset(seq),
        producer_id,
        producer_seq,
        subject: subject.clone(),
        body,
        commit: if is_retire_marker {
            None
        } else {
            match commit {
                Some((group, upto)) => Some(GroupCommit { group, upto }),
                None => None,
            }
        },
    };
    let err = if Subject::new(subject.as_str()).is_err() {
        Some(refusal(ERR_BAD_SUBJECT, format!("bad subject {subject:?}")))
    } else if subject == COMMIT_SUBJECT {
        if !pure_commit {
            Some(refusal(
                ERR_RECORD_REFUSED,
                format!("reserved subject {COMMIT_SUBJECT}"),
            ))
        } else {
            None
        }
    } else if crate::store::is_hidden_record(&rec)
        && !(shared.is_replica.load(Ordering::Acquire)
            || shared.log_head.load(Ordering::Acquire) == 0)
    {
        Some(refusal(
            ERR_RECORD_REFUSED,
            replicated_reserved_msg(&subject),
        ))
    } else {
        None
    };
    if let Some(err) = err {
        return emit(stream, pipe, Err(err));
    }
    emit_op(
        shared,
        stream,
        pipe,
        WriteKind::Replicate {
            rec,
            leader,
            bt_ms,
            conn_diverged: Arc::clone(replicate_diverged),
        },
    )
}

#[allow(clippy::too_many_arguments)]
fn serve_fork_subscribe(
    shared: &Arc<Shared>,
    stream: &mut Conn,
    fork_at: u64,
    replacement_subject: String,
    replacement_body: Vec<u8>,
    filter: String,
    mut until: u64,
    peer: &PeerAuth,
    mut cap_check: StreamCapCheck,
) -> io::Result<()> {
    if let Some((code, err)) = publish_subject_error(&replacement_subject) {
        write_frame(
            stream,
            &encode_response(&Response::Error {
                code,
                msg: format!("replacement {err}"),
            }),
        )?;
        return Ok(());
    }
    let filt = match Filter::new(filter.as_str()) {
        Ok(f) => f,
        Err(_) => {
            write_frame(
                stream,
                &encode_response(&Response::Error {
                    code: ERR_BAD_FILTER,
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
    let _ = stream.set_write_timeout(Some(stream_write_timeout(shared)));
    let mut pinned: Option<u64> = None;
    let mut cursor = 0u64;
    let mut out = Vec::new();
    if let Some(failure) = stream_failure(shared, peer, &mut cap_check, &mut until) {
        return end_stream_failure(stream, &mut out, failure);
    }
    let visible = loop {
        let before = cursor;
        let (step, visible) = {
            let log = shared
                .log
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            let visible = match pinned {
                Some(v) => v,
                None => {
                    let v = shared.head.load(Ordering::Relaxed).min(log.head().0);
                    pinned = Some(v);
                    v
                }
            };
            // A snapshot, never told of gaps: it asks for none.
            let (_, step) = next_chunk(
                &log,
                &mut cursor,
                visible,
                &filt,
                Some(fork_at),
                None,
                TAIL_CHUNK,
            );
            (step, visible)
        };
        let (chunk, scanned_to) = match step {
            crate::store::TailStep::Chunk {
                records,
                scanned_to,
            } => (records, scanned_to),
            crate::store::TailStep::Unreadable(bad_off) => {
                return end_unreadable_cold_record(stream, &mut out, bad_off);
            }
        };
        if chunk.is_empty() {
            if cursor >= visible || cursor <= before {
                break visible;
            }
            if let Some(failure) = stream_failure(shared, peer, &mut cap_check, &mut until) {
                return end_stream_failure(stream, &mut out, failure);
            }
            continue;
        }
        for rec in chunk {
            if let Some(failure) = stream_failure(shared, peer, &mut cap_check, &mut until) {
                return end_stream_failure(stream, &mut out, failure);
            }
            // Below the pinned head, so never the last offset there is.
            cursor = rec.seq.0.saturating_add(1);
            let rec: &BrokerRecord = if rec.seq.0 == fork_at {
                &replacement
            } else {
                &rec
            };
            if crate::store::is_hidden_record(rec) {
                continue;
            }
            if filt.matches_str(&rec.subject) {
                queue_delivery(stream, &mut out, rec)?;
            }
        }
        cursor = cursor.max(scanned_to);
    };
    flush_egress(stream, &mut out)?;
    if let Some(failure) = stream_failure(shared, peer, &mut cap_check, &mut until) {
        return end_stream_failure(stream, &mut out, failure);
    }
    write_frame(
        stream,
        &encode_response(&mark(
            visible,
            visible,
            durable_for(shared, visible),
            String::new(),
        )),
    )?;
    Ok(())
}

fn serve_last(
    shared: &Arc<Shared>,
    stream: &mut Conn,
    pipe: &mut Option<Pipeline>,
    asks: TailAsks,
    filter: String,
    after: String,
    max: u32,
) -> io::Result<bool> {
    finish_pipe(pipe)?;
    let filt = match Filter::new(filter.as_str()) {
        Ok(f) => f,
        Err(_) => {
            return emit(
                stream,
                pipe,
                Err(refusal(ERR_BAD_FILTER, format!("bad filter {filter:?}"))),
            );
        }
    };
    let want = max.min(LAST_PAGE_MAX) as usize;
    let (page, bts, resume, head) = match last_page(shared, &filt, &after, want, asks.broker_times)
    {
        Ok(v) => v,
        Err(msg) => {
            return emit(stream, pipe, Err(refusal(ERR_REFUSED, msg)));
        }
    };
    let mut out = Vec::new();
    for (i, rec) in page.iter().enumerate() {
        let bt_ms = bts.get(i).copied().flatten();
        queue_delivery_maybe_stamped(shared, stream, &mut out, rec, asks, bt_ms)?;
    }
    let resume_str = match resume {
        Some(r) => r,
        None => String::new(),
    };
    append_frame(
        &mut out,
        &encode_response(&mark(head, head, durable_for(shared, head), resume_str)),
    )?;
    flush_egress(stream, &mut out)?;
    Ok(true)
}

fn serve_stats(
    shared: &Arc<Shared>,
    stream: &mut Conn,
    pipe: &mut Option<Pipeline>,
    filter: String,
) -> io::Result<bool> {
    finish_pipe(pipe)?;
    let filt = match Filter::new(filter.as_str()) {
        Ok(f) => f,
        Err(_) => {
            return emit(
                stream,
                pipe,
                Err(refusal(ERR_BAD_FILTER, format!("bad filter {filter:?}"))),
            );
        }
    };
    let mut listeners = Vec::new();
    {
        let held = shared
            .listeners
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        for ep in held.values() {
            listeners.push(ep.clone());
        }
    }
    let now_ms = now_unix_ms();
    let attached_snapshot: Vec<AttachedConnInfo> = {
        maybe_reload_revocation_file(shared);
        // Each lock alone, never two at once: a revocation reload takes `revoked_identities`
        // and then `revoked_principals` (`apply_revocation_file`), so holding either while
        // taking the other, or `attached_conns` between them, closes a lock-order cycle with
        // it (aterm's lock-order census, L0-DEADLOCK). The connections in scope first, then
        // the revocations read against that copy.
        let in_scope: Vec<AttachedConnInfo> = {
            let held = shared
                .attached_conns
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            let mut in_scope = Vec::new();
            for list in held.values() {
                for info in list {
                    let mut matches_scope = false;
                    for (gf, exp) in &info.grants {
                        let live = match exp {
                            Some(dl) => now_ms < *dl,
                            None => true,
                        };
                        if live && (filt.contains(gf) || gf.contains(&filt)) {
                            matches_scope = true;
                            break;
                        }
                    }
                    if matches_scope {
                        in_scope.push(info.clone());
                    }
                }
            }
            in_scope
        };
        let unrevoked: Vec<AttachedConnInfo> = in_scope
            .into_iter()
            .filter(|info| {
                peer_revocation_reason_raw(shared, &info.peer).is_none()
                    && info
                        .peer
                        .cert_valid_before_ms
                        .is_none_or(|exp| now_ms < exp)
            })
            .collect();
        let revoked = shared
            .revoked_principals
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        unrevoked
            .into_iter()
            .filter(|info| {
                revoked.is_empty() || !revoked.contains(&info.principal.to_ascii_lowercase())
            })
            .collect()
    };
    let (oldest, head, pending_wills, dedup_entries, disk_segments, disk_bytes, producers, faces) = {
        let log = shared
            .log
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let visible = shared.head.load(Ordering::Relaxed);
        let oldest = log.oldest(&filt).0;
        let log_stats = log.stats();
        let dedup_entries = count64(log.dedup_len());
        let (seg64, disk_bytes) = log.disk_segments_and_bytes();
        let disk_segments = u32::try_from(seg64).unwrap_or(u32::MAX);
        let raw_faces = log.face_stats(&filt, visible);
        let mut faces = Vec::with_capacity(raw_faces.len());
        for (face, records, bytes) in raw_faces {
            faces.push(FaceStats {
                face,
                records,
                bytes,
            });
        }
        let mut producers = Vec::with_capacity(attached_snapshot.len());
        for p in attached_snapshot {
            let last_bt_ms = log.producer_last_bt_ms(p.producer_id);
            producers.push(AttachedProducerStats {
                principal: p.principal,
                transport: p.transport.to_string(),
                producer_id: p.producer_id,
                attached_at_ms: p.attached_at_ms,
                last_bt_ms,
            });
        }
        producers.sort();
        (
            oldest,
            visible,
            count64(log_stats.pending_wills),
            dedup_entries,
            disk_segments,
            disk_bytes,
            producers,
            faces,
        )
    };
    let stats = WireStats {
        started_at_ms: shared.started_at_ms,
        oldest,
        head,
        pending_wills,
        dedup_entries,
        disk_segments,
        disk_bytes,
        listeners,
        producers,
        faces,
    };
    write_frame(stream, &encode_response(&Response::Stats(stats)))?;
    Ok(true)
}

#[allow(clippy::too_many_arguments)]
fn serve_will(
    shared: &Arc<Shared>,
    stream: &mut Conn,
    conn_id: u64,
    pipe: &mut Option<Pipeline>,
    will: &mut Vec<(WillRecord, u64)>,
    had_will: &mut bool,
    producer_id: u64,
    producer_seq: u64,
    subject: String,
    body: Vec<u8>,
    until: u64,
) -> io::Result<()> {
    finish_pipe(pipe)?;
    if let Some((code, msg)) = publish_subject_error(&subject) {
        write_frame(stream, &encode_response(&Response::Error { code, msg }))?;
        return Ok(());
    }
    if let Some((held, _)) = will.last() {
        if held.producer_id != producer_id {
            write_frame(
                stream,
                &encode_response(&Response::Error {
                    code: ERR_RECORD_REFUSED,
                    msg: format!(
                        "this connection already holds a will for producer {}: a second \
                         Will replaces the first, and replacement is durable only under \
                         the SAME producer id (use another connection for producer {})",
                        held.producer_id, producer_id
                    ),
                }),
            )?;
            return Ok(());
        }
    }
    let candidate = WillRecord {
        producer_id,
        producer_seq,
        subject,
        body,
    };
    if let Err((code, msg)) = submit_blocking(
        shared,
        WriteKind::WillRegister {
            conn_id: Some(conn_id),
            will: candidate.clone(),
        },
    ) {
        write_frame(
            stream,
            &encode_response(&Response::Error {
                code,
                msg: waited_refusal(code, &msg, "will was not persisted"),
            }),
        )?;
        return Ok(());
    }
    *had_will = true;
    will.clear();
    will.push((candidate, until));
    write_frame(stream, &encode_response(&mark_at_head(shared)))
}

/// A `Fetch`: the page, closed by a `Mark` that says the filter's oldest. Below the oldest
/// (`REQUIREMENTS` R4) a reader is told, never handed a page that silently starts later: one
/// that asked for gap notices (`gaps`; R4's addendum A9) is read from `from_offset` while
/// retention still holds records of its filter below the oldest, the notice ahead of the
/// page ([`BrokerLog::fetch_told`]); every other is refused `retained-from=<oldest>`.
fn serve_fetch(
    shared: &Arc<Shared>,
    stream: &mut Conn,
    pipe: &mut Option<Pipeline>,
    asks: TailAsks,
    from_offset: u64,
    filter: String,
    max: u32,
) -> io::Result<bool> {
    finish_pipe(pipe)?;
    let filt = match Filter::new(filter.as_str()) {
        Ok(f) => f,
        Err(_) => {
            return emit(
                stream,
                pipe,
                Err(refusal(ERR_BAD_FILTER, format!("bad filter {filter:?}"))),
            );
        }
    };
    // BELOW THE OLDEST (`REQUIREMENTS` R4): told, never a page that silently starts
    // later. A head query (`max = 0`) is never refused; its `Mark` says the oldest.
    let (read, bts, head, durable, oldest) = {
        let log = shared
            .log
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let head = shared.head.load(Ordering::Relaxed);
        let read = if asks.gaps {
            log.fetch_told(from_offset, &filt, max as usize, FETCH_SCAN_MAX, head)
        } else {
            log.fetch_checked(from_offset, &filt, max as usize, FETCH_SCAN_MAX, head)
                .map(|(page, next)| (page, next, None))
        };
        let mut bts = Vec::new();
        if asks.broker_times {
            if let Ok((ref page, _, _)) = read {
                bts.reserve(page.len());
                for rec in page {
                    bts.push(log.subject_bt_ms(&rec.subject, rec.seq));
                }
            }
        }
        (
            read,
            bts,
            head,
            durable_for(shared, head),
            log.oldest(&filt).0,
        )
    };
    let (page, next, gap) = match read {
        Ok(read) => read,
        Err(floor) => {
            return emit(
                stream,
                pipe,
                Err(refusal(
                    ERR_RECORD_REFUSED,
                    retained_from_msg(&filter, floor.0),
                )),
            );
        }
    };
    let mut out = Vec::new();
    // The notice goes ahead of the page, as a tail's goes ahead of its next record.
    if let Some(gap) = gap {
        append_frame(&mut out, &encode_response(&Response::Gap(gap)))?;
    }
    for (i, rec) in page.iter().enumerate() {
        let bt_ms = bts.get(i).copied().flatten();
        queue_delivery_maybe_stamped(shared, stream, &mut out, rec, asks, bt_ms)?;
    }
    let mut closing = mark(next, head, durable, String::new());
    if let Response::Mark { oldest: o, .. } = &mut closing {
        *o = Some(oldest);
    }
    append_frame(&mut out, &encode_response(&closing))?;
    flush_egress(stream, &mut out)?;
    Ok(true)
}

/// The refusal of a `Fetch` of `filter` below its oldest, `floor`: `retained-from=<floor>`
/// ([`RETAINED_FROM_PREFIX`]), then why in words. Not every record of the filter below the
/// floor was given up (some subject of it may hold records there, which a reader told of
/// gap notices reads), so it says only what is true of all of them: they are not all kept.
fn retained_from_msg(filter: &str, floor: u64) -> String {
    format!(
        "{RETAINED_FROM_PREFIX}{floor}: records of {filter} below offset {floor} are not all \
         kept; read from there"
    )
}

/// Why a relayed record may not be appended, if it may not: it is checked before the dedup index,
/// so a forged record cannot take a real one's key, and off the writer, so a neighbour's burst of
/// signatures holds up no other connection. On every broker, guarded or not: this is the record's
/// own proof, where a grant only says who may carry it. A record that is not its origin's is
/// refused for good ([`ERR_ORIGIN_REFUSED`]); one whose origin this broker does not take now (no
/// key, or a revoked one) is not judged, and is answered so its carrier may wait
/// ([`ERR_ORIGIN_UNKNOWN`]).
#[cfg(feature = "relay")]
fn origin_refusal(
    shared: &Shared,
    producer_id: u64,
    producer_seq: u64,
    subject: &str,
    body: &[u8],
) -> Option<Refusal> {
    let refused = |why: String| Some(refusal(ERR_ORIGIN_REFUSED, why));
    if producer_seq >= crate::ACK_SEQ_BASE {
        return refused(format!(
            "relay: sequence {producer_seq} is in the reserved ack half"
        ));
    }
    let Some(owner) = astream_cap::relay_owner(subject) else {
        return refused(format!("relay: {subject:?} names no owner"));
    };
    if astream_cap::producer_id_of(owner) != producer_id {
        return refused(format!(
            "relay: {subject:?} is not producer {producer_id}'s"
        ));
    }
    let key = {
        let keys = shared
            .origin_keys
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if keys.is_empty() {
            return Some(refusal(
                ERR_RELAY_NOT_READY,
                "relay: this broker has been given no origin keys",
            ));
        }
        keys.get(owner).copied()
    };
    let Some(key) = key else {
        return Some(refusal(
            ERR_ORIGIN_UNKNOWN,
            format!("relay: {owner} is not a known origin"),
        ));
    };
    if peer_revocation_reason(shared, &PeerAuth::from_identity(key)).is_some() {
        return Some(refusal(
            ERR_ORIGIN_UNKNOWN,
            format!("relay: origin {owner} is revoked"),
        ));
    }
    if !crate::origin::verify(&key, subject, producer_seq, body) {
        return refused(format!("relay: bad signature from {owner} on {subject:?}"));
    }
    None
}

/// A build with no signature check takes no relayed record.
#[cfg(not(feature = "relay"))]
fn origin_refusal(
    _shared: &Shared,
    _producer_id: u64,
    _producer_seq: u64,
    _subject: &str,
    _body: &[u8],
) -> Option<Refusal> {
    Some(refusal(
        ERR_RELAY_NOT_READY,
        "this broker was built without astream-broker's `relay` feature",
    ))
}

/// Why a client-chosen subject cannot be appended to: not a valid `Subject`, or the
/// broker-internal commit subject (a record there would bypass exactly-once dedup
/// and never be delivered — consumer-group commits go through `Commit` /
/// `ProcessAndProduce`). Either is permanent.
fn publish_subject_error(subject: &str) -> Option<Refusal> {
    if Subject::new(subject).is_err() {
        Some(refusal(ERR_BAD_SUBJECT, format!("bad subject {subject:?}")))
    } else if is_hidden_subject(subject) {
        Some(refusal(ERR_RECORD_REFUSED, reserved_msg(subject)))
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
/// Binding is the writer's job only the FIRST time: a principal the table already
/// binds to that id, below the visible head, is answered from the broker's copy of
/// the table (`Shared::bindings`) with no writer round trip and no log lock. The copy
/// can be trusted because a promoted binding is never undone while the log is open,
/// and each open seeds its own copy; see the field.
///
/// The ring's bound is decided BEFORE the binding is appended, so an attach that will
/// be refused writes nothing: the durable mutation is the last thing that happens.
#[cfg(feature = "cap")]
fn attach_grant(
    shared: &Arc<Shared>,
    secret: &[u8],
    keyring: &mut Vec<astream_cap::Capability>,
    nonce: Option<&[u8; 32]>,
    peer: &PeerAuth,
    grant: &str,
    proof: &[u8],
) -> Result<(), Refusal> {
    let Some(nonce) = nonce else {
        return Err(refusal(
            ERR_UNAUTHORIZED,
            "unauthorized: Attach without a preceding Hello (the proof of possession is \
             computed over this connection's nonce)",
        ));
    };
    if !astream_cap::verify_attach(secret, grant, nonce, proof) {
        return Err(refusal(
            ERR_UNAUTHORIZED,
            "unauthorized: capability proof does not verify",
        ));
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
        return Err(refusal(
            ERR_UNAUTHORIZED,
            format!("{CAP_EXPIRED_PREFIX} at {exp} (now {now_ms}, unix ms)"),
        ));
    }
    // Genuine under this broker's secret, so `parse` cannot fail (verify_attach parses
    // first) — but fail closed rather than unwrap on a library change.
    let parsed = match astream_cap::Grant::parse(grant) {
        Ok(p) => p,
        Err(e) => return Err(refusal(ERR_UNAUTHORIZED, format!("unauthorized: {e}"))),
    };
    if let Some(principal) = &parsed.principal {
        maybe_reload_revocation_file(shared);
        if shared
            .revoked_principals
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .contains(&principal.to_ascii_lowercase())
        {
            return Err(refusal(
                ERR_UNAUTHORIZED,
                format!("unauthorized: principal {principal:?} has been revoked"),
            ));
        }
    }
    // When running over the authenticated `identity` transport AND the grant names an
    // identity-shaped principal (`n-<16 hex chars>`), require that principal to match
    // the peer's authenticated Ed25519 public key (`identity_principal(&pk)`), closing
    // the principal-impersonation gap if a capability string is leaked between nodes
    // (`REQUIREMENTS` R6). Non-identity role principals (e.g. `agent-7`, `pump`) remain
    // usable over any transport so multi-role capabilities on a single node continue
    // to work.
    if let (Some(cert_principal), Some(principal)) = (&peer.cert_principal, &parsed.principal) {
        if !principal.eq_ignore_ascii_case(cert_principal) {
            return Err(refusal(
                ERR_UNAUTHORIZED,
                format!(
                    "unauthorized: grant principal {principal:?} does not match authenticated \
                     certificate principal {cert_principal:?}"
                ),
            ));
        }
    } else if let (Some(pk), Some(principal)) = (peer.pubkey, &parsed.principal) {
        if is_identity_shaped_principal(principal) {
            let expected = identity_principal(&pk);
            if !principal.eq_ignore_ascii_case(&expected) {
                return Err(refusal(
                    ERR_UNAUTHORIZED,
                    format!(
                        "unauthorized: grant principal {principal:?} does not match authenticated \
                         peer identity {expected:?}"
                    ),
                ));
            }
        }
    }
    // DECIDE THE RING FIRST, MUTATE THE LOG SECOND. Minting and the ring's capacity are
    // pure, local checks; the producer-id binding below is a DURABLE append, so an
    // attach refused for a full ring must be refused before it, leaving the log
    // untouched.
    let cap = match astream_cap::mint(secret, grant) {
        Ok(c) => c,
        Err(e) => return Err(refusal(ERR_UNAUTHORIZED, format!("unauthorized: {e}"))),
    };
    let mut already_present = false;
    for c in keyring.iter() {
        if c.filter == cap.filter {
            already_present = true;
            break;
        }
    }
    if !already_present && keyring.len() >= MAX_KEYRING {
        return Err(refusal(
            ERR_UNAUTHORIZED,
            format!("unauthorized: capability keyring is full ({MAX_KEYRING} grants)"),
        ));
    }
    match (&parsed.mode, &parsed.principal) {
        // A grant that can PUBLISH under a named principal binds that principal's
        // derived producer id, durably, before it authorizes anything.
        (astream_cap::Mode::ReadWrite, Some(principal)) => {
            let producer_id = astream_cap::producer_id_of(principal);
            // ALREADY BOUND: the log's answer is known and final (see
            // `Shared::bindings`), so the writer is not asked again. This is the common
            // case by far — aterm's ring names one principal in four grants, on every
            // connection of every attach — and asking cost an empty batch queued behind
            // the writer's fsync each time. Anything else (unbound, bound to another
            // principal, not yet visible) is the writer's to decide below, unchanged.
            if binding_settled(shared, producer_id, principal) {
                shared.binds_settled.fetch_add(1, Ordering::Relaxed);
            } else if let Err((code, msg)) = submit_blocking(
                shared,
                WriteKind::Bind {
                    producer_id,
                    principal: principal.clone(),
                },
            ) {
                // The writer's code stands: a collision is the authority failing; an
                // I/O error appending the binding is not, and is not known to be
                // permanent.
                return Err(match code {
                    ERR_UNAUTHORIZED => refusal(ERR_UNAUTHORIZED, format!("unauthorized: {msg}")),
                    code => refusal(
                        code,
                        waited_refusal(code, &msg, "the producer binding was not persisted"),
                    ),
                });
            }
        }
        // An UNBOUND read-write grant may publish under any producer id — the god cap
        // the fleet root keeps. It is legal and it is a footgun, so say so once, on
        // stderr, where an operator can see which grant it was.
        (astream_cap::Mode::ReadWrite, None) => {
            if parsed.relay {
                // Writes under an origin's id only where a subject names that origin.
            } else {
                eprintln!(
                    "astream-broker: warn: attached an UNBOUND read-write grant {grant:?} — it may \
                 publish under ANY producer id (no principal binding); mint it as \
                 \"rw,p=<principal>:<filter>\" unless it is deliberately the fleet root"
                );
            }
        }
        // A read-only grant publishes nothing, so it binds nothing: binding it would
        // let a read-only holder append a /a/bind record.
        (astream_cap::Mode::ReadOnly, _) => {}
    }
    let mut kept = Vec::new();
    for c in std::mem::take(keyring) {
        if c.filter != cap.filter {
            kept.push(c);
        }
    }
    kept.push(cap);
    *keyring = kept;
    Ok(())
}

/// The words of the refusal for a request [`cap_authorized_until`] did not authorize
/// at `now_ms`. When the ring WOULD have authorized it before any deadline, the
/// grants that covered it have lapsed, and the refusal says so with
/// [`CAP_EXPIRED_PREFIX`]: the holder needs a fresh mint of the same grant, not a
/// wider one. Otherwise no grant ever covered it, and the refusal says that.
///
/// "Before any deadline" is the instant 0. It is earlier than every `exp=` a ring can
/// hold, because `attach_grant` refuses an `exp=0` grant whatever the clock says
/// (`0 >= 0` is expired). This decides only the WORDS. The request was already
/// refused at `now_ms`, and nothing here can authorize it.
#[cfg(feature = "cap")]
fn ungranted(
    secret: &[u8],
    keyring: &[astream_cap::Capability],
    req: &Request,
    now_ms: u64,
) -> String {
    if cap_authorized_until(secret, keyring, req, 0).is_some() {
        format!(
            "{CAP_EXPIRED_PREFIX} before this request: every grant that covered it has \
             lapsed (now {now_ms}, unix ms)"
        )
    } else {
        "unauthorized: capability does not grant this subject/filter".to_string()
    }
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
/// instant its authority LAPSES. That instant matters to a streaming verb or `Will` —
/// whose authority must still hold when the stream delivers or the connection drops —
/// so those verbs compute it: each half of the request rests on whichever authorizing
/// grant lasts longest, and the request lapses with the first half to go. Any other
/// verb stops at the first grant that authorizes it and answers `u64::MAX` ("authorized
/// now"), which is also the answer for grants without an expiry.
#[cfg(feature = "cap")]
fn stats_auth_filter(filter: &str) -> String {
    if Filter::new(filter).is_err() {
        return filter.to_string();
    }
    if let Some((fleet, _)) = filter.strip_prefix("/f/").and_then(|r| r.split_once('/')) {
        if !fleet.is_empty() && !fleet.contains('*') && !fleet.contains('>') {
            return format!("/f/{fleet}/>");
        }
    }
    "/>".to_string()
}

#[cfg(feature = "cap")]
fn cap_authorized_until(
    secret: &[u8],
    keyring: &[astream_cap::Capability],
    req: &Request,
    now_ms: u64,
) -> Option<u64> {
    #[derive(Clone, Copy)]
    enum CapPred<'a> {
        // A write as a named producer: read-write, filter matches, producer id derived.
        Publish(&'a str, u64),
        // A group advance: read-write on the group name as a subject.
        Commit(&'a str),
        // A read: ANY grant (either mode) whose filter contains the requested one.
        Read(&'a str),
        // A REPLICATED write: read-write and filter-matching, like any write — and
        // UNBOUND, because the record carries a producer id this connection's principal
        // does not derive and never could.
        Replicate(&'a str),
        // A RELAYED write: a relay (or unbound) grant over the subject, under the id of the
        // subject's owner.
        Relay(&'a str, u64),
        // Any genuine, unexpired grant on the connection.
        AnyValid,
        // A genuine, unexpired read-write grant that publishes as `producer_id`.
        Budget(u64),
        // A genuine, unexpired read-write grant of any filter or principal.
        AnyWrite,
    }

    let stats_scope = match req {
        Request::Stats { filter } => stats_auth_filter(filter),
        _ => String::new(),
    };
    let streaming = matches!(
        req,
        Request::Subscribe { .. }
            | Request::SubscribeGroup { .. }
            | Request::ForkSubscribe { .. }
            | Request::Will { .. }
    );
    let (first, second): (CapPred<'_>, Option<CapPred<'_>>) = match req {
        // A `Will` is a publish the broker will make LATER on this connection's
        // behalf, so it is authorized now, exactly as a publish is — including the
        // producer binding. A publish to `RETIRE_SUBJECT` (`/a/retire`) retires the
        // target subject carried in `body`, so it is authorized against that exact
        // target `Subject` under `producer_id` (or `CapPred::Budget(*producer_id)` when
        // `body` is not a valid `Subject`, so an authenticated producer gets
        // `ERR_BAD_SUBJECT` / `ERR_RECORD_REFUSED` from `serve_publish` rather than
        // `ERR_UNAUTHORIZED`).
        Request::Publish {
            subject,
            body,
            producer_id,
            ..
        } if subject == RETIRE_SUBJECT => match std::str::from_utf8(body) {
            Ok(target)
                if Subject::new(target).is_ok()
                    && !is_hidden_subject(target)
                    && !target.starts_with("/a/")
                    && target != "/a" =>
            {
                (CapPred::Publish(target, *producer_id), None)
            }
            _ => (CapPred::Budget(*producer_id), None),
        },
        Request::Retire {
            subject,
            producer_id,
            ..
        } => match Subject::new(subject) {
            Ok(_)
                if !is_hidden_subject(subject)
                    && !subject.starts_with("/a/")
                    && subject != "/a" =>
            {
                (CapPred::Publish(subject, *producer_id), None)
            }
            _ => (CapPred::Budget(*producer_id), None),
        },
        Request::Publish {
            subject,
            producer_id,
            ..
        }
        | Request::FreshPublish {
            subject,
            producer_id,
            ..
        }
        | Request::Will {
            subject,
            producer_id,
            ..
        } => (CapPred::Publish(subject, *producer_id), None),
        Request::Relay {
            subject,
            producer_id,
            ..
        } => (CapPred::Relay(subject, *producer_id), None),
        // The commit HALF of a read-process-write also advances a consumer group,
        // so authorize BOTH the output subject AND the group (as a subject the ring
        // grants) — not the output subject alone.
        Request::ProcessAndProduce {
            out_subject,
            producer_id,
            group,
            ..
        } => (
            CapPred::Publish(out_subject, *producer_id),
            Some(CapPred::Commit(group)),
        ),
        // A replicated record needs a LINK grant on its subject — read-write,
        // filter-matching and unbound — plus, if it carries a commit, an advance of
        // that group. A bound `rw` grant does not reach this verb.
        // The codec's marked retirement uses this exact sentinel instead of a group
        // commit. It still needs the unbound replication grant on /a/retire, but
        // advances no consumer group whose name would need a second grant.
        Request::Replicate {
            subject,
            producer_seq,
            commit: Some((group, 0)),
            ..
        } if subject == RETIRE_SUBJECT
            && *producer_seq == crate::brecord::RETIRE_PRODUCER_SEQ
            && group == crate::proto::REPLICATE_RETIRE_GROUP =>
        {
            (CapPred::Replicate(subject), None)
        }
        Request::Replicate {
            subject, commit: c, ..
        } => match c {
            None => (CapPred::Replicate(subject), None),
            Some((g, _)) => (CapPred::Replicate(subject), Some(CapPred::Commit(g))),
        },
        Request::Subscribe { filter, .. }
        | Request::ForkSubscribe { filter, .. }
        | Request::Last { filter, .. }
        | Request::Fetch { filter, .. } => (CapPred::Read(filter), None),
        // Operator status (`REQUIREMENTS` R5) exposes broker-wide producers, listeners,
        // pending wills, dedup size and disk bytes alongside face counts, so a narrow
        // mailbox or single-subject read grant may not authorize it: require a read
        // grant on `/f/<F>/>` (for a fabric filter) or `/>` (otherwise).
        Request::Stats { .. } => (CapPred::Read(stats_scope.as_str()), None),
        // A group subscription is authorized for BOTH what it reads (filter) and the
        // durable group it commits under (group-as-subject).
        Request::SubscribeGroup { group, filter } => {
            (CapPred::Read(filter), Some(CapPred::Commit(group)))
        }
        // Commit durably advances a consumer group. It MUST verify the capability and
        // be scoped to the group (the group is a subject the ring must grant), or any
        // connection could force another tenant's committed offset forward.
        Request::Commit { group, .. } => (CapPred::Commit(group), None),
        // Both only ever ADD, and both are fully handled before this gate.
        Request::Attach { .. } | Request::Hello => return Some(u64::MAX),
        // These grant nothing, but their `Mark` names the log's head, which an
        // unattached connection is told nothing about: any capability the ring still
        // holds — genuine and unexpired — answers for it.
        Request::Keepalive
        | Request::IdleMarks
        | Request::GapNotices
        | Request::BrokerTimes
        | Request::BurstMarks
        | Request::OriginStamps
        | Request::FenceGaps
        | Request::ClearGapFences => (CapPred::AnyValid, None),
        // A producer's budget is answered to whoever could spend it: a genuine,
        // unexpired read-write grant that publishes as that producer — bound to it,
        // or unbound (the god grant publishes as any). It names no subject, so no
        // filter is matched; a read-only grant, or one bound to another principal,
        // learns nothing about this producer.
        Request::Budget { producer_id } => (CapPred::Budget(*producer_id), None),
        // A settle appends nothing and names nothing, but it spends the device's time on a
        // full flush, as an escalated write does: whoever may write here may ask for one.
        Request::Settle => (CapPred::AnyWrite, None),
    };

    let mut min_until = u64::MAX;
    for pred in [Some(first), second] {
        let Some(pred) = pred else {
            continue;
        };
        let mut best: Option<u64> = None;
        for c in keyring {
            let matched = match pred {
                CapPred::Publish(subject, producer_id) => {
                    astream_cap::grants_publish(secret, c, subject, producer_id, now_ms)
                }
                CapPred::Relay(subject, producer_id) => {
                    astream_cap::grants_relay(secret, c, subject, producer_id, now_ms)
                }
                CapPred::Commit(group) => astream_cap::grants_commit(secret, c, group, now_ms),
                CapPred::Read(filter) => astream_cap::grants_filter(secret, c, filter, now_ms),
                CapPred::Replicate(subject) => {
                    astream_cap::grants(secret, c, subject, now_ms)
                        && matches!(
                            astream_cap::Grant::parse(c.filter.as_str()),
                            Ok(g) if g.principal.is_none()
                        )
                }
                CapPred::AnyValid => {
                    astream_cap::verify(secret, c)
                        && !astream_cap::is_expired(c.filter.as_str(), now_ms)
                }
                CapPred::AnyWrite => {
                    astream_cap::verify(secret, c)
                        && !astream_cap::is_expired(c.filter.as_str(), now_ms)
                        && matches!(
                            astream_cap::Grant::parse(c.filter.as_str()),
                            Ok(g) if g.mode == astream_cap::Mode::ReadWrite
                        )
                }
                CapPred::Budget(producer_id) => {
                    astream_cap::verify(secret, c)
                        && !astream_cap::is_expired(c.filter.as_str(), now_ms)
                        && match astream_cap::Grant::parse(c.filter.as_str()) {
                            Ok(g) => {
                                g.mode == astream_cap::Mode::ReadWrite
                                    && match g.principal.as_deref() {
                                        None => true,
                                        Some(p) => astream_cap::producer_id_of(p) == producer_id,
                                    }
                            }
                            Err(_) => false,
                        }
                }
            };
            if matched {
                if streaming {
                    let exp = astream_cap::expires_at(c.filter.as_str()).unwrap_or(u64::MAX);
                    best = Some(match best {
                        Some(prev) if prev >= exp => prev,
                        _ => exp,
                    });
                } else {
                    best = Some(u64::MAX);
                    break;
                }
            }
        }
        let pred_until = best?;
        if pred_until < min_until {
            min_until = pred_until;
        }
    }
    Some(min_until)
}

/// The refusal for a request naming a subject, filter, group, cursor or grant longer
/// than [`MAX_NAME_LEN`], if it does. Checked before anything parses the name.
fn oversized_name(req: &Request) -> Option<String> {
    const NONE: (&str, &str) = ("", "");
    let names: [(&str, &str); 2] = match req {
        Request::Publish { subject, .. }
        | Request::FreshPublish { subject, .. }
        | Request::Relay { subject, .. }
        | Request::Will { subject, .. }
        | Request::Retire { subject, .. } => [("subject", subject), NONE],
        Request::Subscribe { filter, .. }
        | Request::Fetch { filter, .. }
        | Request::Stats { filter } => [("filter", filter), NONE],
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
            match commit.as_ref() {
                Some((g, _)) => ("group", g.as_str()),
                None => NONE,
            },
        ],
        Request::Last { filter, after, .. } => [("filter", filter), ("cursor", after)],
        Request::Hello
        | Request::Keepalive
        | Request::IdleMarks
        | Request::GapNotices
        | Request::BrokerTimes
        | Request::BurstMarks
        | Request::OriginStamps
        | Request::FenceGaps
        | Request::ClearGapFences
        | Request::Settle
        | Request::Budget { .. } => [NONE, NONE],
    };
    for (what, name) in names {
        if name.len() > MAX_NAME_LEN {
            return Some(format!(
                "{what} too long: {} bytes (limit {MAX_NAME_LEN})",
                name.len()
            ));
        }
    }
    None
}

/// The pipelined ack path for one connection: an ordered, bounded queue of pending acks
/// feeding a dedicated thread that streams them back on a cloned write half. Lets a
/// connection keep many write ops in flight; back-pressures via the bounded queue.
struct Pipeline {
    /// The ops submitted and not yet handed to the writer. Declared first, so a pipeline
    /// dropped without [`finish`](Self::finish) hands them over before anything else of
    /// it goes.
    held: Held,
    /// Ordered queue of per-op ack receivers (bounded → flow control). `send` blocks
    /// when `PIPELINE_DEPTH` acks are outstanding.
    tx: mpsc::SyncSender<Receiver<AckResult>>,
    writer: Option<JoinHandle<io::Result<()>>>,
}

/// THE RUN A CONNECTION'S READER IS HOLDING: write ops it has decoded and reserved ack
/// slots for, not yet handed to the writer. The reader keeps adding to it while the
/// next request has already arrived whole ([`RecvBuf::holds_frame`]), and hands the lot
/// over as ONE [`Queued::Run`] ([`release`](Self::release)) before it can block — on a
/// read, a full ack queue ([`Pipeline::reserve`]), or a request answered after the
/// pending acks ([`Pipeline::finish`]). So the writes a client sent together land in one
/// group-commit batch, one flush for all of them, however long the reader spends on each
/// request (a guarded broker checks every one against the connection's keyring).
/// Submitted one at a time, each could meet the writer idle and be a batch of its own:
/// measured 2026-10-26 on an idle Ordered broker, a publish and a commit written in one
/// write took two batches in 989 of 1,000 tries guarded, and in 8 of 1,000 unguarded.
///
/// What is held is what would otherwise be queued already: every op in it passed the
/// checks a submitted op passes, and its ack slot comes before any later reply's. Holding
/// moves only the moment the writer sees it, by the time the reader takes to decode
/// requests that are already in memory. Dropped, it hands the run over too, so a
/// connection that ends on an error still commits what it read, as it did when each op
/// was queued as it was read, and before the connection's will fires.
struct Held {
    ops: Vec<WriteOp>,
    writes: Sender<Queued>,
}

impl Held {
    /// Hand the run to the writer: one op as itself, more as one [`Queued::Run`]. False
    /// when the writer has gone (the broker is stopping), which drops the ops and with
    /// them their ack senders, so the ack-writer's wait on each slot ends.
    fn release(&mut self) -> bool {
        let queued = if self.ops.len() > 1 {
            Queued::Run(std::mem::take(&mut self.ops))
        } else {
            match self.ops.pop() {
                Some(op) => Queued::Op(op),
                None => return true,
            }
        };
        self.writes.send(queued).is_ok()
    }
}

impl Drop for Held {
    fn drop(&mut self) {
        let _ = self.release();
    }
}

impl Pipeline {
    /// Start an ack-writer on a clone of `stream`'s write half, bounded by
    /// `write_timeout` — the CONNECTION's configured value, not a constant of this
    /// path's own. `set_write_timeout` is `setsockopt(SO_SNDTIMEO)`, a property of the
    /// socket rather than of the descriptor, and `try_clone` shares the file
    /// description: whatever the ack-writer sets here it also sets for the connection
    /// thread's own writes, for the rest of the connection's life, so anything but the
    /// configured [`Broker::set_write_timeout`] value would silently replace it. Its
    /// ops go to the writer through `writes`.
    fn start(
        stream: &Conn,
        write_timeout: Duration,
        writes: Sender<Queued>,
    ) -> io::Result<Pipeline> {
        let wr = stream.try_clone()?;
        let (tx, rx) = mpsc::sync_channel::<Receiver<AckResult>>(PIPELINE_DEPTH);
        // A failed spawn is this connection's error, not a panic that would unwind
        // past `handle_conn` and skip firing the connection's will.
        let writer =
            thread::Builder::new().spawn(move || ack_writer_loop(wr, rx, write_timeout))?;
        Ok(Pipeline {
            held: Held {
                ops: Vec::new(),
                writes,
            },
            tx,
            writer: Some(writer),
        })
    }

    /// Submit a durable mutation: queue its ack slot in order, THEN add the op to the
    /// run the reader holds ([`Held`]), which reaches the writer by the time the reader
    /// could block. Returns false if the ack-writer has gone, or the writer has (the
    /// connection should close).
    ///
    /// Ordering matters for correctness: the ack slot is reserved FIRST. The bounded
    /// queue applies back-pressure here (blocks once PIPELINE_DEPTH acks are
    /// outstanding, having handed the held run over) BEFORE the op reaches the writer,
    /// so a record is never committed unless its ack is already queued to be delivered
    /// in order — closing the "committed durably but ack lost (client sees EOF)" window.
    /// If the writer has since exited, dropping the `WriteOp` closes `ack_tx`, so the
    /// ack-writer's blocked recv on the reserved slot returns cleanly instead of hanging.
    #[cfg(test)]
    fn submit(&mut self, kind: WriteKind) -> bool {
        self.submit_conn_opt(None, kind)
    }

    fn submit_conn_opt(&mut self, conn_id: Option<u64>, kind: WriteKind) -> bool {
        self.submit_with_fresh(conn_id, kind, None)
    }

    fn submit_with_fresh(
        &mut self,
        conn_id: Option<u64>,
        kind: WriteKind,
        fresh: Option<Arc<AtomicBool>>,
    ) -> bool {
        let (ack_tx, ack_rx) = mpsc::channel();
        if !self.reserve(ack_rx) {
            return false; // ack-writer gone (its socket died); nothing committed
        }
        self.held.ops.push(WriteOp {
            kind,
            ack: AckSender {
                sender: ack_tx,
                fresh,
            },
            conn_id,
        });
        true
    }

    /// Queue an already-resolved response (e.g. a validation error) in order.
    fn push_result(&mut self, res: AckResult) -> bool {
        let (tx, rx) = mpsc::channel();
        let _ = tx.send(res);
        self.reserve(rx)
    }

    /// Reserve the next ack slot. When the queue is full the ack-writer may be waiting
    /// on an op still held, so the run is handed over before this waits for room: a
    /// wait with it held would never end.
    fn reserve(&mut self, slot: Receiver<AckResult>) -> bool {
        match self.tx.try_send(slot) {
            Ok(()) => true,
            Err(mpsc::TrySendError::Full(slot)) => self.release() && self.tx.send(slot).is_ok(),
            Err(mpsc::TrySendError::Disconnected(_)) => false,
        }
    }

    /// Hand the held run to the writer ([`Held::release`]).
    fn release(&mut self) -> bool {
        self.held.release()
    }

    /// Flush every queued ack and join the ack-writer (dropping `tx` makes its outer
    /// recv return `Disconnected` once drained), reclaiming the socket for streaming.
    /// The held run goes to the writer first, or the ack-writer would wait on it.
    fn finish(mut self) -> io::Result<()> {
        let _ = self.release();
        drop(self.tx);
        match self.writer.take() {
            Some(j) => match j.join() {
                Ok(res) => res,
                Err(_) => Ok(()),
            },
            None => Ok(()),
        }
    }
}

/// Emit a pre-resolved response in order: through the active pipeline, or inline if no
/// write op has started one yet. Returns false when the ack path is gone (close).
fn emit(stream: &mut Conn, pipe: &mut Option<Pipeline>, res: AckResult) -> io::Result<bool> {
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
fn emit_op(
    shared: &Arc<Shared>,
    stream: &mut Conn,
    pipe: &mut Option<Pipeline>,
    kind: WriteKind,
) -> io::Result<bool> {
    emit_conn_op(shared, stream, pipe, None, kind)
}

fn emit_conn_op(
    shared: &Arc<Shared>,
    stream: &mut Conn,
    pipe: &mut Option<Pipeline>,
    conn_id: Option<u64>,
    kind: WriteKind,
) -> io::Result<bool> {
    let p = match pipe {
        Some(p) => p,
        None => pipe.insert(Pipeline::start(
            stream,
            Duration::from_millis(shared.write_timeout_ms.load(Ordering::Relaxed)),
            shared.writes.clone(),
        )?),
    };
    Ok(p.submit_conn_opt(conn_id, kind))
}

/// A fresh refusal is a writer operation even when validation found it before
/// staging. Latching on the reader would overtake valid earlier requests.
fn emit_fresh_refusal(
    shared: &Arc<Shared>,
    stream: &mut Conn,
    pipe: &mut Option<Pipeline>,
    fresh: &Arc<AtomicBool>,
    err: Refusal,
) -> io::Result<bool> {
    emit_fresh_op(
        shared,
        stream,
        pipe,
        fresh,
        WriteKind::PreRefused {
            producer_id: 0,
            producer_seq: 0,
            err,
        },
    )
}

fn emit_fresh_op(
    shared: &Arc<Shared>,
    stream: &mut Conn,
    pipe: &mut Option<Pipeline>,
    fresh: &Arc<AtomicBool>,
    kind: WriteKind,
) -> io::Result<bool> {
    let p = match pipe {
        Some(p) => p,
        None => pipe.insert(Pipeline::start(
            stream,
            Duration::from_millis(shared.write_timeout_ms.load(Ordering::Relaxed)),
            shared.writes.clone(),
        )?),
    };
    Ok(p.submit_with_fresh(None, kind, Some(Arc::clone(fresh))))
}

/// Answer a producer's write refused before the writer saw it. On a connection that asked to
/// be gap-fenced (`fence`, its id) the refusal goes through the writer in send order, which
/// latches the fence there before anything the producer sent after it is staged
/// ([`WriteKind::PreRefused`]); on any other it is answered in order and fences nothing.
fn emit_producer_refusal(
    shared: &Arc<Shared>,
    stream: &mut Conn,
    pipe: &mut Option<Pipeline>,
    fence: Option<u64>,
    producer_id: u64,
    producer_seq: u64,
    err: Refusal,
) -> io::Result<bool> {
    if fence.is_some() {
        emit_conn_op(
            shared,
            stream,
            pipe,
            fence,
            WriteKind::PreRefused {
                producer_id,
                producer_seq,
                err,
            },
        )
    } else {
        // Through the pipeline even when this is the connection's first write: an inline ack
        // stops the read half, and a client still writing its burst reads no acks until that
        // write returns. A run of refusals fills both ways' buffers and stalls them against
        // each other.
        if pipe.is_none() {
            *pipe = Some(Pipeline::start(
                stream,
                Duration::from_millis(shared.write_timeout_ms.load(Ordering::Relaxed)),
                shared.writes.clone(),
            )?);
        }
        emit(stream, pipe, Err(err))
    }
}

/// Finish the pipeline if one is active (flush acks, join the ack-writer).
fn finish_pipe(pipe: &mut Option<Pipeline>) -> io::Result<()> {
    match pipe.take() {
        Some(p) => p.finish(),
        None => Ok(()),
    }
}

#[cfg(test)]
mod held_tests {
    use super::*;

    /// A pipeline over a one-slot ack queue: an ack-writer that takes each slot in order,
    /// says so on the returned receiver, and waits for its answer (counting the answers);
    /// and a writer that answers every op it is handed (recording how many came together).
    fn tiny() -> (
        Pipeline,
        Receiver<()>,
        JoinHandle<usize>,
        JoinHandle<Vec<usize>>,
    ) {
        let (tx, slots) = mpsc::sync_channel::<Receiver<AckResult>>(1);
        let (writes, queue) = mpsc::channel::<Queued>();
        let (took_tx, took) = mpsc::channel();
        let acker = thread::spawn(move || {
            slots
                .iter()
                .filter(|slot| {
                    let _ = took_tx.send(());
                    slot.recv().is_ok()
                })
                .count()
        });
        let writer = thread::spawn(move || {
            let mut runs = Vec::new();
            for queued in queue {
                let ops = match queued {
                    Queued::Op(op) => vec![op],
                    Queued::Run(ops) => ops,
                    Queued::DropFences(_) => continue,
                    Queued::Stop => break,
                };
                runs.push(ops.len());
                for op in ops {
                    let _ = op.ack.send(Ok((0, false)));
                }
            }
            runs
        });
        let pipe = Pipeline {
            held: Held {
                ops: Vec::new(),
                writes,
            },
            tx,
            writer: None,
        };
        (pipe, took, acker, writer)
    }

    /// A one-minute HANG DETECTOR for something that must happen, never a budget.
    const HANG: Duration = Duration::from_secs(60);

    /// **A FULL ACK QUEUE NEVER WAITS ON A HELD OP.** With one slot, the ack-writer waits
    /// on the first op's answer while the queue holds the second's slot; the third
    /// submit finds the queue full. Were it to wait for room with the first two still
    /// held, nothing would ever answer the first (it is not the writer's yet) and the
    /// connection would hang. It hands the held run over first: every op is answered,
    /// and the first two reached the writer together.
    #[test]
    fn a_full_ack_queue_hands_the_held_run_over_before_it_waits() {
        let (mut pipe, took, acker, writer) = tiny();
        let (done_tx, done) = mpsc::channel();
        let submitter = thread::spawn(move || {
            let mut submitted = pipe.submit(WriteKind::Flush);
            took.recv_timeout(HANG)
                .expect("the ack-writer takes the first slot");
            submitted &= (0..2).all(|_| pipe.submit(WriteKind::Flush));
            let finished = pipe.finish().is_ok();
            let _ = done_tx.send((submitted, finished));
        });
        // A one-minute HANG DETECTOR for something that must happen, never a budget.
        let (submitted, finished) = done
            .recv_timeout(HANG)
            .expect("the third submit waited for room behind an op it still held");
        assert!(submitted && finished);
        submitter.join().unwrap();
        assert_eq!(acker.join().unwrap(), 3, "every op answered, in order");
        let runs = writer.join().unwrap();
        assert_eq!(runs.iter().sum::<usize>(), 3);
        assert_eq!(
            runs.first(),
            Some(&2),
            "the two held ops went over as one run"
        );
    }

    /// **A PIPELINE DROPPED WITHOUT FINISHING STILL HANDS ITS RUN OVER**, as a connection
    /// that ends on an error does: what the reader read and held reaches the writer, as it
    /// did when each op was queued as it was read.
    #[test]
    fn a_dropped_pipeline_hands_its_held_run_to_the_writer() {
        let (mut pipe, _took, acker, writer) = tiny();
        assert!(pipe.submit(WriteKind::Flush));
        drop(pipe);
        assert_eq!(acker.join().unwrap(), 1);
        assert_eq!(writer.join().unwrap(), [1]);
    }
}

/// The ack-writer half of a pipelined connection: stream each op's ack back in order.
///
/// Acks that are ALREADY resolved — a group-commit batch resolves a whole window at
/// once — are gathered and written together, one socket write (one sealed record)
/// for the lot instead of one each. What is gathered is written before this thread
/// blocks on anything, so no ack ever waits on a later one. A socket error tears the
/// connection down; an ack the global writer dropped (shutdown) ends the loop.
fn ack_writer_loop(
    mut wr: Conn,
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
        Err((code, msg)) => Response::Error { code, msg },
    }
}

/// Turn a writer ack into the wire response.
fn write_ack(stream: &mut Conn, ack: AckResult) -> io::Result<()> {
    write_frame(stream, &encode_response(&ack_response(ack)))
}

/// Commit the writer's accumulated batch and carry its full-flush horizon state forward.
fn finish_writer_batch(
    shared: &Arc<Shared>,
    batch: &mut Vec<WriteOp>,
    dirty_since: &mut Option<Instant>,
) {
    if batch.is_empty() {
        return;
    }
    let dirty = process_batch(shared, std::mem::take(batch));
    let previous = dirty_since.take();
    *dirty_since = if dirty {
        Some(previous.unwrap_or_else(Instant::now))
    } else {
        None
    };
}

/// The single writer thread: drain queued mutations into a batch and group-commit them
/// with ONE fsync. The batch self-tunes to load — everything that queued while the
/// previous fsync ran is drained at once — so throughput scales with offered
/// concurrency while each record keeps the Strict (fsync'd-before-ack) guarantee.
///
/// IT LEAVES ON THE STOP, never on a poll. Idle, it SLEEPS on its queue with no timer,
/// so an idle broker's writer never wakes ([`BrokerStats::writer_wakeups`]); a horizon
/// falling due is the only timed wake. Shutdown ([`stop_writer`]) queues a
/// [`Queued::Stop`] behind every op already queued: the writer commits those, then
/// whatever else is queued when it reaches the stop — an op that raced shutdown in is
/// committed, not dropped — and returns, so the join behind it waits on that final
/// batch and nothing else. (It also leaves if the channel closes, which cannot happen
/// while [`Shared`] holds the sender.)
///
/// THE ORDERED HORIZON lives here, on the one thread that appends. A full flush issued
/// from any other thread would usually make the writer's next `write()` wait behind it,
/// and its barrier too. Measured on one Mac (APFS, macOS 27.0.1,
/// 2026-10-21; aterm `docs/measured/flush-wait-2026-10-21.md`): while an `F_FULLFSYNC`
/// from another thread of the process was in flight, every `F_BARRIERFSYNC` the probe
/// caught waited for it to end (992 of 992, on the flushed file and two others), and so
/// did 72-99% of the `fsync(2)`s, growing appends, creates and renames caught in the
/// same directory tree; a 64-byte `pread` and an in-place page-cache `pwrite` never did.
/// A separate flusher thread would therefore still hold up the writer for the whole
/// flush: with this broker's log full-flushed from a probe thread, each of the 89
/// publishes that began with more than 2 ms of a flush left was acked no earlier than
/// 1 ms before that flush ended. Under continuous traffic, that is up to one ack a
/// horizon that takes a full flush's time.
///
/// `dirty_since` is when the first batch no full flush covers was acked (set as
/// that batch finishes, cleared by every full flush that catches the durable head up);
/// once the horizon has passed since then the writer issues a full flush — after the
/// current batch's acks, or on the idle timeout, which is the time left — outside the
/// log lock, and skipped when one already covers the head. Measuring from the first
/// uncovered ack, not from the last full flush, keeps a sparse burst at ONE full flush:
/// otherwise the first post after every quiet horizon would pay one. So the oldest ack
/// not on stable media is at most horizon + one batch + one full flush old. A stopping
/// writer leaves the horizon to the clean close, which flushes in full. Idle marks and
/// keepalives are wire frames, never records: they never make the log dirty, and a
/// horizon flush writes to no socket.
fn writer_loop(shared: &Arc<Shared>, rx: Receiver<Queued>) {
    let mut dirty_since: Option<Instant> = None;
    let mut stopping = false;
    loop {
        let first = if stopping {
            // Stopped: only what is queued already, then leave.
            match rx.try_recv() {
                Ok(queued) => Some(queued),
                Err(_) => return,
            }
        } else {
            match (shared.horizon, dirty_since) {
                // A horizon running: no later than it falls due.
                (Some(h), Some(t)) => match rx.recv_timeout(h.saturating_sub(t.elapsed())) {
                    Ok(queued) => Some(queued),
                    Err(mpsc::RecvTimeoutError::Timeout) => {
                        shared.writer_wakeups.fetch_add(1, Ordering::Relaxed);
                        None
                    }
                    Err(mpsc::RecvTimeoutError::Disconnected) => return,
                },
                // Nothing owed: for as long as the queue is empty.
                _ => match rx.recv() {
                    Ok(queued) => Some(queued),
                    Err(mpsc::RecvError) => return,
                },
            }
        };
        if let Some(first) = first {
            let mut batch = Vec::new();
            let mut next = Some(first);
            while let Some(queued) = next {
                match queued {
                    Queued::Op(op) => batch.push(op),
                    // Whole, even past BATCH_MAX: a run is at most a pipeline's depth of
                    // ops (each holds an ack slot; `Pipeline::reserve`).
                    Queued::Run(ops) => batch.extend(ops),
                    // A connection's decoded writes were queued before this marker. Judge
                    // them under its fences, then remove those fences before any later work.
                    Queued::DropFences(conn_id) => {
                        finish_writer_batch(shared, &mut batch, &mut dirty_since);
                        shared
                            .sticky_fences
                            .lock()
                            .unwrap_or_else(std::sync::PoisonError::into_inner)
                            .drop_conn(conn_id);
                    }
                    Queued::Stop => stopping = true,
                }
                // Nothing more queued right now → commit what we have.
                next = if batch.len() < BATCH_MAX {
                    rx.try_recv().ok()
                } else {
                    None
                };
            }
            finish_writer_batch(shared, &mut batch, &mut dirty_since);
        }
        if stopping {
            continue;
        }
        if let (Some(h), Some(t)) = (shared.horizon, dirty_since) {
            if t.elapsed() >= h {
                let dirty = horizon_flush(shared);
                dirty_since = if dirty { Some(Instant::now()) } else { None };
            }
        }
    }
}

/// The horizon's full flush: owed through the log's head now, issued outside the lock
/// through the log's own descriptor (shared), skipped when a full flush already covers
/// it. Whether the log is still dirty afterwards: never after a failure, which poisons
/// the log — no later flush can cover what that one was to (`BrokerLog::full_flush_failed`).
fn horizon_flush(shared: &Shared) -> bool {
    let (target, handle, served_before) = {
        let mut log = shared
            .log
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let target = log.head().0;
        if !log.full_flush_owed(target) {
            return false;
        }
        (target, log.flush_handle(), log.served())
    };
    let res = handle.full();
    let (_, dirty, wake) = settle_full_flush(shared, target, res, served_before);
    fire_tail_wakes(shared, wake);
    dirty
}

/// Record, under the log lock, the outcome of a full flush through `target` issued
/// outside it, and publish what it changed: the durable head, the visible head a held
/// batch kept back (never in the Replicated tier, whose visible head is the quorum's),
/// whether the log still serves Ordered, and — if the log latched to Strict — the copy
/// `Hello` answers from. The durable head after it (or the error a waiting op is
/// answered with), whether the log is still dirty, and the tail wake plan
/// ([`publish_log_state`]).
fn settle_full_flush(
    shared: &Shared,
    target: u64,
    res: io::Result<()>,
    served_before: crate::ServedInfo,
) -> (Result<u64, String>, bool, WakePlan) {
    // Declared before the guard so unwind also releases the lock first.
    let retired;
    let mut log = shared
        .log
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let outcome = match res {
        Ok(()) => {
            log.full_flush_done(target);
            Ok(log.durable_head().0)
        }
        Err(e) => {
            log.full_flush_failed(&e);
            Err(format!(
                "durability flush failed: {e}; the outcome is unknown, and the log refuses \
                 every write until it is reopened: resend then"
            ))
        }
    };
    let wake;
    (wake, retired) = publish_log_state(shared, &mut log, served_before);
    let dirty = log.poisoned().is_none() && log.durable_head() < log.head();
    drop(log);
    drop(retired);
    (outcome, dirty, wake)
}

/// Count a retention call's first wait for the writer's current batch to settle.
/// The lock acquisition stays at each call site so its guard lifetime is explicit.
#[cfg(feature = "retention")]
fn record_retention_wait(shared: &Shared, waited: &mut bool) {
    if !*waited {
        *waited = true;
        shared.retention_waits.fetch_add(1, Ordering::Relaxed);
    }
}

/// Publish the log's base where the lock-free readers find it, under the log lock.
fn publish_floor(shared: &Shared, log: &BrokerLog) {
    shared.base.store(log.base().0, Ordering::Release);
}

/// [`publish_floor`], and whether the log is due a retention tick: after the rules are set
/// and after every planning, whatever it began (a tick that changes nothing too).
#[cfg(feature = "retention")]
fn publish_retention(shared: &Shared, log: &BrokerLog) {
    publish_floor(shared, log);
    shared
        .retain_due
        .store(log.retention_due(), Ordering::Relaxed);
}

/// Plan which parked subscriber tails to wake for newly visible records in
/// `[before .. visible)` (or a `durable_mark_moved` advance), called under `shared.log`.
fn plan_tail_wakes(
    shared: &Shared,
    log: &BrokerLog,
    before: u64,
    visible: u64,
    durable_mark_moved: bool,
) -> WakePlan {
    if !shared.selective_tail_wake.load(Ordering::Acquire) {
        let any = before < visible && log.any_deliverable(Offset(before), Offset(visible));
        return if any || durable_mark_moved {
            WakePlan::Broadcast
        } else {
            WakePlan::None
        };
    }
    let sums = log.visible_summaries(Offset(before), Offset(visible));
    let mut has_any_deliverable = false;
    for s in sums.iter() {
        if !s.is_hidden() {
            has_any_deliverable = true;
            break;
        }
    }
    let parkers = shared
        .tail_parkers
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let mut to_wake: Vec<Arc<TailParker>> = Vec::new();
    for p in parkers.iter() {
        let mut st = p
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let mut first_match: Option<u64> = None;
        if has_any_deliverable {
            for s in sums.iter() {
                if !s.is_hidden() && p.filter.matches_str(s.subject()) {
                    first_match = Some(s.offset());
                    break;
                }
            }
        }
        let owe_durable = durable_mark_moved && p.idle_marks;
        if let Some(m) = first_match {
            if !st.has_unread_match && st.safe_skip_to == before {
                st.safe_skip_to = tail_skip_clamp(m, visible);
            }
            st.has_unread_match = true;
            st.matched_head = tail_wake_head_advance(st.matched_head, visible);
            p.needs_wake.store(true, Ordering::Release);
            to_wake.push(p.clone());
        } else if owe_durable {
            if !st.has_unread_match && st.safe_skip_to == before && before < visible {
                st.safe_skip_to = tail_skip_clamp(visible, visible);
            }
            st.matched_head = tail_wake_head_advance(st.matched_head, visible);
            p.needs_wake.store(true, Ordering::Release);
            to_wake.push(p.clone());
        } else if !st.has_unread_match && st.safe_skip_to == before && before < visible {
            st.safe_skip_to = tail_skip_clamp(visible, visible);
        }
    }
    if to_wake.is_empty() {
        WakePlan::None
    } else {
        WakePlan::Selective(to_wake)
    }
}

/// Publish the log's heads and tier where the lock-free readers find them. Called with
/// the log lock held, which is what a parked tail's predicate reads them under, so no
/// wakeup is lost between "nothing to do" and "wait".
fn publish_log_state(
    shared: &Shared,
    log: &mut BrokerLog,
    served_before: crate::ServedInfo,
) -> (WakePlan, Option<crate::LastViewGarbage>) {
    shared.is_replica.store(log.is_replica(), Ordering::Release);
    shared.log_head.store(log.head().0, Ordering::Release);
    #[cfg(feature = "retention")]
    {
        shared.log_bytes.store(log.durable_len(), Ordering::Relaxed);
        shared
            .retain_due
            .store(log.retention_due(), Ordering::Relaxed);
    }
    publish_floor(shared, log);
    // Durable first, then visible: a thread that sees the visible head move past an
    // escalated record then also sees the durable head that covers it.
    let durable_before = shared.durable.swap(log.durable_head().0, Ordering::Release);
    let durable_mark_moved = shared.durable_marks && log.durable_head().0 > durable_before;
    let (wake, published) = if shared.replicator.is_none() {
        let visible = log.visible_head();
        let before = shared.head.swap(visible.0, Ordering::Release);
        (
            plan_tail_wakes(shared, log, before, visible.0, durable_mark_moved),
            Some(visible.0),
        )
    } else if durable_mark_moved {
        let cur_vis = shared.head.load(Ordering::Relaxed);
        (plan_tail_wakes(shared, log, cur_vis, cur_vis, true), None)
    } else {
        (WakePlan::None, None)
    };
    let served = log.served();
    if served != served_before {
        *shared
            .hello
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = HelloCopy::of(log);
    }
    let garbage = match published {
        Some(visible) => publish_last_history(log, visible),
        None => None,
    };
    (wake, garbage)
}

// This is called only with the ACTUAL head just published under the log lock,
// never with a Last request's input or the promoted log head. An unexpected domain
// refusal retains history; new reads outside its published range return a typed error.
fn publish_last_history(log: &mut BrokerLog, visible: u64) -> Option<crate::LastViewGarbage> {
    if log.poisoned().is_some() {
        return None;
    }
    match log.publish_last_visible(visible) {
        Ok(retired) => Some(retired),
        Err(error) => {
            eprintln!("astream-broker: cannot advance last-value history: {error}");
            None
        }
    }
}

/// Execute `plan` outside the log lock after producer acks have been dispatched.
fn fire_tail_wakes(shared: &Shared, plan: WakePlan) {
    match plan {
        WakePlan::None => {}
        WakePlan::Broadcast => {
            shared.tail_broadcasts.fetch_add(1, Ordering::Relaxed);
            shared.tail.notify_all();
        }
        WakePlan::Selective(parkers) => {
            shared
                .selective_tail_wakes
                .fetch_add(count64(parkers.len()), Ordering::Relaxed);
            for p in parkers {
                p.cv.notify_one();
            }
        }
    }
}

/// Wake every parked subscriber tail across both broadcast (`shared.tail`) and
/// selective (`shared.tail_parkers`) condvars (used for shutdown, revocations, and
/// live mode switches).
fn notify_all_tails(shared: &Shared) {
    shared.tail.notify_all();
    let parkers = shared
        .tail_parkers
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .clone();
    for p in parkers {
        p.cv.notify_one();
    }
}

/// Clamp selective tail parker state down to `new_vis` under `shared.log` when a
/// replica's log is truncated via `truncate_replica_to`.
fn reset_tail_parkers_to(shared: &Shared, new_vis: u64) {
    let parkers = shared
        .tail_parkers
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    for p in parkers.iter() {
        let mut st = p
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        st.safe_skip_to = tail_skip_clamp(st.safe_skip_to, new_vis);
        st.matched_head = tail_skip_clamp(st.matched_head, new_vis);
        st.has_unread_match = false;
        p.needs_wake.store(false, Ordering::Release);
    }
}

/// The writer's side of [`Broker::pause_next_batch`] and [`Broker::pause_next_acks`],
/// at `point`: take the armed rendezvous if it is for this point (it is one-shot), say
/// the batch is here, and hold — at [`BatchPoint::Staged`] the caller still has the log
/// lock — until the test resumes it or drops its handle. A rendezvous armed for the
/// other point is left for that point to take.
fn hold_paused_batch(shared: &Shared, point: BatchPoint) {
    let slot = {
        let mut seam = shared
            .batch_pause
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        match &seam.slot {
            Some(slot) if slot.at == point => {}
            _ => return,
        }
        shared.batch_pause_armed.store(false, Ordering::Release);
        seam.slot.take()
    };
    if let Some(slot) = slot {
        let _ = slot.reached.send(());
        let _ = slot.resume.recv();
    }
}

/// Stage a whole batch under the log lock, write and fsync it once with the lock RELEASED,
/// promote it under the lock again, then ack each op. A staged-record
/// I/O error poisons the batch (rolled back, all error); a too-large / reserved /
/// diverged record is an op-level error that does not abort the rest; an fsync error
/// fails the whole batch (none durable). The parked subscriber tails are woken once
/// the batch's head is published, and only if the offsets it made visible hold a
/// record some subscriber could be delivered (see the end). In the Replicated tier the
/// batch is committed locally, then every committed-but-unconfirmed record is shipped
/// to the followers OUTSIDE the lock, and each op is acked only if its offset is below
/// the resulting quorum watermark.
///
/// THE HELD HEAD (Ordered and Relaxed, when a batch holds an escalated record — or a
/// resend of one, or a `Flush`): the Replicated tier's pattern, with a full flush where
/// it ships.
///
/// 1. Stage and commit: staged and begun under the lock, the write and the barrier (or
///    nothing) with it RELEASED, promoted under it again (`commit_begin`,
///    `BatchWrite::run`, `commit_end`). Its pure answer ([`Committed`](crate::store))
///    names the visible head — the first escalated record, or the log's head — and the
///    full flush owed.
/// 2. Still under the lock: publish that visible head, take a flush handle (the file's
///    own descriptor, shared), release the lock.
/// 3. Ack every op whose record is below the visible head (and is not a resend of an
///    escalated record no full flush covers yet), and every will registration, which
///    answers for its own commit. The per-connection ack writer writes
///    each connection's acks in request order whatever order they are sent in, so an
///    early send never reorders a pipeline. Wake the tails if a deliverable record became
///    visible.
/// 4. OUTSIDE the lock: the full flush.
/// 5. Under the lock again: the durable head rises, the visible head is published past
///    the held records; release, ack the rest, and wake the tails for what that made
///    visible (or, on a log that served Ordered at its open, for the durable marks it
///    may owe). A flush that fails records the run `Lossy`, poisons the log until it
///    is reopened (the records it was to cover stay held: a later flush that succeeds
///    says nothing about them) and answers the waiting ops "outcome unknown".
///
/// Every reader is bounded by the visible head (Fetch reads it under the lock, Last
/// pins it, a tail delivers below it), so an escalated record is never visible before
/// it is durable, and no ack precedes visibility (read-your-writes). Strict never takes
/// this path: its every batch is flushed in full by its own commit (in `BatchWrite::run`,
/// with the log lock released), as before.
///
/// Returns whether the log is DIRTY afterwards — records acked that no full flush
/// covers — which starts the writer's horizon.
#[allow(clippy::type_complexity)]
fn stage_batch_ops(
    shared: &Shared,
    guard: &mut BrokerLog,
    batch: Vec<WriteOp>,
    visible_head: u64,
    mut rejoined_left: usize,
) -> (
    Vec<AckSender>,
    Vec<AckResult>,
    Vec<bool>,
    FlushAsked,
    Vec<bool>,
    Vec<Option<StickyOpMeta>>,
    bool,
    Option<(crate::LogIdentity, Offset)>,
) {
    let mut acks: Vec<AckSender> = Vec::new();
    let mut results: Vec<AckResult> = Vec::new();
    // Which ops are `Flush` requests: answered with the durable head once the batch's
    // full flush (if any) has run.
    let mut flushes: Vec<bool> = Vec::new();
    let mut wants_flush = FlushAsked::No;
    // Which ops are acked on the LOCAL commit alone, with no quorum gate. See the
    // `local_only` arm of the ack loop below: a `/a/will` registration is the broker's
    // own bookkeeping, never delivered to anyone, and its acknowledgement decides what
    // the CONNECTION does with the will — so it must answer for the record's own fate,
    // not for a follower's. An ungated moot conditional `Retire` (whose subject is
    // already absent below `visible_head` with no unconfirmed retire in flight) is also
    // answered at once.
    let mut local_only: Vec<bool> = Vec::new();
    let mut sticky_meta: Vec<Option<StickyOpMeta>> = Vec::new();
    let mut fences_guard = if shared.has_sticky_batch_refusal {
        Some(match shared.sticky_fences.lock() {
            Ok(g) => g,
            Err(p) => p.into_inner(),
        })
    } else {
        None
    };
    let mut poisoned = false;
    // A LOG ALREADY POISONED refuses EVERY op of the batch in the one wording
    // (`store::poisoned_refusal`, which starts `proto::LOG_POISONED_PREFIX`), so a
    // producer reads the condition off its own answer, whichever op of the batch is
    // its. Staging would refuse the first op so and abort the batch, but every op after
    // it would read only "batch aborted (prior append I/O error)", and which op comes
    // first is the order connections reached the writer: a producer whose ops always
    // landed behind another's would never be told the log will take nothing until it
    // is reopened, and would retry on a connection that is worth nothing. The batch
    // aborts exactly as before (nothing staged, the file rolled back to its durable
    // length).
    let refused_poisoned = guard.poisoned().map(crate::store::poisoned_refusal);
    // The leader's log identity, from the highest-offset replicated record this batch
    // staged that carried one, with that offset: adopted once the batch commits, if
    // that record is the log's newest (see below).
    let mut adopt: Option<(crate::LogIdentity, Offset)> = None;
    for op in batch {
        let fresh = op.ack.fresh.clone();
        acks.push(op.ack);
        let mut is_local = matches!(op.kind, WriteKind::WillRegister { .. });
        flushes.push(matches!(op.kind, WriteKind::Flush | WriteKind::Settle));
        let op_sticky = match (op.conn_id, &op.kind) {
            (
                Some(cid),
                WriteKind::Publish {
                    producer_id,
                    producer_seq,
                    ..
                }
                | WriteKind::Relay {
                    producer_id,
                    producer_seq,
                    ..
                }
                | WriteKind::ProcessAndProduce {
                    producer_id,
                    producer_seq,
                    ..
                }
                | WriteKind::PreRefused {
                    producer_id,
                    producer_seq,
                    ..
                },
            ) => Some(StickyOpMeta {
                conn_id: cid,
                producer_id: *producer_id,
                producer_seq: *producer_seq,
            }),
            _ => None,
        };
        if let Some(msg) = &refused_poisoned {
            if let Some(fence) = &fresh {
                fence.store(true, Ordering::Relaxed);
            }
            if let (Some(fences), Some(m)) = (fences_guard.as_deref_mut(), op_sticky) {
                fences.record_refusal(m.conn_id, m.producer_id, m.producer_seq);
            }
            local_only.push(is_local);
            sticky_meta.push(None);
            results.push(Err(refusal(ERR_REFUSED, msg.clone())));
            poisoned = true;
            continue;
        }
        if fresh
            .as_ref()
            .is_some_and(|fence| fence.load(Ordering::Relaxed))
        {
            local_only.push(is_local);
            sticky_meta.push(None);
            results.push(Err(refusal(
                crate::proto::ERR_FRESH_FENCED,
                "fresh publication fenced: reconnect before publishing again",
            )));
            continue;
        }
        if poisoned {
            if let Some(fence) = &fresh {
                fence.store(true, Ordering::Relaxed);
            }
            if let (Some(fences), Some(m)) = (fences_guard.as_deref_mut(), op_sticky) {
                if let Err(fence_seq) = fences.check(m.conn_id, m.producer_id, m.producer_seq) {
                    local_only.push(is_local);
                    sticky_meta.push(None);
                    results.push(Err(refusal(
                        ERR_REFUSED,
                        crate::sticky_fence::format_gap_fenced_msg(fence_seq, m.producer_seq),
                    )));
                    continue;
                }
                fences.record_refusal(m.conn_id, m.producer_id, m.producer_seq);
            }
            local_only.push(is_local);
            sticky_meta.push(None);
            results.push(Err(refusal(
                ERR_REFUSED,
                "batch aborted (prior append I/O error)",
            )));
            continue;
        }
        if let (Some(fences), Some(m)) = (fences_guard.as_deref_mut(), op_sticky) {
            if let Err(fence_seq) = fences.check(m.conn_id, m.producer_id, m.producer_seq) {
                local_only.push(is_local);
                sticky_meta.push(None);
                results.push(Err(refusal(
                    ERR_REFUSED,
                    crate::sticky_fence::format_gap_fenced_msg(fence_seq, m.producer_seq),
                )));
                continue;
            }
        }
        let staged = match op.kind {
            WriteKind::PreRefused { err, .. } => {
                if let Some(fence) = &fresh {
                    fence.store(true, Ordering::Relaxed);
                }
                if let (Some(fences), Some(m)) = (fences_guard.as_deref_mut(), op_sticky) {
                    fences.record_refusal(m.conn_id, m.producer_id, m.producer_seq);
                }
                local_only.push(is_local);
                sticky_meta.push(None);
                results.push(Err(err));
                continue;
            }
            WriteKind::FreshPublish {
                producer_id,
                producer_seq,
                subject,
                body,
            } => {
                // The same key lookup as ordinary publish, including staged keys
                // and producer lineage, while holding the writer's log lock.
                if !is_hidden_subject(&subject) {
                    if let Some(offset) = guard.produced_dup(producer_id, producer_seq) {
                        if let Some(fence) = &fresh {
                            fence.store(true, Ordering::Relaxed);
                        }
                        local_only.push(is_local);
                        sticky_meta.push(None);
                        results.push(Err(refusal(
                            crate::proto::ERR_FRESH_HELD,
                            format!("fresh publication key already held at {}", offset.0),
                        )));
                        continue;
                    }
                }
                guard.stage_publish(producer_id, producer_seq, subject, body)
            }
            WriteKind::Publish {
                producer_id,
                producer_seq,
                subject,
                body,
            } => guard.stage_publish(producer_id, producer_seq, subject, body),
            WriteKind::Relay {
                producer_id,
                producer_seq,
                subject,
                body,
            } => guard.stage_relay(producer_id, producer_seq, subject, body),
            WriteKind::Commit { group, upto } => match guard.stage_commit(group, upto) {
                Ok(off) => Ok((off, false)),
                Err(e) => Err(e),
            },
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
            WriteKind::Replicate {
                rec,
                leader,
                bt_ms,
                conn_diverged,
            } => {
                if conn_diverged.load(Ordering::Relaxed) {
                    Err(StageErr::Diverged(format!(
                        "replica diverged on this connection prior to offset {}: reconnect after truncating to common prefix",
                        rec.seq.0
                    )))
                } else if guard.is_replica()
                    && matches!(
                        leader,
                        Some(ldr)
                            if ldr.id == guard.identity().id
                                && crate::failover::failover_fences_stale(
                                    ldr.generation,
                                    guard.identity().generation,
                                )
                    )
                {
                    let ldr_gen = match leader {
                        Some(ldr) => ldr.generation,
                        None => 0,
                    };
                    Err(StageErr::Diverged(format!(
                        "replica fenced stale leader generation {ldr_gen} < adopted generation {}",
                        guard.identity().generation
                    )))
                } else {
                    let staged = guard.stage_replica_with_bt(rec, bt_ms);
                    if let Err(StageErr::Diverged(msg)) = &staged {
                        if msg.starts_with("replica diverged at offset ") {
                            conn_diverged.store(true, Ordering::Relaxed);
                        }
                    }
                    if let (Ok((off, _)), Some(leader)) = (&staged, leader) {
                        if !matches!(adopt, Some((_, through)) if *off < through) {
                            adopt = Some((leader, *off));
                        }
                    }
                    staged
                }
            }
            WriteKind::Bind {
                producer_id,
                principal,
            } => guard.stage_bind(producer_id, principal),
            WriteKind::WillRegister { conn_id, will } => {
                match guard.stage_will_register_for_conn(conn_id, &will) {
                    Ok(off) => Ok((off, false)),
                    Err(e) => Err(e),
                }
            }
            WriteKind::WillFire { conn_id, will } => guard.stage_will_fire_for_conn(conn_id, will),
            WriteKind::WillDrop { conn_id } => {
                guard.drop_live_will(conn_id);
                Ok((Offset::ZERO, false))
            }
            WriteKind::Retire {
                producer_id,
                target_subject,
            } => guard.stage_retire(producer_id, target_subject),
            WriteKind::RetireConditional {
                producer_id,
                subject,
                offset,
                log,
            } => match guard.stage_retire_conditional(
                producer_id,
                subject,
                offset,
                log,
                visible_head,
            ) {
                Ok((off, deduped, ungated)) => {
                    is_local = ungated;
                    Ok((off, deduped))
                }
                Err(e) => Err(e),
            },
            // Stages nothing; answered below, with the durable head.
            WriteKind::Flush => {
                wants_flush = wants_flush.max(FlushAsked::Covering);
                Ok((Offset::ZERO, false))
            }
            WriteKind::Settle => {
                wants_flush = FlushAsked::Always;
                Ok((Offset::ZERO, false))
            }
            WriteKind::RejoinFollowers => {
                is_local = true;
                let count = std::mem::take(&mut rejoined_left);
                Ok((Offset(u64::try_from(count).unwrap_or(u64::MAX)), false))
            }
            // The tick's own bookkeeping, which it waits for: answered on the local commit,
            // as a will registration is, never on a quorum or a held head's flush.
            #[cfg(feature = "retention")]
            WriteKind::Forget { subjects } => {
                is_local = true;
                match guard.stage_forgets(subjects) {
                    Ok(n) => Ok((Offset(n), n == 0)),
                    Err(e) => Err(e),
                }
            }
        };
        local_only.push(is_local);
        // The code says whether the same op can EVER land (`proto::ERR_*`): the
        // record's own shape cannot change on a resend, so it is permanent; the
        // outcomes that are the log's state of the moment (an I/O error, a replica's
        // spine) are not known to be; and a spent subject budget, which only another
        // producer's record or a smaller count lifts, has a code of its own so the
        // producer can decide by what it knows about who writes the subject.
        let (code, msg) = match staged {
            Ok((off, deduped)) => {
                if let (Some(fences), Some(m)) = (fences_guard.as_deref_mut(), op_sticky) {
                    fences.record_commit(m.conn_id, m.producer_id, m.producer_seq);
                    sticky_meta.push(Some(m));
                } else {
                    sticky_meta.push(None);
                }
                results.push(Ok((off.0, deduped)));
                continue;
            }
            Err(StageErr::TooLarge) => (ERR_RECORD_REFUSED, "message too large".to_string()),
            Err(StageErr::BadSubject(msg)) => (ERR_BAD_SUBJECT, msg),
            Err(StageErr::Reserved(subject)) => (ERR_RECORD_REFUSED, reserved_msg(&subject)),
            Err(StageErr::Cut(msg)) => (ERR_RECORD_REFUSED, msg),
            // Not permanent: another producer can introduce this subject, and an
            // identical request then updates an existing index entry without
            // spending a new slot. Not ERR_REFUSED either: nothing transient failed,
            // and a producer that alone writes the subject can drop the record.
            Err(StageErr::SubjectBound(msg)) => (ERR_SUBJECT_BOUND, msg),
            // Only a `Bind`, at attach: the producer id is another principal's.
            Err(StageErr::Collision(msg)) => (ERR_UNAUTHORIZED, msg),
            Err(
                StageErr::RetireCharged(msg) | StageErr::RetireWill(msg) | StageErr::RetireLog(msg),
            ) => (ERR_RETIRE_REFUSED, msg),
            // Not a failure: the fence did its job and the will appended nothing.
            Err(StageErr::Fenced(msg)) => (ERR_REFUSED, msg),
            // Also not a failure: a replica appends nothing of its own making.
            Err(StageErr::Replica(msg)) => (ERR_REFUSED, msg),
            // A gap is repaired by re-shipping; the leader reads the message, not this.
            Err(StageErr::Diverged(msg)) => (ERR_REFUSED, msg),
            // Decided in here, under the lock that appends: a replicated hidden record
            // offered to a log this broker owns, and a will offered the reserved ack
            // half. Op-level, like every other refusal above — the file is untouched.
            Err(StageErr::ReservedReplica(msg)) => (ERR_RECORD_REFUSED, msg),
            Err(StageErr::SeqReserved(msg)) => (ERR_RECORD_REFUSED, msg),
            Err(StageErr::Io(e)) => {
                poisoned = true;
                (ERR_REFUSED, format!("append failed: {e}"))
            }
        };
        if let Some(fence) = &fresh {
            fence.store(true, Ordering::Relaxed);
        }
        if let (Some(fences), Some(m)) = (fences_guard.as_deref_mut(), op_sticky) {
            fences.record_refusal(m.conn_id, m.producer_id, m.producer_seq);
        }
        sticky_meta.push(None);
        results.push(Err(refusal(code, msg)));
    }
    (
        acks,
        results,
        flushes,
        wants_flush,
        local_only,
        sticky_meta,
        poisoned,
        adopt,
    )
}

fn process_batch(shared: &Arc<Shared>, batch: Vec<WriteOp>) -> bool {
    let mut rejoined = 0usize;
    // Replicated tier: if an operator asked to rejoin fenced followers, un-fence them
    // first so the immediately following `redial` + `replicate` catches them up in this
    // same batch. Network I/O runs before taking the log lock.
    if let Some(rep) = &shared.replicator {
        let mut has_rejoin = false;
        for op in &batch {
            if matches!(op.kind, WriteKind::RejoinFollowers) {
                has_rejoin = true;
                break;
            }
        }
        if has_rejoin {
            let floor = shared.base.load(Ordering::Acquire);
            rejoined = rep.rejoin(floor);
        }
        rep.redial(&shared.running);
    }
    shared.writer_batches.fetch_add(1, Ordering::Relaxed);
    // Declared before both guards: release detached history after them on unwind.
    let retired;
    // The batch lock for the batch's whole life, its write and flush included (lock
    // order: batch → log); only retention ever waits on it (`Shared::batch`).
    let batch_held = shared
        .batch
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let mut guard = shared
        .log
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let head_before = guard.head();
    let served_before = guard.served();
    let visible_head = shared.head.load(Ordering::Relaxed);
    // The wills this batch settles (`BrokerStats::wills_settled`), counted once its head
    // is published below.
    let wills = batch
        .iter()
        .filter(|op| {
            matches!(
                op.kind,
                WriteKind::WillFire { .. } | WriteKind::WillDrop { .. }
            )
        })
        .count();
    let (acks, results, flushes, wants_flush, local_only, sticky_meta, poisoned, adopt) =
        stage_batch_ops(shared, &mut guard, batch, visible_head, rejoined);
    // The `pause_next_batch` test seam: staged, log lock held, nothing written yet.
    if shared.batch_pause_armed.load(Ordering::Acquire) {
        hold_paused_batch(shared, BatchPoint::Staged);
    }
    // Commit the batch: one write and one flush for everyone (unless poisoned — then
    // roll back), in the three halves of `BrokerLog::commit_batch`, with the log lock
    // RELEASED around the write and the flush. Begin, under the lock: seal the batch,
    // pick the flush its tier owes, take its bytes. Nothing is promoted, so nothing a
    // reader can see has changed when the lock goes.
    let begun = if poisoned {
        guard.abort_batch();
        Err(refusal(ERR_REFUSED, "batch aborted before fsync"))
    } else {
        match guard.commit_begin() {
            Ok(b) => Ok(b),
            Err(e) => Err(refusal(ERR_REFUSED, format!("commit failed: {e}"))),
        }
    };
    // The write and the flush, WITHOUT the log lock: every reader — a `Fetch` page, a
    // `Last` round, a tail copying what the last batch made visible — takes the lock
    // meanwhile and reads the log as it stood before this batch. The batch lock is still
    // held (retention waits on it), and the staged batch refuses every other mutation
    // until its end. Then end, under the lock again: promote the batch if the flush
    // returned `Ok` — promotion after durability, as before — or roll it back.
    let (mut guard, commit_res) = match begun {
        Ok(Begun::Write(mut write)) => {
            drop(guard);
            // The `pause_next_write` test seam: begun, log lock RELEASED, nothing
            // written yet.
            if shared.batch_pause_armed.load(Ordering::Acquire) {
                hold_paused_batch(shared, BatchPoint::Writing);
            }
            let res = write.run();
            let mut relocked = shared
                .log
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            let ended = match relocked.commit_end(write, res) {
                Ok(c) => Ok(c),
                Err(e) => Err(refusal(ERR_REFUSED, format!("commit failed: {e}"))),
            };
            (relocked, ended)
        }
        // An empty batch writes and flushes nothing, so it never lets the lock go (a full
        // flush it still owes — a resent escalated op — is issued below, as for any batch).
        Ok(Begun::Empty(committed)) => (guard, Ok(committed)),
        Err(refused) => (guard, Err(refused)),
    };
    // A REPLICA reports its leader's identity: its offsets are the leader's, so a
    // client that fails over to it keeps the ones it persisted. Adopted only once the
    // records that carried it are durable here, only when they reach the log's newest
    // record (an echo of a shared prefix vouches for nothing above it), and only by a
    // log that IS a replica and has not been found holding a record its leader does
    // not (`adopt_identity` asks all three). Failing to record it is not the batch's
    // failure — the records are committed — and leaves this follower reporting its
    // own identity, which costs a client that fails over a re-read, never a skipped
    // record.
    if let (Ok(_), Some((leader, through))) = (&commit_res, adopt) {
        if let Err(e) = guard.adopt_identity(leader, through) {
            eprintln!(
                "astream-broker: this replica could not record its leader's log identity \
                 {leader}: {e}; it keeps reporting {}",
                guard.identity()
            );
        }
        // The one place a running broker's identity (and with it the lineage) changes,
        // so the copy `Hello` answers from is refreshed here, under the log lock,
        // before this batch's records become visible. Whatever the adoption decided:
        // copying the log's own answer cannot be wrong, and a replicated batch is not
        // a hot path.
        *shared
            .hello
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = HelloCopy::of(&guard);
    }
    // Replicated tier: gather every committed-but-unconfirmed record — from the lowest
    // follower prefix to the head, cheap Arc clones — under the lock, to ship AFTER
    // releasing it: network I/O never holds the log lock (the delivery discipline).
    let to_ship = match &shared.replicator {
        Some(rep) if commit_res.is_ok() => {
            let base = rep.min_upto(guard.base().0, guard.head().0);
            Some(guard.read_from_stamped(Offset(base)))
        }
        _ => None,
    };
    // THE FULL FLUSH OWED, if any (step 1 of the held head): what the commit names —
    // an escalated record, or a resend of one, no full flush covers — or, for a
    // `Flush` request, the head (skipped, and counted so, when a full flush already
    // covers it; a flush the commit owes covers the request too), and for a `Settle`,
    // the head whatever covers it: every flush here is issued after the batch's requests
    // were read, which is what a settle answers for. Its handle is taken
    // here, under the lock (step 2); the flush itself runs outside it (step 4). Taking
    // it cannot fail — it shares the log's own descriptor — so a broker short of
    // descriptors never mistakes a flush it could not issue for one that failed.
    let owed = match &commit_res {
        Ok(committed) => match committed.owe_full {
            Some(o) => Some(o.0),
            None => {
                let head = guard.head().0;
                let issue = match wants_flush {
                    // A settle's flush is the point, whatever it covers; none on a
                    // poisoned log, whose every op the batch already refused.
                    FlushAsked::Always => guard.poisoned().is_none(),
                    FlushAsked::Covering => guard.full_flush_owed(head),
                    FlushAsked::No => false,
                };
                issue.then_some(head)
            }
        },
        Err(_) => None,
    };
    let flush = match owed {
        Some(target) => Some((target, guard.flush_handle())),
        None => None,
    };
    // Strict/Ordered/Relaxed: publish the visible head — the log's head, or HELD at the
    // first record a full flush still owes — and the durable head, under the lock (the
    // tail's wait predicate reads them under this lock, so no wakeup is lost between
    // "caught up" and "wait"); and the tier, if the commit latched it to Strict.
    //
    // Whether the tails are woken (see the end) is decided here too, over what this
    // publish made VISIBLE: the old visible head to the new, which a held batch keeps
    // short of the log's head. The records it holds are woken for by the flush that
    // releases them (`settle_full_flush`), not by this commit.
    let wake;
    (wake, retired) = publish_log_state(shared, &mut guard, served_before);
    // After the head: a binding enters the attach path's copy only once the head that
    // covers it is published (`binding_settled` reads them in the other order, and
    // declines a binding at or above the visible head — a held one included). Only
    // from a batch that committed: a failed one promoted nothing to copy (and one that
    // failed AFTER promoting poisoned the log, whose bindings the writer then refuses
    // to re-confirm — they stay out of the copy, as they stay out of an ack). And
    // BEFORE the acks below: a connection's connection thread reads its next grant
    // only once this batch has answered its first, so its later `rw,p=` grants of the
    // same principal find the binding here — one writer round trip per connection, not
    // one per grant. Copied after the acks, they would race this copy for it
    // (`pause_next_acks` lets a test stand at the acks and see the copy done).
    if commit_res.is_ok() && shared.cap_secret.is_some() {
        copy_new_bindings(shared, &guard);
    }
    if guard.head() == head_before {
        shared.empty_batches.fetch_add(1, Ordering::Relaxed);
    }
    // After the head, under the log lock, so a reader that sees a will counted sees
    // whatever it appended, and its own later write queues behind it.
    if wills > 0 {
        shared
            .wills_settled
            .fetch_add(count64(wills), Ordering::Relaxed);
    }
    let durable_now = guard.durable_head().0;
    let dirty = guard.durable_head() < guard.head();
    drop(guard);
    // The batch is committed or rolled back: retention may rewrite the file again.
    drop(batch_held);
    drop(retired);
    let dirty = finish_batch_acks_and_flush(
        shared,
        commit_res,
        to_ship,
        flush,
        acks,
        results,
        local_only,
        sticky_meta,
        flushes,
        wake,
        durable_now,
        dirty,
        served_before,
    );
    #[cfg(feature = "retention")]
    ask_retention_after_batch(shared);
    dirty
}

/// AFTER A BATCH, the retention it may owe: when the batch took some class of the rules
/// past its bytes ([`BrokerLog::retention_due`]) or the log past a cap
/// ([`Broker::set_max_retained_records`], [`Broker::set_max_retained_bytes`]), ask the
/// retention tick for a tick now. Never a compaction here, after the batch's acks and
/// replication: the tick runs it off the ack path (`retention_tick`). With no rules and no
/// cap (the default) three `Relaxed` loads, and no lock.
#[cfg(feature = "retention")]
fn ask_retention_after_batch(shared: &Shared) {
    let due = shared.retain_due.load(Ordering::Relaxed);
    let max_records = shared.max_retained_records.load(Ordering::Relaxed) as u64;
    let max_bytes = shared.max_retained_bytes.load(Ordering::Relaxed) as u64;
    if !due && max_records == 0 && max_bytes == 0 {
        return;
    }
    let bytes = shared.log_bytes.load(Ordering::Relaxed);
    let records = shared
        .log_head
        .load(Ordering::Relaxed)
        .saturating_sub(shared.base.load(Ordering::Relaxed));
    if due || (max_records > 0 && records > max_records) || (max_bytes > 0 && bytes > max_bytes) {
        ask_tick(shared);
    }
}

/// Ask the retention tick for a tick now (`TickState::due`).
#[cfg(feature = "retention")]
fn ask_tick(shared: &Shared) {
    let mut t = shared
        .tick
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    t.due = true;
    shared.tick_cv.notify_one();
}

/// THE CAPS' FLOOR for a tick (`set_max_retained_records` / `_bytes`): over a cap, the
/// oldest half of the safe visible prefix, and at least what keeps half the record cap —
/// the cut the writer's caps took before they ran through the tick. `0` (none) under
/// both caps, with no cap set, or with nothing below `ceiling` to drop.
#[cfg(feature = "retention")]
fn caps_floor(shared: &Shared, log: &BrokerLog, ceiling: u64) -> u64 {
    let max_records = shared.max_retained_records.load(Ordering::Relaxed);
    let max_bytes = shared.max_retained_bytes.load(Ordering::Relaxed);
    if max_records == 0 && max_bytes == 0 {
        return 0;
    }
    let (base, head) = (log.base().0, log.head().0);
    let records = usize::try_from(head.saturating_sub(base)).unwrap_or(usize::MAX);
    let bytes = usize::try_from(log.durable_len()).unwrap_or(usize::MAX);
    let over_records = max_records > 0 && records > max_records;
    let over_bytes = max_bytes > 0 && bytes > max_bytes;
    if (!over_records && !over_bytes) || ceiling <= base {
        return 0;
    }
    let span = ceiling.saturating_sub(base);
    let mut cut = base.saturating_add((span / 2).max(1));
    if max_records > 0 {
        let target_keep = (max_records / 2).max(1) as u64;
        let by_count = head.saturating_sub(target_keep);
        if by_count > cut {
            cut = by_count;
        }
    }
    cut.min(ceiling)
}

/// ONE RETENTION TICK at `now_ms` (unix ms; a test's hand clock), off the ack path: begin
/// between batches — the cut the rules take, at least the caps' floor, never above the
/// visible head (nor, replicated, what every follower holds) — then the held store's
/// frames and the compaction's copy with no lock held, then the finish between batches.
///
/// One compaction at a time (`Shared::compaction`, lock order compaction → batch → log).
/// A tick that would `wait` for a retention call's (or another tick's) compaction does;
/// the tick's thread does not: it SKIPS (`None`), as the writer's caps skipped a batch,
/// since the compaction under way is already moving the base and the next batch over a
/// bound, or the next interval, asks again. Either way the tick is counted
/// (`TickState::ticks`, `skips`) and whoever waits on one is woken.
#[cfg(feature = "retention")]
fn retention_tick(
    shared: &Shared,
    now_ms: u64,
    wait: bool,
) -> io::Result<Option<crate::RetentionTick>> {
    let one = if wait {
        Some(match shared.compaction.try_lock() {
            Ok(held) => held,
            Err(std::sync::TryLockError::Poisoned(poisoned)) => poisoned.into_inner(),
            Err(std::sync::TryLockError::WouldBlock) => {
                shared.compaction_waits.fetch_add(1, Ordering::Relaxed);
                shared
                    .compaction
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner)
            }
        })
    } else {
        match shared.compaction.try_lock() {
            Ok(held) => Some(held),
            Err(std::sync::TryLockError::Poisoned(poisoned)) => Some(poisoned.into_inner()),
            Err(std::sync::TryLockError::WouldBlock) => None,
        }
    };
    let tick = match one {
        Some(held) => {
            let tick = retention_tick_run(shared, now_ms);
            drop(held);
            tick.map(Some)
        }
        None => Ok(None),
    };
    let mut t = shared
        .tick
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    match &tick {
        Ok(None) => t.skips = t.skips.saturating_add(1),
        _ => t.ticks = t.ticks.saturating_add(1),
    }
    shared.tick_done.notify_all();
    tick
}

/// [`retention_tick`]'s work, the compaction lock held.
#[cfg(feature = "retention")]
fn retention_tick_run(shared: &Shared, now_ms: u64) -> io::Result<crate::RetentionTick> {
    // What every follower holds, asked before the batch and log locks: the replicator's
    // links are held across a ship, which a tick must not wait on with the log locked.
    // Read a moment early it is only lower, and the base moves only under `_one`.
    let followers = match &shared.replicator {
        Some(rep) => rep.min_upto(
            shared.base.load(Ordering::Acquire),
            shared.log_head.load(Ordering::Acquire),
        ),
        None => u64::MAX,
    };
    let mut waited = false;
    let begun = {
        let _batch = match shared.batch.try_lock() {
            Ok(held) => held,
            Err(std::sync::TryLockError::WouldBlock) => {
                record_retention_wait(shared, &mut waited);
                shared
                    .batch
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner)
            }
            Err(std::sync::TryLockError::Poisoned(poisoned)) => {
                panic!("retention: the writer panicked inside a batch ({poisoned})")
            }
        };
        let mut log = shared
            .log
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let ceiling = shared
            .head
            .load(Ordering::Relaxed)
            .min(log.head().0)
            .min(followers);
        let at_least = caps_floor(shared, &log, ceiling);
        let begun = log.retention_begin(now_ms, ceiling, at_least);
        // The planning reset each class's room whatever it began, a tick that changes
        // nothing too: the writer asks by it from here.
        publish_retention(shared, &log);
        match begun? {
            Some(job) => Ok(job),
            // A tick that changes nothing still forgets what the last one could not.
            None => Err(log.forgettable()),
        }
    };
    let mut job = match begun {
        Ok(job) => job,
        Err(forget) => {
            let base = shared.base.load(Ordering::Acquire);
            return Ok(crate::RetentionTick {
                base_before: base,
                base,
                forgotten: forget_by_writer(shared, forget),
                ..crate::RetentionTick::default()
            });
        }
    };
    // The held store's frames and the bulk of the copy: no lock held, so no publish's
    // ack waits for them.
    if let Err(e) = job.run() {
        let mut log = shared
            .log
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        log.retention_abandon(job);
        publish_retention(shared, &log);
        return Err(e);
    }
    let _batch = match shared.batch.try_lock() {
        Ok(held) => held,
        Err(std::sync::TryLockError::WouldBlock) => {
            record_retention_wait(shared, &mut waited);
            shared
                .batch
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
        }
        Err(std::sync::TryLockError::Poisoned(poisoned)) => {
            panic!("retention: the writer panicked inside a batch ({poisoned})")
        }
    };
    let mut log = shared
        .log
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let mut tick = log.retention_finish(job)?;
    publish_retention(shared, &log);
    let forget = log.forgettable();
    // The writer stages the forgets: neither lock is held while the tick waits for it.
    drop(log);
    drop(_batch);
    tick.forgotten = forget_by_writer(shared, forget);
    Ok(tick)
}

/// THE TICK'S FORGETS, staged by the writer as one op ([`WriteKind::Forget`]) and waited
/// for, the compaction lock held so no other retention moves the base meanwhile: how many
/// it forgot. `0` for none asked, and for a writer that is stopping (the next open's tick
/// finds the same subjects). A tick that forgot as many as it may
/// ([`FORGET_MAX`](crate::retention::FORGET_MAX)) asks for another, for the rest.
#[cfg(feature = "retention")]
fn forget_by_writer(shared: &Shared, subjects: Vec<(String, Offset)>) -> u64 {
    if subjects.is_empty() {
        return 0;
    }
    let (tx, rx) = mpsc::channel();
    let op = WriteOp {
        kind: WriteKind::Forget { subjects },
        ack: tx.into(),
        conn_id: None,
    };
    if shared.writes.send(Queued::Op(op)).is_err() {
        return 0;
    }
    let forgotten = match rx.recv() {
        Ok(Ok((n, _))) => n,
        Ok(Err(_)) | Err(mpsc::RecvError) => 0,
    };
    if usize::try_from(forgotten).is_ok_and(|n| n >= crate::retention::FORGET_MAX) {
        ask_tick(shared);
    }
    forgotten
}

/// THE RETENTION TICK's thread: a tick whenever one is asked for (`ask_tick`) or the
/// [interval](Broker::set_retention_interval) passes, by the wall clock, until the broker
/// stops. A failed tick is logged, one line, and the next waits for the interval whatever
/// asks sooner, so a log that cannot compact is not retried once per batch.
#[cfg(feature = "retention")]
fn ticker_loop(shared: &Shared) {
    let mut backoff = false;
    loop {
        {
            let t = shared
                .tick
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            let every = Duration::from_millis(shared.retention_interval_ms.load(Ordering::Relaxed));
            let (mut t, _) = shared
                .tick_cv
                .wait_timeout_while(t, every, |t| !t.stop && (backoff || !t.due))
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if t.stop {
                return;
            }
            t.due = false;
        }
        match retention_tick(shared, now_unix_ms(), false) {
            Ok(_) => backoff = false,
            Err(e) => {
                eprintln!(
                    "astream-broker: the retention tick failed, and waits out its interval \
                     before the next: {e}"
                );
                backoff = true;
            }
        }
    }
}

/// Start the retention tick's thread, once: the first rules or cap a broker is given. Its
/// caller asks for the tick it wants FIRST (`ask_tick`): a thread started after the ask
/// takes it as its first tick, where one started before it could take an earlier ask
/// (`set_retention_interval`'s) and then this one, a second tick at its start.
#[cfg(feature = "retention")]
fn ensure_ticker(shared: &Arc<Shared>) {
    let mut slot = shared
        .ticker
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    if slot.is_some() || !shared.running.load(Ordering::Relaxed) {
        return;
    }
    let t_shared = Arc::clone(shared);
    *slot = Some(thread::spawn(move || ticker_loop(&t_shared)));
}

/// Stop the retention tick's thread and join it, its tick in progress finished: at
/// shutdown, before the writer's join and the log's clean close, so no tick meets a
/// closed log.
fn stop_ticker(shared: &Shared) {
    #[cfg(feature = "retention")]
    {
        shared
            .tick
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .stop = true;
        shared.tick_cv.notify_all();
        let ticker = shared
            .ticker
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .take();
        if let Some(t) = ticker {
            let _ = t.join();
        }
    }
    #[cfg(not(feature = "retention"))]
    let _ = shared;
}

fn record_sticky_ack_refusal(shared: &Shared, meta: Option<StickyOpMeta>, send: &AckResult) {
    let Some(m) = meta else {
        return;
    };
    if send.is_ok() || !shared.has_sticky_batch_refusal {
        return;
    }
    let mut fences = match shared.sticky_fences.lock() {
        Ok(g) => g,
        Err(p) => p.into_inner(),
    };
    fences.record_refusal(m.conn_id, m.producer_id, m.producer_seq);
}

#[allow(clippy::too_many_arguments, clippy::type_complexity)]
fn finish_batch_acks_and_flush(
    shared: &Arc<Shared>,
    commit_res: Result<crate::store::Committed, (u8, String)>,
    to_ship: Option<Vec<(Arc<BrokerRecord>, Option<u64>)>>,
    flush: Option<(u64, crate::storage::FlushHandle)>,
    acks: Vec<AckSender>,
    results: Vec<AckResult>,
    local_only: Vec<bool>,
    sticky_meta: Vec<Option<StickyOpMeta>>,
    flushes: Vec<bool>,
    mut wake: WakePlan,
    durable_now: u64,
    mut dirty: bool,
    served_before: crate::ServedInfo,
) -> bool {
    // Replicated tier: ship, then publish the quorum watermark as the visible head —
    // again under the log lock, for the same no-lost-wakeup reason — and wake.
    let watermark = match (&shared.replicator, to_ship) {
        (Some(rep), Some(records)) => {
            let wm = rep.replicate(&records, &shared.running);
            // This binding outlives the guard even if later bookkeeping unwinds.
            let retired;
            let mut g = shared
                .log
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            // MONOTONE + HEAD-BOUNDED (`Astream.Broker.TlaEpochWatermarkReplication`):
            // a record a quorum once held is not un-held because a follower later
            // restarted empty and its link reset to re-ship from 0 — the visible head
            // only ever advances (`replica_ack_monotone`) and is bounded by the durable
            // head (`committed_watermark`).
            let committed_wm = g.record_replica_ack(Offset(wm)).0;
            let prev = shared.head.fetch_max(committed_wm, Ordering::Relaxed);
            let hwm = crate::proto::replica_ack_monotone(prev, committed_wm);
            // What a quorum now holds that it did not, whichever batch appended it: a
            // record from an earlier batch becomes visible when a later batch's ship
            // confirms it.
            wake = plan_tail_wakes(shared, &g, prev, hwm, false);
            retired = publish_last_history(&mut g, hwm);
            drop(g);
            drop(retired);
            Some(hwm)
        }
        (Some(_), None) => Some(shared.head.load(Ordering::Relaxed)),
        (None, _) => None,
    };
    // The `pause_next_acks` test seam: committed, head published, bindings copied, log
    // lock released, nothing answered yet.
    if shared.batch_pause_armed.load(Ordering::Acquire) {
        hold_paused_batch(shared, BatchPoint::BeforeAcks);
    }
    // Ack each op BEFORE waking 64+ parked subscriber threads (`notify_all`), so the
    // producer's ack-writer immediately receives its batch acks instead of waiting
    // behind a thundering herd of woken subscriber threads.
    //
    // Durable AND (if Replicated) below the quorum watermark, else error.
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
    //
    // THE HELD HEAD (step 3): with a full flush owed, an op whose record is at or above
    // the visible head — or a resend of an escalated record no full flush covers — waits
    // for it, and so does a `Flush` request; every other op is answered now.
    //
    // `local_only` IS EXEMPT HERE TOO, for the reason it is exempt from the quorum: a
    // will registration's ack answers for its `/a/will` record's own fate, and that
    // record is committed — promoted, on the log, at the tier's promise like any
    // record the table does not name. Made to wait, a flush that then failed answered it
    // "will was not persisted" while the log kept the will, which the next open fired: a
    // goodbye for a producer told it registered nothing. No reader is shown the record
    // early by acking it (a hidden subject is delivered to nobody), so nothing is lost by
    // answering it with the commit.
    let mut waiting: Vec<(AckSender, AckResult, bool, bool, Option<StickyOpMeta>)> = Vec::new();
    for ((((ack, res), local), meta), is_flush) in acks
        .into_iter()
        .zip(results)
        .zip(local_only)
        .zip(sticky_meta)
        .zip(flushes)
    {
        let send = match (&commit_res, res) {
            // An op that failed on its own terms (too large / reserved / diverged / the
            // append or poisoned-log error that aborted the batch) keeps its own, more
            // specific message; the ops a batch failure took down with it get the batch's.
            (Ok(_), Err(refused)) => Err(refused),
            // ...but a batch that rolled back decided nothing for good: its refusals
            // were judged against records that never landed (the subject bound counts
            // the batch's own new subjects), so a resend may land. Not known to be
            // permanent, whatever the op was refused for.
            (Err(_), Err((_, msg))) => Err(refusal(ERR_REFUSED, msg)),
            (Err(msg), Ok(_)) => Err(msg.clone()),
            (Ok(committed), Ok((off, deduped))) => {
                let held = if is_flush {
                    flush.is_some()
                } else {
                    flush.is_some() && !local && !committed.acks_now(off, deduped)
                };
                if held {
                    waiting.push((ack, Ok((off, deduped)), is_flush, local, meta));
                    continue;
                }
                if is_flush {
                    Ok((durable_now, false))
                } else {
                    match watermark {
                        Some(wm) if !crate::proto::offset_is_committed(wm, off) && !local => {
                            Err(refusal(ERR_REFUSED, "not replicated to quorum"))
                        }
                        _ => Ok((off, deduped)),
                    }
                }
            }
        };
        record_sticky_ack_refusal(shared, meta, &send);
        let _ = ack.send(send);
    }
    // WAKE THE TAILS ONLY FOR SOMETHING THEY COULD DELIVER. Every parked tail waits on
    // the one `Condvar`, so a broadcast resumes all of them, and each resumed tail takes
    // the log lock to read what it was woken for. That used to happen after EVERY
    // batch, including the two kinds no subscriber can be delivered anything from:
    //
    // - a batch that made nothing visible. In Strict and Relaxed that is a batch that
    //   appended nothing — every op deduplicated or refused, or an attach's re-bind of
    //   a principal the writer found bound (`empty_batches`). In Replicated it is one
    //   whose ship moved the quorum watermark past nothing new, which an empty batch
    //   need not be: it still ships what the followers lack, and a retry of a publish
    //   refused for want of a quorum can confirm it (`wake` above is `prev..hwm`);
    // - a batch whose newly visible records are all hidden (`is_hidden_subject`): a
    //   group commit, a will registration, a binding, a retirement.
    //
    // A lone delivery through aterm's bridge is a publish batch and then a commit-only
    // batch — aterm commits its inbox group once per burst (aterm `78e8cbfdaf`: once no
    // inbox record is queued, or every 256 records), so a delivery nothing is queued
    // behind pays a commit of its own, while a refused record's notice and its commit go
    // out as one `ProcessAndProduce` ack — and the second broadcast doubled the herd:
    // with S parked tails, 2S wakeups per lone delivery instead of S (cost study B4
    // step 1). A tail that read the commit, matched nothing and then
    // probed its peer also sat out the next wakeup inside the probe (see `tail_loop`).
    //
    // SKIPPING THEM LOSES NOTHING. A tail parks only while `head <= cursor`, read under
    // the log lock the head was published under above, and it is woken by anything
    // else that can end or feed it: the next batch that does make a deliverable record
    // visible, a revocation, shutdown (each broadcasts on its own), its authority's
    // lapse and its liveness poll (each bounds its wait). A tail left parked past a
    // hidden-only batch reads those offsets the next time it wakes, skips them as it
    // always skipped them, and has delivered nothing later for it: there was nothing
    // in them to deliver.
    //
    // NOR DOES IT MOVE A MARK. The tail's cursor sits below those offsets until then,
    // and the cursor is what a `Mark` reports — but a parked tail writes nothing, marks
    // included, and once resumed it reads before it marks again (the park branch marks
    // only after a read came back empty, the delivery branch only after a chunk). So
    // the skip delays no mark and changes none that is written: a mark written before
    // the park named the cursor and head of that moment, as it always did. It is NOT
    // that a mark's cursor has reached the head it names: the delivery branch's idle
    // mark after a chunk cut short at `TAIL_CHUNK`, and the park branch's when a batch
    // lands between the tail's read and its mark, pair the cursor with a newer head,
    // and did before this skip as they do now.
    //
    // A REVOCATION OR SHUTDOWN WAKE IS BOUNDED BY THE POLL, AS IT WAS. Each sets its
    // flag and calls `notify_all` without the log lock, so a notify that lands between a
    // tail's predicate check and its wait is lost. Any later batch, a commit included,
    // used to resume such a tail sooner; now only a deliverable one or the poll does.
    // The worst case is one poll either way (200 ms by default), and a revoked tail is
    // delivered nothing meanwhile: the delivery loop checks revocation per record.
    //
    // NOT YET: WAKING ONLY THE TAILS WHOSE FILTER MATCHES (cost study B4 step 2). A
    // deliverable record still resumes every parked tail, matching or not, so S tails
    // cost S wakeups per message. Waking only the matching ones needs a parker per tail
    // registered with its filter and the writer matching each new record against every
    // registered filter. That replaces the one-lock argument above with a per-tail
    // wake-flag protocol (a tail clears its flag before it reads; the writer sets it
    // after it publishes the head), puts S filter matches per record on the writer's
    // thread, and leaves each non-matching tail up to a liveness poll behind the
    // visible head, to read in one go when it next wakes. The herd it would remove
    // costs microseconds at aterm's handful of tails per broker, so it waits for a
    // broker with many tails to need it. MEASURED, so that broker knows what it pays:
    // since a quiet tail no longer sits deaf in a blocking probe (`tail_loop`), every
    // tail is parked when a publish lands and the publish resumes all of them — at 33
    // tails (Relaxed, publish then commit, `broker_wake_bench fanout 32`) 33.0
    // wakeups per message, where about half the tails used to miss each broadcast
    // inside a probe (28.4-32.2 over two broadcasts), and publish → recv p50 0.165 ms
    // against 0.131 ms before at load 2.9-10.6, 0.141 against 0.128 ms at load
    // 2.8-4.3 (n = 1800 each, interleaved). At 6 tails and at 1 the p50 did not move
    // (0.045-0.073 against 0.052-0.070 ms; 0.022-0.054 against 0.021-0.059 ms).
    //
    // THE HELD HEAD wakes for what it releases: a batch held for its full flush made
    // visible only what precedes its escalated record, and the flush that releases the
    // rest decides its own wake over the same old-to-new visible range
    // (`settle_full_flush`) — plus, on a log that served Ordered at its open, a full
    // flush that moved the durable head, which may owe an idle-marks subscriber a
    // durable mark.
    fire_tail_wakes(shared, wake);
    // Steps 4 and 5: the full flush, OUTSIDE the lock, then its outcome under it —
    // the durable head, the visible head past the held records — and the waiting ops.
    if let Some((target, handle)) = flush {
        // The `pause_next_flush` test seam: step 3 done (every op the held head does not
        // keep back answered, the tails woken), the log lock released, the full flush not
        // yet issued.
        if shared.batch_pause_armed.load(Ordering::Acquire) {
            hold_paused_batch(shared, BatchPoint::BeforeFlush);
        }
        let res = handle.full();
        let (outcome, still_dirty, wake) = settle_full_flush(shared, target, res, served_before);
        dirty = still_dirty;
        for (ack, res, is_flush, local, meta) in waiting {
            let send = match (&outcome, res) {
                (Ok(durable), Ok(_)) if is_flush => Ok((*durable, false)),
                (Ok(_), res) => match (watermark, res) {
                    (Some(wm), Ok((off, _)))
                        if !crate::proto::offset_is_committed(wm, off) && !local =>
                    {
                        Err(refusal(ERR_REFUSED, "not replicated to quorum"))
                    }
                    (_, res) => res,
                },
                (Err(msg), _) => Err(refusal(ERR_REFUSED, msg.clone())),
            };
            record_sticky_ack_refusal(shared, meta, &send);
            let _ = ack.send(send);
        }
        fire_tail_wakes(shared, wake);
    }
    dirty
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
    broker_times: bool,
) -> Result<
    (
        Vec<Arc<BrokerRecord>>,
        Vec<Option<u64>>,
        Option<String>,
        u64,
    ),
    String,
> {
    let mut out: Vec<Arc<BrokerRecord>> = Vec::new();
    let mut out_bts: Vec<Option<u64>> = Vec::new();
    let mut cursor = after.to_string();
    // The head every round reads against and the answer reports. Read under the log
    // lock on the first round (see below) and never re-read: that is what makes the
    // multi-round walk a snapshot rather than a splice of rounds taken at different
    // heads.
    let mut pinned: Option<crate::LastView> = None;
    for round in 0..LAST_RESUME_ROUNDS {
        // The FIRST round reads its head under the SAME lock as its page —
        // `shared.head` (the subscriber-visible head, the quorum watermark in the
        // Replicated tier), never `log.head()`. Under the lock: the seek, at most
        // LAST_SCAN_MAX retirement-plus-index visits, and pointer clones — never the socket writes the
        // caller does, which happen with it released.
        let (step, round_bts, head) = {
            let log = shared
                .log
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if pinned.is_none() {
                let head = shared.head.load(Ordering::Relaxed);
                pinned = Some(log.last_view_at(head).map_err(|error| error.to_string())?);
            }
            let Some(view) = pinned.as_mut() else {
                return Err("last: missing owned view".into());
            };
            let head = view.visible();
            let step = log
                .last_matching(
                    filt,
                    &cursor,
                    want.saturating_sub(out.len()),
                    LAST_SCAN_MAX,
                    view,
                )
                .map_err(|error| error.to_string())?;
            let mut round_bts = Vec::new();
            if broker_times {
                if let crate::LastStep::Page(ref page, _) = step {
                    for rec in page {
                        round_bts.push(log.last_record_bt_ms(view, rec));
                    }
                }
            }
            (step, round_bts, head)
        };
        let (page, resume) = match step {
            crate::LastStep::Pending => continue,
            crate::LastStep::Page(page, resume) => (page, resume),
        };
        out.extend(page);
        if broker_times {
            out_bts.extend(round_bts);
        }
        match resume {
            // The prefix range ran out: the answer is complete.
            None => return Ok((out, out_bts, None, head)),
            // Cut by `max`, or stopped on an entry the filter matches: either way the
            // cursor is a subject the caller's own filter covers.
            Some(s) if filt.matches_str(&s) || out.len() >= want => {
                return Ok((out, out_bts, Some(s), head));
            }
            // Cut by the scan bound on a non-matching entry: keep walking.
            Some(s) => cursor = s,
        }
        // The round boundary, with the log lock released — the window a concurrent
        // publisher gets, and the one a test needs to occupy to prove the head above
        // does not move with it. Taken out of the lock before waiting so the test is
        // free to touch the broker.
        let pause = {
            let mut slot = shared
                .last_round_pause
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if matches!(&*slot, Some(p) if p.round == round) {
                slot.take()
            } else {
                None
            }
        };
        if let Some(pause) = pause {
            if pause.reached.send(()).is_ok() {
                let _ = pause.resume.recv();
            }
        }
    }
    Err(format!(
        "last: {LAST_RESUME_ROUNDS} scan rounds under {:?} reached no position this filter \
         covers; narrow the filter's literal prefix",
        filt.as_str()
    ))
}

/// Up to `max` records from `*cursor` up to (not including) `head`, read under the log
/// lock the caller holds, and first, for a tail that asked (`told`), the gap notice it is
/// owed before them ([`BrokerLog::gap_notice`]; R4's addendum, A9).
///
/// The cursor is not clamped: below the base, [`BrokerLog::read_chunk`] reads the held
/// records from where it is, and moves it up to the base once none is left below, so a
/// tail whose filter holds nothing there still reaches the base and parks. What it can no
/// longer be delivered is what the notice tells.
fn next_chunk(
    log: &BrokerLog,
    cursor: &mut u64,
    head: u64,
    filter: &Filter,
    also_at: Option<u64>,
    told: Option<&mut Told>,
    max: usize,
) -> (Option<crate::proto::Gap>, crate::store::TailStep) {
    let gap = match told {
        Some(t) => log.gap_notice(filter, *cursor, t),
        None => None,
    };
    (gap, log.read_tail_chunk(cursor, head, filter, also_at, max))
}

struct TailParkerGuard<'a> {
    shared: &'a Shared,
    id: u64,
}

impl Drop for TailParkerGuard<'_> {
    fn drop(&mut self) {
        let mut parkers = self
            .shared
            .tail_parkers
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let mut retained = Vec::new();
        while let Some(p) = parkers.pop() {
            if p.id != self.id {
                retained.push(p);
            }
        }
        *parkers = retained;
    }
}

/// Tell a tail what retention gave up below it ([`Response::Gap`]), at once: ahead of
/// every record it is delivered after it.
fn write_gap<S: Write>(stream: &mut S, gap: crate::proto::Gap) -> io::Result<()> {
    write_frame(stream, &encode_response(&Response::Gap(gap)))
}

/// Stream every visible record matching `filter` from `cursor`, then tail live, until
/// the peer goes, the broker stops, the peer's identity key or capability principal is
/// revoked, or — on a guarded broker — the authority that admitted the subscription
/// lapses at `until` (unix ms; `u64::MAX`: never), which ends the stream with an
/// `unauthorized` error.
fn tail_sync_selective_before_read(
    parker: &TailParker,
    base_off: u64,
    visible: u64,
    cursor: &mut u64,
    told: &mut Option<Told>,
) -> bool {
    let mut st = parker
        .state
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    if st.safe_skip_to > *cursor {
        *cursor = st.safe_skip_to;
        if let Some(ref mut t) = told {
            t.advance_to(*cursor);
        }
    }
    if !st.has_unread_match
        && tail_wake_is_caught_up(st.matched_head, *cursor)
        && *cursor >= base_off
    {
        *cursor = (*cursor).max(visible);
        if let Some(ref mut t) = told {
            t.advance_to(*cursor);
        }
        st.safe_skip_to = *cursor;
        st.matched_head = *cursor;
        st.has_unread_match = false;
        parker.needs_wake.store(false, Ordering::Release);
        true
    } else {
        false
    }
}

#[allow(clippy::too_many_arguments)]
fn tail_fetch_chunk_locked(
    shared: &Shared,
    log: &BrokerLog,
    parker: &TailParker,
    cursor: &mut u64,
    visible: u64,
    filter: &Filter,
    told: &mut Option<Told>,
    chunk: usize,
    broker_times: bool,
    batch_bts: &mut Vec<Option<u64>>,
) -> (Option<crate::proto::Gap>, crate::store::TailStep) {
    let visible = visible.min(log.head().0);
    let (g, step) = if visible > *cursor {
        next_chunk(log, cursor, visible, filter, None, told.as_mut(), chunk)
    } else {
        (
            None,
            crate::store::TailStep::Chunk {
                records: Vec::new(),
                scanned_to: *cursor,
            },
        )
    };
    if shared.selective_tail_wake.load(Ordering::Relaxed)
        && *cursor >= visible
        && *cursor >= log.base().0
    {
        let mut st = parker
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        st.safe_skip_to = *cursor;
        st.matched_head = *cursor;
        st.has_unread_match = false;
        parker.needs_wake.store(false, Ordering::Release);
    }
    if broker_times {
        if let crate::store::TailStep::Chunk { ref records, .. } = step {
            for rec in records {
                batch_bts.push(log.subject_bt_ms(&rec.subject, rec.seq));
            }
        }
    }
    (g, step)
}

#[allow(clippy::too_many_arguments)]
fn tail_park_and_fetch_chunk(
    shared: &Shared,
    parker: &TailParker,
    cursor: &mut u64,
    filter: &Filter,
    told: &mut Option<Told>,
    chunk: usize,
    asks: TailAsks,
    peer: &PeerAuth,
    seen_epoch: Option<u64>,
    until: u64,
    marked_durable: u64,
    park: Duration,
    batch_bts: &mut Vec<Option<u64>>,
) -> (Option<crate::proto::Gap>, crate::store::TailStep) {
    let mut guard = shared
        .log
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let mut parked = false;
    let mut resumes = 0u64;
    let seen_mode_epoch = shared.selective_mode_epoch.load(Ordering::Relaxed);
    let use_selective = shared.selective_tail_wake.load(Ordering::Relaxed);
    let wait_start = Instant::now();
    let mut last_timed_out = false;
    loop {
        if parked {
            resumes = resumes.saturating_add(1);
        }
        let sighup_pending = shared.has_revocation_file.load(Ordering::Relaxed)
            && astream_sys::sighup_generation() != shared.sighup_seen.load(Ordering::Relaxed);
        let epoch_changed = Some(shared.revocation_epoch.load(Ordering::Relaxed)) != seen_epoch;
        let mode_changed = shared.selective_mode_epoch.load(Ordering::Relaxed) != seen_mode_epoch;
        let caught_up = if use_selective {
            let visible = shared.head.load(Ordering::Relaxed);
            tail_sync_selective_before_read(parker, guard.base().0, visible, cursor, told)
        } else {
            shared.head.load(Ordering::Relaxed) <= *cursor
        };
        let wait = shared.running.load(Ordering::Relaxed)
            && !sighup_pending
            && !epoch_changed
            && !mode_changed
            && peer_revocation_reason_raw(shared, peer).is_none()
            && caught_up
            && !(asks.idle_marks
                && shared.durable_marks
                && marked_durable < *cursor
                && shared.durable.load(Ordering::Relaxed) > marked_durable);
        if wait != parked {
            if wait {
                shared.parked_tails.fetch_add(1, Ordering::Relaxed);
            } else {
                shared.parked_tails.fetch_sub(1, Ordering::Relaxed);
            }
            parked = wait;
        }
        if !wait || last_timed_out {
            break;
        }
        let Some(rem) = park.checked_sub(wait_start.elapsed()) else {
            break;
        };
        if rem.is_zero() {
            break;
        }
        let wait_res = if use_selective {
            parker.cv.wait_timeout(guard, rem)
        } else {
            shared.tail.wait_timeout(guard, rem)
        };
        let (next_guard, timeout_res) = wait_res.unwrap_or_else(std::sync::PoisonError::into_inner);
        guard = next_guard;
        last_timed_out = timeout_res.timed_out();
    }
    if parked {
        shared.parked_tails.fetch_sub(1, Ordering::Relaxed);
    }
    shared.tail_wakeups.fetch_add(resumes, Ordering::Relaxed);

    let visible = shared.head.load(Ordering::Relaxed).min(guard.head().0);
    let sighup_pending = shared.has_revocation_file.load(Ordering::Relaxed)
        && astream_sys::sighup_generation() != shared.sighup_seen.load(Ordering::Relaxed);
    let epoch_changed = Some(shared.revocation_epoch.load(Ordering::Relaxed)) != seen_epoch;
    if visible > *cursor
        && !sighup_pending
        && !epoch_changed
        && peer_revocation_reason_raw(shared, peer).is_none()
        && lapsed(until).is_none()
    {
        if shared.selective_tail_wake.load(Ordering::Relaxed) {
            let _ = tail_sync_selective_before_read(parker, guard.base().0, visible, cursor, told);
        }
        if visible > *cursor {
            return tail_fetch_chunk_locked(
                shared,
                &guard,
                parker,
                cursor,
                visible,
                filter,
                told,
                chunk,
                asks.broker_times,
                batch_bts,
            );
        }
    }
    (
        None,
        crate::store::TailStep::Chunk {
            records: Vec::new(),
            scanned_to: *cursor,
        },
    )
}

#[allow(clippy::too_many_arguments)]
fn tail_deliver_batch(
    shared: &Shared,
    stream: &mut Conn,
    out: &mut Vec<u8>,
    batch: Vec<Arc<BrokerRecord>>,
    scanned_to: u64,
    batch_bts: &[Option<u64>],
    cursor: &mut u64,
    filter: &Filter,
    asks: TailAsks,
    peer: &PeerAuth,
    cap_check: &mut StreamCapCheck,
    until: &mut u64,
) -> io::Result<Option<bool>> {
    if batch.is_empty() {
        if let Some(failure) = stream_failure(shared, peer, cap_check, until) {
            end_stream_failure(stream, out, failure)?;
            return Ok(None);
        }
        *cursor = (*cursor).max(scanned_to);
        return Ok(Some(false));
    }
    let mut wrote = false;
    for (i, rec) in batch.into_iter().enumerate() {
        if let Some(failure) = stream_failure(shared, peer, cap_check, until) {
            end_stream_failure(stream, out, failure)?;
            return Ok(None);
        }
        *cursor = match rec.seq.checked_next() {
            Some(o) => o.0,
            None => {
                flush_egress(stream, out)?;
                return Ok(None);
            }
        };
        if crate::store::is_hidden_record(&rec) {
            continue;
        }
        if filter.matches_str(&rec.subject) {
            let bt_ms = batch_bts.get(i).copied().flatten();
            queue_delivery_maybe_stamped(shared, stream, out, &rec, asks, bt_ms)?;
            wrote = true;
        }
    }
    flush_egress(stream, out)?;
    *cursor = (*cursor).max(scanned_to);
    Ok(Some(wrote))
}

#[allow(clippy::too_many_arguments)]
fn tail_loop(
    shared: &Arc<Shared>,
    stream: &mut Conn,
    mut cursor: u64,
    filter: Filter,
    mut until: u64,
    asks: TailAsks,
    peer: &PeerAuth,
    mut cap_check: StreamCapCheck,
) -> io::Result<()> {
    let idle_marks = asks.idle_marks;
    let parker_id = shared.next_parker_id.fetch_add(1, Ordering::Relaxed);
    let init_base = shared.base.load(Ordering::Acquire);
    let init_head = shared.head.load(Ordering::Acquire);
    let need_init_scan = init_head > cursor || cursor < init_base;
    let parker = Arc::new(TailParker {
        id: parker_id,
        filter: filter.clone(),
        idle_marks,
        cv: Condvar::new(),
        needs_wake: AtomicBool::new(need_init_scan),
        state: Mutex::new(TailParkerState {
            safe_skip_to: cursor,
            matched_head: tail_wake_head_advance(cursor, init_head),
            has_unread_match: need_init_scan,
        }),
    });
    shared
        .tail_parkers
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .push(parker.clone());
    let _parker_guard = TailParkerGuard {
        shared,
        id: parker_id,
    };
    let mut told = if asks.gaps {
        Some(Told::at(cursor))
    } else {
        None
    };
    #[cfg(test)]
    let mut pause = shared
        .tail_pause
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .take();
    #[cfg(test)]
    let chunk = pause.as_ref().map_or(TAIL_CHUNK, |p| p.chunk);
    #[cfg(not(test))]
    let chunk = TAIL_CHUNK;
    let _ = stream.set_read_timeout(Some(PEER_PROBE_TIMEOUT));
    let _ = stream.set_write_timeout(Some(stream_write_timeout(shared)));
    let mut out = Vec::new();
    let mut probed = Instant::now();
    let liveness_poll = Duration::from_millis(shared.liveness_poll_ms.load(Ordering::Relaxed));
    let idle_mark = Duration::from_millis(shared.idle_mark_ms.load(Ordering::Relaxed));
    let mut wrote_at = Instant::now();
    let mut said_caught_up = false;
    let mut marked_durable: u64 = 0;
    // A `Request::BurstMarks` reader is owed a `Mark` at each catch-up after a delivery.
    let mut owes_burst_mark = asks.burst_marks;
    loop {
        let mut gap = None;
        let mut batch_bts = Vec::new();
        let fast_caught_up = if shared.selective_tail_wake.load(Ordering::Acquire) {
            !parker.needs_wake.load(Ordering::Acquire)
                && cursor >= shared.base.load(Ordering::Acquire)
        } else {
            shared.head.load(Ordering::Acquire) <= cursor
        };
        let mut scanned_to = cursor;
        let mut did_scan = false;
        let mut batch = if fast_caught_up {
            Vec::new()
        } else {
            let log = shared
                .log
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            let visible = shared.head.load(Ordering::Relaxed).min(log.head().0);
            if shared.selective_tail_wake.load(Ordering::Relaxed) {
                let _ = tail_sync_selective_before_read(
                    &parker,
                    log.base().0,
                    visible,
                    &mut cursor,
                    &mut told,
                );
            }
            let before = cursor;
            let (g, step) = tail_fetch_chunk_locked(
                shared,
                &log,
                &parker,
                &mut cursor,
                visible,
                &filter,
                &mut told,
                chunk,
                asks.broker_times,
                &mut batch_bts,
            );
            drop(log);
            gap = g;
            match step {
                crate::store::TailStep::Chunk {
                    records,
                    scanned_to: st,
                } => {
                    scanned_to = st;
                    did_scan = !records.is_empty() || st > before;
                    records
                }
                crate::store::TailStep::Unreadable(bad_off) => {
                    if let Some(g) = gap.take() {
                        if let Some(failure) =
                            stream_failure(shared, peer, &mut cap_check, &mut until)
                        {
                            return end_stream_failure(stream, &mut out, failure);
                        }
                        write_gap(stream, g)?;
                    }
                    return end_unreadable_cold_record(stream, &mut out, bad_off);
                }
            }
        };
        if let Some(g) = gap.take() {
            if let Some(failure) = stream_failure(shared, peer, &mut cap_check, &mut until) {
                return end_stream_failure(stream, &mut out, failure);
            }
            write_gap(stream, g)?;
            wrote_at = Instant::now();
        }
        if !did_scan {
            if let Some(failure) = stream_failure(shared, peer, &mut cap_check, &mut until) {
                return end_stream_failure(stream, &mut out, failure);
            }
            if owes_burst_mark
                || idle_marks
                    && (!said_caught_up
                        || wrote_at.elapsed() >= idle_mark
                        || (shared.durable_marks
                            && marked_durable < cursor
                            && shared.durable.load(Ordering::Relaxed) > marked_durable))
            {
                let head = shared.head.load(Ordering::Relaxed);
                marked_durable = durable_for(shared, head);
                write_mark(stream, cursor, head, marked_durable)?;
                said_caught_up = true;
                owes_burst_mark = false;
                wrote_at = Instant::now();
            }
            #[cfg(test)]
            tail_pause_at(&mut pause, PauseAt::Park, cursor);
            let park = match until {
                u64::MAX => liveness_poll,
                t => liveness_poll.min(Duration::from_millis(t.saturating_sub(now_unix_ms()))),
            };
            let before = cursor;
            let (g, step) = tail_park_and_fetch_chunk(
                shared,
                &parker,
                &mut cursor,
                &filter,
                &mut told,
                chunk,
                asks,
                peer,
                cap_check.seen_epoch,
                until,
                marked_durable,
                park,
                &mut batch_bts,
            );
            gap = g;
            if let Some(g) = gap.take() {
                if let Some(failure) = stream_failure(shared, peer, &mut cap_check, &mut until) {
                    return end_stream_failure(stream, &mut out, failure);
                }
                write_gap(stream, g)?;
                wrote_at = Instant::now();
            }
            match step {
                crate::store::TailStep::Chunk {
                    records,
                    scanned_to: st,
                } => {
                    batch = records;
                    scanned_to = st;
                    let woke_scan = !batch.is_empty() || st > before;
                    if !woke_scan {
                        let head = shared.head.load(Ordering::Relaxed);
                        if !shared.running.load(Ordering::Relaxed) && head <= cursor {
                            return Ok(());
                        }
                        if let Some(failure) =
                            stream_failure(shared, peer, &mut cap_check, &mut until)
                        {
                            return end_stream_failure(stream, &mut out, failure);
                        }
                        if head <= cursor {
                            probed = Instant::now();
                            if probe_peer(shared, stream) {
                                return Ok(());
                            }
                        }
                        continue;
                    }
                }
                crate::store::TailStep::Unreadable(bad_off) => {
                    return end_unreadable_cold_record(stream, &mut out, bad_off);
                }
            }
        }
        let Some(wrote) = tail_deliver_batch(
            shared,
            stream,
            &mut out,
            batch,
            scanned_to,
            &batch_bts,
            &mut cursor,
            &filter,
            asks,
            peer,
            &mut cap_check,
            &mut until,
        )?
        else {
            return Ok(());
        };
        #[cfg(test)]
        tail_pause_at(&mut pause, PauseAt::FirstChunk, cursor);
        if wrote {
            wrote_at = Instant::now();
            owes_burst_mark = asks.burst_marks;
        } else if idle_marks && wrote_at.elapsed() >= idle_mark {
            if let Some(failure) = stream_failure(shared, peer, &mut cap_check, &mut until) {
                return end_stream_failure(stream, &mut out, failure);
            }
            let head = shared.head.load(Ordering::Relaxed);
            marked_durable = durable_for(shared, head);
            write_mark(stream, cursor, head, marked_durable)?;
            wrote_at = Instant::now();
        }
        if !wrote && probed.elapsed() >= liveness_poll {
            probed = Instant::now();
            if probe_peer(shared, stream) {
                return Ok(());
            }
        }
    }
}

/// Tell a subscriber where its tail stands — resume from `next`, `head` is the visible
/// head, `durable` the durable head — with nothing to deliver: the catch-up, idle and
/// durable marks (see [`IDLE_MARK`]).
fn write_mark<S: Write>(stream: &mut S, next: u64, head: u64, durable: u64) -> io::Result<()> {
    write_frame(
        stream,
        &encode_response(&mark(next, head, durable, String::new())),
    )
}

/// The durable head a `Mark` read with visible head `head` reports: the log's durable
/// head, never above the visible one (in the Replicated tier the quorum watermark can lag
/// what the leader flushed; a reader can ask only about records it can see).
fn durable_for(shared: &Shared, head: u64) -> u64 {
    shared.durable.load(Ordering::Relaxed).min(head)
}

/// A `Mark` as this broker sends every one: with the durable head, so a reader on any
/// host can tell which of the records it was shown are on stable media (`Mark.durable`).
fn mark(next: u64, head: u64, durable: u64, resume: String) -> Response {
    Response::Mark {
        next,
        head,
        resume,
        durable: Some(durable),
        oldest: None,
    }
}

/// A `Mark` at the visible head now (`next == head`): what acknowledges an `Attach`, a
/// `Will`, a `Keepalive` or `IdleMarks`.
fn mark_at_head(shared: &Shared) -> Response {
    let head = shared.head.load(Ordering::Relaxed);
    mark(head, head, durable_for(shared, head), String::new())
}

/// Bytes of framed output a streaming verb gathers before it writes: one socket write
/// (and, sealed, one AEAD record per 64 KiB) per this much, not one per record.
const EGRESS_CHUNK: usize = 64 * 1024;

/// Gather `rec` as a framed `Delivery` in `out`, writing `out` to `stream` once it
/// holds [`EGRESS_CHUNK`] bytes. Used by `ForkSubscribe` where the replacement record
/// at `fork_offset` is counterfactual and must not populate [`Shared::delivery_crc_cache`].
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

fn queue_delivery_maybe_stamped<S: Write>(
    shared: &Shared,
    stream: &mut S,
    out: &mut Vec<u8>,
    rec: &BrokerRecord,
    asks: TailAsks,
    bt_ms: Option<u64>,
) -> io::Result<()> {
    if asks.broker_times || asks.origin_stamps {
        let origin = asks
            .origin_stamps
            .then_some((rec.producer_id, rec.producer_seq));
        append_delivery_frame_stamped(out, rec.seq.0, &rec.subject, &rec.body, bt_ms, origin)?;
        if out.len() >= EGRESS_CHUNK {
            flush_egress(stream, out)?;
        }
        Ok(())
    } else {
        queue_delivery_cached(shared, stream, out, rec)
    }
}

const fn crc_cache_slot(
    cache: &[Mutex<Option<CachedDeliveryCrc>>; 4096],
    offset: u64,
) -> &Mutex<Option<CachedDeliveryCrc>> {
    &cache[(offset as usize) & 4095]
}

/// Gather `rec` as a framed `Delivery` in `out` using [`Shared::delivery_crc_cache`] so
/// repeat reads can reuse the payload CRC-32/IEEE, writing `out`
/// to `stream` once it holds [`EGRESS_CHUNK`] bytes. The caller ends its batch with
/// [`flush_egress`].
fn queue_delivery_cached<S: Write>(
    shared: &Shared,
    stream: &mut S,
    out: &mut Vec<u8>,
    rec: &BrokerRecord,
) -> io::Result<()> {
    let slot = crc_cache_slot(shared.delivery_crc_cache.as_ref(), rec.seq.0);
    let cached = {
        let held = slot
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        *held
    };
    let crc = match cached {
        Some(hit) if hit.offset == rec.seq.0 => hit.crc,
        _ => {
            // Hash outside the slot lock. Concurrent misses may duplicate work, never mix keys/CRCs.
            let crc = compute_delivery_crc(rec.seq.0, &rec.subject, &rec.body);
            *slot
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner) = Some(CachedDeliveryCrc {
                offset: rec.seq.0,
                crc,
            });
            crc
        }
    };
    append_delivery_frame_with_crc(out, rec.seq.0, &rec.subject, &rec.body, Some(crc))?;
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

/// [`peer_gone`], counted in [`BrokerStats::peer_probes`].
fn probe_peer(shared: &Shared, stream: &mut Conn) -> bool {
    shared.peer_probes.fetch_add(1, Ordering::Relaxed);
    peer_gone(stream)
}

/// Whether the subscriber's peer has closed its end. After SUBSCRIBE the client
/// only reads, so a `read` returns EOF (`Ok(0)`) iff the peer closed; a hard
/// error (reset/pipe) is also gone; `WouldBlock`/`TimedOut` means still connected.
/// (`UnixStream::peek` would avoid consuming, but it is unstable on this toolchain;
/// any unexpected post-subscribe byte is simply ignored.)
///
/// THE READ DOES NOT BLOCK. It used to wait out the socket's read timeout,
/// [`PEER_PROBE_TIMEOUT`] (1 ms asked, 1.13 ms measured), and the tail cannot be
/// woken inside a socket read: a commit that landed meanwhile found nobody waiting on
/// the `Condvar`, and its record reached the subscriber only once the probe ended. On
/// the Relaxed tier a matching record 0.3 ms behind a batch some tail did not match
/// took p50 0.80-0.84 ms to arrive against 0.07 ms alone (cost study B3). Strict hid
/// it — the next batch's F_FULLFSYNC (3 ms or more) always outlasted the probe — and
/// the Ordered tier's 0.13-0.6 ms flush would not. Now the socket is switched to
/// non-blocking for this one read and back, so the probe answers at once.
///
/// Why a switch and not a flag on the read: std has no per-call `MSG_DONTWAIT`, and
/// the crate forbids `unsafe`. The switch is safe because the tail is the only thread
/// using the socket from SUBSCRIBE on (the pipeline's ack-writer was finished first;
/// the connection registry's handle only ever shuts the socket down), and the mode is
/// restored before the tail writes again. If the switch is refused the read falls back
/// to the read timeout `tail_loop` arms, still bounded. If the mode cannot be
/// restored the peer is reported gone: a delivery write in non-blocking mode would
/// fail on the first full socket buffer, mid-frame, and ending the subscription here —
/// the client resumes from its cursor — is the honest form of that failure.
fn peer_gone(stream: &mut Conn) -> bool {
    let mut probe = [0u8; 1];
    let switched = stream.set_nonblocking(true).is_ok();
    let gone = match stream.read(&mut probe) {
        Ok(0) => true,
        Ok(_) => false,
        Err(e) => !matches!(
            e.kind(),
            io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut
        ),
    };
    if switched && stream.set_nonblocking(false).is_err() {
        return true;
    }
    gone
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(all(unix, feature = "stream"))]
    #[test]
    fn shutdown_flushes_and_closes_a_stream_only_broker_without_dropping_it() {
        for tier in [Durability::Ordered { horizon: None }, Durability::Relaxed] {
            let root = crate::test_scratch::Scratch::new("stream-shutdown");
            let path = root.path().join("log");
            let broker = Broker::open_with(&path, tier).unwrap();
            let (ours, theirs) = UnixStream::pair().unwrap();
            let serving = broker.serve_stream(Arc::new(theirs), [7; 32]).unwrap();
            let link: Arc<dyn crate::stream_link::StreamLink> = Arc::new(ours);
            link.set_read_timeout(Some(Duration::from_secs(60)))
                .unwrap();
            let (mut client, _closer) = crate::connect_stream(link);
            client.publish(7, 1, "/shutdown", b"kept").unwrap();
            assert_eq!(
                BrokerLog::check_open(&path, None).unwrap_err().kind(),
                io::ErrorKind::AlreadyExists
            );
            broker.shutdown();
            let _ended =
                within_a_minute("shutdown ends the adopted stream", move || serving.join())
                    .unwrap();
            assert_eq!(
                broker.durable_head(),
                broker.head(),
                "shutdown covers every acknowledged record"
            );
            assert!(
                matches!(crate::logid::read(&crate::storage::Dir::Os(path.clone())).unwrap(),
                crate::logid::Prior::Recorded(s) if s.state == crate::logid::State::Closed)
            );
            let reopened = Broker::open_with(&path, Durability::Strict).unwrap();
            assert_eq!(reopened.head(), 1);
            broker.shutdown();
        }
    }

    #[cfg(feature = "cap")]
    #[test]
    fn a_marked_retire_needs_replication_authority_but_advances_no_group() {
        let secret = b"captured replication authority";
        let ident = crate::LogIdentity {
            id: [7; 16],
            generation: 3,
        };
        let record = BrokerRecord::marked_retire(Offset(7), 42, "/t/session/ev");
        let request = crate::proto::decode_request(&encode_replica_record(&record, None, &ident))
            .expect("the actual replication encoder and decoder agree on the marker");
        assert!(matches!(
            &request,
            Request::Replicate {
                subject,
                producer_seq: crate::brecord::RETIRE_PRODUCER_SEQ,
                commit: Some((group, 0)),
                ..
            } if subject == RETIRE_SUBJECT && group == crate::proto::REPLICATE_RETIRE_GROUP
        ));
        let mint = |grant| astream_cap::mint(secret, grant).unwrap();
        let marker_cap = mint("rw:/a/retire");
        assert_eq!(
            cap_authorized_until(secret, &[marker_cap], &request, 10),
            Some(u64::MAX),
            "a valid marker advances no consumer group"
        );
        for cap in [
            mint("ro:/a/retire"),
            mint("rw:/elsewhere/>"),
            mint("rw,p=n-peer:/a/retire"),
            mint("rw,exp=10:/a/retire"),
        ] {
            assert_eq!(cap_authorized_until(secret, &[cap], &request, 10), None);
        }
        assert_eq!(cap_authorized_until(secret, &[], &request, 10), None);
        let broad = mint("rw:/>");
        let malformed = |subject: &str, producer_seq, upto| Request::Replicate {
            seq: 7,
            producer_id: 42,
            producer_seq,
            subject: subject.into(),
            body: b"/t/session/ev".to_vec(),
            commit: Some((crate::proto::REPLICATE_RETIRE_GROUP.into(), upto)),
            leader: Some(ident),
        };
        for bad in [
            malformed("/t/not-the-marker", crate::brecord::RETIRE_PRODUCER_SEQ, 0),
            malformed(RETIRE_SUBJECT, 9, 0),
            malformed(RETIRE_SUBJECT, crate::brecord::RETIRE_PRODUCER_SEQ, 1),
        ] {
            assert_eq!(
                cap_authorized_until(secret, std::slice::from_ref(&broad), &bad, 10),
                None,
                "sentinel text alone must not waive a real group grant"
            );
            assert!(crate::proto::decode_request(&crate::proto::encode_request(&bad)).is_none());
        }
        let commit = Request::Replicate {
            seq: 8,
            producer_id: 42,
            producer_seq: 2,
            subject: "/t/output".into(),
            body: b"result".to_vec(),
            commit: Some(("/g/consumer".into(), 5)),
            leader: Some(ident),
        };
        let commit = crate::proto::decode_request(&crate::proto::encode_request(&commit))
            .expect("an ordinary replicated group commit round-trips");
        let output = mint("rw:/t/>");
        let group = mint("rw:/g/consumer");
        assert_eq!(
            cap_authorized_until(secret, std::slice::from_ref(&output), &commit, 10),
            None,
            "a real commit still needs its consumer group's grant"
        );
        assert_eq!(
            cap_authorized_until(secret, std::slice::from_ref(&group), &commit, 10),
            None,
            "the group grant does not grant the replicated output"
        );
        assert_eq!(
            cap_authorized_until(secret, &[output, group], &commit, 10),
            Some(u64::MAX)
        );
    }

    /// A follower link at confirmed prefix `upto`; `live` gives it a connected socket
    /// (a loopback pair), otherwise it is down.
    fn link(upto: u64, fenced: Option<&str>, live: bool) -> FollowerLink {
        let stream = live.then(|| {
            let l = TcpListener::bind("127.0.0.1:0").unwrap();
            TcpStream::connect(l.local_addr().unwrap()).unwrap()
        });
        FollowerLink {
            leader: crate::LogIdentity {
                id: [0; 16],
                generation: 0,
            },
            addr: "127.0.0.1:0".to_string(),
            transport: LinkTransport::Plain,
            stream: stream.map(FollowerStream::Plain),
            upto,
            fenced: fenced.map(str::to_string),
            fresh: false,
            timeout_failures: 0,
            next_dial_at: None,
            #[cfg(feature = "cap")]
            cap: None,
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
            b.shared.log_head.store(l.head().0, Ordering::Relaxed);
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

    #[cfg(feature = "cap")]
    #[test]
    fn stream_checks_refresh_epochs_and_tighten_the_grants_deadline() {
        const SECRET: &[u8] = b"captured-stream-secret";
        let a = astream_cap::mint(SECRET, "ro,p=s-a,exp=1010:/a/>").unwrap();
        let b = astream_cap::mint(SECRET, "ro,p=s-b,exp=1100:/a/>").unwrap();
        let request = || Request::Subscribe {
            from_offset: 0,
            filter: "/a/>".to_string(),
        };
        let mut check = StreamCapCheck {
            keyring: vec![a.clone(), b.clone()],
            req: Some(request()),
            seen_epoch: None,
        };
        let mut until = 1100;
        assert_eq!(check.validate(0, 1000, &mut until, Some(SECRET)), None);
        assert_eq!(check.seen_epoch, Some(0));
        assert_eq!(until, 1100);

        let mut revoked = RevocationSet::new();
        assert!(revoked.insert("s-b".to_string()));
        prune_capability_keyring(&revoked, &mut check.keyring);
        assert_eq!(check.validate(1, 1005, &mut until, Some(SECRET)), None);
        assert_eq!(until, 1010);
        assert_eq!(
            check.validate(1, 1020, &mut until, Some(SECRET)),
            Some(StreamFailure::Expired {
                until: 1010,
                now: 1020
            })
        );

        // The first validation cannot consume an epoch sampled after revocation
        // while trusting the stale keyring captured before it.
        let mut first = StreamCapCheck {
            keyring: vec![b],
            req: Some(request()),
            seen_epoch: None,
        };
        prune_capability_keyring(&revoked, &mut first.keyring);
        let mut until = 1100;
        assert_eq!(
            first.validate(1, 1005, &mut until, Some(SECRET)),
            Some(StreamFailure::Revoked(
                "unauthorized: capability principal has been revoked"
            ))
        );

        // If the remaining covering grant has already expired, time-zero parsing
        // only selects the typed expiry explanation; it does not authorize output.
        let mut expired = StreamCapCheck {
            keyring: vec![a.clone()],
            req: Some(request()),
            seen_epoch: None,
        };
        let mut until = 1100;
        assert_eq!(
            expired.validate(1, 1020, &mut until, Some(SECRET)),
            Some(StreamFailure::Expired {
                until: 1010,
                now: 1020
            })
        );
        let mut shorter = StreamCapCheck {
            keyring: vec![a],
            req: Some(request()),
            seen_epoch: None,
        };
        let mut until = 1008;
        assert_eq!(shorter.validate(0, 1005, &mut until, Some(SECRET)), None);
        assert_eq!(
            until, 1008,
            "reauthorization never extends the original admission"
        );

        // No guard: an unrelated revocation must still advance the accepted epoch
        // before the caller uses it in the park predicate.
        let mut unguarded = StreamCapCheck {
            keyring: Vec::new(),
            req: None,
            seen_epoch: None,
        };
        let mut until = u64::MAX;
        assert_eq!(unguarded.validate(1, 0, &mut until, None), None);
        assert_eq!(unguarded.seen_epoch, Some(1));
        assert_eq!(unguarded.validate(2, 0, &mut until, None), None);
        assert_eq!(unguarded.seen_epoch, Some(2));
    }

    #[test]
    fn revocation_sources_preserve_manual_entries_and_explicit_unrevokes() {
        let mut principals = RevocationSet::new();
        let manual = "s-overlap".to_string();
        let file_only = "s-file".to_string();
        assert!(principals.is_empty());

        // A manual revoke before a matching file entry survives file removal.
        assert!(principals.insert(manual.clone()));
        principals.replace_file(HashSet::from([manual.clone(), file_only.clone()]));
        assert!(principals.contains(&file_only));
        principals.replace_file(HashSet::new());
        assert!(principals.contains(&manual));
        assert!(!principals.contains(&file_only));
        assert!(principals.remove(&manual));
        assert!(!principals.remove(&manual));
        assert!(principals.is_empty());

        // File first: recording a manual source still returns false while effective,
        // yet that source must remain after a later empty file replacement.
        principals.replace_file(HashSet::from([manual.clone()]));
        assert!(!principals.insert(manual.clone()));
        principals.replace_file(HashSet::new());
        assert!(principals.contains(&manual));

        // Explicit un-revoke clears both sources. A later file load can reassert it.
        principals.replace_file(HashSet::from([manual.clone()]));
        assert!(principals.remove(&manual));
        assert!(!principals.contains(&manual));
        principals.replace_file(HashSet::from([manual.clone()]));
        assert!(principals.contains(&manual));
        principals.replace_file(HashSet::new());
        assert!(principals.is_empty());

        let pk = [0x11; 32];
        let derived = identity_principal(&pk);
        let mut identities = RevocationSet::new();
        assert_eq!(
            insert_identity_revocation(&mut identities, &mut principals, pk),
            (true, true)
        );
        identities.replace_file(HashSet::from([pk]));
        principals.replace_file(HashSet::from([derived.clone()]));
        identities.replace_file(HashSet::new());
        principals.replace_file(HashSet::new());
        assert!(identities.contains(&pk));
        assert!(principals.contains(&derived));

        // An identity already present can still restrict its cleared principal.
        // The first answer stays false; the separate change answer must advance
        // the caller's epoch and wake tails.
        assert!(principals.remove(&derived));
        assert_eq!(
            insert_identity_revocation(&mut identities, &mut principals, pk),
            (false, true)
        );
        assert_eq!(
            insert_identity_revocation(&mut identities, &mut principals, pk),
            (false, false)
        );

        assert!(identities.remove(&pk));
        assert!(principals.remove(&derived));
        identities.replace_file(HashSet::from([pk]));
        principals.replace_file(HashSet::from([derived.clone()]));
        assert_eq!(
            insert_identity_revocation(&mut identities, &mut principals, pk),
            (false, false)
        );
        identities.replace_file(HashSet::new());
        principals.replace_file(HashSet::new());
        assert!(identities.contains(&pk));
        assert!(principals.contains(&derived));
        assert!(identities.remove(&pk));
        assert!(principals.remove(&derived));
        assert!(identities.is_empty() && principals.is_empty());
    }

    #[test]
    fn monotone_clock_and_revocation_file_enforcement() {
        let (_tmp, b, mut h, _sock) = filled("revfile", 1);
        let t1 = b.now_ms();
        let t2 = b.now_ms();
        assert!(t1 > 0 && t2 >= t1, "broker clock must be non-decreasing");

        let rev_path =
            std::env::temp_dir().join(format!("asb_revfile_{}_{}.txt", std::process::id(), t1));
        let pk_hex = "11".repeat(32);
        std::fs::write(
            &rev_path,
            format!("# comment line\n{pk_hex}\ns-revokedsession\n"),
        )
        .unwrap();
        let count = b.load_revocation_file(&rev_path).unwrap();
        let _ = std::fs::remove_file(&rev_path);
        assert_eq!(count, 2);
        let pk = [0x11u8; 32];
        assert!(b.is_identity_revoked(&pk));
        assert!(b.is_principal_revoked(&crate::identity_principal(&pk)));
        assert!(b.is_principal_revoked("s-revokedsession"));
        assert!(b.unrevoke_principal("s-revokedsession"));
        assert!(!b.is_principal_revoked("s-revokedsession"));
        h.shutdown();
    }

    #[cfg(unix)]
    #[test]
    fn credit_windowed_pipelined_publish_and_replicated_watermark_integration() {
        let pid = std::process::id();
        let f_log = format!("/tmp/asb_unit_rep_f_{pid}.log");
        let f_rep = format!("{f_log}.replica");
        let l_log = format!("/tmp/asb_unit_rep_l_{pid}.log");
        let l_sock = format!("/tmp/asb_unit_rep_l_{pid}.sock");
        let _ = std::fs::remove_file(&f_log);
        let _ = std::fs::remove_file(&f_rep);
        let _ = std::fs::remove_file(&l_log);
        let _ = std::fs::remove_file(&l_sock);
        let _tmp = Cleanup(vec![f_log.clone(), f_rep, l_log.clone(), l_sock.clone()]);

        let follower = Broker::open_replica_with(&f_log, Durability::Relaxed).unwrap();
        let mut f_handle = follower.serve_tcp("127.0.0.1:0").unwrap();
        let f_addr = f_handle.tcp_addr().unwrap().to_string();

        let leader = Broker::open_replicated(&l_log, &[f_addr], 1).unwrap();
        let mut l_handle = leader.serve(&l_sock).unwrap();

        let mut client = crate::Client::connect(&l_sock).unwrap();
        let payloads: Vec<Vec<u8>> = (0..128)
            .map(|i| format!("msg-{i:04}").into_bytes())
            .collect();
        let refs: Vec<&[u8]> = payloads.iter().map(Vec::as_slice).collect();
        let acks = client.publish_pipelined(77, "/t/pipe", &refs, 32).unwrap();
        assert_eq!(acks.len(), 128);
        for (i, &(off, deduped)) in acks.iter().enumerate() {
            assert_eq!(off, i as u64);
            assert!(!deduped);
        }
        assert_eq!(leader.head(), 128);
        assert_eq!(leader.visible_head(), 128);
        assert_eq!(
            leader
                .shared
                .log
                .lock()
                .unwrap()
                .committed_watermark_offset(),
            Offset(128)
        );
        assert_eq!(follower.head(), 128);

        l_handle.shutdown();
        f_handle.shutdown();
    }

    /// A BATCH THAT ROLLED BACK DECIDED NOTHING FOR GOOD. The distinct-subject bound
    /// counts the batch's own new subjects, so a record refused at the bound behind
    /// one that took the producer's last slot was judged against a record that, once
    /// the commit fails, never landed — and resent, it lands. Its refusal is therefore
    /// not known to be permanent (`ERR_REFUSED`), though it keeps its own message.
    #[cfg(unix)]
    #[test]
    fn a_refusal_inside_a_batch_that_rolled_back_is_not_permanent() {
        use crate::store::MAX_SUBJECTS_PER_PRODUCER;
        let log = format!("/tmp/asb_unit_rollback_{}.log", std::process::id());
        let _ = std::fs::remove_file(&log);
        let _tmp = Cleanup(vec![log.clone()]);
        let b = Broker::open(&log).unwrap();
        // Producer 1 one slot short of its bound, in one batch (one fsync).
        {
            let mut l = b.shared.log.lock().unwrap();
            for seq in 0..MAX_SUBJECTS_PER_PRODUCER as u64 - 1 {
                l.stage_publish(1, seq, format!("/t/{seq}"), vec![])
                    .unwrap();
            }
            l.commit_batch().unwrap();
            b.shared.head.store(l.head().0, Ordering::Relaxed);
            b.shared.log_head.store(l.head().0, Ordering::Relaxed);
        }
        let publish = |producer_seq: u64, subject: &str| {
            let (ack, rx) = mpsc::channel();
            let kind = WriteKind::Publish {
                producer_id: 1,
                producer_seq,
                subject: subject.to_string(),
                body: vec![],
            };
            (
                WriteOp {
                    kind,
                    ack: ack.into(),
                    conn_id: None,
                },
                rx,
            )
        };

        // `/t/last` takes the last slot; `/t/behind` is refused at the bound for it;
        // then the fsync fails and the batch rolls back.
        b.inject_faults(InjectedFaults {
            write: false,
            sync: true,
            truncate: false,
        });
        let (last, last_ack) = publish(1 << 20, "/t/last");
        let (behind, behind_ack) = publish((1 << 20) + 1, "/t/behind");
        process_batch(&b.shared, vec![last, behind]);
        let (code, _) = last_ack.recv().unwrap().unwrap_err();
        assert_eq!(code, ERR_REFUSED, "the record the fsync took down");
        let (code, msg) = behind_ack.recv().unwrap().unwrap_err();
        assert!(msg.contains("distinct subjects"), "its own words: {msg}");
        assert_eq!(
            code, ERR_REFUSED,
            "judged against a rolled-back batch: {msg}"
        );

        // Why: the slot it was refused for is free again, so the same record lands.
        b.inject_faults(InjectedFaults::default());
        let (again, again_ack) = publish((1 << 20) + 1, "/t/behind");
        process_batch(&b.shared, vec![again]);
        assert!(again_ack.recv().unwrap().is_ok(), "the resend landed");

        // The control: the same refusal in a batch that COMMITS keeps the code that
        // names it — the producer is now at its bound for real.
        let (over, over_ack) = publish((1 << 20) + 2, "/t/over");
        process_batch(&b.shared, vec![over]);
        let (code, msg) = over_ack.recv().unwrap().unwrap_err();
        assert_eq!(code, ERR_SUBJECT_BOUND, "a committed batch's bound: {msg}");
    }
    /// Cached deliveries keep the full offset, including bit31 and all high bits.
    #[test]
    fn delivery_crc_cache_keeps_the_entire_offset() {
        let root = crate::test_scratch::Scratch::new("crc-key");
        // Unserved broker: owned log and writer only, no listener or daemon process.
        let broker = Broker::open_with(root.path().join("log"), Durability::Relaxed).unwrap();
        let mut stream = Vec::<u8>::new();
        let record = |offset, body: &[u8]| BrokerRecord {
            seq: Offset(offset),
            producer_id: 1,
            producer_seq: 1,
            subject: "/t/cache".into(),
            body: body.to_vec(),
            commit: None,
        };
        let (bit31, high32) = {
            let mut cached = |rec: &BrokerRecord| {
                let mut out = Vec::new();
                queue_delivery_cached(&broker.shared, &mut stream, &mut out, rec).unwrap();
                let expected = astream_wire::Frame::new(encode_response(&Response::Delivery {
                    offset: rec.seq.0,
                    subject: rec.subject.clone(),
                    body: rec.body.clone(),
                }))
                .encode()
                .unwrap();
                out == expected && astream_wire::Frame::decode(&out).is_ok_and(|d| d.is_some())
            };
            let zero = record(0, b"zero");
            let ordinary = record(17, b"ordinary");
            assert!(cached(&zero), "empty cache and offset zero");
            assert!(cached(&zero), "offset zero cache hit");
            assert!(cached(&ordinary), "different-slot cache miss");
            assert!(cached(&ordinary), "ordinary cache hit");
            let bit31 = cached(&record(17 + (1u64 << 31), b"different bit31 record"));
            let high32 = cached(&record(17 + (1u64 << 32), b"different high32 record"));
            (bit31, high32)
        };
        // Counterfactual fork deliveries keep their own CRC and never seed the live cache.
        let live = record(9, b"live");
        let fork = record(9, b"counterfactual");
        let mut fork_out = Vec::new();
        queue_delivery(&mut stream, &mut fork_out, &fork).unwrap();
        let mut live_out = Vec::new();
        queue_delivery_cached(&broker.shared, &mut stream, &mut live_out, &live).unwrap();
        let live_expected = astream_wire::Frame::new(encode_response(&Response::Delivery {
            offset: live.seq.0,
            subject: live.subject.clone(),
            body: live.body.clone(),
        }))
        .encode()
        .unwrap();
        assert_eq!(
            (bit31, high32, live_out == live_expected),
            (true, true, true)
        );
    }

    /// Run `f` on its own thread and wait for it — a one-minute HANG DETECTOR, never a
    /// latency budget: a shutdown that wedges fails here instead of hanging the suite.
    fn within_a_minute<T: Send + 'static>(what: &str, f: impl FnOnce() -> T + Send + 'static) -> T {
        let (tx, rx) = mpsc::channel();
        thread::spawn(move || {
            let _ = tx.send(f());
        });
        rx.recv_timeout(Duration::from_secs(60))
            .unwrap_or_else(|_| panic!("{what} did not return within a minute"))
    }

    /// A STRANGER listener that takes every connection, as a live server does: accept
    /// and read each until one SENDS a byte — the test's sentinel, dialed once the
    /// shutdown under test has returned — and report how many came before it. A
    /// wakeup dial sends nothing, so its read ends at EOF when shutdown drops it.
    /// Returns the receiver of that count.
    fn stranger<S: Read>(
        mut accept: impl FnMut() -> io::Result<S> + Send + 'static,
    ) -> Receiver<usize> {
        let (tx, rx) = mpsc::channel();
        thread::spawn(move || {
            let mut dials = 0;
            loop {
                let mut conn = accept().unwrap();
                if conn.read(&mut [0u8; 1]).unwrap_or(0) == 1 {
                    break;
                }
                dials += 1;
            }
            let _ = tx.send(dials);
        });
        rx
    }

    /// The stranger's count, under the hang detector, once `sentinel` sent its byte.
    fn stranger_took(took: &Receiver<usize>, mut sentinel: impl Write) -> usize {
        sentinel.write_all(b"!").unwrap();
        took.recv_timeout(Duration::from_secs(60))
            .expect("the stranger never saw the sentinel")
    }

    /// A wakeup dial that CONNECTS is no proof it reached THIS acceptor. On macOS/BSD
    /// a socket bound to `127.0.0.1:P` beside a broker's `0.0.0.0:P` — a legal bind:
    /// std, OpenSSH `-L` and most servers set `SO_REUSEADDR` — takes every loopback
    /// connection to P, and loopback is what shutdown dials for a wildcard bind
    /// (`asb serve 0.0.0.0:<port> --tcp --allow-remote`). Here the handle's dial
    /// address is pointed at such a stranger directly: the same end state, without
    /// opening a wildcard listener on the test host. Shutdown redialed the stranger
    /// forever when any connected dial reset its give-up count; it must abandon its own
    /// acceptor after [`ACCEPT_WAKE_ATTEMPTS`] rounds its acceptor never answered.
    #[test]
    fn a_tcp_wake_dial_another_listener_answers_is_not_redialed_forever() {
        let root = crate::test_scratch::Scratch::new("tcp-stranger");
        let b = Broker::open_with(root.path().join("log"), Durability::Relaxed).unwrap();
        let mut h = b.serve_tcp("127.0.0.1:0").unwrap();
        assert!(h.blocks_in_accept());
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let theirs = listener.local_addr().unwrap();
        let took = stranger(move || listener.accept().map(|(s, _)| s));
        let own = match &mut h.endpoint {
            Endpoint::Tcp { dial, .. } => std::mem::replace(dial, theirs),
            #[cfg(unix)]
            Endpoint::Unix { .. } => unreachable!("serve_tcp made a TCP endpoint"),
        };
        within_a_minute("shutdown with a stranger answering its dials", move || {
            h.shutdown()
        });
        let s = b.stats();
        assert_eq!(
            (s.acceptors_abandoned, s.accepted),
            (1, 0),
            "(abandoned, accepted): the acceptor was never reached, and shutdown gave up"
        );
        // The stranger took the dials: at least one, at most the bound. (A dial whose
        // handshake the stranger's side finished only after the sentinel's could only
        // lower the count, so neither end of the range can fail by load.)
        let took = stranger_took(&took, TcpStream::connect(theirs).unwrap());
        assert!(
            (1..=ACCEPT_WAKE_ATTEMPTS as usize).contains(&took),
            "the stranger took {took} wakeup dials"
        );
        // The abandoned acceptor is still parked on its own address; a connection
        // that reaches it finds the cleared flags and lets it leave.
        drop(TcpStream::connect(own).unwrap());
    }

    /// The Unix face of the same rule: a `serve` that bound the path itself (its private
    /// name unusable, [`Broker::bind_unix`]) and over whose path another process renamed
    /// its own listening socket before this one read the path's inode records the OTHER
    /// socket's inode, so its names pass every identity check and its wakeup dials
    /// connect, to the other listener. Built here directly: the listener nameless, the
    /// endpoint naming a stranger's socket and a wake name linked to it. Shutdown must
    /// give up after [`ACCEPT_WAKE_ATTEMPTS`] unanswered rounds, and leave the socket
    /// path alone — no dial through it ever reached this acceptor, so it is the other
    /// listener's — while removing the wake name it made.
    #[cfg(unix)]
    #[test]
    fn a_unix_wake_dial_another_listener_answers_is_not_redialed_forever() {
        static SEQ: AtomicU64 = AtomicU64::new(0);
        let k = SEQ.fetch_add(1, Ordering::Relaxed);
        let pid = std::process::id();
        // Under /tmp: a Darwin TMPDIR can push a socket path past SUN_LEN.
        let ours = format!("/tmp/asb_unit_wk_{pid}_{k}_a.sock");
        let theirs = format!("/tmp/asb_unit_wk_{pid}_{k}_s.sock");
        let (ours_wake, theirs_wake) = (format!("{ours}.wake"), format!("{theirs}.wake"));
        let _tmp = Cleanup(vec![
            ours.clone(),
            ours_wake.clone(),
            theirs.clone(),
            theirs_wake.clone(),
        ]);
        let root = crate::test_scratch::Scratch::new("unix-stranger");
        let b = Broker::open_with(root.path().join("log"), Durability::Relaxed).unwrap();
        let mut h = b.serve(&ours).unwrap();
        assert!(h.blocks_in_accept());
        let listener = UnixListener::bind(&theirs).unwrap();
        let node = node_at(Path::new(&theirs)).unwrap();
        let took = stranger(move || listener.accept().map(|(s, _)| s));
        std::fs::hard_link(&theirs, &theirs_wake).unwrap();
        std::fs::remove_file(&ours).unwrap();
        std::fs::remove_file(&ours_wake).unwrap();
        h.endpoint = Endpoint::Unix {
            path: PathBuf::from(&theirs),
            node: Some(node),
            wake: Some(PathBuf::from(&theirs_wake)),
        };
        within_a_minute("shutdown with a stranger answering its dials", move || {
            h.shutdown()
        });
        let s = b.stats();
        assert_eq!(
            (s.acceptors_abandoned, s.accepted),
            (1, 0),
            "(abandoned, accepted): the acceptor was never reached, and shutdown gave up"
        );
        assert_eq!(
            node_at(Path::new(&theirs)),
            Some(node),
            "the other broker's socket path survives"
        );
        assert_eq!(
            node_at(Path::new(&theirs_wake)),
            None,
            "the wake name this broker made is removed"
        );
        // A Unix connect is queued on the listener before it returns, and the stranger
        // accepts in that order, so the count is exact: one dial a round, every round
        // unanswered.
        let took = stranger_took(&took, UnixStream::connect(&theirs).unwrap());
        assert_eq!(
            took, ACCEPT_WAKE_ATTEMPTS as usize,
            "wakeup dials the stranger took"
        );
    }

    /// Removes each path and every `<path>.*` name beside it when dropped, so a test
    /// leaves nothing behind whether it passes or panics: the names a broker made for
    /// it, and a private one left by a test that failed inside `serve`. Each path is a
    /// test's own.
    #[cfg(unix)]
    struct Leaves(Vec<String>);

    #[cfg(unix)]
    impl Drop for Leaves {
        fn drop(&mut self) {
            for path in &self.0 {
                for name in sibling_names(path) {
                    let _ = std::fs::remove_file(format!("{path}.{name}"));
                }
                let _ = std::fs::remove_file(path);
            }
        }
    }

    /// Two socket paths under /tmp for one test, `<tag>`'s own (a Darwin TMPDIR can push
    /// a socket path past SUN_LEN): the broker's, and the foreign socket's it renames in.
    #[cfg(unix)]
    fn renamed_in_paths(tag: &str) -> (Leaves, String, String) {
        static SEQ: AtomicU64 = AtomicU64::new(0);
        let k = SEQ.fetch_add(1, Ordering::Relaxed);
        let pid = std::process::id();
        let ours = format!("/tmp/asb_unit_{tag}_{pid}_{k}_a.sock");
        let theirs = format!("/tmp/asb_unit_{tag}_{pid}_{k}_s.sock");
        (Leaves(vec![ours.clone(), theirs.clone()]), ours, theirs)
    }

    /// The longest socket path under /tmp a socket address holds, `<tag>`'s own: its
    /// private name and its wake name fit none, so `serve` binds the path itself.
    #[cfg(unix)]
    fn longest_socket_path(tag: &str) -> String {
        static SEQ: AtomicU64 = AtomicU64::new(0);
        let k = SEQ.fetch_add(1, Ordering::Relaxed);
        let mut path = format!("/tmp/asb_unit_{tag}_{}_{k}_", std::process::id());
        while std::os::unix::net::SocketAddr::from_pathname(format!("{path}x")).is_ok() {
            path.push('x');
        }
        assert!(
            private_socket_name(Path::new(&path)).is_none(),
            "{path}: a private name fits"
        );
        path
    }

    /// Serve `b` at `path` with `hooks` armed on this thread, each run once, in order,
    /// at the first [`ServeAt`] it names ([`SERVE_HOOKS`]); every one must have run.
    #[cfg(unix)]
    fn serve_with(
        b: &Broker,
        path: &str,
        hooks: Vec<(ServeAt, ServeHook)>,
    ) -> io::Result<BrokerHandle> {
        SERVE_HOOKS.with(|armed| *armed.borrow_mut() = hooks);
        let served = b.serve(path);
        let left: Vec<ServeAt> =
            SERVE_HOOKS.with(|armed| armed.borrow_mut().drain(..).map(|(at, _)| at).collect());
        assert!(left.is_empty(), "serve never reached {left:?}");
        served
    }

    /// A hook that renames `from` over `to`.
    #[cfg(unix)]
    fn rename(from: &str, to: &str) -> ServeHook {
        let (from, to) = (from.to_string(), to.to_string());
        Box::new(move || std::fs::rename(&from, &to).unwrap())
    }

    /// What else is named `<path>.*` beside `path`: the names a broker made for it.
    #[cfg(unix)]
    fn sibling_names(path: &str) -> Vec<String> {
        let path = Path::new(path);
        let (Some(dir), Some(file)) = (path.parent(), path.file_name()) else {
            return Vec::new();
        };
        let prefix = format!("{}.", file.to_string_lossy());
        let mut names: Vec<String> = std::fs::read_dir(dir)
            .into_iter()
            .flatten()
            .filter_map(|e| e.ok())
            .filter_map(|e| {
                let name = e.file_name().to_string_lossy().into_owned();
                name.strip_prefix(&prefix).map(str::to_string)
            })
            .collect();
        names.sort();
        names
    }

    /// A LIVE socket renamed over the path while `serve` is between its bind and its
    /// path naming its listener — another broker putting its own in place — is never
    /// taken as this broker's: `serve` answers `AddrInUse`, as for a live socket it
    /// finds there first, and leaves that socket at the path and no name of its own.
    #[cfg(unix)]
    #[test]
    fn a_live_socket_renamed_over_the_path_while_serve_binds_is_refused() {
        let (_names, ours, theirs) = renamed_in_paths("rnl");
        let root = crate::test_scratch::Scratch::new("renamed-live");
        let b = Broker::open_with(root.path().join("log"), Durability::Relaxed).unwrap();
        let _foreign = UnixListener::bind(&theirs).unwrap();
        let node = node_at(Path::new(&theirs)).unwrap();
        let err = serve_with(&b, &ours, vec![(ServeAt::Bound, rename(&theirs, &ours))])
            .err()
            .expect("serve took a live socket renamed over its path as its own");
        assert_eq!(err.kind(), io::ErrorKind::AddrInUse, "{err}");
        assert_eq!(
            node_at(Path::new(&ours)),
            Some(node),
            "the live socket stays at the path"
        );
        assert_eq!(sibling_names(&ours), Vec::<String>::new(), "names left");
    }

    /// Linux's full stream backlog reports EAGAIN to a nonblocking attempt; an
    /// interrupted, in-progress or otherwise inconclusive probe is equally no
    /// permission to unlink. Inject the outcomes without waiting on a live queue.
    /// The definitive stale control still removes the captured socket node.
    #[cfg(unix)]
    #[test]
    fn an_inconclusive_nonblocking_probe_never_reclaims_a_socket() {
        let (_names, ours, _) = renamed_in_paths("probe-unknown");
        drop(UnixListener::bind(&ours).unwrap());
        let node = node_at(Path::new(&ours)).unwrap();
        for (kind, why) in [
            (io::ErrorKind::WouldBlock, "Linux full listener backlog"),
            (io::ErrorKind::Interrupted, "interrupted attempt"),
            (io::ErrorKind::PermissionDenied, "permission withheld"),
            (
                io::ErrorKind::Other,
                "in-progress or already-pending connection",
            ),
        ] {
            let mut probes = 0;
            let error = claim_socket_path_with(Path::new(&ours), |_| {
                probes += 1;
                Err(io::Error::new(kind, why))
            })
            .expect_err("inconclusive evidence keeps the socket");
            assert_eq!(error.kind(), io::ErrorKind::AddrInUse, "{why}");
            assert_eq!(probes, 1, "the probe is never retried: {why}");
            assert_eq!(node_at(Path::new(&ours)), Some(node), "{why}");
        }
        assert!(claim_socket_path_with(Path::new(&ours), |_| Ok(())).is_err());
        assert_eq!(
            node_at(Path::new(&ours)),
            Some(node),
            "a live datagram stays"
        );
        claim_socket_path_with(Path::new(&ours), |_| {
            Err(io::ErrorKind::ConnectionRefused.into())
        })
        .unwrap();
        assert_eq!(
            node_at(Path::new(&ours)),
            None,
            "the definitive stale control"
        );
    }

    /// Cleanup of a live private sibling does not dial its stream listener. Such
    /// a dial would queue here and could block forever once a Linux queue is full.
    /// No latency assertion is needed: a queued stream connection is the failure.
    #[cfg(unix)]
    #[test]
    fn a_live_private_sibling_keeps_its_accept_queue_untouched() {
        let (_names, ours, _) = renamed_in_paths("probe-private");
        let private = format!("{ours}.1.0");
        let listener = UnixListener::bind(&private).unwrap();
        listener.set_nonblocking(true).unwrap();
        let node = node_at(Path::new(&private)).unwrap();
        let root = crate::test_scratch::Scratch::new("private-probe");
        let broker = Broker::open_with(root.path().join("log"), Durability::Relaxed).unwrap();
        let mut handle = broker
            .serve(&ours)
            .expect("a live sibling cannot hold up serving");
        assert_eq!(
            node_at(Path::new(&private)),
            Some(node),
            "the live sibling remains"
        );
        assert_eq!(
            listener.accept().unwrap_err().kind(),
            io::ErrorKind::WouldBlock,
            "cleanup must never enqueue a stream connect"
        );
        assert_eq!(handle.names_listener(), Some(true));
        handle.shutdown();
    }

    /// The same window, a STALE socket renamed in (no socket bound to it: what a killed
    /// broker leaves): `serve` removes it, as it removes one it finds there first, and its
    /// own listener takes the path. [`BrokerHandle::names_listener`] says so, and says
    /// when another socket is renamed over the path later.
    #[cfg(unix)]
    #[test]
    fn a_stale_socket_renamed_over_the_path_while_serve_binds_is_replaced() {
        let (_names, ours, theirs) = renamed_in_paths("rns");
        let root = crate::test_scratch::Scratch::new("renamed-stale");
        let b = Broker::open_with(root.path().join("log"), Durability::Relaxed).unwrap();
        drop(UnixListener::bind(&theirs).unwrap());
        let stale = node_at(Path::new(&theirs)).unwrap();
        let mut h = serve_with(&b, &ours, vec![(ServeAt::Bound, rename(&theirs, &ours))]).unwrap();
        assert_ne!(
            node_at(Path::new(&ours)),
            Some(stale),
            "the stale socket is still at the path"
        );
        assert_eq!(h.names_listener(), Some(true));
        assert!(
            UnixStream::connect(&ours).is_ok(),
            "the path reaches nobody"
        );
        assert_eq!(sibling_names(&ours), ["wake"], "names left");
        let _later = UnixListener::bind(&theirs).unwrap();
        std::fs::rename(&theirs, &ours).unwrap();
        assert_eq!(h.names_listener(), Some(false), "another socket's path");
        h.shutdown();
    }

    /// A LIVE socket renamed over the path once `serve` linked its own there, before
    /// `serve` returned: the identity `serve` keeps is its listener's, read under the
    /// private name, so [`BrokerHandle::names_listener`] says the path names another
    /// socket; the wake name, linked from the private name, names its listener, so
    /// shutdown reaches its acceptor through it and leaves the other socket at the path.
    #[cfg(unix)]
    #[test]
    fn a_socket_renamed_over_the_path_once_serve_linked_it_is_not_its_own() {
        let (_names, ours, theirs) = renamed_in_paths("rnk");
        let root = crate::test_scratch::Scratch::new("renamed-linked");
        let b = Broker::open_with(root.path().join("log"), Durability::Relaxed).unwrap();
        let _foreign = UnixListener::bind(&theirs).unwrap();
        let foreign = node_at(Path::new(&theirs)).unwrap();
        let mut h = serve_with(&b, &ours, vec![(ServeAt::Linked, rename(&theirs, &ours))]).unwrap();
        assert_eq!(
            h.names_listener(),
            Some(false),
            "the other socket taken as its own"
        );
        let Endpoint::Unix {
            node: Some(own),
            wake: Some(wake),
            ..
        } = &h.endpoint
        else {
            panic!("no identity, or no wake name");
        };
        assert_ne!(*own, foreign, "the other socket's identity kept");
        assert_eq!(node_at(wake), Some(*own), "a wake name for another socket");
        let wake = wake.clone();
        h.shutdown();
        assert_eq!(
            b.stats().acceptors_abandoned,
            0,
            "shutdown never reached its acceptor"
        );
        assert_eq!(
            node_at(Path::new(&ours)),
            Some(foreign),
            "the other socket lost the path"
        );
        assert_eq!(node_at(&wake), None, "the wake name is left");
    }

    /// A stale socket at the path that another broker replaces with its own LIVE one
    /// while `serve` judges it stale, before `serve` removes it: `serve` removes only the
    /// stale socket it judged, so the live one keeps the path, and `serve` answers
    /// `AddrInUse`, as for a live socket it finds there first.
    #[cfg(unix)]
    #[test]
    fn a_live_socket_put_in_place_of_a_stale_one_as_serve_judges_it_is_kept() {
        let (_names, ours, aside) = renamed_in_paths("rnj");
        let root = crate::test_scratch::Scratch::new("renamed-judged");
        let b = Broker::open_with(root.path().join("log"), Durability::Relaxed).unwrap();
        drop(UnixListener::bind(&ours).unwrap());
        let live = std::rc::Rc::new(std::cell::RefCell::new(None));
        // The stale socket is moved aside rather than unlinked, so no filesystem can give
        // its inode number to the live one.
        let put: ServeHook = {
            let (live, ours) = (std::rc::Rc::clone(&live), ours.clone());
            Box::new(move || {
                std::fs::rename(&ours, &aside).unwrap();
                *live.borrow_mut() = Some(UnixListener::bind(&ours).unwrap());
            })
        };
        let err = serve_with(&b, &ours, vec![(ServeAt::Judged, put)])
            .err()
            .expect("serve displaced a live socket put at its path");
        assert_eq!(err.kind(), io::ErrorKind::AddrInUse, "{err}");
        assert!(live.borrow().is_some());
        assert!(
            UnixStream::connect(&ours).is_ok(),
            "the live socket lost the path"
        );
        assert_eq!(sibling_names(&ours), Vec::<String>::new(), "names left");
    }

    /// A stream connect that fails otherwise than by refusal shows no socket stale: one
    /// to a LIVE datagram socket fails by its type, and `serve` leaves that socket in
    /// place and answers `AddrInUse`.
    #[cfg(unix)]
    #[test]
    fn a_live_datagram_socket_at_the_path_is_not_stale() {
        let (_names, ours, _) = renamed_in_paths("dgl");
        let root = crate::test_scratch::Scratch::new("live-datagram");
        let b = Broker::open_with(root.path().join("log"), Durability::Relaxed).unwrap();
        let _datagram = std::os::unix::net::UnixDatagram::bind(&ours).unwrap();
        let node = node_at(Path::new(&ours)).unwrap();
        let err = b
            .serve(&ours)
            .err()
            .expect("serve replaced a live datagram socket");
        assert_eq!(err.kind(), io::ErrorKind::AddrInUse, "{err}");
        assert_eq!(node_at(Path::new(&ours)), Some(node), "it lost the path");
    }

    /// A LIVE listener whose backlog is full refuses a stream connect as a stale socket
    /// does (on macOS; Linux holds the connect instead), but a datagram connect fails by
    /// its type: `serve` leaves it in place and answers `AddrInUse`.
    #[cfg(target_os = "macos")]
    #[test]
    fn a_listener_whose_backlog_is_full_is_not_stale() {
        let (_names, ours, _) = renamed_in_paths("full");
        let root = crate::test_scratch::Scratch::new("full-backlog");
        let b = Broker::open_with(root.path().join("log"), Durability::Relaxed).unwrap();
        let _full = UnixListener::bind(&ours).unwrap();
        let node = node_at(Path::new(&ours)).unwrap();
        let refused = (0..4096).find_map(|_| UnixStream::connect(&ours).err());
        assert_eq!(
            refused.map(|e| e.kind()),
            Some(io::ErrorKind::ConnectionRefused),
            "the backlog never filled"
        );
        let err = b
            .serve(&ours)
            .err()
            .expect("serve replaced a listener whose backlog is full");
        assert_eq!(err.kind(), io::ErrorKind::AddrInUse, "{err}");
        assert_eq!(node_at(Path::new(&ours)), Some(node), "it lost the path");
    }

    /// The stale private names a broker killed inside `serve` left beside the path,
    /// those with this process's pid and the numbers it takes next among them (its pid
    /// reused), are removed before `serve` binds, so it binds under a private name of
    /// its own, not the path; a live one and a file that is not a socket stay.
    #[cfg(unix)]
    #[test]
    fn a_private_name_a_killed_broker_left_is_removed() {
        let (_names, ours, _) = renamed_in_paths("prv");
        let root = crate::test_scratch::Scratch::new("private-left");
        let b = Broker::open_with(root.path().join("log"), Durability::Relaxed).unwrap();
        let pid = std::process::id();
        let next = PRIVATE_SEQ.load(Ordering::Relaxed);
        for name in (next..next + 32)
            .map(|n| format!("{pid}.{n}"))
            .chain(["1.0".to_string()])
        {
            drop(UnixListener::bind(format!("{ours}.{name}")).unwrap());
        }
        let _live = UnixListener::bind(format!("{ours}.2.0")).unwrap();
        std::fs::write(format!("{ours}.3.0"), "").unwrap();
        let unbound: ServeHook = {
            let ours = ours.clone();
            Box::new(move || {
                assert_eq!(
                    node_at(Path::new(&ours)),
                    None,
                    "serve bound the path itself"
                );
            })
        };
        let mut h = serve_with(&b, &ours, vec![(ServeAt::Bound, unbound)]).unwrap();
        assert_eq!(h.names_listener(), Some(true));
        assert_eq!(sibling_names(&ours), ["2.0", "3.0", "wake"], "names left");
        h.shutdown();
    }

    /// A path whose private name fits no socket address is bound itself, its identity
    /// read there: [`BrokerHandle::names_listener`] says it names the listener, clients
    /// reach it, and nothing is made beside it (its wake name does not fit either, so it
    /// polls). A path removed just after that bind is `NotFound`: no client could reach
    /// the listener, so `serve` keeps none.
    #[cfg(unix)]
    #[test]
    fn a_path_too_long_for_a_private_name_is_bound_itself() {
        let ours = longest_socket_path("lng");
        let _names = Leaves(vec![ours.clone()]);
        let root = crate::test_scratch::Scratch::new("bound-itself");
        let b = Broker::open_with(root.path().join("log"), Durability::Relaxed).unwrap();
        let bound: ServeHook = {
            let ours = ours.clone();
            Box::new(move || {
                assert!(
                    node_at(Path::new(&ours)).is_some(),
                    "serve did not bind the path itself"
                );
            })
        };
        let mut h = serve_with(&b, &ours, vec![(ServeAt::Bound, bound)]).unwrap();
        assert_eq!(h.names_listener(), Some(true));
        assert!(!h.blocks_in_accept(), "a wake name that does not fit");
        assert!(
            UnixStream::connect(&ours).is_ok(),
            "the path reaches nobody"
        );
        assert_eq!(sibling_names(&ours), Vec::<String>::new(), "names made");
        h.shutdown();
        assert_eq!(node_at(Path::new(&ours)), None, "shutdown left its socket");

        let root = crate::test_scratch::Scratch::new("bound-itself-removed");
        let b = Broker::open_with(root.path().join("log"), Durability::Relaxed).unwrap();
        let removed: ServeHook = {
            let ours = ours.clone();
            Box::new(move || std::fs::remove_file(&ours).unwrap())
        };
        let err = serve_with(&b, &ours, vec![(ServeAt::Bound, removed)])
            .err()
            .expect("serve kept a listener no path names");
        assert_eq!(err.kind(), io::ErrorKind::NotFound, "{err}");
    }

    /// A listener whose identity `serve` could not read cannot tell its own socket at the
    /// path from another's, so its shutdown removes nothing there. Built here directly
    /// (a read that fails otherwise than by the path's absence has no portable cause): a
    /// polling listener, its recorded identity cleared, and a LIVE socket renamed over
    /// its path.
    #[cfg(unix)]
    #[test]
    fn shutdown_without_an_identity_leaves_the_path() {
        let ours = longest_socket_path("nid");
        let (_names, _, theirs) = renamed_in_paths("nid");
        let _ours = Leaves(vec![ours.clone()]);
        let root = crate::test_scratch::Scratch::new("no-identity");
        let b = Broker::open_with(root.path().join("log"), Durability::Relaxed).unwrap();
        let mut h = b.serve(&ours).unwrap();
        assert!(!h.blocks_in_accept(), "a wake name that does not fit");
        h.endpoint = Endpoint::Unix {
            path: PathBuf::from(&ours),
            node: None,
            wake: None,
        };
        assert_eq!(h.names_listener(), None);
        let _foreign = UnixListener::bind(&theirs).unwrap();
        let foreign = node_at(Path::new(&theirs)).unwrap();
        std::fs::rename(&theirs, &ours).unwrap();
        h.shutdown();
        assert_eq!(
            node_at(Path::new(&ours)),
            Some(foreign),
            "shutdown removed a socket it could not tell from its own"
        );
    }

    /// A file that is not a socket, put at the path while `serve` binds, is never
    /// replaced, and `serve` answers `AlreadyExists`, as for one it finds there first:
    /// one renamed over the path before the link, and one written there in place of a
    /// stale socket renamed in, once `serve` judged that socket stale and before it
    /// removed it.
    #[cfg(unix)]
    #[test]
    fn a_file_put_at_the_path_while_serve_binds_is_never_replaced() {
        let (_names, ours, theirs) = renamed_in_paths("rnf");
        let root = crate::test_scratch::Scratch::new("renamed-file");
        let b = Broker::open_with(root.path().join("log"), Durability::Relaxed).unwrap();
        std::fs::write(&theirs, "a user's file").unwrap();
        let err = serve_with(&b, &ours, vec![(ServeAt::Bound, rename(&theirs, &ours))])
            .err()
            .expect("serve replaced a file renamed over its path");
        assert_eq!(err.kind(), io::ErrorKind::AlreadyExists, "{err}");
        assert_eq!(std::fs::read_to_string(&ours).unwrap(), "a user's file");
        assert_eq!(sibling_names(&ours), Vec::<String>::new(), "names left");

        std::fs::remove_file(&ours).unwrap();
        drop(UnixListener::bind(&theirs).unwrap());
        // The stale socket is moved aside rather than unlinked, so no filesystem can give
        // its inode number to the file.
        let write: ServeHook = {
            let (ours, aside) = (ours.clone(), theirs.clone());
            Box::new(move || {
                std::fs::rename(&ours, &aside).unwrap();
                std::fs::write(&ours, "a user's file").unwrap();
            })
        };
        let hooks = vec![
            (ServeAt::Bound, rename(&theirs, &ours)),
            (ServeAt::Judged, write),
        ];
        let err = serve_with(&b, &ours, hooks)
            .err()
            .expect("serve replaced a file put at its path");
        assert_eq!(err.kind(), io::ErrorKind::AlreadyExists, "{err}");
        assert_eq!(std::fs::read_to_string(&ours).unwrap(), "a user's file");
        assert_eq!(sibling_names(&ours), Vec::<String>::new(), "names left");
    }

    /// [`BrokerHandle::names_listener`] follows a symlink at the path, as a client's
    /// connect does: one to this listener's own socket names it, one to another socket
    /// or to nothing does not; and shutdown leaves the symlink.
    #[cfg(unix)]
    #[test]
    fn names_listener_follows_a_symlink_as_a_client_does() {
        let (_names, ours, theirs) = renamed_in_paths("sym");
        let root = crate::test_scratch::Scratch::new("symlinked");
        let b = Broker::open_with(root.path().join("log"), Durability::Relaxed).unwrap();
        let mut h = b.serve(&ours).unwrap();
        assert!(h.blocks_in_accept(), "no wake name to point at");
        let point = |to: &str| {
            std::fs::remove_file(&ours).unwrap();
            std::os::unix::fs::symlink(to, &ours).unwrap();
        };
        point(&format!("{ours}.wake"));
        assert_eq!(
            h.names_listener(),
            Some(true),
            "a symlink to its own socket"
        );
        assert!(
            UnixStream::connect(&ours).is_ok(),
            "the symlink reaches nobody"
        );
        let _foreign = UnixListener::bind(&theirs).unwrap();
        point(&theirs);
        assert_eq!(
            h.names_listener(),
            Some(false),
            "a symlink to another socket"
        );
        point(&format!("{theirs}.none"));
        assert_eq!(h.names_listener(), Some(false), "a symlink to nothing");
        h.shutdown();
        assert!(
            std::fs::symlink_metadata(&ours)
                .unwrap()
                .file_type()
                .is_symlink(),
            "shutdown removed the symlink"
        );
    }

    /// The private-name shape [`clear_private_names`] removes: `<file>.<digits>.<digits>`
    /// and nothing else.
    #[cfg(unix)]
    #[test]
    fn a_private_name_is_its_files_name_and_two_numbers() {
        use std::ffi::OsStr;
        let file = OsStr::new("b.sock");
        assert!(is_private_name(file, OsStr::new("b.sock.812.0")));
        for other in [
            "b.sock",
            "b.sock.812",
            "b.sock.812.",
            "b.sock..0",
            "b.sock.x.0",
            "b.sock.812.0.1",
            "b.sockx.812.0",
            "b.sock.wake",
            "a.sock.812.0",
        ] {
            assert!(!is_private_name(file, OsStr::new(other)), "{other}");
        }
    }

    /// The liveness probe answers at once and leaves the stream as it found it. The
    /// probed end has NO read timeout, so a probe that blocked would park for good
    /// (the hang detector says so). Then that end writes 1 MiB, far past a Unix
    /// socket's buffer, before its peer reads a byte: a stream the probe left
    /// non-blocking would fail that write with `WouldBlock` and close, and the peer's
    /// `read_exact` would see the end of the stream short of 1 MiB. Last, a peer that
    /// closed reads as gone.
    #[cfg(unix)]
    #[test]
    fn the_peer_probe_neither_blocks_nor_leaves_the_stream_non_blocking() {
        const LEN: usize = 1 << 20;
        let (a, mut b) = UnixStream::pair().unwrap();
        let mut a = Conn::Unix(a);
        b.set_read_timeout(Some(Duration::from_secs(60))).unwrap();
        let (probed, rx) = mpsc::channel();
        let writer = thread::spawn(move || {
            let _ = probed.send(peer_gone(&mut a));
            // `a` closes as this returns, so a failed write ends `b`'s stream short.
            a.write_all(&vec![7u8; LEN]).map_err(|e| e.kind())
        });
        let gone = rx
            .recv_timeout(Duration::from_secs(60))
            .expect("the probe blocked on a socket with nothing to read");
        assert!(!gone, "a connected peer read as gone");
        let mut got = vec![0u8; LEN];
        b.read_exact(&mut got)
            .expect("the probed end stopped writing short of 1 MiB");
        assert!(got.iter().all(|&x| x == 7));
        let wrote = within_a_minute("the 1 MiB write", move || writer.join().unwrap());
        assert_eq!(wrote, Ok(()), "the write after the probe failed");

        let (c, d) = UnixStream::pair().unwrap();
        drop(d);
        assert!(
            peer_gone(&mut Conn::Unix(c)),
            "a closed peer read as connected"
        );
    }

    /// THE LOG LOCK IS HELD WHILE STAGING AND FREE FOR THE WRITE, read straight off the
    /// mutex with `try_lock`, which never waits: with the writer parked at
    /// `pause_next_batch` (staged, the commit not begun) it is held — the negative
    /// control, and the point a reader still waits out, for staging alone — and with the
    /// writer parked at `pause_next_write` (begun, nothing written) it is free. The
    /// readers that use that freedom are `tests/suite/unlocked_write.rs`.
    #[test]
    fn the_log_lock_is_held_while_staging_and_free_for_the_write() {
        let root = crate::test_scratch::Scratch::new("lock-points");
        let b = Broker::open(root.path().join("log")).unwrap();
        let publish = |seq: u64| {
            let shared = Arc::clone(&b.shared);
            thread::spawn(move || {
                let kind = WriteKind::Publish {
                    producer_id: 1,
                    producer_seq: seq,
                    subject: format!("/t/{seq}"),
                    body: vec![],
                };
                submit_blocking(&shared, kind)
            })
        };
        // Armed one at a time: arming a pause replaces one still armed.
        for held in [true, false] {
            let (pause, seq) = if held {
                (b.pause_next_batch(), 1)
            } else {
                (b.pause_next_write(), 2)
            };
            let parked = publish(seq);
            let pause = within_a_minute("the writer to reach the pause", move || {
                assert!(pause.wait(), "the writer stopped before the pause");
                pause
            });
            let busy = matches!(
                b.shared.log.try_lock(),
                Err(std::sync::TryLockError::WouldBlock)
            );
            assert_eq!(
                busy,
                held,
                "the log lock at the {} pause",
                if held { "staged" } else { "write" }
            );
            pause.resume();
            let acked = within_a_minute("the parked publish's ack", move || parked.join().unwrap());
            assert_eq!(acked, Ok((seq - 1, false)));
        }
    }

    /// IN THE WRITE WINDOW THE LOG REFUSES EVERY OTHER MUTATION. With the writer parked at the
    /// start of a batch's write (`pause_next_write`: begun, the log lock RELEASED), the log
    /// lock can be taken — and the log itself turns away everything that could touch the
    /// file or the batch on its way to it: staging into the batch, an un-batched append, a
    /// second begin, the clean close and retention all fail with the in-flight refusal,
    /// the head unmoved. This is what a broker retention call would meet if it did not
    /// first take the writer's batch lock (`retention_waits_for_a_batch_being_written` in
    /// `tests/suite/unlocked_write.rs` shows that it waits instead). Once resumed, the batch
    /// commits and the log takes mutations again.
    #[test]
    fn in_the_write_window_the_log_refuses_every_other_mutation() {
        let root = crate::test_scratch::Scratch::new("write-window");
        let b = Broker::open(root.path().join("log")).unwrap();
        let pause = b.pause_next_write();
        let shared = Arc::clone(&b.shared);
        let parked = thread::spawn(move || {
            let kind = WriteKind::Publish {
                producer_id: 1,
                producer_seq: 1,
                subject: "/t/a".to_string(),
                body: b"a".to_vec(),
            };
            submit_blocking(&shared, kind)
        });
        let pause = within_a_minute("the writer to reach the paused write", move || {
            assert!(pause.wait(), "the writer stopped before the paused write");
            pause
        });

        let shared = Arc::clone(&b.shared);
        let refusals = within_a_minute("the log lock in the write window", move || {
            let mut log = shared.log.lock().unwrap();
            let mut said: Vec<(&str, String)> = Vec::new();
            match log.stage_publish(2, 1, "/t/b".to_string(), vec![]) {
                Err(StageErr::Io(e)) => said.push(("stage", e.to_string())),
                other => panic!("staging into the batch in flight: {other:?}"),
            }
            let e = log.publish(3, 1, "/t/c".to_string(), vec![]).unwrap_err();
            said.push(("un-batched publish", e.to_string()));
            let e = log.commit_begin().err().expect("a second begin");
            said.push(("second begin", e.to_string()));
            let e = log.close_clean().unwrap_err();
            said.push(("clean close", e.to_string()));
            #[cfg(feature = "retention")]
            {
                let e = log.retain_before(Offset(1)).unwrap_err();
                said.push(("retention", e.to_string()));
            }
            (log.head().0, said)
        });
        let (head, said) = refusals;
        assert_eq!(head, 0, "the batch in flight is not promoted");
        for (what, msg) in &said {
            assert!(
                msg.contains("a batch is being written outside the log lock"),
                "{what} in the write window: {msg}"
            );
        }

        pause.resume();
        let acked = within_a_minute("the parked publish's ack", move || parked.join().unwrap());
        assert_eq!(acked, Ok((0, false)));
        let mut log = b.shared.log.lock().unwrap();
        assert_eq!(log.head().0, 1, "committed");
        assert_eq!(
            log.stage_publish(2, 1, "/t/b".to_string(), vec![]).unwrap(),
            (Offset(1), false),
            "the log stages again once the batch has ended"
        );
        log.abort_batch();
    }

    /// RETENTION AFTER A WRITER PANIC FAILS, AND NEVER HANGS. A writer that panics inside
    /// a batch dies holding the batch lock and poisons it; a retention call after that
    /// panics, as it did when it met the writer's poisoned LOG lock — it does not wait
    /// forever on a lock its own `try_lock` already took (`batch_settled`). The panic
    /// is a thread standing in for the writer: one that takes the batch lock and dies
    /// with it, the way `process_batch` would if a `lock().unwrap()` inside it panicked.
    /// Every call is under the one-minute hang detector, and each retention call's
    /// panic is caught in its own thread, so the broker itself is dropped normally.
    #[cfg(feature = "retention")]
    #[test]
    fn retention_after_a_writer_panic_fails_and_never_hangs() {
        let root = crate::test_scratch::Scratch::new("batch-poisoned");
        let b = Arc::new(Broker::open(root.path().join("log")).unwrap());
        let shared = Arc::clone(&b.shared);
        let died = thread::spawn(move || {
            let _batch = shared.batch.lock().unwrap();
            panic!("the stand-in writer dies inside its batch");
        })
        .join();
        assert!(died.is_err(), "the stand-in writer did not panic");
        assert!(b.shared.batch.is_poisoned(), "the batch lock is poisoned");

        for call in [
            "retain_before",
            "retain_before_carrying_state",
            "set_retention",
        ] {
            let b2 = Arc::clone(&b);
            let failed = within_a_minute("retention after the writer panicked", move || {
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| match call {
                    "retain_before" => b2.retain_before(0).map(drop),
                    "retain_before_carrying_state" => b2.retain_before_carrying_state(0).map(drop),
                    _ => b2.set_retention(
                        crate::Retention::new(
                            vec![crate::Rule::prefix("/t/>").unwrap()],
                            crate::Rule::default_keeping_all(),
                        )
                        .unwrap(),
                    ),
                }))
                .is_err()
            });
            assert!(failed, "{call} returned past a dead writer");
        }
        assert_eq!(b.stats().retention_waits, 0, "nothing waited");
    }

    /// THE RULES ARE SET PAST THE WILLS AN OPEN FIRES. A broker's open fires every will
    /// its log still holds (`fire_will`, queued to the writer, answered by nobody), and
    /// whoever opened it sets its rules at once — `asb serve --retain-file`, aterm's open
    /// — with no flush between. Here a will is registered, the writer is parked in the
    /// write window of the next batch, and the will is fired exactly as the open fires it,
    /// into that batch. `set_retention` from another thread waits for the batch (counted,
    /// `retention_waits` 0 → 1) instead of answering inside it; resumed, the will's record
    /// commits and the rules are set. NEGATIVE CONTROL (planted, scratch-reverted):
    /// `set_retention` without the batch lock is refused "a batch is being written outside
    /// the log lock", and the `Ok` below fails.
    #[cfg(feature = "retention")]
    #[test]
    fn the_rules_are_set_past_the_wills_an_open_fires() {
        let root = crate::test_scratch::Scratch::new("rules-past-wills");
        let b = Arc::new(Broker::open(root.path().join("log")).unwrap());
        let will = WillRecord {
            producer_id: 9,
            producer_seq: crate::will_seq(1).unwrap(),
            subject: "/f/F/pub/n1/presence".to_string(),
            body: b"v=1 state=gone".to_vec(),
        };
        let shared = Arc::clone(&b.shared);
        let registered = within_a_minute("the will's registration", move || {
            submit_blocking(
                &shared,
                WriteKind::WillRegister {
                    conn_id: None,
                    will,
                },
            )
        });
        assert!(registered.is_ok(), "{registered:?}");
        let pending = b.shared.log.lock().unwrap().pending_wills();
        assert_eq!(pending.len(), 1, "the will the next open would fire");
        let head = b.head();

        let pause = b.pause_next_write();
        for will in pending {
            fire_will(&b.shared, will);
        }
        let pause = within_a_minute("the writer to reach the will's write", move || {
            assert!(pause.wait(), "the writer stopped before the paused write");
            pause
        });
        let b2 = Arc::clone(&b);
        let setting = thread::spawn(move || {
            b2.set_retention(
                crate::Retention::new(
                    vec![crate::Rule::prefix("/f/*/pub/*/*/ev").unwrap()],
                    crate::Rule::default_keeping_all(),
                )
                .unwrap(),
            )
        });
        let deadline = Instant::now() + Duration::from_secs(60);
        while !setting.is_finished() && b.stats().retention_waits == 0 {
            assert!(
                Instant::now() < deadline,
                "set_retention neither waited nor answered"
            );
            thread::yield_now();
        }
        assert!(
            !setting.is_finished(),
            "set_retention answered inside the will's write window: {:?}",
            setting.join()
        );
        pause.resume();
        let set = within_a_minute("set_retention after the will's batch", move || {
            setting.join().unwrap()
        });
        assert!(set.is_ok(), "{set:?}");
        assert_eq!(b.stats().retention_waits, 1);
        assert_eq!(b.head(), head + 1, "the will fired");
        assert!(b.retention().is_some(), "the rules are set");
    }

    /// OFF THE ACK PATH (6E-1a): a broker's compaction copies the kept suffix with no
    /// lock held, so a publish acks while the copy runs, and the finish copies what was
    /// acked meanwhile. The compaction's seam holds the copy at its start
    /// (`compact::gate`); with it held, three publishes go through the writer and each
    /// acks under the one-minute hang detector. Released, the compaction drops six, and
    /// a reopen reads offsets 6 to 12, the three among them. The seam's meter shows the
    /// copy's two flushes: the unlocked one covers the suffix as it stood at the begin,
    /// and the one the finish makes under the locks covers only the three acked during
    /// the copy. NEGATIVE CONTROLS: a compaction holding the batch lock across its copy
    /// fails this (no ack until the copy ends, which the gate never lets it); one whose
    /// unlocked copy does not flush makes its finish flush the whole suffix under the
    /// locks, and fails the meter's assertion.
    #[cfg(feature = "retention")]
    #[test]
    fn a_publish_acks_while_a_compaction_copies() {
        let root = crate::test_scratch::Scratch::new("compact-off-ack");
        let path = root.path().join("log");
        let b = Arc::new(Broker::open(&path).unwrap());
        let shared = Arc::clone(&b.shared);
        let publish = move |seq: u64| {
            let shared = Arc::clone(&shared);
            thread::spawn(move || {
                let kind = WriteKind::Publish {
                    producer_id: 1,
                    producer_seq: seq,
                    subject: "/t/x".to_string(),
                    body: format!("m{seq}").into_bytes(),
                };
                submit_blocking(&shared, kind)
            })
        };
        for seq in 0..10 {
            let acked = publish(seq);
            let acked = within_a_minute("a seed publish", move || acked.join().unwrap());
            assert_eq!(acked, Ok((seq, false)));
        }
        let (gate, held) = crate::compact::gate();
        let meter = Arc::new(crate::compact::Meter::default());
        b.shared
            .log
            .lock()
            .unwrap()
            .arm_compact_seam(crate::compact::Seam {
                gate: Some(gate),
                meter: Some(Arc::clone(&meter)),
                ..crate::compact::Seam::default()
            });
        let len = |p: &std::path::Path| std::fs::metadata(p).unwrap().len();
        let b2 = Arc::clone(&b);
        let compaction = thread::spawn(move || b2.retain_before(6));
        let held = within_a_minute("the compaction's copy to reach the gate", move || {
            assert!(held.wait(), "the compaction ended before its copy");
            held
        });
        // The begin is done and nothing was appended since: the log's length at the begin.
        let begun = len(&path);
        for seq in 10..13 {
            let parked = publish(seq);
            let acked = within_a_minute("a publish's ack while the copy is held", move || {
                parked.join().unwrap()
            });
            assert_eq!(acked, Ok((seq, false)), "acked while the copy is held");
        }
        let taken = len(&path) - begun;
        held.resume();
        let dropped = within_a_minute("the compaction", move || compaction.join().unwrap());
        assert_eq!(dropped.unwrap(), 6);
        {
            let log = b.shared.log.lock().unwrap();
            assert_eq!((log.base(), log.head()), (Offset(6), Offset(13)));
        }
        let kept = len(&path);
        assert_eq!(
            *meter.flushes.lock().unwrap(),
            vec![kept - taken, taken],
            "the unlocked copy flushes the suffix as it stood; the locked finish flushes only \
             what was acked during the copy"
        );
        drop(b);
        let log = BrokerLog::open(&path).unwrap();
        let kept: Vec<(u64, Vec<u8>)> = log
            .read_from(Offset::ZERO)
            .iter()
            .map(|r| (r.seq.0, r.body.clone()))
            .collect();
        let want: Vec<(u64, Vec<u8>)> = (6..13u64)
            .map(|i| (i, format!("m{i}").into_bytes()))
            .collect();
        assert_eq!(
            kept, want,
            "the records acked during the copy are in the file"
        );
    }

    /// ONE COMPACTION AT A TIME (6E-1a): `Shared::compaction` is held across a compaction's
    /// begin, its unlocked copy and its finish, so a second retention call waits for the
    /// first to end and then compacts the log the first left. The first is held at its
    /// copy's start (`compact::gate`), where the lock must read taken; the second is
    /// started, the first released and joined, and the second must then reach the gate
    /// itself, be released and compact from the first's base. Every wait is a one-minute
    /// hang detector. NEGATIVE CONTROL: a compaction that does not take the lock fails
    /// the lock's assertion (and, two of them overlapping, the second's begin replaces the
    /// first's `<log>.kept`, which the first's finish renames over the log: a log that
    /// refuses to open).
    #[cfg(feature = "retention")]
    #[test]
    fn compactions_on_one_broker_run_one_at_a_time() {
        let root = crate::test_scratch::Scratch::new("compact-one-at-a-time");
        let path = root.path().join("log");
        let b = Arc::new(Broker::open(&path).unwrap());
        for seq in 0..10u64 {
            let shared = Arc::clone(&b.shared);
            let acked = within_a_minute("a seed publish", move || {
                let kind = WriteKind::Publish {
                    producer_id: 1,
                    producer_seq: seq,
                    subject: "/t/x".to_string(),
                    body: format!("m{seq}").into_bytes(),
                };
                submit_blocking(&shared, kind)
            });
            assert_eq!(acked, Ok((seq, false)));
        }
        let (gate, held) = crate::compact::gate();
        b.shared
            .log
            .lock()
            .unwrap()
            .arm_compact_seam(crate::compact::Seam {
                gate: Some(gate),
                ..crate::compact::Seam::default()
            });
        let b1 = Arc::clone(&b);
        let first = thread::spawn(move || b1.retain_before(4));
        let held = within_a_minute("the first compaction's copy to reach the gate", move || {
            assert!(held.wait(), "the first compaction ended before its copy");
            held
        });
        assert!(
            matches!(
                b.shared.compaction.try_lock(),
                Err(std::sync::TryLockError::WouldBlock)
            ),
            "a compaction's copy runs holding the compaction lock"
        );
        let b2 = Arc::clone(&b);
        let second = thread::spawn(move || b2.retain_before(8));
        held.resume();
        let first = within_a_minute("the first compaction", move || first.join().unwrap());
        assert_eq!(first.unwrap(), 4);
        let held = within_a_minute(
            "the second compaction's copy to reach the gate",
            move || {
                assert!(held.wait(), "the second compaction ended before its copy");
                held
            },
        );
        held.resume();
        let second = within_a_minute("the second compaction", move || second.join().unwrap());
        assert_eq!(
            second.unwrap(),
            4,
            "the second compacts from the first's base"
        );
        {
            let log = b.shared.log.lock().unwrap();
            assert_eq!((log.base(), log.head()), (Offset(8), Offset(10)));
        }
        drop(b);
        let log = BrokerLog::open(&path).unwrap();
        let kept: Vec<(u64, Vec<u8>)> = log
            .read_from(Offset::ZERO)
            .iter()
            .map(|r| (r.seq.0, r.body.clone()))
            .collect();
        let want: Vec<(u64, Vec<u8>)> = (8..10u64)
            .map(|i| (i, format!("m{i}").into_bytes()))
            .collect();
        assert_eq!(kept, want);
    }

    /// A LOG THAT LATCHES TO STRICT KEEPS MARKING WHAT IT MADE DURABLE. A tail that
    /// attached while the log served Ordered — like a connection whose `Hello` said so —
    /// may hold back what it is delivered until a durable mark covers it (aterm's
    /// notifier pages only those), and nothing on its stream says the tier changed. So
    /// when the device refuses a barrier while serving, the batch it refused is flushed
    /// in full (and every batch after it), and the tail is still sent a durable mark for
    /// each batch it was delivered — not only the idle mark an interval later, an hour
    /// here, which a busy subscription never reaches. Before this, the latch cleared the
    /// flag the tail loop sends durable marks under, and this read waited out its hang
    /// detector. Apple only: elsewhere Ordered is served Strict from the open, and
    /// nothing latches.
    #[cfg(unix)]
    #[test]
    fn a_latched_log_keeps_marking_what_it_made_durable() {
        static SEQ: AtomicU64 = AtomicU64::new(0);
        let root = crate::test_scratch::Scratch::new("latch-marks");
        let sock = format!(
            "/tmp/asb_unit_latch_{}_{}.sock",
            std::process::id(),
            SEQ.fetch_add(1, Ordering::Relaxed)
        );
        let _ = std::fs::remove_file(&sock);
        let _tmp = Cleanup(vec![sock.clone()]);
        let b = Broker::open_opts(
            root.path().join("log"),
            OpenOptions::new(Durability::Ordered { horizon: None }),
            || Ok(Prepared::Nothing),
        )
        .unwrap();
        if b.served_durability().served != crate::Tier::Ordered {
            // Only where the barrier does not exist at all: on Apple this log is served
            // Ordered, or the test proves nothing and says so.
            assert_eq!(b.served_durability().reason, crate::ServedReason::NotApple);
            return;
        }
        b.set_idle_mark(Duration::from_secs(3600));
        let _h = b.serve(&sock).unwrap();
        let mut sub = crate::Client::connect(&sock)
            .unwrap()
            .subscribe(0, "/o/>")
            .unwrap();
        // A hang detector, never a budget: the mark this test waits for must come.
        sub.set_read_timeout(Some(Duration::from_secs(60))).unwrap();
        assert!(
            matches!(
                sub.recv_event().unwrap(),
                Some(crate::Event::Mark { next: 0, .. })
            ),
            "the catch-up mark"
        );
        // Read until `off` is delivered and a durable mark covers it, in either order
        // (the mark follows the delivery on one stream, but read both ways round).
        fn delivered_and_marked(sub: &mut crate::Subscription<UnixStream>, off: u64) {
            let (mut delivered, mut marked) = (false, false);
            while !delivered || !marked {
                match sub.recv_event().unwrap().expect("the broker stays up") {
                    crate::Event::Delivery { offset, .. } => {
                        assert_eq!(offset, off);
                        delivered = true;
                    }
                    crate::Event::Mark { durable, .. } => {
                        marked = durable.is_some_and(|d| d > off);
                    }
                    crate::Event::Gap(g) => panic!("nothing is retained here, yet told {g:?}"),
                }
            }
        }
        let mut c = crate::Client::connect(&sock).unwrap();
        // Served Ordered: the first batch is barriered, not durable, and its delivery is
        // not followed by a durable mark.
        let (first, _) = c.publish(1, 1, "/o/a", b"one").unwrap();
        assert!(b.durable_head() <= first, "barriered, not flushed in full");
        assert!(matches!(
            sub.recv_event().unwrap(),
            Some(crate::Event::Delivery { offset, .. }) if offset == first
        ));
        // The device refuses the next barrier: the log latches, and that batch — and
        // with it the first — is flushed in full before its ack.
        b.shared
            .log
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .refuse_barrier = true;
        let (second, _) = c.publish(1, 2, "/o/b", b"two").unwrap();
        let served = b.served_durability();
        assert_eq!(
            (served.served, served.reason),
            (
                crate::Tier::Strict,
                crate::ServedReason::LatchedAfterBarrierError
            )
        );
        assert!(b.durable_head() > second, "the latch flushed it in full");
        delivered_and_marked(&mut sub, second);
        // And every batch after the latch, flushed in full like a Strict one's.
        let (third, _) = c.publish(1, 3, "/o/c", b"three").unwrap();
        delivered_and_marked(&mut sub, third);
    }

    /// The held head's tests, deterministic: ops submitted straight to the writer, each
    /// with its own ack channel, so what step 3 sent is IN the channel by the time the
    /// writer stands at `pause_next_flush` — `try_recv` there is exact, not a race with
    /// the flush. Relaxed (the escalation table holds the head on every platform), and
    /// Ordered where it is served.
    mod held_head {
        use super::*;
        use crate::{Escalate, Escalation};
        use std::sync::mpsc::TryRecvError;

        const MINUTE: Duration = Duration::from_secs(60); // a hang detector, never a budget

        fn escalating(tag: &str, durability: Durability) -> (crate::test_scratch::Scratch, Broker) {
            let root = crate::test_scratch::Scratch::new(tag);
            let mut o = OpenOptions::new(durability);
            o.escalation = Escalation::new([Escalate::Subject("/e/>".into())]);
            let b =
                Broker::open_opts(root.path().join("log"), o, || Ok(Prepared::Nothing)).unwrap();
            (root, b)
        }

        fn submit(b: &Broker, kind: WriteKind) -> Receiver<AckResult> {
            let (tx, rx) = mpsc::channel();
            b.shared
                .writes
                .send(Queued::Op(WriteOp {
                    kind,
                    ack: tx.into(),
                    conn_id: None,
                }))
                .unwrap();
            rx
        }

        fn publish(producer_id: u64, producer_seq: u64, subject: &str) -> WriteKind {
            WriteKind::Publish {
                producer_id,
                producer_seq,
                subject: subject.to_string(),
                body: b"x".to_vec(),
            }
        }

        /// The tiers whose head an escalated record holds on this platform.
        fn holding() -> Vec<Durability> {
            let mut tiers = vec![Durability::Relaxed];
            if cfg!(target_vendor = "apple") {
                tiers.push(Durability::Ordered { horizon: None });
            }
            tiers
        }

        /// In the window between step 3 and the full flush — the window the held head is
        /// FOR — the op before the escalated record is answered, and the escalated op and
        /// the one after it are NOT: the visible head stands at the escalated record and
        /// the durable head below it. Then the flush answers them and releases the head.
        /// (Asserted after an ack arrives instead, a broker that acked first and flushed a
        /// moment later passes whenever the test is slower than the flush.)
        #[test]
        fn nothing_the_head_holds_is_answered_before_the_flush() {
            for durability in holding() {
                let (_root, b) = escalating("held-acks", durability);
                assert_ne!(b.served_durability().served, crate::Tier::Strict);
                // Hold the writer on a first batch, so the next three ops form ONE batch.
                let gate = b.pause_next_batch();
                let first = submit(&b, publish(1, 1, "/o/a"));
                assert!(gate.wait_at_most(MINUTE), "the first batch staged");
                let plain = submit(&b, publish(2, 1, "/o/b"));
                let esc = submit(&b, publish(2, 2, "/e/b"));
                let after = submit(&b, publish(2, 3, "/o/c"));
                let flush = b.pause_next_flush();
                gate.resume();
                assert_eq!(first.recv_timeout(MINUTE).unwrap(), Ok((0, false)));
                assert!(
                    flush.wait_at_most(MINUTE),
                    "{durability:?}: a flush is owed"
                );
                assert_eq!(plain.try_recv(), Ok(Ok((1, false))), "{durability:?}");
                assert_eq!(esc.try_recv(), Err(TryRecvError::Empty), "{durability:?}");
                assert_eq!(after.try_recv(), Err(TryRecvError::Empty), "{durability:?}");
                assert_eq!(
                    b.visible_head(),
                    2,
                    "{durability:?}: held at the escalated record"
                );
                assert!(
                    b.durable_head() <= 2,
                    "{durability:?}: nothing above it is durable"
                );
                flush.resume();
                assert_eq!(esc.recv_timeout(MINUTE).unwrap(), Ok((2, false)));
                assert_eq!(after.recv_timeout(MINUTE).unwrap(), Ok((3, false)));
                assert_eq!(
                    (b.visible_head(), b.durable_head()),
                    (4, 4),
                    "{durability:?}"
                );
            }
        }

        /// A WILL REGISTRATION in a held batch is answered by its own commit — at step 3,
        /// not after the flush — so a flush that then FAILS cannot tell the connection
        /// "will was not persisted" while the log keeps the `/a/will` record (which the
        /// next open would fire: a goodbye for a producer told it registered nothing).
        /// The escalated publish beside it is refused "outcome unknown", as it must be.
        #[test]
        fn a_will_registration_in_a_held_batch_is_answered_by_its_commit() {
            for durability in holding() {
                let (_root, b) = escalating("held-will", durability);
                // Every full flush fails; Relaxed's batch issues none and Ordered's issues
                // a barrier, so only the held head's flush meets the fault.
                b.inject_faults(InjectedFaults {
                    write: false,
                    sync: true,
                    truncate: false,
                });
                let gate = b.pause_next_batch();
                let first = submit(&b, publish(1, 1, "/o/a"));
                assert!(gate.wait_at_most(MINUTE), "the first batch staged");
                let esc = submit(&b, publish(1, 2, "/e/a"));
                let will = submit(
                    &b,
                    WriteKind::WillRegister {
                        conn_id: None,
                        will: WillRecord {
                            producer_id: 7,
                            producer_seq: 1,
                            subject: "/w/gone".to_string(),
                            body: b"bye".to_vec(),
                        },
                    },
                );
                gate.resume();
                assert_eq!(first.recv_timeout(MINUTE).unwrap(), Ok((0, false)));
                let refused = esc.recv_timeout(MINUTE).unwrap().unwrap_err();
                assert_eq!(refused.0, ERR_REFUSED);
                assert!(
                    refused.1.contains("durability flush failed"),
                    "{}",
                    refused.1
                );
                assert_eq!(
                    will.recv_timeout(MINUTE).unwrap(),
                    Ok((2, false)),
                    "{durability:?}: the will is on the log, and the connection is told so"
                );
            }
        }

        fn commit(group: &str, upto: u64) -> WriteKind {
            WriteKind::Commit {
                group: group.to_string(),
                upto,
            }
        }

        /// `Broker::group_start` COUNTS A COMMIT WITH ITS BATCH, NEVER BEFORE. With the
        /// writer paused at its write — the commit's batch staged and sealed, the log
        /// lock let go — the read answers (it would wait out a held lock), and answers
        /// the log as it stood before the batch: the group has never committed, the
        /// visible head is short of the commit record. The commit's ack finds both
        /// moved, and another group's place untouched. Strict, Ordered and Relaxed.
        #[test]
        fn group_start_counts_a_commit_with_its_batch() {
            for durability in [
                Durability::Strict,
                Durability::Ordered { horizon: None },
                Durability::Relaxed,
            ] {
                let (_root, b) = escalating("group-start", durability);
                assert_eq!(
                    submit(&b, publish(1, 1, "/o/a"))
                        .recv_timeout(MINUTE)
                        .unwrap(),
                    Ok((0, false))
                );
                assert_eq!(b.group_start("/g/a"), 0, "{durability:?}: never committed");
                let write = b.pause_next_write();
                let acked = submit(&b, commit("/g/a", 0));
                assert!(
                    write.wait_at_most(MINUTE),
                    "{durability:?}: the commit's batch is writing"
                );
                assert_eq!(
                    (b.group_start("/g/a"), b.visible_head()),
                    (0, 1),
                    "{durability:?}: a batch not yet promoted counts for nothing"
                );
                write.resume();
                assert_eq!(acked.recv_timeout(MINUTE).unwrap(), Ok((1, false)));
                assert_eq!(
                    (b.group_start("/g/a"), b.visible_head()),
                    (1, 2),
                    "{durability:?}: the commit counts with its record visible"
                );
                assert_eq!(b.group_start("/g/b"), 0, "{durability:?}: its own group's");
            }
        }

        /// A commit a HELD batch carries (the escalation table names its group) counts in
        /// `Broker::group_start` only once the full flush that releases it has succeeded:
        /// in the window before that flush — the log lock free, the record written — the
        /// group still starts where it did, exactly where a `SubscribeGroup` would.
        #[test]
        fn a_held_commit_counts_in_group_start_after_its_flush() {
            for durability in holding() {
                let root = crate::test_scratch::Scratch::new("group-start-held");
                let mut o = OpenOptions::new(durability);
                o.escalation = Escalation::new([Escalate::Group("/g/held".into())]);
                let b = Broker::open_opts(root.path().join("log"), o, || Ok(Prepared::Nothing))
                    .unwrap();
                assert_eq!(
                    submit(&b, publish(1, 1, "/o/a"))
                        .recv_timeout(MINUTE)
                        .unwrap(),
                    Ok((0, false))
                );
                let flush = b.pause_next_flush();
                let acked = submit(&b, commit("/g/held", 0));
                assert!(
                    flush.wait_at_most(MINUTE),
                    "{durability:?}: the held commit owes a full flush"
                );
                assert_eq!(
                    (b.group_start("/g/held"), b.visible_head()),
                    (0, 1),
                    "{durability:?}: held at the commit record"
                );
                flush.resume();
                assert_eq!(acked.recv_timeout(MINUTE).unwrap(), Ok((1, false)));
                assert_eq!(
                    (b.group_start("/g/held"), b.visible_head()),
                    (1, 2),
                    "{durability:?}: released with its flush"
                );
            }
        }
    }

    /// CONNECTION CLOSE IS ORDERED AFTER ITS DECODED WRITES. A connection's first write is
    /// refused and latches its producer fence. With the writer held on unrelated work, its
    /// successor is queued, then the connection closes. The successor is still refused before
    /// the close marker removes the fence; a sentinel queued after the close lands and proves
    /// the marker ran. Clearing in [`ConnGuard::drop`] instead makes the successor land and is
    /// this test's negative control.
    #[test]
    fn a_connection_close_drops_its_fences_after_its_queued_writes() {
        const MINUTE: Duration = Duration::from_secs(60); // a hang detector, never a budget
        const CONN: u64 = 77;
        const PRODUCER: u64 = 9;

        let root = crate::test_scratch::Scratch::new("close-fence-order");
        let b = Broker::open_opts(
            root.path().join("log"),
            OpenOptions::new(Durability::Strict).with_sticky_batch_refusal(true),
            || Ok(Prepared::Nothing),
        )
        .unwrap();
        let submit = |conn_id, kind| {
            let (tx, rx) = mpsc::channel();
            b.shared
                .writes
                .send(Queued::Op(WriteOp {
                    kind,
                    ack: tx.into(),
                    conn_id,
                }))
                .unwrap();
            rx
        };
        let publish = |producer_id, producer_seq, subject: &str| WriteKind::Publish {
            producer_id,
            producer_seq,
            subject: subject.to_string(),
            body: b"x".to_vec(),
        };

        let refused = submit(
            Some(CONN),
            WriteKind::PreRefused {
                producer_id: PRODUCER,
                producer_seq: 1,
                err: refusal(ERR_REFUSED, "first refused"),
            },
        );
        assert_eq!(
            refused.recv_timeout(MINUTE).unwrap(),
            Err(refusal(ERR_REFUSED, "first refused"))
        );
        assert_eq!(
            b.shared
                .sticky_fences
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .len(),
            1,
            "the first refusal latched the connection's fence"
        );

        let gate = b.pause_next_batch();
        let blocker = submit(None, publish(1, 1, "/other/blocker"));
        assert!(
            gate.wait_at_most(MINUTE),
            "the writer held before the close"
        );
        let successor = submit(Some(CONN), publish(PRODUCER, 2, "/ordered/second"));
        drop(ConnGuard {
            shared: &b.shared,
            id: CONN,
            fences_gaps: Cell::new(true),
        });
        let sentinel = submit(None, publish(2, 1, "/other/sentinel"));
        gate.resume();

        assert_eq!(blocker.recv_timeout(MINUTE).unwrap(), Ok((0, false)));
        let fenced = successor.recv_timeout(MINUTE).unwrap().unwrap_err();
        assert_eq!(
            crate::sticky_fence::parse_gap_fenced_seq(&fenced.1),
            Some(1),
            "the queued successor was judged before close removed its fence: {fenced:?}"
        );
        assert_eq!(sentinel.recv_timeout(MINUTE).unwrap(), Ok((1, false)));
        assert!(
            b.shared
                .sticky_fences
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .is_empty(),
            "the close marker removed the fence before the sentinel"
        );
        assert_eq!(b.head(), 2, "the fenced successor never landed");
    }

    /// The writer's stop ([`stop_writer`]), driven straight through its queue so what is
    /// queued around the stop is exact, not a race with shutdown.
    mod writer_stop {
        use super::*;

        const MINUTE: Duration = Duration::from_secs(60); // a hang detector, never a budget

        fn submit(b: &Broker, producer_seq: u64) -> Receiver<AckResult> {
            let (tx, rx) = mpsc::channel();
            let kind = WriteKind::Publish {
                producer_id: 1,
                producer_seq,
                subject: format!("/s/{producer_seq}"),
                body: b"x".to_vec(),
            };
            b.shared
                .writes
                .send(Queued::Op(WriteOp {
                    kind,
                    ack: tx.into(),
                    conn_id: None,
                }))
                .unwrap();
            rx
        }

        /// THE STOP ENDS THE WRITER AFTER EVERYTHING QUEUED BEFORE IT AND BESIDE IT.
        /// With the writer held inside a batch, an op, the stop and an op that raced
        /// shutdown in behind it are queued; once the batch goes on, all three ops are
        /// committed and answered at their offsets, and the writer thread returns — a
        /// join under a one-minute hang detector — having woken on no timer. A writer
        /// that left at the stop would drop the op queued before it in the same drain
        /// (its ack `Disconnected`); one that committed up to the stop and left, the op
        /// behind it.
        #[test]
        fn a_stopped_writer_commits_what_is_queued_then_returns() {
            let root = crate::test_scratch::Scratch::new("writer-stop");
            let b = Broker::open(root.path().join("log")).unwrap();
            let gate = b.pause_next_batch();
            let first = submit(&b, 1);
            assert!(gate.wait_at_most(MINUTE), "the first batch staged");
            let before = submit(&b, 2);
            b.shared.running.store(false, Ordering::Relaxed);
            b.shared.writes.send(Queued::Stop).unwrap();
            let after = submit(&b, 3);
            let writer = b
                .shared
                .writer
                .lock()
                .unwrap()
                .take()
                .expect("the writer runs");
            gate.resume();
            assert!(
                within_a_minute("the stopped writer", move || writer.join().is_ok()),
                "the writer panicked"
            );
            assert_eq!(first.try_recv(), Ok(Ok((0, false))));
            assert_eq!(
                before.try_recv(),
                Ok(Ok((1, false))),
                "queued before the stop"
            );
            assert_eq!(
                after.try_recv(),
                Ok(Ok((2, false))),
                "queued after the stop"
            );
            assert_eq!(b.stats().writer_wakeups, 0, "the writer woke on a timer");
        }
    }

    /// THE POISON IS READ WITHOUT THE LOG LOCK. A failed rollback poisons a Strict log;
    /// then the writer is parked inside a batch, HOLDING the log lock — read straight off
    /// the mutex with `try_lock`, the NEGATIVE CONTROL: a read that took the lock would
    /// wait here until the batch resumes. Meanwhile `poisoned`, `flush_counts` and
    /// `wait_poisoned` all answer, and so does a fresh connection's `Hello`, whose health
    /// entry names the same poison — each under a one-minute hang detector, never a
    /// latency budget. Before this, `poisoned` took the log lock, which the writer holds
    /// across a rollback's truncate and a failed flush's identity I/O: the look waited
    /// out the very failure it was looking for.
    #[cfg(unix)]
    #[test]
    fn the_poison_and_the_flush_counts_are_read_without_the_log_lock() {
        let root = crate::test_scratch::Scratch::new("vitals-unlocked");
        let sock = root.path().join("sock");
        let b = Arc::new(Broker::open(root.path().join("log")).unwrap());
        let _h = b.serve(&sock).unwrap();
        let mut c = crate::Client::connect(&sock).unwrap();
        c.publish(1, 1, "/o/a", b"before").unwrap();
        b.inject_faults(InjectedFaults {
            write: false,
            sync: true,
            truncate: true,
        });
        c.publish(1, 2, "/o/a", b"orphan").unwrap_err();
        b.inject_faults(InjectedFaults::default());
        let why = b.poisoned().expect("the failed rollback poisoned the log");

        let pause = b.pause_next_batch();
        c.send_publish(1, 3, "/o/a", b"parks the writer").unwrap();
        let pause = within_a_minute("the writer to reach the pause", move || {
            assert!(pause.wait(), "the writer stopped before the pause");
            pause
        });
        assert!(
            matches!(
                b.shared.log.try_lock(),
                Err(std::sync::TryLockError::WouldBlock)
            ),
            "the parked writer holds the log lock"
        );
        let reader = Arc::clone(&b);
        let (poisoned, failed, waited, told) =
            within_a_minute("the vitals, read beside a held log lock", move || {
                let mut fresh = crate::Client::connect(&sock).unwrap();
                fresh.hello().unwrap();
                (
                    reader.poisoned(),
                    reader.flush_counts().failed,
                    reader.wait_poisoned(Duration::from_secs(3600)),
                    fresh.broker_health().cloned(),
                )
            });
        assert_eq!(poisoned.as_deref(), Some(why.as_str()));
        assert_eq!(failed, 1, "the rollback's failed flush is counted");
        assert_eq!(waited.as_deref(), Some(why.as_str()), "no wait: poisoned");
        let told = told.expect("this broker's Hello carries the health entry");
        assert_eq!(told.poisoned.as_deref(), Some(why.as_str()));
        assert_eq!(told.flushes.failed, 1);
        pause.resume();
        let err = c.recv_publish_ack().unwrap_err();
        assert!(
            crate::broker_refusal(&err).is_some_and(crate::BrokerRefusal::is_poisoned),
            "{err}"
        );
    }

    /// Spin until `cond` holds — a one-minute HANG DETECTOR, never a latency budget.
    fn until_a_minute(what: &str, mut cond: impl FnMut() -> bool) {
        let deadline = Instant::now() + Duration::from_secs(60);
        while !cond() {
            assert!(Instant::now() < deadline, "{what}: never happened");
            thread::yield_now();
        }
    }

    /// A `Hello` THAT NAMES THE POISON NAMES THE LATCH WITH IT. On Relaxed with `/e/>`
    /// escalated (a full flush the table owes, on every platform), an escalated
    /// publish's full flush fails: the log latches to Strict and is poisoned, in one
    /// publication. The test HOLDS the copy `Hello` answers from (`Shared::hello`)
    /// across the failure, so the writer cannot refresh it — and the copy still says
    /// Relaxed once the poison is out (the window is real: the NEGATIVE CONTROL), while
    /// the answer assembled from it and the vitals (`hello_answer`) says poisoned AND
    /// served Strict (`LatchedAfterFlushFailure`). Before, the tier came from the copy
    /// alone, and one answer told the poison beside the tier from before the latch.
    #[cfg(unix)]
    #[test]
    fn a_hello_that_names_the_poison_names_the_latch_with_it() {
        let root = crate::test_scratch::Scratch::new("hello-latch");
        let sock = root.path().join("sock");
        let mut o = OpenOptions::new(Durability::Relaxed);
        o.escalation = crate::Escalation::new([crate::Escalate::Subject("/e/>".into())]);
        let b = Arc::new(
            Broker::open_opts(root.path().join("log"), o, || Ok(Prepared::Nothing)).unwrap(),
        );
        let _h = b.serve(&sock).unwrap();
        let mut c = crate::Client::connect(&sock).unwrap();
        c.publish(1, 1, "/o/a", b"page cache").unwrap();
        b.inject_faults(InjectedFaults {
            write: false,
            sync: true,
            truncate: false,
        });
        let held = b.shared.hello.lock().unwrap();
        let (tx, refused) = mpsc::channel();
        thread::spawn(move || {
            let _ = tx.send(c.publish(1, 2, "/e/a", b"a person's word").is_err());
        });
        let waiter = Arc::clone(&b);
        let why = within_a_minute("the poison", move || {
            waiter.wait_poisoned(Duration::from_secs(3600))
        })
        .expect("the failed full flush poisoned the log");
        assert_eq!(
            held.ext.durability.map(|s| s.served),
            Some(crate::proto::Tier::Relaxed),
            "the copy is not refreshed yet"
        );
        let told = hello_answer(held.clone(), &b.shared.vitals, false);
        drop(held);
        let health = told.ext.health.expect("the health entry");
        assert_eq!(health.poisoned.as_deref(), Some(why.as_str()));
        let served = told.ext.durability.expect("the tier served");
        assert_eq!(
            (served.requested, served.served, served.reason),
            (
                crate::proto::Tier::Relaxed,
                crate::proto::Tier::Strict,
                crate::proto::ServedReason::LatchedAfterFlushFailure
            ),
            "the poison is told beside the latched tier"
        );
        assert!(
            refused.recv_timeout(Duration::from_secs(60)).unwrap(),
            "the escalated publish is refused"
        );
        assert_eq!(b.served_durability(), served);
    }

    /// `wait_poisoned` SLEEPS ON THE POISON AND ON THE STOP. A waiter given an hour is
    /// seen PARKED first (the vitals' `parked` seam, counted under their lock before it
    /// sleeps, so what the test does next is something it must be woken for); then a
    /// failed rollback poisons the log, and it wakes with the reason. On a second,
    /// healthy broker a parked waiter wakes with `None` when the last listener shuts
    /// down. Each under a one-minute hang detector against its hour: a stop that forgot
    /// to wake the vitals leaves its waiter asleep, and fails here (a waiter that has
    /// not parked yet reads the stop without being woken, which is why it must be seen
    /// parked). NEGATIVE CONTROL: on a healthy broker a zero timeout returns `None` at
    /// once.
    #[cfg(unix)]
    #[test]
    fn wait_poisoned_wakes_at_the_poison_and_at_the_stop() {
        let parked_waiter = |b: &Arc<Broker>| {
            let w = Arc::clone(b);
            let (tx, rx) = mpsc::channel();
            thread::spawn(move || {
                let _ = tx.send(w.wait_poisoned(Duration::from_secs(3600)));
            });
            until_a_minute("the waiter parks", || {
                b.shared.vitals.parked.load(Ordering::SeqCst) == 1
            });
            rx
        };

        let root = crate::test_scratch::Scratch::new("wait-poisoned");
        let sock = root.path().join("sock");
        let b = Arc::new(Broker::open(root.path().join("log")).unwrap());
        let _h = b.serve(&sock).unwrap();
        assert_eq!(b.wait_poisoned(Duration::ZERO), None, "healthy: no poison");
        let mut c = crate::Client::connect(&sock).unwrap();
        c.publish(1, 1, "/o/a", b"before").unwrap();
        let rx = parked_waiter(&b);
        b.inject_faults(InjectedFaults {
            write: false,
            sync: true,
            truncate: true,
        });
        c.publish(1, 2, "/o/a", b"orphan").unwrap_err();
        let woke = rx
            .recv_timeout(Duration::from_secs(60))
            .expect("the poison woke the waiter");
        assert!(woke.is_some());
        assert_eq!(woke, b.poisoned());

        let root = crate::test_scratch::Scratch::new("wait-stopped");
        let b = Arc::new(Broker::open(root.path().join("log")).unwrap());
        let mut h = b.serve(root.path().join("sock")).unwrap();
        let rx = parked_waiter(&b);
        h.shutdown();
        assert_eq!(
            rx.recv_timeout(Duration::from_secs(60))
                .expect("the stop woke the waiter"),
            None
        );
    }

    /// A POISON THAT LANDS AFTER A SNAPSHOT IS TAKEN IS WRITTEN AT ONCE, not a period
    /// later. `keep_health` with an hour's period writes its first snapshot — healthy —
    /// and the test holds it there, before its thread starts (the thread's slot, held);
    /// a failed rollback then poisons the log, and the thread is let go. It must name
    /// the poison under a one-minute hang detector, against its hour: the snapshot it
    /// last wrote did not name it. Before, the thread looked at the poison itself before
    /// its first wait, found it set, took it as written, and slept the hour while the
    /// sidecar said `poisoned=no` of a log that refused every write. A periodic write
    /// has the same window: the poison landing while it creates, writes and renames the
    /// file — slow on exactly the failing disk that poisons a log.
    #[cfg(unix)]
    #[test]
    fn a_poison_after_the_snapshot_is_written_at_once_not_a_period_later() {
        let root = crate::test_scratch::Scratch::new("health-race");
        let log = root.path().join("log");
        let sock = root.path().join("sock");
        let b = Arc::new(Broker::open(&log).unwrap());
        let _h = b.serve(&sock).unwrap();
        let mut c = crate::Client::connect(&sock).unwrap();
        c.publish(1, 1, "/o/a", b"before").unwrap();

        let slot = b.shared.health_thread.lock().unwrap();
        let keeper = Arc::clone(&b);
        let (tx, kept) = mpsc::channel();
        thread::spawn(move || {
            let _ = tx.send(keeper.keep_health(Duration::from_secs(3600)).is_ok());
        });
        let read = |log: &Path| crate::health::read_health(log).unwrap();
        until_a_minute("the first snapshot is published", || read(&log).is_some());
        assert_eq!(read(&log).unwrap().health.poisoned, None, "healthy");

        b.inject_faults(InjectedFaults {
            write: false,
            sync: true,
            truncate: true,
        });
        c.publish(1, 2, "/o/a", b"orphan").unwrap_err();
        let why = b.poisoned().expect("the failed rollback poisoned the log");
        drop(slot);
        assert!(kept.recv_timeout(Duration::from_secs(60)).unwrap());
        until_a_minute("the sidecar names the poison, an hour early", || {
            read(&log).unwrap().health.poisoned.as_deref() == Some(why.as_str())
        });
    }

    #[cfg(unix)]
    #[test]
    fn pipelined_multi_follower_replication_confirms_across_three_replicas() {
        static SEQ: AtomicU64 = AtomicU64::new(0);
        let k = SEQ.fetch_add(1, Ordering::Relaxed);
        let pid = std::process::id();
        // Under /tmp: a Darwin TMPDIR can push a socket path past SUN_LEN.
        let l_sock = format!("/tmp/asb_pmr_{pid}_{k}.sock");
        let _tmp = Cleanup(vec![l_sock.clone(), format!("{l_sock}.wake")]);
        let root = crate::test_scratch::Scratch::new("pmr");
        let f1_log = root.path().join("f1.log");
        let f2_log = root.path().join("f2.log");
        let f3_log = root.path().join("f3.log");
        let l_log = root.path().join("leader.log");

        let f1 = Broker::open_replica_with(&f1_log, Durability::Relaxed).unwrap();
        let f2 = Broker::open_replica_with(&f2_log, Durability::Relaxed).unwrap();
        let f3 = Broker::open_replica_with(&f3_log, Durability::Relaxed).unwrap();
        let mut h1 = f1.serve_tcp("127.0.0.1:0").unwrap();
        let mut h2 = f2.serve_tcp("127.0.0.1:0").unwrap();
        let mut h3 = f3.serve_tcp("127.0.0.1:0").unwrap();
        let addrs = vec![
            h1.tcp_addr().unwrap().to_string(),
            h2.tcp_addr().unwrap().to_string(),
            h3.tcp_addr().unwrap().to_string(),
        ];

        let leader = Broker::open_replicated(&l_log, &addrs, 3).unwrap();
        let mut lh = leader.serve(&l_sock).unwrap();

        let mut client = crate::Client::connect(&l_sock).unwrap();
        let payloads: Vec<Vec<u8>> = (0..160)
            .map(|i| format!("multi-{i:04}").into_bytes())
            .collect();
        let refs: Vec<&[u8]> = payloads.iter().map(Vec::as_slice).collect();
        let acks = client.publish_pipelined(99, "/t/multi", &refs, 64).unwrap();
        assert_eq!(acks.len(), 160);
        assert_eq!(leader.head(), 160);
        assert_eq!(leader.visible_head(), 160);
        assert_eq!(f1.head(), 160);
        assert_eq!(f2.head(), 160);
        assert_eq!(f3.head(), 160);

        lh.shutdown();
        h1.shutdown();
        h2.shutdown();
        h3.shutdown();
    }
}

#[cfg(all(test, feature = "retention"))]
#[path = "retention_tick_tests.rs"]
mod retention_tick_tests;

#[cfg(all(test, unix, feature = "retention"))]
#[path = "held_tail_wire_tests.rs"]
mod held_tail_wire_tests;

#[cfg(test)]
#[path = "fresh_publish_tests.rs"]
mod fresh_publish_tests;

#[cfg(all(test, unix, feature = "cap"))]
#[path = "disconnected_will_tests.rs"]
mod disconnected_will_tests;
