#![forbid(unsafe_code)]
//! `astream-broker` — astream's **servable broker**: the message bus you actually
//! connect to.
//!
//! A thread-per-connection daemon that turns astream's invariants into a usable
//! system, over a local Unix-domain socket ([`Broker::serve`], same-machine), plain
//! TCP ([`Broker::serve_tcp`] — plaintext, trusted network only), or — with the
//! `aead` feature — an XChaCha20-Poly1305-sealed TCP transport
//! (`Broker::serve_tcp_sealed`, confidential + authenticated). With the `cap`
//! feature a broker opened by `Broker::open_guarded` enforces signed capabilities on
//! its accept path — presented as a proof of possession over a per-connection nonce
//! (`Hello` → `Nonce` → `Attach` → `Mark`), so the capability's tag never crosses the
//! wire, and held on a bounded per-connection keyring. The same Frame protocol rides
//! every transport, and a caller that picks the transport at runtime reaches all of
//! them through ONE function: [`connect`] takes a [`Transport`] and hands back a
//! transport-erased [`AnyClient`] plus the [`Closer`] that ends it from another thread
//! and bounds its reads and writes, with an optional connect timeout.
//!
//! - **PUBLISH** appends to a durable log with **exactly-once ingest** — a re-sent
//!   `(producer_id, producer_seq)` is not re-appended and returns its original
//!   offset (survives a broker restart). Writes are GROUP-COMMITTED: one writer
//!   thread batches every mutation and, at the Strict tier, fsyncs once per batch
//!   (`ack ⟹ fsync'd`); a single connection can pipeline many publishes.
//! - **SUBSCRIBE(filter, from_offset)** streams every matching record (the
//!   `astream_wire::Filter` grammar) in offset order, gaplessly, then tails live.
//! - **RESUME**: a consumer that crashes reconnects with `from_offset =
//!   last_committed + 1` and continues with no gaps and no dups.
//! - **REPLAY-SUBSCRIPTION**: `subscribe(filter, 0)` re-delivers full history
//!   deterministically — time-travel as a native operation.
//! - **DURABLE CONSUMER GROUPS**: `commit` / `subscribe_group` keep a group's
//!   committed offset ON the broker, and `process_and_produce` is the atomic
//!   read-process-write transaction (output + commit in one durable record) — true
//!   end-to-end exactly-once processing.
//! - **RETAINED STATE**: `Last{filter, after, max}` is the last record of every
//!   matching subject, paged in subject order and closed by a `Mark{next, head}` a
//!   `subscribe` on the same connection can tail on from. [`Client::last_walk`] and
//!   [`Client::last_all`] page it to the end on the resume cursor and keep the FIRST
//!   page's mark — the one splice point a paged answer has.
//! - **BOUNDED READS**: `Fetch{from, filter, max}` reads at most `max` matching
//!   records while scanning at most `FETCH_SCAN_MAX`, and — unlike every other
//!   streaming verb — leaves the connection usable.
//! - **A LAST WILL**: `Will{..}` is the record the broker appends when your
//!   connection ends, deduped by your own producer key and fenced by any later
//!   record of yours; every will the log still holds is re-fired on open.
//! - **FORK-DELIVERY and cognition routing** build on the same SUBSCRIBE primitive.
//! - **The durability dial**: Strict (fsync per batch), Relaxed (page cache), and
//!   Replicated ([`Broker::open_replicated`]: an ack waits for a follower quorum).
//!   [`ShardedBroker`] runs N share-nothing partitions.
//!
//! Everything is std-only (threads + `Mutex`/`Condvar` + sockets) over the
//! `astream_wire` codec; `forbid(unsafe)`. The default build has zero third-party
//! deps — the optional `cap` / `aead` features pull the vetted in-tree crypto crates.
//!
//! Honest boundary: delivery to the socket is ordered, gapless, and AT-LEAST-ONCE
//! (the consumer's cursor or a durable group commit makes it effectively exactly-once;
//! [`drain`] / [`take`] / [`ack`] are that inbox loop as library helpers).

pub mod brecord;
pub mod broker;
pub mod client;
pub mod proto;
/// cfg(unix): sharding binds one Unix-domain socket per shard, and std has no
/// Unix-domain sockets on Windows (where the broker serves TCP only).
#[cfg(unix)]
pub mod sharded;
pub mod store;

pub use brecord::{BrokerRecord, BREC_VERSION, MAX_RECORD_PAYLOAD};
pub use broker::{Broker, BrokerHandle};
pub use client::{
    ack, connect, drain, take, AnyClient, AnyStream, AnySubscription, Client, Closer, Event, Page,
    Record, Subscription, SubscriptionCloser, Transport, Walk, ACK_SEQ_BASE, LAST_WALK_PAGES_MAX,
};

/// Static public-key identity types (Rung 8), re-exported so callers of
/// [`Broker::serve_tcp_identity`] / [`Client::connect_tcp_identity`] can build an
/// identity without depending on `astream-aead` directly.
#[cfg(feature = "identity")]
pub use astream_aead::{IdentityKeypair, ID_PUB_LEN};
pub use proto::{Request, Response};
#[cfg(unix)]
pub use sharded::{ShardedBroker, ShardedClient, ShardedHandle, ShardedSubscription};
pub use store::{BrokerLog, Durability, InjectedFaults};
