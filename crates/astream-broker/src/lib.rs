#![forbid(unsafe_code)]
// Explicit `match` / `let ... else` / `contains_key` forms are used in verified code
// paths so `trustc` discharges Level-0 obligations without closure calls, residual trait
// projections, or `hardened_error_discard` unknowns.
#![allow(
    clippy::manual_div_ceil,
    clippy::manual_map,
    clippy::manual_ok_err,
    clippy::manual_unwrap_or_default,
    clippy::map_entry,
    clippy::question_mark
)]
//! `astream-broker` — astream's **servable broker**: the message bus you actually
//! connect to.
//!
//! A thread-per-connection daemon that turns astream's invariants into a usable
//! system, over a local Unix-domain socket ([`Broker::serve`], same-machine), plain
//! TCP ([`Broker::serve_tcp`] — plaintext, trusted network only), or — with the
//! `aead` feature — an XChaCha20-Poly1305-sealed TCP transport
//! (`Broker::serve_tcp_sealed`, confidential + authenticated; ring's ChaCha20-Poly1305
//! under the HChaCha20 subkey `astream-aead` derives). With the `cap`
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
//!   record of yours; every will the log still holds is re-fired on open. A TCP
//!   client that keeps alive ([`Client::keepalive_if_idle`]) is held to
//!   [`KEEPALIVE_DEADLINE`], so one that vanishes without a FIN ends — and its will
//!   fires — instead of holding its connection until the broker restarts.
//! - **LOG IDENTITY**: the answer to `Hello` names the log served — a
//!   [`LogIdentity`], a random id and a generation that moves whenever an offset may
//!   have come to name a different record (a repair's cut, an older copy restored, a
//!   Relaxed run's power loss) — so a client that persisted offsets checks them first
//!   ([`Client::log_identity`]); a replica reports its leader's. Beside it rides a
//!   [`Lineage`] — where generations still agree, so a reader resumes at
//!   [`LogIdentity::continues`] instead of forgetting — and the tier the broker serves
//!   ([`Client::log_lineage`], [`Client::served_durability`]).
//! - **HEALTH, FROM THE BROKER ITSELF**: the answer to every `Hello` says whether the
//!   log is POISONED (it refuses every write until it is reopened) and why, and what its
//!   flushes did ([`HelloHealth`], [`Client::broker_health`]) — read by the broker without
//!   the log's lock, as are [`Broker::poisoned`] and [`Broker::wait_poisoned`]. It names
//!   the log's DEVICE too, and whether its full flush drains it ([`LogDevice`],
//!   [`Client::log_device`]), so a writer of its own on that device settles its
//!   barriered writes by the broker's flush ([`Client::settle`]) rather than draining the
//!   device again. The rest of the operator's snapshot ([`BrokerHealth`]: what the log
//!   holds, who is attached, what is parked) is kept beside the log in `<log>.health`
//!   ([`OpenOptions::health_every`], [`Broker::keep_health`]), which another process
//!   reads with [`read_health`] and is told whether the broker that wrote it still serves
//!   the log.
//! - **FORK-DELIVERY and cognition routing** build on the same SUBSCRIBE primitive.
//! - **The durability dial**: Strict (a full flush per batch), Ordered (an ordering
//!   barrier per batch, `F_BARRIERFSYNC`: a power loss leaves a prefix of whole batches,
//!   the newest possibly lost and the loss announced; a full flush issued once a horizon
//!   has passed since the first ack none covers, so that ack is at most the horizon plus
//!   one batch and one full flush from stable media — and with no horizon, no age bounds
//!   the loss), Relaxed (page cache), and Replicated
//!   ([`Broker::open_replicated`]: an ack waits for a follower quorum). On Ordered and
//!   Relaxed an ESCALATION TABLE ([`Escalation`], in [`OpenOptions`]) names the records a
//!   person would miss: the broker holds them unseen and unacked until a full flush has
//!   made them durable, outside the log lock. Every `Mark` carries the durable head, and
//!   `Hello` the tier served ([`Broker::durable_head`], [`Client::seen_durable`],
//!   [`Client::served_durability`]).
//!   [`ShardedBroker`] runs N share-nothing partitions. Every batch is SEALED with its
//!   record count (its other records marked as continuing it) and every open records a
//!   durable floor, so after a power loss the log is a prefix of whole batches (Strict)
//!   or its longest intact prefix (Relaxed, with the loss announced by the generation)
//!   — no refusal for a torn write once a sealing build has opened it, but for the one
//!   residual [`Durability::Strict`] names. [`Broker::open_opts`] is the one open the
//!   other constructors are shorthands for.
//!
//! Everything is std-only (threads + `Mutex`/`Condvar` + sockets) over the
//! `astream_wire` codec; `forbid(unsafe)`. The default build has zero third-party
//! deps — the optional `cap` / `aead` features pull the vetted in-tree crypto crates.
//!
//! Honest boundary: delivery to the socket is ordered, gapless, and AT-LEAST-ONCE
//! (the consumer's cursor or a durable group commit makes it effectively exactly-once;
//! [`drain`] / [`take`] / [`ack`] are that inbox loop as library helpers).

// A contracted fn is written once, through `contract_fn!`: under a Trust compiler
// (`cfg(clean_islands)`, build.rs) it carries its `ensures` clause, which no stock rustc can
// parse, and every other compiler gets the plain fn.
#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

// Plain-Rust twins of the functions this crate's Clean islands compile, for a compiler
// that cannot lex the islands.
#[cfg(any(test, not(clean_islands)))]
mod twins;

#[cfg(test)]
mod append_tests;
pub mod brecord;
pub mod broker;
pub mod client;
/// Crash-safe, streaming compaction (the `retention` feature's rewrite of the log).
#[cfg(feature = "retention")]
mod compact;
#[cfg(test)]
mod crash_sim;
mod escalation;
pub mod failover;
pub mod federation;
pub mod health;
#[cfg(feature = "retention")]
mod held;
mod last_view;
pub use last_view::{
    last_view_available_advance, last_view_not_above_pub, last_view_not_before_avail,
    last_view_prune_clamp, last_view_prune_within_quantum, last_view_window_admits_code, LastStep,
    LastView, LastViewError, LastViewGarbage,
};
mod dedup;
pub mod logid;
#[cfg(feature = "relay")]
pub mod origin;
/// The power-loss model of a compaction's files, for its crash tests.
#[cfg(all(test, unix, feature = "retention"))]
mod power_loss;
pub mod proto;
mod recover;
pub mod refill;
mod relay_floor;
#[cfg(feature = "retention")]
pub mod retention;
pub mod sharded;
#[cfg(any(test, debug_assertions))]
mod sim_device;
pub mod sticky_fence;
mod storage;
pub mod store;
#[cfg(feature = "stream")]
mod stream_link;
mod tier;
#[cfg(test)]
mod tier_tests;

pub use astream_wire::{
    CausalCut, CausalEdge, CutViolation, FabricReceipt, ReceiptError, ReceiptVerdict, V1Receipt,
};
pub use brecord::{
    brecord_clamp_body_len, brecord_version_current, BrokerRecord, BREC_VERSION, COMMIT_TAG_RETIRE,
    MAX_RECORD_PAYLOAD, RETIRE_PRODUCER_SEQ,
};
pub use broker::{
    broker_batch_clamp, broker_wake_attempts_within_cap, identity_principal, rate_clock_advance,
    rate_tokens_clamp, rate_tokens_sufficient, tail_skip_clamp, tail_wake_head_advance,
    tail_wake_is_caught_up, Broker, BrokerHandle, BrokerStats, FollowerTransport, IDLE_MARK,
    IDLE_MARK_DEADLINE, KEEPALIVE_DEADLINE, KEEPALIVE_INTERVAL,
};
#[cfg(feature = "stream")]
pub use client::connect_stream;
pub use client::{
    ack, acks_owed, broker_refusal, client_walk_page_advance, client_walk_within_limit, connect,
    drain, protocol_mismatch, take, AcksOwed, AnyClient, AnyStream, AnySubscription, BrokerRefusal,
    Client, Closer, CreditWindow, Event, FreshPublish, Page, Pipelined, ProtocolMismatch, Record,
    StampedPage, StampedRecord, SubjectBudget, Subscription, SubscriptionCloser, Transport, Walk,
    ACK_SEQ_BASE, LAST_WALK_PAGES_MAX, MAX_FRESH_PIPELINE_BYTES,
};
pub use federation::{
    federation_cursor_advance, federation_hop_allowed, federation_incarnation_fresh,
    federation_route_preferred, federation_seq_clamp, parse_federation_rules, parse_rewrite_spec,
    FederatedCut, FederationBridge, FederationBridgeCloser, FederationConfig, FederationDirectory,
    FederationEndpoint, FederationError, FederationLink, FederationMesh, FederationMeshConfig,
    FederationMeshReport, FederationReport, FederationRule, FederationRunner,
    FederationRunnerCloser, FederationWire, PeerAdvertisement, PeerHealthState, PeerRouteEntry,
    PeerTransportKind, RegionRouteDecision, Seated, SubjectRewrite, DEFAULT_FEDERATION_BATCH,
    DEFAULT_PEER_REGISTRY_PREFIX, DEFAULT_ROUTE_HYSTERESIS_US, HELD_BYTES, HELD_CAP,
    MAX_FEDERATION_PEERS, MAX_FEDERATION_REGIONS, MAX_FEDERATION_RTT_US, MAX_FEDERATION_RULES,
    MAX_PEER_EXPORT_PREFIXES,
};
#[cfg(feature = "stream")]
pub use stream_link::{StreamDial, StreamLink};
/// What a log's residency tier did, counted: `Broker::tier_tally` reads it in a test or debug
/// build, and the type is compiled in every build so a caller names it rather than a copy.
pub use tier::TierTally;

/// Capability minting and principal derivation (`cap` feature), re-exported so
/// callers of [`Broker::open_guarded`] / [`Client::attach`] can mint and derive
/// producer IDs without depending on `astream-cap` directly.
#[cfg(feature = "cap")]
pub use astream_cap::{mint, producer_id_of, Capability};

#[cfg(all(feature = "identity", unix))]
pub use astream_aead::SshAgentServer;
/// External identity authority, CA certificate, rotation, trust-store, and `ssh-agent`
/// types (Rung 9), re-exported so callers of [`Broker::serve_tcp_certified`] /
/// [`Client::connect_tcp_certified`] can issue, rotate, and present certificates without
/// depending on `astream-aead` directly.
#[cfg(feature = "identity")]
pub use astream_aead::{
    CertRole, CertTrustStore, CertificateAuthority, HostCertRotator, IdentityCertificate,
    IdentitySigner, SharedCertTrust, SshAgentSigner, VerifiedPeerCert,
};
/// Static public-key identity types (Rung 8), re-exported so callers of
/// [`Broker::serve_tcp_identity`] / [`Client::connect_tcp_identity`] can build an
/// identity without depending on `astream-aead` directly.
#[cfg(feature = "identity")]
pub use astream_aead::{IdentityKeypair, ID_PUB_LEN};
/// Zero-gap AEAD-over-UDP roaming transport types (`AROM` v1), re-exported so
/// callers of [`Broker::serve_udp_roaming`] / [`Client::connect_udp_roaming`] can
/// migrate live sessions without depending on `astream-aead` directly.
#[cfg(feature = "handshake")]
pub use astream_aead::{
    RoamCloser, RoamHandle, RoamListener, RoamStream, ROAM_WIRE_MAGIC, ROAM_WIRE_VERSION,
};
#[cfg(feature = "retention")]
pub use broker::RETENTION_INTERVAL;
pub use escalation::{
    parse_escalation, parse_escalation_file, Escalate, Escalation, EscalationParseError,
    EscalationParseKind,
};
pub use failover::{
    elect_highest_candidate, failover_epoch_advance, failover_fences_stale, failover_lease_expired,
    failover_quorum_clamp, inspect_node_log, promote_replica_log, repair_follower_for_leader,
    ElectionCandidate, ElectionWinner, FailoverCluster, FailoverDaemon, FailoverDaemonCloser,
    FailoverEvent, FailoverLeaseConfig, FailoverNodeSpec, FailoverSnapshot, PromotedReplica,
    DEFAULT_FAILOVER_GUARD_BAND_MS, DEFAULT_FAILOVER_LEASE_TTL_MS, MAX_FAILOVER_CLUSTER_NODES,
    MAX_FAILOVER_EVENTS, MAX_FAILOVER_LEASE_TTL_MS,
};
pub use health::{
    health_path, read_health, BrokerHealth, HealthRead, HealthWriter, Residency, HEALTH_SUFFIX,
};
pub use logid::{
    identity_path, logid_generation_advance, logid_lineage_within_cap, Lineage, LogIdentity,
};
pub use proto::{
    AttachedProducerStats, FaceStats, Gap, HelloHealth, LogDevice, NonceExt, Request, Response,
    ServedInfo, ServedReason, Tier, WireStats, ERR_FRESH_FENCED, ERR_FRESH_HELD, ERR_RATE_LIMITED,
    ERR_RETIRE_REFUSED, HELLO_REASON_MAX, RATE_LIMITED_PREFIX, REQUEST_BROKER_TIMES,
    REQUEST_BURST_MARKS, REQUEST_FRESH_PUBLISH, REQUEST_GAP_FENCES, REQUEST_GAP_NOTICES,
    REQUEST_RELAY, REQUEST_RETIRE, REQUEST_SETTLE, REQUEST_STATS, REQUEST_TOLD_FETCH,
};
pub use recover::{recover_keep_within_len, recover_unit_start_advance};
pub use refill::{
    refill_cursor_at_least_oldest, refill_debt_clamp, refill_join_cursor_max, LaneSchedule,
    RefillStep, SharedRefillMeter, SharedRefillPlan, DEFAULT_REFILL_SPLIT_SLACK, MAX_REFILL_LANES,
    REFILL_ROW_COST,
};
#[cfg(feature = "retention")]
pub use retention::{parse_rule_line, parse_rules, record_bytes, Class, Keep, Retention, Rule};
pub use sharded::{sharded_clamp_index, sharded_count_nonzero, ShardedBroker, ShardedHandle};
#[cfg(unix)]
pub use sharded::{ShardedClient, ShardedEvent, ShardedSubscription};
#[cfg(any(test, debug_assertions))]
pub use sim_device::SimDevice;
pub use sticky_fence::{
    format_gap_fenced_msg, parse_gap_fenced_seq, sticky_fence_admits, sticky_fence_admits_code,
    sticky_fence_min_seq, sticky_fence_seq_allowed, sticky_fence_table_within_cap,
    StickyFenceTable, GAP_FENCED_PREFIX, MAX_STICKY_FENCES,
};
pub use storage::{storage_len_advance, storage_truncate_within_len};
#[cfg(feature = "anti-rollback")]
pub use store::AntiRollback;
#[cfg(feature = "retention")]
pub use store::RetentionTick;
#[cfg(all(feature = "at-rest", unix))]
pub use store::SealedLog;
pub use store::{
    at_rest_version_advance, at_rest_version_is_bound, broker_bt_advance, incarnation_base,
    incarnation_of, is_hidden_record, on_boot_volume, seal_path, store_ack_seq_in_reserved_half,
    store_head_advance, will_seq, Acks, Boot, BrokerLog, CheckedPublishError, Durability,
    FlushCounts, InjectedFaults, InterruptedStep, LogStats, OpenCheck, OpenOptions, Prepared,
    RateLimit, ToldPage, Volume, INC_MAX, MAX_RATE_BUDGET, ORDERED_HORIZON, RETIRE_SUBJECT,
    WILL_SEQ_LOW,
};

#[cfg(test)]
mod test_scratch;
