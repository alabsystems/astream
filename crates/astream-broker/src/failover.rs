// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Quorum leader election, epoch-fenced replica promotion, and divergent-follower rejoin
//! (`docs/ROADMAP.md` "replicated-tier failure-injection matrix").
//!
//! Coordinates multi-node failover over [`crate::BrokerLog`] and [`crate::Broker`]:
//!
//! 1. **Majority-quorum candidate election ([`elect_highest_candidate`]):** requires a
//!    strict majority (`cluster_size / 2 + 1`) of non-diverged cluster nodes, clamping vote
//!    counts through Clean-origin [`failover_quorum_clamp`] and selecting the candidate
//!    with the highest `(generation, head_offset)`.
//! 2. **Epoch-advancing replica promotion ([`promote_replica_log`]):** advances the
//!    cluster [`LogIdentity`] generation monotonically via Clean-origin
//!    [`failover_epoch_advance`], records a [`Lineage`] step `(new_generation, head_offset)`
//!    in `<log>.id` BEFORE removing `<log>.replica` so client cursors `< head_offset`
//!    continue seamlessly via [`LogIdentity::continues`], and ensures followers that adopt
//!    the new epoch immediately fence any deposed zombie leader via
//!    [`failover_fences_stale`].
//! 3. **Divergent-tail truncation & follower rejoin ([`repair_follower_for_leader`]):**
//!    converts a deposed leader or divergent follower into a clean replica truncated back
//!    to the common committed prefix so [`crate::Broker::rejoin_followers`] catches it up.

use crate::logid::{Lineage, LogIdentity};
use crate::store::BrokerLog;
use astream_wire::Offset;
use std::io;
use std::path::Path;

#[cfg(clean_islands)]
#[path = "failover_island.rs"]
mod failover_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{failover_epoch_advance, failover_quorum_clamp};
#[cfg(clean_islands)]
pub use failover_island::{failover_epoch_advance, failover_quorum_clamp};

contract_fn! {
    /// Verified check that a replicated record's leader generation `leader_gen` is stale
    /// relative to a replica's adopted generation `adopted_gen` (`leader_gen < adopted_gen`),
    /// linked via `clean-kernel-defeq` to `failover_fences_stale_isl`.
    #[must_use]
    pub const fn failover_fences_stale(leader_gen: u64, adopted_gen: u64) -> bool
    clauses [ensures result == (leader_gen < adopted_gen)]
    {
        leader_gen < adopted_gen
    }
}

/// Durable log snapshot of one cluster node participating in a failover election.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ElectionCandidate {
    /// Node index within `0..cluster_size`.
    pub node_id: usize,
    /// Node's settled [`LogIdentity`] on disk.
    pub identity: LogIdentity,
    /// Node's durable `head` offset (`next`).
    pub head_offset: u64,
    /// Node's retention `base` offset.
    pub base_offset: u64,
    /// Whether the node's replica log was marked diverged during replication.
    pub diverged: bool,
}

/// Result of a majority-quorum leader election ([`elect_highest_candidate`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ElectionWinner {
    /// Winning node index (`0..cluster_size`).
    pub node_id: usize,
    /// Winning node's durable `head` offset.
    pub head_offset: u64,
    /// Winning node's retention `base` offset.
    pub base_offset: u64,
    /// Highest `(id, generation)` epoch observed across the quorum for the winning spine.
    pub highest_epoch: LogIdentity,
    /// Clamped count of eligible quorum votes (`<= cluster_size`).
    pub quorum_votes: u64,
    /// Required strict majority (`cluster_size / 2 + 1`).
    pub required_quorum: u64,
}

/// Outcome of promoting a replica log to cluster leader ([`promote_replica_log`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PromotedReplica {
    /// Promoted leader's new [`LogIdentity`] (`generation` strictly advanced when `head > 0`).
    pub identity: LogIdentity,
    /// Promoted leader's [`Lineage`] (carrying `(new_generation, head_offset)`).
    pub lineage: Lineage,
    /// Durable `head` offset at promotion time.
    pub head_offset: u64,
    /// Durable retention `base` offset at promotion time.
    pub base_offset: u64,
}

/// Select the most up-to-date leader candidate from a strict majority quorum
/// (`cluster_size / 2 + 1`) of distinct, non-diverged nodes in `0..cluster_size`.
///
/// Candidates are ranked lexicographically by `(identity.generation, head_offset)`,
/// breaking ties by lowest `node_id`.
pub fn elect_highest_candidate(
    cluster_size: usize,
    candidates: &[ElectionCandidate],
) -> Result<ElectionWinner, String> {
    if cluster_size == 0 || cluster_size > 1024 {
        return Err(format!(
            "invalid cluster_size {cluster_size}: expected 1..=1024"
        ));
    }
    let mut seen = Vec::new();
    let mut s = 0usize;
    while s < cluster_size {
        seen.push(false);
        s = s.saturating_add(1);
    }

    let mut eligible_votes = 0u64;
    let mut best: Option<ElectionCandidate> = None;

    let mut i = 0usize;
    while i < candidates.len() {
        let Some(&cand) = candidates.get(i) else {
            break;
        };
        i = i.saturating_add(1);
        if cand.node_id >= cluster_size {
            return Err(format!(
                "candidate node_id {} out of range for cluster_size {cluster_size}",
                cand.node_id
            ));
        }
        if seen.get(cand.node_id).copied().unwrap_or(true) {
            return Err(format!(
                "duplicate election candidate node_id {}",
                cand.node_id
            ));
        }
        if let Some(slot) = seen.get_mut(cand.node_id) {
            *slot = true;
        }
        if cand.diverged {
            continue;
        }
        eligible_votes = eligible_votes.saturating_add(1);
        let replace = match best {
            None => true,
            Some(cur) => {
                if cand.identity.generation != cur.identity.generation {
                    cand.identity.generation > cur.identity.generation
                } else if cand.head_offset != cur.head_offset {
                    cand.head_offset > cur.head_offset
                } else {
                    cand.node_id < cur.node_id
                }
            }
        };
        if replace {
            best = Some(cand);
        }
    }

    let cluster_u64 = cluster_size as u64;
    let quorum_votes = failover_quorum_clamp(eligible_votes, cluster_u64);
    let required_quorum = (cluster_u64 / 2).saturating_add(1);
    if quorum_votes < required_quorum {
        return Err(format!(
            "insufficient quorum: {quorum_votes} eligible node(s) reachable, need {required_quorum} of {cluster_size}"
        ));
    }

    let Some(winner) = best else {
        return Err("no eligible candidate in quorum".to_string());
    };

    // Track the highest generation across any quorum member sharing the winner's log id.
    let mut max_gen = winner.identity.generation;
    let mut j = 0usize;
    while j < candidates.len() {
        let Some(&cand) = candidates.get(j) else {
            break;
        };
        j = j.saturating_add(1);
        if !cand.diverged && cand.identity.id == winner.identity.id {
            max_gen = failover_epoch_advance(max_gen, cand.identity.generation);
        }
    }

    Ok(ElectionWinner {
        node_id: winner.node_id,
        head_offset: winner.head_offset,
        base_offset: winner.base_offset,
        highest_epoch: LogIdentity {
            id: winner.identity.id,
            generation: max_gen,
        },
        quorum_votes,
        required_quorum,
    })
}

fn open_stopped_strict_cold(log_path: &Path) -> io::Result<BrokerLog> {
    BrokerLog::open_opts(
        log_path,
        crate::OpenOptions::new(crate::Durability::Strict).with_resident_budget(0),
        BrokerLog::prepare_nothing,
    )
}

/// Inspect a stopped node log at `log_path` under `Strict` durability and return its
/// [`ElectionCandidate`] state for [`elect_highest_candidate`].
pub fn inspect_node_log(node_id: usize, log_path: &Path) -> io::Result<ElectionCandidate> {
    let mut log = open_stopped_strict_cold(log_path)?;
    let cand = ElectionCandidate {
        node_id,
        identity: log.identity(),
        head_offset: log.head().0,
        base_offset: log.base().0,
        diverged: log.is_diverged(),
    };
    log.close_clean()?;
    Ok(cand)
}

/// Promote a stopped replica log at `log_path` to become the new cluster leader:
///
/// - Verifies the log is currently a declared replica (`<log>.replica`) and not diverged.
/// - Advances `<log>.id` generation monotonically past `min_cluster_epoch` (and records a
///   [`Lineage`] step `(new_generation, head)` when `head > 0`), durably flushing both
///   `<log>` and `<log>.id` BEFORE removing `<log>.replica`.
/// - Closes the log cleanly so [`crate::Broker::open_replicated`] immediately serves the
///   new leader epoch.
pub fn promote_replica_log(
    log_path: &Path,
    min_cluster_epoch: Option<LogIdentity>,
) -> io::Result<PromotedReplica> {
    let mut log = open_stopped_strict_cold(log_path)?;
    let (identity, lineage) = log.promote_replica(min_cluster_epoch)?;
    let head_offset = log.head().0;
    let base_offset = log.base().0;
    log.close_clean()?;
    Ok(PromotedReplica {
        identity,
        lineage,
        head_offset,
        base_offset,
    })
}

/// Prepare a stopped follower (or deposed ex-leader) log at `follower_log_path` to rejoin
/// under a promoted leader whose fork point is at `common_head`:
///
/// - Ensures `<log>.replica` is durably declared (`declare_replica`) so a deposed leader
///   never fires local wills on reopen.
/// - If `log.head() > common_head` (e.g. uncommitted/unquorumed split-brain tail records
///   written before failover) or if the replica was flagged diverged, truncates the tail
///   cleanly to `common_head` via [`BrokerLog::truncate_replica_to`].
///
/// Returns the number of dropped tail records.
pub fn repair_follower_for_leader(
    follower_log_path: &Path,
    common_head: Offset,
) -> io::Result<u64> {
    let mut log = open_stopped_strict_cold(follower_log_path)?;
    if !log.is_replica() {
        log.declare_replica()?;
    }
    let cur_head = log.head();
    let dropped = if cur_head.0 > common_head.0 {
        log.truncate_replica_to(common_head)?
    } else {
        0
    };
    log.close_clean()?;
    Ok(dropped)
}

/// Maximum nodes supported by [`FailoverCluster`] and [`FailoverDaemon`].
pub const MAX_FAILOVER_CLUSTER_NODES: usize = 16;

/// Maximum leader-lease TTL or guard band (`60_000` ms) enforced via [`failover_quorum_clamp`].
pub const MAX_FAILOVER_LEASE_TTL_MS: u64 = 60_000;

/// Default leader-lease TTL (`1_500` ms).
pub const DEFAULT_FAILOVER_LEASE_TTL_MS: u64 = 1_500;

/// Default post-TTL election guard band (`250` ms).
pub const DEFAULT_FAILOVER_GUARD_BAND_MS: u64 = 250;

/// Maximum recent [`FailoverEvent`] entries retained in [`FailoverDaemon`].
pub const MAX_FAILOVER_EVENTS: usize = 256;

contract_fn! {
    /// Verified check that a monotonic clock sample `now_ms` has reached or passed
    /// `threshold_ms` (`lease_deadline_ms + guard_band_ms`), linked via
    /// `clean-kernel-defeq` to `failover_lease_expired_isl`.
    #[must_use]
    pub const fn failover_lease_expired(now_ms: u64, threshold_ms: u64) -> bool
    clauses [ensures result == (threshold_ms <= now_ms)]
    {
        threshold_ms <= now_ms
    }
}

/// Lease-heartbeat, probe-timeout, and replica-rejoin policy for [`FailoverCluster`]
/// and [`FailoverDaemon`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FailoverLeaseConfig {
    /// Monotonic leader-lease TTL in milliseconds (`1..=MAX_FAILOVER_LEASE_TTL_MS`).
    pub lease_ttl_ms: u64,
    /// Additional guard band in milliseconds (`0..=MAX_FAILOVER_LEASE_TTL_MS`) after
    /// `lease_deadline_ms` before triggering an autonomous quorum election.
    pub guard_band_ms: u64,
    /// Background daemon heartbeat poll interval.
    pub heartbeat_interval: std::time::Duration,
    /// Per-connect/read/write TCP `Hello` probe timeout against the active leader.
    pub probe_timeout: std::time::Duration,
    /// Per-follower replication round-trip timeout passed to [`crate::Broker::open_replicated_with`].
    pub follower_timeout: std::time::Duration,
    /// Automatically truncate and rejoin deposed ex-leaders once their log lock is released.
    pub auto_rejoin_deposed: bool,
}

impl Default for FailoverLeaseConfig {
    fn default() -> Self {
        Self::new(
            DEFAULT_FAILOVER_LEASE_TTL_MS,
            DEFAULT_FAILOVER_GUARD_BAND_MS,
        )
    }
}

impl FailoverLeaseConfig {
    /// Construct a bounded lease configuration, clamping `lease_ttl_ms` into
    /// `1..=MAX_FAILOVER_LEASE_TTL_MS` and `guard_band_ms` into `0..=MAX_FAILOVER_LEASE_TTL_MS`
    /// via Clean-origin [`failover_quorum_clamp`].
    #[must_use]
    pub const fn new(lease_ttl_ms: u64, guard_band_ms: u64) -> Self {
        let clamped_ttl = failover_quorum_clamp(lease_ttl_ms, MAX_FAILOVER_LEASE_TTL_MS);
        let ttl = if clamped_ttl < 1 { 1 } else { clamped_ttl };
        let guard = failover_quorum_clamp(guard_band_ms, MAX_FAILOVER_LEASE_TTL_MS);
        Self {
            lease_ttl_ms: ttl,
            guard_band_ms: guard,
            heartbeat_interval: std::time::Duration::from_millis(200),
            probe_timeout: std::time::Duration::from_millis(300),
            follower_timeout: std::time::Duration::from_millis(1_200),
            auto_rejoin_deposed: true,
        }
    }

    /// Set the background daemon heartbeat interval (clamped to `>= 1ms`).
    #[must_use]
    pub const fn with_heartbeat_interval(mut self, interval: std::time::Duration) -> Self {
        if interval.is_zero() {
            self.heartbeat_interval = std::time::Duration::from_millis(1);
        } else {
            self.heartbeat_interval = interval;
        }
        self
    }

    /// Set the TCP `Hello` probe timeout (clamped to `>= 1ms`).
    #[must_use]
    pub const fn with_probe_timeout(mut self, timeout: std::time::Duration) -> Self {
        if timeout.is_zero() {
            self.probe_timeout = std::time::Duration::from_millis(1);
        } else {
            self.probe_timeout = timeout;
        }
        self
    }

    /// Set the per-follower replication round-trip timeout (clamped to `>= 1ms`).
    #[must_use]
    pub const fn with_follower_timeout(mut self, timeout: std::time::Duration) -> Self {
        if timeout.is_zero() {
            self.follower_timeout = std::time::Duration::from_millis(1);
        } else {
            self.follower_timeout = timeout;
        }
        self
    }

    /// Enable or disable automatic tail-repair and replica rejoin of deposed leaders.
    #[must_use]
    pub const fn with_auto_rejoin_deposed(mut self, enabled: bool) -> Self {
        self.auto_rejoin_deposed = enabled;
        self
    }
}

/// Durable log path and TCP bind address for one node in a [`FailoverCluster`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FailoverNodeSpec {
    /// Path to this node's durable [`BrokerLog`].
    pub log_path: std::path::PathBuf,
    /// Initial TCP bind address (`127.0.0.1:0` allocates an ephemeral loopback port that is
    /// remembered and reused across promotions and replica rejoins).
    pub bind_addr: std::net::SocketAddr,
}

impl FailoverNodeSpec {
    /// Construct a node specification with an explicit TCP bind address.
    #[must_use]
    pub fn new(log_path: std::path::PathBuf, bind_addr: std::net::SocketAddr) -> Self {
        Self {
            log_path,
            bind_addr,
        }
    }

    /// Construct a loopback node specification on an OS-assigned ephemeral port (`127.0.0.1:0`).
    #[must_use]
    pub fn loopback_ephemeral(log_path: std::path::PathBuf) -> Self {
        Self {
            log_path,
            bind_addr: std::net::SocketAddr::from(([127, 0, 0, 1], 0)),
        }
    }
}

/// Transition emitted by [`FailoverCluster::tick_at`] and recorded by [`FailoverDaemon`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FailoverEvent {
    /// Active leader answered a live TCP `Hello` probe unpoisoned at its expected epoch.
    HeartbeatRenewed {
        leader_node: usize,
        identity: LogIdentity,
        lease_deadline_ms: u64,
    },
    /// Active leader failed a live TCP `Hello` probe (unreachable, poisoned, or epoch mismatch).
    ProbeFailed {
        leader_node: usize,
        consecutive_failures: u64,
        lease_deadline_ms: u64,
        reason: String,
    },
    /// Lease expired past `lease_deadline_ms + guard_band_ms` and a surviving majority quorum
    /// elected and promoted `new_leader` to `identity`.
    Promoted {
        old_leader: usize,
        new_leader: usize,
        identity: LogIdentity,
        lineage: Lineage,
        fork_head_offset: u64,
        quorum_votes: u64,
    },
    /// A deposed or stopped node had any divergent tail truncated back to the fork point,
    /// reopened as a declared replica, and rejoined the active leader's replication quorum.
    FollowerRejoined {
        node_id: usize,
        dropped_tail_records: u64,
        rejoined_links: usize,
    },
    /// Lease expired, but fewer than `cluster_size / 2 + 1` non-diverged replicas were reachable.
    QuorumUnavailable { old_leader: usize, reason: String },
}

/// Point-in-time operational snapshot of [`FailoverCluster`] / [`FailoverDaemon`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FailoverSnapshot {
    /// Currently active leader node index (`0..cluster_size`).
    pub leader_node: usize,
    /// Bound TCP address of the currently active leader.
    pub leader_addr: std::net::SocketAddr,
    /// Settled [`LogIdentity`] `(id, generation)` of the currently active leader.
    pub leader_identity: LogIdentity,
    /// [`Lineage`] steps accumulated at the latest leader promotion.
    pub leader_lineage: Lineage,
    /// Current monotonic leader-lease deadline in milliseconds.
    pub lease_deadline_ms: u64,
    /// Total successful TCP leader heartbeat renewals.
    pub heartbeat_renewals: u64,
    /// Consecutive failed TCP leader probes since the last renewal or promotion.
    pub consecutive_probe_failures: u64,
    /// Total autonomous replica-to-leader promotions completed.
    pub promotions: u64,
    /// Total deposed/stopped nodes repaired and rejoined as replicas.
    pub rejoined_nodes: u64,
    /// Assigned TCP addresses of all cluster nodes (`0..cluster_size`).
    pub node_addrs: Vec<std::net::SocketAddr>,
    /// Which cluster nodes currently have a live managed [`crate::Broker`] + TCP listener.
    pub node_live: Vec<bool>,
}

struct ManagedNode {
    broker: crate::Broker,
    handle: crate::BrokerHandle,
}

impl ManagedNode {
    fn shutdown(mut self) {
        self.handle.shutdown();
        drop(self.broker);
    }
}

fn parse_bound_socket_addr(handle: &crate::BrokerHandle) -> io::Result<std::net::SocketAddr> {
    let Some(raw) = handle.tcp_addr() else {
        return Err(io::Error::other("TCP BrokerHandle missing tcp_addr"));
    };
    match raw.parse::<std::net::SocketAddr>() {
        Ok(addr) => Ok(addr),
        Err(e) => Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("invalid bound TCP SocketAddr {raw:?}: {e}"),
        )),
    }
}

fn serve_node_tcp(
    broker: &crate::Broker,
    addr: std::net::SocketAddr,
) -> io::Result<(crate::BrokerHandle, std::net::SocketAddr)> {
    let mut attempt = 0u32;
    loop {
        match broker.serve_tcp(addr) {
            Ok(handle) => {
                let bound = parse_bound_socket_addr(&handle)?;
                return Ok((handle, bound));
            }
            Err(e) => {
                attempt = attempt.saturating_add(1);
                if e.kind() == io::ErrorKind::AddrInUse && attempt < 5 {
                    std::thread::sleep(std::time::Duration::from_millis(5));
                    continue;
                }
                return Err(e);
            }
        }
    }
}

fn probe_leader_tcp(
    addr: &std::net::SocketAddr,
    timeout: std::time::Duration,
    expected_identity: LogIdentity,
) -> Result<(), String> {
    let stream = match std::net::TcpStream::connect_timeout(addr, timeout) {
        Ok(s) => s,
        Err(e) => return Err(format!("leader TCP connect {addr} failed: {e}")),
    };
    let _ = stream.set_nodelay(true);
    let _ = stream.set_read_timeout(Some(timeout));
    let _ = stream.set_write_timeout(Some(timeout));
    let mut client = crate::Client::from_stream(stream);
    let got_id = match client.log_identity() {
        Ok(Some(id)) => id,
        Ok(None) => return Err("leader Hello carried no LogIdentity".to_string()),
        Err(e) => return Err(format!("leader Hello failed: {e}")),
    };
    if let Some(health) = client.broker_health() {
        if let Some(ref reason) = health.poisoned {
            return Err(format!("leader log is poisoned: {reason}"));
        }
    }
    if got_id != expected_identity {
        return Err(format!(
            "leader LogIdentity mismatch: expected {expected_identity:?}, got {got_id:?}"
        ));
    }
    Ok(())
}

#[allow(clippy::manual_unwrap_or)]
fn monotonic_clock_ms(origin: &std::time::Instant) -> u64 {
    let elapsed = origin.elapsed().as_millis();
    let clamped = match u64::try_from(elapsed) {
        Ok(ms) => ms,
        Err(_) => u64::MAX / 2,
    };
    1_000u64.saturating_add(clamped)
}

/// Deterministic lease-heartbeat replicated cluster controller driving live TCP leader probes,
/// guard-band lease expiry ([`failover_lease_expired`]), majority-quorum candidate election
/// ([`elect_highest_candidate`]), epoch-advancing replica promotion ([`promote_replica_log`]),
/// and automatic divergent-tail truncation + replica rejoin ([`repair_follower_for_leader`]).
pub struct FailoverCluster {
    specs: Vec<FailoverNodeSpec>,
    assigned_addrs: Vec<std::net::SocketAddr>,
    live: Vec<Option<ManagedNode>>,
    node_offline: Vec<bool>,
    pending_rejoin: Vec<Option<Offset>>,
    leader_node: usize,
    leader_identity: LogIdentity,
    leader_lineage: Lineage,
    config: FailoverLeaseConfig,
    clock_origin: std::time::Instant,
    lease_deadline_ms: u64,
    heartbeat_renewals: u64,
    consecutive_probe_failures: u64,
    promotions: u64,
    rejoined_nodes: u64,
}

#[allow(clippy::manual_range_contains, clippy::manual_unwrap_or)]
impl FailoverCluster {
    /// Open an `N`-node (`3..=MAX_FAILOVER_CLUSTER_NODES`) replicated cluster with
    /// `initial_leader` serving [`crate::Broker::open_replicated_with`] and all other nodes serving
    /// declared [`crate::Broker::open_replica`] TCP listeners.
    pub fn open(
        specs: Vec<FailoverNodeSpec>,
        initial_leader: usize,
        config: FailoverLeaseConfig,
    ) -> io::Result<Self> {
        let count = specs.len();
        if count < 3 || count > MAX_FAILOVER_CLUSTER_NODES {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!(
                    "FailoverCluster requires 3..={MAX_FAILOVER_CLUSTER_NODES} nodes, got {count}"
                ),
            ));
        }
        if initial_leader >= count {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("initial_leader {initial_leader} out of range for {count} nodes"),
            ));
        }

        let placeholder_addr = std::net::SocketAddr::from(([127, 0, 0, 1], 0));
        let mut assigned_addrs = Vec::with_capacity(count);
        let mut live: Vec<Option<ManagedNode>> = Vec::with_capacity(count);
        let mut node_offline = Vec::with_capacity(count);
        let mut pending_rejoin = Vec::with_capacity(count);
        let mut idx = 0usize;
        while idx < count {
            assigned_addrs.push(placeholder_addr);
            live.push(None);
            node_offline.push(false);
            pending_rejoin.push(None);
            idx = idx.saturating_add(1);
        }

        // First open and bind every follower replica so the initial leader can sync to them at open.
        let mut j = 0usize;
        while j < count {
            if j != initial_leader {
                let Some(spec) = specs.get(j) else {
                    break;
                };
                let broker = match crate::Broker::open_replica(&spec.log_path) {
                    Ok(b) => b,
                    Err(e) => {
                        shutdown_partial_nodes(&mut live);
                        return Err(e);
                    }
                };
                let (handle, bound) = match serve_node_tcp(&broker, spec.bind_addr) {
                    Ok(pair) => pair,
                    Err(e) => {
                        drop(broker);
                        shutdown_partial_nodes(&mut live);
                        return Err(e);
                    }
                };
                if let Some(slot) = assigned_addrs.get_mut(j) {
                    *slot = bound;
                }
                if let Some(slot) = live.get_mut(j) {
                    *slot = Some(ManagedNode { broker, handle });
                }
            }
            j = j.saturating_add(1);
        }

        let follower_addrs = collect_follower_addrs(&assigned_addrs, initial_leader);
        let follower_quorum = count / 2;
        let Some(leader_spec) = specs.get(initial_leader) else {
            shutdown_partial_nodes(&mut live);
            return Err(io::Error::other("missing initial_leader spec"));
        };
        let leader_broker = match crate::Broker::open_replicated_with(
            &leader_spec.log_path,
            &follower_addrs,
            follower_quorum,
            config.follower_timeout,
        ) {
            Ok(b) => b,
            Err(e) => {
                shutdown_partial_nodes(&mut live);
                return Err(e);
            }
        };
        let leader_identity = leader_broker.log_identity();
        let (leader_handle, leader_bound) =
            match serve_node_tcp(&leader_broker, leader_spec.bind_addr) {
                Ok(pair) => pair,
                Err(e) => {
                    drop(leader_broker);
                    shutdown_partial_nodes(&mut live);
                    return Err(e);
                }
            };
        if let Some(slot) = assigned_addrs.get_mut(initial_leader) {
            *slot = leader_bound;
        }
        if let Some(slot) = live.get_mut(initial_leader) {
            *slot = Some(ManagedNode {
                broker: leader_broker,
                handle: leader_handle,
            });
        }

        let clock_origin = std::time::Instant::now();
        let now_ms = monotonic_clock_ms(&clock_origin);
        let lease_deadline_ms =
            failover_epoch_advance(0, now_ms.saturating_add(config.lease_ttl_ms));

        Ok(Self {
            specs,
            assigned_addrs,
            live,
            node_offline,
            pending_rejoin,
            leader_node: initial_leader,
            leader_identity,
            leader_lineage: Lineage::default(),
            config,
            clock_origin,
            lease_deadline_ms,
            heartbeat_renewals: 0,
            consecutive_probe_failures: 0,
            promotions: 0,
            rejoined_nodes: 0,
        })
    }

    /// Current cluster configuration.
    #[must_use]
    pub const fn config(&self) -> &FailoverLeaseConfig {
        &self.config
    }

    /// Active leader node index (`0..cluster_size`).
    #[must_use]
    pub const fn leader_node(&self) -> usize {
        self.leader_node
    }

    /// Bound TCP [`std::net::SocketAddr`] of the active leader.
    #[must_use]
    pub fn leader_addr(&self) -> std::net::SocketAddr {
        match self.assigned_addrs.get(self.leader_node) {
            Some(&addr) => addr,
            None => std::net::SocketAddr::from(([127, 0, 0, 1], 0)),
        }
    }

    /// Active leader [`LogIdentity`].
    #[must_use]
    pub const fn leader_identity(&self) -> LogIdentity {
        self.leader_identity
    }

    /// [`Lineage`] recorded at the latest leader promotion.
    #[must_use]
    pub const fn leader_lineage(&self) -> &Lineage {
        &self.leader_lineage
    }

    /// Borrow a live node's in-process [`crate::Broker`] if currently running.
    #[must_use]
    pub fn node_broker(&self, node_id: usize) -> Option<&crate::Broker> {
        match self.live.get(node_id) {
            Some(Some(node)) => Some(&node.broker),
            _ => None,
        }
    }

    /// Point-in-time operational snapshot of the cluster.
    #[must_use]
    pub fn snapshot(&self) -> FailoverSnapshot {
        let mut node_live = Vec::new();
        let mut i = 0usize;
        while i < self.live.len() {
            let is_up = matches!(self.live.get(i), Some(Some(_)));
            node_live.push(is_up);
            i = i.saturating_add(1);
        }
        FailoverSnapshot {
            leader_node: self.leader_node,
            leader_addr: self.leader_addr(),
            leader_identity: self.leader_identity,
            leader_lineage: self.leader_lineage.clone(),
            lease_deadline_ms: self.lease_deadline_ms,
            heartbeat_renewals: self.heartbeat_renewals,
            consecutive_probe_failures: self.consecutive_probe_failures,
            promotions: self.promotions,
            rejoined_nodes: self.rejoined_nodes,
            node_addrs: self.assigned_addrs.clone(),
            node_live,
        }
    }

    /// Crash / power-off `node_id`: shuts down its managed TCP listener, drops its in-process
    /// [`crate::Broker`], and marks the host powered-off until [`Self::restore_node_power`].
    /// If `node_id` was a follower, queues it for replica rejoin once power returns.
    pub fn crash_node(&mut self, node_id: usize) -> bool {
        if node_id >= self.specs.len() {
            return false;
        }
        let mut stopped = false;
        let mut last_head = 0u64;
        if let Some(slot) = self.live.get_mut(node_id) {
            if let Some(node) = slot.take() {
                last_head = node.broker.visible_head();
                node.shutdown();
                stopped = true;
            }
        }
        if let Some(off_flag) = self.node_offline.get_mut(node_id) {
            *off_flag = true;
        }
        if node_id != self.leader_node {
            if let Some(rejoin_slot) = self.pending_rejoin.get_mut(node_id) {
                if rejoin_slot.is_none() {
                    *rejoin_slot = Some(Offset(last_head));
                }
            }
        }
        stopped
    }

    /// Restore host power for `node_id` after [`Self::crash_node`], allowing pending replica
    /// repair and quorum rejoin on the next tick.
    pub fn restore_node_power(&mut self, node_id: usize) -> bool {
        let Some(off_flag) = self.node_offline.get_mut(node_id) else {
            return false;
        };
        let was_offline = *off_flag;
        *off_flag = false;
        was_offline
    }

    /// Partition ONLY the current leader's managed TCP listener while returning its live
    /// [`crate::Broker`] to the caller: if the caller also holds a secondary listener (e.g.
    /// via `Broker::serve`), the deposed leader remains a live split-brain zombie
    /// holding its log lock until the caller drops both the secondary handle and returned
    /// [`crate::Broker`].
    pub fn partition_leader_tcp(&mut self) -> Option<crate::Broker> {
        let slot = self.live.get_mut(self.leader_node)?;
        let mut managed = slot.take()?;
        managed.handle.shutdown();
        Some(managed.broker)
    }

    /// Advance one heartbeat / failover / rejoin cycle using the cluster's monotonic clock.
    pub fn tick_now(&mut self) -> Vec<FailoverEvent> {
        let now_ms = monotonic_clock_ms(&self.clock_origin);
        self.tick_at(now_ms)
    }

    /// Advance one deterministic heartbeat / failover / rejoin cycle at monotonic timestamp `now_ms`.
    pub fn tick_at(&mut self, now_ms: u64) -> Vec<FailoverEvent> {
        let mut events = Vec::new();
        if self.config.auto_rejoin_deposed {
            self.try_rejoin_pending(&mut events);
        }
        let leader_addr = self.leader_addr();
        match probe_leader_tcp(
            &leader_addr,
            self.config.probe_timeout,
            self.leader_identity,
        ) {
            Ok(()) => {
                self.consecutive_probe_failures = 0;
                self.heartbeat_renewals = self.heartbeat_renewals.saturating_add(1);
                let next_deadline = now_ms.saturating_add(self.config.lease_ttl_ms);
                self.lease_deadline_ms =
                    failover_epoch_advance(self.lease_deadline_ms, next_deadline);
                events.push(FailoverEvent::HeartbeatRenewed {
                    leader_node: self.leader_node,
                    identity: self.leader_identity,
                    lease_deadline_ms: self.lease_deadline_ms,
                });
            }
            Err(reason) => {
                self.consecutive_probe_failures = self.consecutive_probe_failures.saturating_add(1);
                events.push(FailoverEvent::ProbeFailed {
                    leader_node: self.leader_node,
                    consecutive_failures: self.consecutive_probe_failures,
                    lease_deadline_ms: self.lease_deadline_ms,
                    reason,
                });
                let threshold = self
                    .lease_deadline_ms
                    .saturating_add(self.config.guard_band_ms);
                if failover_lease_expired(now_ms, threshold) {
                    let outcome = self.promote_on_expired_lease(now_ms);
                    let promoted_ok = matches!(outcome, FailoverEvent::Promoted { .. });
                    events.push(outcome);
                    if promoted_ok && self.config.auto_rejoin_deposed {
                        self.try_rejoin_pending(&mut events);
                    }
                }
            }
        }
        events
    }

    fn promote_on_expired_lease(&mut self, now_ms: u64) -> FailoverEvent {
        let old_leader = self.leader_node;
        let count = self.specs.len();
        let mut candidates = Vec::new();
        let mut j = 0usize;
        while j < count {
            if j != old_leader {
                let offline = self.node_offline.get(j).copied().unwrap_or(true);
                if !offline {
                    if let Some(Some(node)) = self.live.get(j) {
                        candidates.push(ElectionCandidate {
                            node_id: j,
                            identity: node.broker.log_identity(),
                            head_offset: node.broker.head(),
                            base_offset: node.broker.base(),
                            diverged: node.broker.is_diverged(),
                        });
                    }
                }
            }
            j = j.saturating_add(1);
        }

        let winner = match elect_highest_candidate(count, &candidates) {
            Ok(w) => w,
            Err(reason) => return FailoverEvent::QuorumUnavailable { old_leader, reason },
        };
        let new_leader = winner.node_id;

        let Some(winner_spec) = self.specs.get(new_leader) else {
            return FailoverEvent::QuorumUnavailable {
                old_leader,
                reason: "missing winning candidate spec".to_string(),
            };
        };
        let winner_log_path = winner_spec.log_path.clone();
        let Some(&winner_bind_addr) = self.assigned_addrs.get(new_leader) else {
            return FailoverEvent::QuorumUnavailable {
                old_leader,
                reason: "missing winning candidate address".to_string(),
            };
        };

        // Release only the winning replica's BrokerLog lock while keeping other followers live.
        if let Some(slot) = self.live.get_mut(new_leader) {
            if let Some(node) = slot.take() {
                node.shutdown();
            }
        }

        let promoted = match promote_replica_log(&winner_log_path, Some(winner.highest_epoch)) {
            Ok(p) => p,
            Err(e) => {
                // Best-effort reopen as replica so the node is not stranded offline.
                if let Ok(rep) = crate::Broker::open_replica(&winner_log_path) {
                    if let Ok((handle, bound)) = serve_node_tcp(&rep, winner_bind_addr) {
                        if let Some(a) = self.assigned_addrs.get_mut(new_leader) {
                            *a = bound;
                        }
                        if let Some(slot) = self.live.get_mut(new_leader) {
                            *slot = Some(ManagedNode {
                                broker: rep,
                                handle,
                            });
                        }
                    }
                }
                return FailoverEvent::QuorumUnavailable {
                    old_leader,
                    reason: format!("promote_replica_log failed on node {new_leader}: {e}"),
                };
            }
        };

        let follower_addrs = collect_follower_addrs(&self.assigned_addrs, new_leader);
        let follower_quorum = count / 2;
        let leader_broker = match crate::Broker::open_replicated_with(
            &winner_log_path,
            &follower_addrs,
            follower_quorum,
            self.config.follower_timeout,
        ) {
            Ok(b) => b,
            Err(e) => {
                return FailoverEvent::QuorumUnavailable {
                    old_leader,
                    reason: format!(
                        "open_replicated_with failed on promoted node {new_leader}: {e}"
                    ),
                };
            }
        };
        let (leader_handle, leader_bound) = match serve_node_tcp(&leader_broker, winner_bind_addr) {
            Ok(pair) => pair,
            Err(e) => {
                drop(leader_broker);
                return FailoverEvent::QuorumUnavailable {
                    old_leader,
                    reason: format!("serve_tcp failed on promoted node {new_leader}: {e}"),
                };
            }
        };
        if let Some(a) = self.assigned_addrs.get_mut(new_leader) {
            *a = leader_bound;
        }
        if let Some(slot) = self.live.get_mut(new_leader) {
            *slot = Some(ManagedNode {
                broker: leader_broker,
                handle: leader_handle,
            });
        }

        // If the deposed leader was still managed in-process (e.g. poisoned), stop it so its log
        // lock releases cleanly for replica repair and rejoin.
        if let Some(old_slot) = self.live.get_mut(old_leader) {
            if let Some(old_node) = old_slot.take() {
                old_node.shutdown();
            }
        }
        if let Some(rejoin_slot) = self.pending_rejoin.get_mut(old_leader) {
            *rejoin_slot = Some(Offset(promoted.head_offset));
        }

        self.leader_node = new_leader;
        self.leader_identity = promoted.identity;
        self.leader_lineage = promoted.lineage.clone();
        self.consecutive_probe_failures = 0;
        self.promotions = self.promotions.saturating_add(1);
        let next_deadline = now_ms.saturating_add(self.config.lease_ttl_ms);
        self.lease_deadline_ms = failover_epoch_advance(self.lease_deadline_ms, next_deadline);

        FailoverEvent::Promoted {
            old_leader,
            new_leader,
            identity: promoted.identity,
            lineage: promoted.lineage,
            fork_head_offset: promoted.head_offset,
            quorum_votes: winner.quorum_votes,
        }
    }

    fn try_rejoin_pending(&mut self, events: &mut Vec<FailoverEvent>) {
        let count = self.specs.len();
        let mut j = 0usize;
        while j < count {
            if j != self.leader_node {
                let offline = self.node_offline.get(j).copied().unwrap_or(true);
                let already_live = matches!(self.live.get(j), Some(Some(_)));
                let fork_opt = self.pending_rejoin.get(j).copied().flatten();
                if !offline && !already_live {
                    if let Some(fork_head) = fork_opt {
                        if let (Some(spec), Some(&bind_addr)) =
                            (self.specs.get(j), self.assigned_addrs.get(j))
                        {
                            if let Ok(dropped) =
                                repair_follower_for_leader(&spec.log_path, fork_head)
                            {
                                if let Ok(rep) = crate::Broker::open_replica(&spec.log_path) {
                                    if let Ok((handle, bound)) = serve_node_tcp(&rep, bind_addr) {
                                        if let Some(a) = self.assigned_addrs.get_mut(j) {
                                            *a = bound;
                                        }
                                        if let Some(slot) = self.live.get_mut(j) {
                                            *slot = Some(ManagedNode {
                                                broker: rep,
                                                handle,
                                            });
                                        }
                                        if let Some(rejoin_slot) = self.pending_rejoin.get_mut(j) {
                                            *rejoin_slot = None;
                                        }
                                        let rejoined_links = match self.live.get(self.leader_node) {
                                            Some(Some(leader_node)) => {
                                                match leader_node.broker.rejoin_followers() {
                                                    Ok(n) => n,
                                                    Err(_) => 0,
                                                }
                                            }
                                            _ => 0,
                                        };
                                        self.rejoined_nodes = self.rejoined_nodes.saturating_add(1);
                                        events.push(FailoverEvent::FollowerRejoined {
                                            node_id: j,
                                            dropped_tail_records: dropped,
                                            rejoined_links,
                                        });
                                    }
                                }
                            }
                        }
                    }
                }
            }
            j = j.saturating_add(1);
        }
    }

    /// Gracefully shut down every live managed node in the cluster, stopping the active leader
    /// before followers so no in-flight replication batch stalls on a stopped follower.
    pub fn shutdown_all(&mut self) {
        if let Some(leader_slot) = self.live.get_mut(self.leader_node) {
            if let Some(leader) = leader_slot.take() {
                leader.shutdown();
            }
        }
        shutdown_partial_nodes(&mut self.live);
    }
}

impl Drop for FailoverCluster {
    fn drop(&mut self) {
        self.shutdown_all();
    }
}

fn shutdown_partial_nodes(live: &mut [Option<ManagedNode>]) {
    let mut i = 0usize;
    while i < live.len() {
        if let Some(slot) = live.get_mut(i) {
            if let Some(node) = slot.take() {
                node.shutdown();
            }
        }
        i = i.saturating_add(1);
    }
}

fn collect_follower_addrs(
    assigned_addrs: &[std::net::SocketAddr],
    leader_node: usize,
) -> Vec<String> {
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < assigned_addrs.len() {
        if i != leader_node {
            if let Some(addr) = assigned_addrs.get(i) {
                out.push(addr.to_string());
            }
        }
        i = i.saturating_add(1);
    }
    out
}

struct DaemonShared {
    cluster: std::sync::Mutex<FailoverCluster>,
    events: std::sync::Mutex<std::collections::VecDeque<FailoverEvent>>,
    wake_state: std::sync::Mutex<u64>,
    cv: std::sync::Condvar,
    running: std::sync::atomic::AtomicBool,
    heartbeat_interval: std::time::Duration,
}

fn bump_and_notify(shared: &DaemonShared) {
    {
        let mut seq = shared
            .wake_state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        *seq = seq.saturating_add(1);
    }
    shared.cv.notify_all();
}

fn failover_daemon_loop(shared: std::sync::Arc<DaemonShared>) {
    while shared.running.load(std::sync::atomic::Ordering::Acquire) {
        let batch = {
            let mut cluster = shared
                .cluster
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            cluster.tick_now()
        };
        if !batch.is_empty() {
            let mut log = shared
                .events
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            let mut idx = 0usize;
            while idx < batch.len() {
                if let Some(ev) = batch.get(idx) {
                    while log.len() >= MAX_FAILOVER_EVENTS {
                        let _ = log.pop_front();
                    }
                    log.push_back(ev.clone());
                }
                idx = idx.saturating_add(1);
            }
        }
        bump_and_notify(&shared);

        if !shared.running.load(std::sync::atomic::Ordering::Acquire) {
            break;
        }
        let guard = shared
            .wake_state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let seen = *guard;
        if shared.running.load(std::sync::atomic::Ordering::Acquire) {
            let wait_res = shared.cv.wait_timeout(guard, shared.heartbeat_interval);
            if let Ok((g2, _)) = wait_res {
                let _ = (*g2, seen);
            }
        }
    }
}

/// Thread-safe cooperative stop handle for [`FailoverDaemon`].
#[derive(Clone)]
pub struct FailoverDaemonCloser {
    shared: std::sync::Arc<DaemonShared>,
}

impl std::fmt::Debug for FailoverDaemonCloser {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FailoverDaemonCloser")
            .field("closed", &self.is_closed())
            .finish()
    }
}

impl FailoverDaemonCloser {
    /// Signal the background [`FailoverDaemon`] loop to exit immediately.
    pub fn close(&self) {
        self.shared
            .running
            .store(false, std::sync::atomic::Ordering::Release);
        bump_and_notify(&self.shared);
    }

    /// Whether [`Self::close`] or [`FailoverDaemon::shutdown`] has been invoked.
    #[must_use]
    pub fn is_closed(&self) -> bool {
        !self
            .shared
            .running
            .load(std::sync::atomic::Ordering::Acquire)
    }
}

/// Autonomous background lease-heartbeat failover daemon wrapping [`FailoverCluster`].
///
/// Continuously probes the active leader over TCP on `heartbeat_interval`, renews its
/// monotonic lease while healthy, automatically runs majority-quorum election and crash-safe
/// replica promotion once `lease_deadline_ms + guard_band_ms` expires, and automatically
/// truncates and rejoins deposed ex-leaders once their log lock is released.
pub struct FailoverDaemon {
    shared: std::sync::Arc<DaemonShared>,
    worker: Option<std::thread::JoinHandle<()>>,
}

impl FailoverDaemon {
    /// Start the background lease-heartbeat failover daemon thread over `cluster`.
    pub fn start(cluster: FailoverCluster) -> io::Result<Self> {
        let heartbeat_interval = cluster.config().heartbeat_interval;
        let shared = std::sync::Arc::new(DaemonShared {
            cluster: std::sync::Mutex::new(cluster),
            events: std::sync::Mutex::new(std::collections::VecDeque::new()),
            wake_state: std::sync::Mutex::new(0),
            cv: std::sync::Condvar::new(),
            running: std::sync::atomic::AtomicBool::new(true),
            heartbeat_interval,
        });
        let worker_shared = std::sync::Arc::clone(&shared);
        let worker = std::thread::Builder::new()
            .name("astream-failover".to_string())
            .spawn(move || failover_daemon_loop(worker_shared))?;
        Ok(Self {
            shared,
            worker: Some(worker),
        })
    }

    /// Return a cloneable cooperative stop handle for this daemon.
    #[must_use]
    pub fn closer(&self) -> FailoverDaemonCloser {
        FailoverDaemonCloser {
            shared: std::sync::Arc::clone(&self.shared),
        }
    }

    /// Wake the background daemon thread immediately to run a probe/failover/rejoin cycle.
    pub fn nudge(&self) {
        bump_and_notify(&self.shared);
    }

    /// Point-in-time cluster snapshot.
    #[must_use]
    pub fn snapshot(&self) -> FailoverSnapshot {
        self.shared
            .cluster
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .snapshot()
    }

    /// Current active leader TCP [`std::net::SocketAddr`].
    #[must_use]
    pub fn leader_addr(&self) -> std::net::SocketAddr {
        self.shared
            .cluster
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .leader_addr()
    }

    /// Current active leader [`LogIdentity`].
    #[must_use]
    pub fn leader_identity(&self) -> LogIdentity {
        self.shared
            .cluster
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .leader_identity()
    }

    /// Retained recent [`FailoverEvent`] log (`<= MAX_FAILOVER_EVENTS`).
    #[must_use]
    pub fn events(&self) -> Vec<FailoverEvent> {
        let log = self
            .shared
            .events
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let mut out = Vec::new();
        let mut idx = 0usize;
        while idx < log.len() {
            if let Some(ev) = log.get(idx) {
                out.push(ev.clone());
            }
            idx = idx.saturating_add(1);
        }
        out
    }

    /// Crash / power-off `node_id` and immediately wake the daemon thread.
    pub fn crash_node(&self, node_id: usize) -> bool {
        let res = self
            .shared
            .cluster
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .crash_node(node_id);
        bump_and_notify(&self.shared);
        res
    }

    /// Restore host power for `node_id` and immediately wake the daemon thread so it repairs
    /// and rejoins `node_id` as a replica.
    pub fn restore_node_power(&self, node_id: usize) -> bool {
        let res = self
            .shared
            .cluster
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .restore_node_power(node_id);
        bump_and_notify(&self.shared);
        res
    }

    /// Attach an additional Unix-domain socket listener onto the currently active leader
    /// [`crate::Broker`] (useful before [`Self::partition_leader_tcp`] to exercise live
    /// split-brain zombie client writes).
    #[cfg(unix)]
    pub fn serve_leader_unix(&self, socket_path: &Path) -> io::Result<crate::BrokerHandle> {
        let cluster = self
            .shared
            .cluster
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let leader_id = cluster.leader_node();
        let Some(broker) = cluster.node_broker(leader_id) else {
            return Err(io::Error::new(
                io::ErrorKind::NotConnected,
                "active leader has no live in-process Broker",
            ));
        };
        broker.serve(socket_path)
    }

    /// Partition ONLY the active leader's managed TCP listener, returning its live
    /// [`crate::Broker`] and waking the daemon thread.
    pub fn partition_leader_tcp(&self) -> Option<crate::Broker> {
        let out = self
            .shared
            .cluster
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .partition_leader_tcp();
        bump_and_notify(&self.shared);
        out
    }

    /// The daemon's wake sequence as it stands, its lock held for the read alone, so a wait
    /// that compares it later holds no guard in between.
    fn wake_seq(&self) -> u64 {
        *self
            .shared
            .wake_state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    /// Block on the daemon's condition variable (no polling sleeps) until
    /// `snapshot().leader_identity.generation >= min_generation` or `timeout` elapses.
    pub fn wait_for_generation(
        &self,
        min_generation: u64,
        timeout: std::time::Duration,
    ) -> io::Result<FailoverSnapshot> {
        let started = std::time::Instant::now();
        loop {
            let seen = self.wake_seq();
            let snap = self.snapshot();
            if snap.leader_identity.generation >= min_generation {
                return Ok(snap);
            }
            let elapsed = started.elapsed();
            if elapsed >= timeout {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    format!(
                        "timed out waiting for failover generation >= {min_generation} (at {})",
                        snap.leader_identity.generation
                    ),
                ));
            }
            let rem = timeout.saturating_sub(elapsed);
            let guard = self
                .shared
                .wake_state
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if *guard == seen {
                let _ = self.shared.cv.wait_timeout(guard, rem);
            }
        }
    }

    /// Block on the daemon's condition variable (no polling sleeps) until
    /// `snapshot().rejoined_nodes >= min_rejoined` or `timeout` elapses.
    pub fn wait_for_rejoined_count(
        &self,
        min_rejoined: u64,
        timeout: std::time::Duration,
    ) -> io::Result<FailoverSnapshot> {
        let started = std::time::Instant::now();
        loop {
            let seen = self.wake_seq();
            let snap = self.snapshot();
            if snap.rejoined_nodes >= min_rejoined {
                return Ok(snap);
            }
            let elapsed = started.elapsed();
            if elapsed >= timeout {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    format!(
                        "timed out waiting for rejoined_nodes >= {min_rejoined} (at {})",
                        snap.rejoined_nodes
                    ),
                ));
            }
            let rem = timeout.saturating_sub(elapsed);
            let guard = self
                .shared
                .wake_state
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if *guard == seen {
                let _ = self.shared.cv.wait_timeout(guard, rem);
            }
        }
    }

    /// Block on the daemon's condition variable (no polling sleeps) until
    /// `snapshot().heartbeat_renewals >= min_renewals` or `timeout` elapses.
    pub fn wait_for_renewals(
        &self,
        min_renewals: u64,
        timeout: std::time::Duration,
    ) -> io::Result<FailoverSnapshot> {
        let started = std::time::Instant::now();
        loop {
            let seen = self.wake_seq();
            let snap = self.snapshot();
            if snap.heartbeat_renewals >= min_renewals {
                return Ok(snap);
            }
            let elapsed = started.elapsed();
            if elapsed >= timeout {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    format!(
                        "timed out waiting for heartbeat_renewals >= {min_renewals} (at {})",
                        snap.heartbeat_renewals
                    ),
                ));
            }
            let rem = timeout.saturating_sub(elapsed);
            let guard = self
                .shared
                .wake_state
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if *guard == seen {
                let _ = self.shared.cv.wait_timeout(guard, rem);
            }
        }
    }

    /// Stop the background daemon thread and cleanly shut down all managed cluster nodes.
    pub fn shutdown(&mut self) {
        self.shared
            .running
            .store(false, std::sync::atomic::Ordering::Release);
        bump_and_notify(&self.shared);
        if let Some(jh) = self.worker.take() {
            let _ = jh.join();
        }
        self.shared
            .cluster
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .shutdown_all();
    }
}

impl Drop for FailoverDaemon {
    fn drop(&mut self) {
        self.shutdown();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(byte: u8, generation: u64) -> LogIdentity {
        LogIdentity {
            id: [byte; 16],
            generation,
        }
    }

    #[test]
    fn election_requires_strict_majority_and_picks_highest_generation_then_head() {
        // 1 of 3 reachable -> refused (need 2 of 3).
        let err = elect_highest_candidate(
            3,
            &[ElectionCandidate {
                node_id: 1,
                identity: id(0xAA, 0),
                head_offset: 50,
                base_offset: 0,
                diverged: false,
            }],
        )
        .unwrap_err();
        assert!(err.contains("insufficient quorum"));

        // Diverged node does not count toward quorum!
        let err_div = elect_highest_candidate(
            3,
            &[
                ElectionCandidate {
                    node_id: 1,
                    identity: id(0xAA, 0),
                    head_offset: 50,
                    base_offset: 0,
                    diverged: false,
                },
                ElectionCandidate {
                    node_id: 2,
                    identity: id(0xAA, 0),
                    head_offset: 55,
                    base_offset: 0,
                    diverged: true,
                },
            ],
        )
        .unwrap_err();
        assert!(err_div.contains("insufficient quorum"));

        // Higher generation beats higher stale head_offset!
        let win = elect_highest_candidate(
            3,
            &[
                ElectionCandidate {
                    node_id: 0,
                    identity: id(0xAA, 0),
                    head_offset: 99,
                    base_offset: 0,
                    diverged: false,
                },
                ElectionCandidate {
                    node_id: 2,
                    identity: id(0xAA, 1),
                    head_offset: 40,
                    base_offset: 0,
                    diverged: false,
                },
            ],
        )
        .unwrap();
        assert_eq!(win.node_id, 2);
        assert_eq!(win.head_offset, 40);
        assert_eq!(win.highest_epoch, id(0xAA, 1));
        assert_eq!(win.quorum_votes, 2);
        assert_eq!(win.required_quorum, 2);
    }

    #[test]
    fn stopped_failover_opens_logs_with_zero_resident_budget_and_repairs_tail() {
        let root = crate::test_scratch::Scratch::new("failover-cold-open");
        let leader_path = root.path().join("leader");
        let replica_path = root.path().join("replica");

        {
            let mut leader = BrokerLog::open(&leader_path).unwrap();
            for seq in 1..=64u64 {
                leader
                    .publish(7, seq, format!("/f/ev/{seq}"), vec![b'x'; 64])
                    .unwrap();
            }
            leader.close_clean().unwrap();
        }
        {
            let mut replica = BrokerLog::open(&replica_path).unwrap();
            replica.declare_replica().unwrap();
            replica.close_clean().unwrap();
        }

        let cold = open_stopped_strict_cold(&leader_path).unwrap();
        assert_eq!((cold.residency().0, cold.residency().2), (1, 64));
        assert!(cold.hot_capacity_for_test() <= 16);
        drop(cold);

        let cand = inspect_node_log(0, &leader_path).unwrap();
        assert_eq!(
            (cand.head_offset, cand.base_offset, cand.diverged),
            (64, 0, false)
        );

        let promoted = promote_replica_log(&replica_path, Some(cand.identity)).unwrap();
        assert!(promoted.identity.generation > cand.identity.generation);

        let dropped = repair_follower_for_leader(&leader_path, Offset(20)).unwrap();
        assert_eq!(dropped, 44);
        let repaired = inspect_node_log(0, &leader_path).unwrap();
        assert_eq!((repaired.head_offset, repaired.diverged), (20, false));
    }

    #[test]
    fn failover_cluster_enforces_guard_band_and_rejects_sub_quorum_before_promoting() {
        let root = crate::test_scratch::Scratch::new("failover-cluster-guard");
        let specs = vec![
            FailoverNodeSpec::loopback_ephemeral(root.path().join("n0.log")),
            FailoverNodeSpec::loopback_ephemeral(root.path().join("n1.log")),
            FailoverNodeSpec::loopback_ephemeral(root.path().join("n2.log")),
        ];
        let cfg = FailoverLeaseConfig::new(1_500, 250)
            .with_probe_timeout(std::time::Duration::from_millis(120))
            .with_follower_timeout(std::time::Duration::from_millis(800));
        let mut cluster = FailoverCluster::open(specs, 0, cfg).unwrap();

        let gen0 = cluster.leader_identity();
        assert_eq!(gen0.generation, 0);

        {
            let mut pub0 = crate::Client::connect_tcp(cluster.leader_addr()).unwrap();
            for seq in 1..=4u64 {
                assert_eq!(
                    pub0.publish(11, seq, "/a/fo/unit", format!("u{seq}").as_bytes())
                        .unwrap(),
                    (seq - 1, false)
                );
            }
        }

        // Renew leader 0's lease at t = 1_200 -> lease_deadline_ms = max(2_500, 2_700) = 2_700.
        let ev_renew = cluster.tick_at(1_200);
        assert_eq!(
            ev_renew,
            vec![FailoverEvent::HeartbeatRenewed {
                leader_node: 0,
                identity: gen0,
                lease_deadline_ms: 2_700,
            }]
        );

        // Crash leader 0: before guard band (2_700 + 250 = 2_950), t = 2_949 must NOT promote!
        assert!(cluster.crash_node(0));
        let ev_guard = cluster.tick_at(2_949);
        assert_eq!(ev_guard.len(), 1);
        assert!(matches!(
            ev_guard.first(),
            Some(FailoverEvent::ProbeFailed {
                leader_node: 0,
                consecutive_failures: 1,
                lease_deadline_ms: 2_700,
                ..
            })
        ));
        assert_eq!(cluster.leader_node(), 0);
        assert_eq!(cluster.snapshot().promotions, 0);

        // Also crash follower 2 so only 1 of 3 nodes (n1) is reachable -> t = 2_950 refuses election!
        assert!(cluster.crash_node(2));
        let ev_subq = cluster.tick_at(2_950);
        assert!(ev_subq
            .iter()
            .any(|e| matches!(e, FailoverEvent::QuorumUnavailable { old_leader: 0, .. })));
        assert_eq!(cluster.leader_node(), 0);
        assert_eq!(cluster.snapshot().promotions, 0);

        // Restore power to follower 2: t = 3_000 rejoins n2 and promotes n1 to generation 1 in one tick!
        assert!(cluster.restore_node_power(2));
        let ev_prom = cluster.tick_at(3_000);
        assert!(ev_prom.iter().any(|e| matches!(
            e,
            FailoverEvent::Promoted {
                old_leader: 0,
                new_leader: 1,
                fork_head_offset: 4,
                quorum_votes: 2,
                ..
            }
        )));
        assert_eq!(cluster.leader_node(), 1);
        assert_eq!(cluster.leader_identity().id, gen0.id);
        assert_eq!(cluster.leader_identity().generation, 1);
        assert_eq!(
            cluster
                .leader_identity()
                .continues(gen0, cluster.leader_lineage()),
            Some(4)
        );

        // Restore power to deposed n0: t = 3_050 repairs & rejoins n0 cleanly as a replica!
        assert!(cluster.restore_node_power(0));
        let ev_rejoin = cluster.tick_at(3_050);
        assert!(ev_rejoin.iter().any(|e| matches!(
            e,
            FailoverEvent::FollowerRejoined {
                node_id: 0,
                dropped_tail_records: 0,
                ..
            }
        )));
        assert_eq!(cluster.snapshot().node_live, vec![true, true, true]);
        cluster.shutdown_all();
    }
}
