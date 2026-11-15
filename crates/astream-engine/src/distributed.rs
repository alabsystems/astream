// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

#![allow(clippy::manual_is_ascii_check)]

//! Distributed durable execution over an ordered broker log (`docs/ROADMAP.md`
//! "distributed durable execution", `docs/DESIGN-astream-term.md` §13).
//!
//! Lifts [`crate::WorkflowJournal`] and [`crate::DagJournal`] from single-host files to
//! multi-worker distributed coordination over any [`WorkflowBus`] (implemented in-memory
//! by [`InMemoryWorkflowBus`] and over live TCP/Unix broker connections via
//! `astream-broker::Client`).
//!
//! ## Protocol & Guarantees
//!
//! 1. **Broker-time (`bt=`) lease coordination (`ADLS` v1):** before executing a ready
//!    DAG node `u`, a worker publishes an `ADLS` lease claim carrying `(node_id,
//!    worker_id, lease_ttl_ms, dep_digest)` to `{prefix}/lease/{node_id}` and scans the
//!    ordered log through its own claim's offset. Lease expiry (`stamp_bt_ms +
//!    lease_ttl_ms`, monotonically advanced via [`dist_lease_expiry_advance`]) is derived
//!    solely from the broker's monotone `bt=` timestamp on the claim record — workers
//!    never trust peer wall clocks.
//! 2. **Deterministic lease ownership & expired-lease takeover:** every worker replays
//!    the identical ordered log prefix and computes the identical active lease holder.
//!    A competing claim arriving while the current lease is still live
//!    (`!dist_lease_expired(holder_expiry, claim_bt_ms)`) is deterministically ignored;
//!    once `dist_lease_expired(holder_expiry, claim_bt_ms)` holds, the first takeover
//!    claim in broker offset order wins the lease.
//! 3. **Canonical earliest-offset commit winner (`ADAG` v1):** step commits are published
//!    to `{prefix}/commit/{node_id}` using [`crate::dag::encode_dag_record`], binding the
//!    node's SHA-256 `(id, sorted_deps)` digest. If a stalled worker wakes up as a zombie
//!    and publishes a late duplicate commit after takeover, [`dist_winner_offset_min`]
//!    retains the earliest valid commit offset so every downstream step and every worker
//!    observes byte-identical parent outputs.

use crate::dag::{
    dag_deps_satisfied, decode_dag_record, encode_dag_record, DagSpec, DAG_RECORD_MAGIC,
};
use astream_digest::ct_eq;
use astream_wire::{steps, Filter, Subject};
use std::collections::{BTreeSet, HashMap};
use std::io;
use std::ops::Bound::{Excluded, Unbounded};
use std::sync::{Arc, Mutex};

#[cfg(clean_islands)]
#[path = "dist_dag_island.rs"]
mod dist_dag_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{dist_lease_expiry_advance, dist_winner_offset_min};
#[cfg(clean_islands)]
pub use dist_dag_island::{dist_lease_expiry_advance, dist_winner_offset_min};

contract_fn! {
    /// Kernel-certified check that a step lease expiring at `lease_expiry_ms` has expired
    /// at broker timestamp `now_bt_ms` (`lease_expiry_ms <= now_bt_ms`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `dist_lease_expired_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn dist_lease_expired(lease_expiry_ms: u64, now_bt_ms: u64) -> bool
    clauses [ensures result == (lease_expiry_ms <= now_bt_ms)]
    {
        lease_expiry_ms <= now_bt_ms
    }
}

/// Four-byte magic prefix (`"ADLS"`) inside each distributed step-lease claim record.
pub const DIST_LEASE_MAGIC: [u8; 4] = *b"ADLS";
/// Format version for `ADLS` distributed lease claim records.
pub const DIST_LEASE_VERSION: u8 = 1;
/// Fixed byte length of an `ADLS` v1 record:
/// `magic(4) + version(1) + node_id(8) + worker_id(8) + lease_ttl_ms(8) + dep_digest(32)`.
pub const DIST_LEASE_LEN: usize = 61;

/// Maximum number of steps supported in a single [`DistributedWorkflow`] or [`DistributedDag`].
pub const MAX_DISTRIBUTED_STEPS: usize = 4096;
/// Maximum workflow subject-prefix byte length.
pub const MAX_WORKFLOW_PREFIX_BYTES: usize = 128;
/// Default page size per [`WorkflowBus::fetch_records`] call.
const DEFAULT_FETCH_BATCH: u32 = 256;
/// Hard liveness bound on consecutive [`WorkflowBus::fetch_records`] pages per sync.
const MAX_SYNC_PAGES: usize = 16_384;

/// Stamped bus record `(offset, subject, body, bt_ms)` read from a [`WorkflowBus`].
pub type BusRecord = (u64, String, Vec<u8>, Option<u64>);

/// Transport seam over an ordered, broker-stamped pub/sub log.
pub trait WorkflowBus {
    /// Publish `body` to `subject` under `(producer_id, producer_seq)`, returning
    /// `(offset, deduped)`.
    fn publish_record(
        &mut self,
        producer_id: u64,
        producer_seq: u64,
        subject: &str,
        body: &[u8],
    ) -> io::Result<(u64, bool)>;

    /// Bounded stamped scan of records matching `filter` at `offset >= from_offset`,
    /// returning `(records, (next_scan_offset, log_head))`.
    fn fetch_records(
        &mut self,
        from_offset: u64,
        filter: &str,
        max: u32,
    ) -> io::Result<(Vec<BusRecord>, (u64, u64))>;
}

/// Fault classification for distributed workflow and DAG log replay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DistributedFault {
    /// Workflow subject prefix is empty, too long, or not a valid [`Subject`].
    InvalidPrefix {
        /// Rejected prefix string.
        prefix: String,
    },
    /// Step or node count exceeds [`MAX_DISTRIBUTED_STEPS`].
    TooManySteps {
        /// Requested step count.
        requested: usize,
    },
    /// Lease record on `{prefix}/lease/*` could not be decoded as `ADLS` v1.
    MalformedLease {
        /// Broker offset of the malformed record.
        offset: u64,
    },
    /// Commit record on `{prefix}/commit/*` or `{prefix}/step/*` could not be decoded.
    MalformedCommit {
        /// Broker offset of the malformed record.
        offset: u64,
    },
    /// Record named a `node_id` or `step_index` outside `0..total` or mismatched its subject suffix.
    UnknownNode {
        /// Broker offset of the offending record.
        offset: u64,
        /// Decoded node/step identifier.
        node_id: u64,
    },
    /// Stored SHA-256 `(node_id, sorted_deps)` digest did not match local [`DagSpec`].
    SpecMismatch {
        /// Broker offset of the offending record.
        offset: u64,
        /// Node whose dependency set drifted.
        node_id: u64,
    },
    /// Commit record for `node_id` landed before parent dependency `missing_dep` committed.
    TopologicalViolation {
        /// Broker offset of the offending commit record.
        offset: u64,
        /// Child node ID.
        node_id: u64,
        /// Uncommitted parent dependency ID.
        missing_dep: u64,
    },
    /// Bus sync exceeded `MAX_SYNC_PAGES` without reaching the log head.
    ScanLimitExceeded,
}

impl std::fmt::Display for DistributedFault {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let msg = match self {
            DistributedFault::InvalidPrefix { prefix } => {
                format!("invalid distributed workflow subject prefix: {prefix:?}")
            }
            DistributedFault::TooManySteps { requested } => format!(
                "distributed workflow step count {requested} exceeds cap {MAX_DISTRIBUTED_STEPS}"
            ),
            DistributedFault::MalformedLease { offset } => {
                format!("malformed ADLS lease record at broker offset {offset}")
            }
            DistributedFault::MalformedCommit { offset } => {
                format!("malformed workflow commit record at broker offset {offset}")
            }
            DistributedFault::UnknownNode { offset, node_id } => {
                format!("unknown or mismatched workflow node {node_id} at broker offset {offset}")
            }
            DistributedFault::SpecMismatch { offset, node_id } => format!(
                "distributed DAG spec mismatch for node {node_id} at broker offset {offset}"
            ),
            DistributedFault::TopologicalViolation {
                offset,
                node_id,
                missing_dep,
            } => format!(
                "topological violation at broker offset {offset}: node {node_id} committed before parent {missing_dep}"
            ),
            DistributedFault::ScanLimitExceeded => {
                format!("distributed workflow sync exceeded {MAX_SYNC_PAGES} pages")
            }
        };
        f.write_str(&msg)
    }
}

impl std::error::Error for DistributedFault {}

impl DistributedFault {
    fn into_io(self) -> io::Error {
        io::Error::new(io::ErrorKind::InvalidData, self)
    }
}

/// Encode an `ADLS` v1 distributed step-lease claim record.
#[must_use]
pub fn encode_lease_record(
    node_id: u64,
    worker_id: u64,
    lease_ttl_ms: u64,
    dep_digest: &[u8; 32],
) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&DIST_LEASE_MAGIC);
    out.push(DIST_LEASE_VERSION);
    out.extend_from_slice(&node_id.to_le_bytes());
    out.extend_from_slice(&worker_id.to_le_bytes());
    out.extend_from_slice(&lease_ttl_ms.to_le_bytes());
    out.extend_from_slice(dep_digest);
    out
}

/// Decode an `ADLS` v1 distributed step-lease claim record into
/// `(node_id, worker_id, lease_ttl_ms, dep_digest)`.
#[must_use]
pub fn decode_lease_record(body: &[u8]) -> Option<(u64, u64, u64, [u8; 32])> {
    if body.len() != DIST_LEASE_LEN {
        return None;
    }
    let &[m0, m1, m2, m3, ver, ref rest @ ..] = body else {
        return None;
    };
    if [m0, m1, m2, m3] != DIST_LEASE_MAGIC || ver != DIST_LEASE_VERSION {
        return None;
    }
    let node_id = read_u64_le(rest, 0)?;
    let worker_id = read_u64_le(rest, 8)?;
    let lease_ttl_ms = read_u64_le(rest, 16)?;
    let digest_slice = rest.get(24..56)?;
    let mut digest = [0u8; 32];
    digest.copy_from_slice(digest_slice);
    Some((node_id, worker_id, lease_ttl_ms, digest))
}

fn read_u64_le(bytes: &[u8], start: usize) -> Option<u64> {
    let &[b0, b1, b2, b3, b4, b5, b6, b7, ..] = bytes.get(start..)? else {
        return None;
    };
    Some(u64::from_le_bytes([b0, b1, b2, b3, b4, b5, b6, b7]))
}

fn validate_workflow_prefix(prefix: &str) -> Result<(), DistributedFault> {
    if prefix.is_empty()
        || prefix.len() > MAX_WORKFLOW_PREFIX_BYTES
        || !prefix.starts_with('/')
        || prefix.ends_with('/')
        || prefix == "/a/commit"
        || prefix.starts_with("/a/commit/")
        || prefix == "/a/bind"
        || prefix.starts_with("/a/bind/")
        || prefix == "/a/will"
        || prefix.starts_with("/a/will/")
        || prefix == "/a/retire"
        || prefix.starts_with("/a/retire/")
    {
        return Err(DistributedFault::InvalidPrefix {
            prefix: prefix.to_string(),
        });
    }
    if Subject::new(prefix).is_err() {
        return Err(DistributedFault::InvalidPrefix {
            prefix: prefix.to_string(),
        });
    }
    Ok(())
}

fn parse_u64_decimal(raw: &str) -> Option<u64> {
    let bytes = raw.as_bytes();
    let &[first, ref tail_check @ ..] = bytes else {
        return None;
    };
    if first == b'0' && !tail_check.is_empty() {
        return None;
    }
    let mut acc = 0u64;
    let mut rest = bytes;
    while let &[b, ref tail @ ..] = rest {
        if !matches!(b, b'0'..=b'9') {
            return None;
        }
        let digit = b.saturating_sub(b'0') as u64;
        acc = acc.checked_mul(10)?;
        acc = acc.checked_add(digit)?;
        rest = tail;
    }
    Some(acc)
}

// ============================================================================
// Deterministic Shared In-Memory WorkflowBus (for unit tests & local fleets)
// ============================================================================

#[derive(Debug)]
struct InMemoryBusState {
    records: Vec<BusRecord>,
    dedup: HashMap<(u64, u64), u64>,
    clock_ms: u64,
}

/// Deterministic, cloneable in-memory [`WorkflowBus`] with producer `(id, seq)` dedup and
/// an explicit monotone broker-time clock (`advance_clock_ms`).
#[derive(Debug, Clone)]
pub struct InMemoryWorkflowBus {
    inner: Arc<Mutex<InMemoryBusState>>,
}

impl Default for InMemoryWorkflowBus {
    fn default() -> Self {
        Self::new(1_000)
    }
}

impl InMemoryWorkflowBus {
    /// Create a fresh in-memory workflow bus starting at `initial_clock_ms`.
    #[must_use]
    pub fn new(initial_clock_ms: u64) -> Self {
        Self {
            inner: Arc::new(Mutex::new(InMemoryBusState {
                records: Vec::new(),
                dedup: HashMap::new(),
                clock_ms: initial_clock_ms,
            })),
        }
    }

    /// Advance the simulated monotone broker clock by `delta_ms`, returning the new `bt_ms`.
    pub fn advance_clock_ms(&self, delta_ms: u64) -> u64 {
        let mut guard = match self.inner.lock() {
            Ok(g) => g,
            Err(p) => p.into_inner(),
        };
        guard.clock_ms = guard.clock_ms.saturating_add(delta_ms);
        guard.clock_ms
    }

    /// Current simulated broker clock (`bt_ms`).
    #[must_use]
    pub fn clock_ms(&self) -> u64 {
        let guard = match self.inner.lock() {
            Ok(g) => g,
            Err(p) => p.into_inner(),
        };
        guard.clock_ms
    }

    /// Current log head offset (`records.len()`).
    #[must_use]
    pub fn head(&self) -> u64 {
        let guard = match self.inner.lock() {
            Ok(g) => g,
            Err(p) => p.into_inner(),
        };
        guard.records.len() as u64
    }
}

impl WorkflowBus for InMemoryWorkflowBus {
    fn publish_record(
        &mut self,
        producer_id: u64,
        producer_seq: u64,
        subject: &str,
        body: &[u8],
    ) -> io::Result<(u64, bool)> {
        if Subject::new(subject).is_err() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("invalid subject: {subject:?}"),
            ));
        }
        let mut guard = match self.inner.lock() {
            Ok(g) => g,
            Err(p) => p.into_inner(),
        };
        if producer_seq != 0 {
            if let Some(&orig) = guard.dedup.get(&(producer_id, producer_seq)) {
                return Ok((orig, true));
            }
        }
        let offset = guard.records.len() as u64;
        let bt_ms = guard.clock_ms;
        guard
            .records
            .push((offset, subject.to_string(), body.to_vec(), Some(bt_ms)));
        if producer_seq != 0 {
            guard.dedup.insert((producer_id, producer_seq), offset);
        }
        Ok((offset, false))
    }

    fn fetch_records(
        &mut self,
        from_offset: u64,
        filter: &str,
        max: u32,
    ) -> io::Result<(Vec<BusRecord>, (u64, u64))> {
        let parsed = match Filter::new(filter) {
            Ok(f) => f,
            Err(e) => return Err(io::Error::new(io::ErrorKind::InvalidInput, e.to_string())),
        };
        let guard = match self.inner.lock() {
            Ok(g) => g,
            Err(p) => p.into_inner(),
        };
        let head = guard.records.len() as u64;
        if max == 0 || from_offset >= head {
            return Ok((Vec::new(), (head, head)));
        }
        let mut out = Vec::new();
        let mut idx = usize::try_from(from_offset).unwrap_or(usize::MAX);
        let mut next_off = head;
        while idx < guard.records.len() {
            if out.len() >= max as usize {
                next_off = idx as u64;
                break;
            }
            if let Some(rec) = guard.records.get(idx) {
                if let Ok(subj) = Subject::new(&rec.1) {
                    if parsed.matches(&subj) {
                        out.push(rec.clone());
                    }
                }
            }
            idx = idx.saturating_add(1);
        }
        Ok((out, (next_off, head)))
    }
}

// ============================================================================
// Distributed Linear Workflow (`0..total`)
// ============================================================================

/// Distributed crash-resumable linear workflow (`0..total`) backed by any [`WorkflowBus`].
#[derive(Debug)]
pub struct DistributedWorkflow<B> {
    bus: B,
    prefix: String,
    total_steps: usize,
    producer_id: u64,
    next_seq: u64,
    scan_cursor: u64,
    winner_offsets: Vec<u64>,
    committed: Vec<Option<Vec<u8>>>,
}

impl<B: WorkflowBus> DistributedWorkflow<B> {
    /// Open or attach to a distributed linear workflow of `total_steps` under `prefix`,
    /// replaying all committed step records currently on `bus`.
    pub fn open(
        bus: B,
        prefix: impl Into<String>,
        total_steps: usize,
        producer_id: u64,
    ) -> io::Result<Self> {
        let prefix = prefix.into();
        if let Err(e) = validate_workflow_prefix(&prefix) {
            return Err(e.into_io());
        }
        if total_steps > MAX_DISTRIBUTED_STEPS {
            return Err(DistributedFault::TooManySteps {
                requested: total_steps,
            }
            .into_io());
        }
        let mut winner_offsets = Vec::new();
        let mut committed = Vec::new();
        let mut i = 0usize;
        while i < total_steps {
            winner_offsets.push(u64::MAX);
            committed.push(None);
            i = i.saturating_add(1);
        }
        let mut wf = Self {
            bus,
            prefix,
            total_steps,
            producer_id,
            next_seq: 1,
            scan_cursor: 0,
            winner_offsets,
            committed,
        };
        wf.sync()?;
        Ok(wf)
    }

    /// Borrow the underlying [`WorkflowBus`].
    #[must_use]
    pub const fn bus(&self) -> &B {
        &self.bus
    }

    /// Mutably borrow the underlying [`WorkflowBus`].
    pub fn bus_mut(&mut self) -> &mut B {
        &mut self.bus
    }

    /// Consume the workflow handle and return the underlying [`WorkflowBus`].
    #[must_use]
    pub fn into_bus(self) -> B {
        self.bus
    }

    /// Number of contiguous committed steps `0..k` from the start of the workflow.
    #[must_use]
    pub fn committed_steps(&self) -> usize {
        let mut count = 0usize;
        while count < self.total_steps {
            if matches!(self.committed.get(count), Some(Some(_))) {
                count = count.saturating_add(1);
            } else {
                break;
            }
        }
        count
    }

    /// Committed output for `step_index`, if committed.
    #[must_use]
    pub fn output(&self, step_index: usize) -> Option<&[u8]> {
        match self.committed.get(step_index) {
            Some(Some(buf)) => Some(buf.as_slice()),
            _ => None,
        }
    }

    /// Replay any newly published step records from the bus.
    pub fn sync(&mut self) -> io::Result<()> {
        let filter = format!("{}/step/*", self.prefix);
        let step_prefix = format!("{}/step/", self.prefix);
        let mut pages = 0usize;
        loop {
            if pages >= MAX_SYNC_PAGES {
                return Err(DistributedFault::ScanLimitExceeded.into_io());
            }
            pages = pages.saturating_add(1);
            let (rows, (next, head)) =
                self.bus
                    .fetch_records(self.scan_cursor, &filter, DEFAULT_FETCH_BATCH)?;
            for (offset, subject, body, _bt_ms) in rows {
                let Some(suffix) = subject.strip_prefix(&step_prefix) else {
                    return Err(DistributedFault::MalformedCommit { offset }.into_io());
                };
                let Some(subj_step) = parse_u64_decimal(suffix) else {
                    return Err(DistributedFault::MalformedCommit { offset }.into_io());
                };
                let scan = steps::scan_steps_from(&body, subj_step);
                if scan.end != steps::StepEnd::Clean || scan.steps.len() != 1 {
                    return Err(DistributedFault::MalformedCommit { offset }.into_io());
                }
                let Some((decoded_idx, range)) = scan.steps.first() else {
                    return Err(DistributedFault::MalformedCommit { offset }.into_io());
                };
                if *decoded_idx != subj_step {
                    return Err(DistributedFault::UnknownNode {
                        offset,
                        node_id: *decoded_idx,
                    }
                    .into_io());
                }
                let Ok(slot_idx) = usize::try_from(subj_step) else {
                    return Err(DistributedFault::UnknownNode {
                        offset,
                        node_id: subj_step,
                    }
                    .into_io());
                };
                if slot_idx >= self.total_steps {
                    return Err(DistributedFault::UnknownNode {
                        offset,
                        node_id: subj_step,
                    }
                    .into_io());
                }
                // Sequential invariant: step `k > 0` requires step `k - 1` committed earlier.
                if slot_idx > 0 {
                    let prev_done = matches!(self.committed.get(slot_idx - 1), Some(Some(_)));
                    if !prev_done {
                        return Err(DistributedFault::TopologicalViolation {
                            offset,
                            node_id: subj_step,
                            missing_dep: (slot_idx - 1) as u64,
                        }
                        .into_io());
                    }
                }
                let payload = body.get(range.clone()).unwrap_or(&[]).to_vec();
                let cur_win = self
                    .winner_offsets
                    .get(slot_idx)
                    .copied()
                    .unwrap_or(u64::MAX);
                let next_win = dist_winner_offset_min(cur_win, offset);
                if next_win == offset && offset < cur_win {
                    if let Some(w_slot) = self.winner_offsets.get_mut(slot_idx) {
                        *w_slot = next_win;
                    }
                    if let Some(c_slot) = self.committed.get_mut(slot_idx) {
                        *c_slot = Some(payload);
                    }
                }
            }
            self.scan_cursor = next;
            if next >= head {
                break;
            }
        }
        Ok(())
    }

    /// Execute any uncommitted steps `k` in `0..total_steps`, passing the canonical
    /// output of step `k - 1` (or `&[]` for step `0`), publishing each step frame to the
    /// bus, and returning the canonical outputs of all `0..total_steps`.
    pub fn run<F>(&mut self, mut exec: F) -> io::Result<Vec<Vec<u8>>>
    where
        F: FnMut(usize, &[u8]) -> io::Result<Vec<u8>>,
    {
        self.sync()?;
        let mut idx = 0usize;
        while idx < self.total_steps {
            self.sync()?;
            let already = matches!(self.committed.get(idx), Some(Some(_)));
            if !already {
                let prev_bytes: Vec<u8> = if idx == 0 {
                    Vec::new()
                } else {
                    match self.committed.get(idx - 1) {
                        Some(Some(v)) => v.clone(),
                        _ => {
                            return Err(io::Error::other(
                                "distributed workflow missing committed predecessor",
                            ));
                        }
                    }
                };
                let out = exec(idx, &prev_bytes)?;
                let framed = match steps::encode_step(idx as u64, &out) {
                    Ok(f) => f,
                    Err(e) => return Err(io::Error::other(e)),
                };
                let subj = format!("{}/step/{idx}", self.prefix);
                let seq = self.next_seq;
                self.next_seq = self.next_seq.saturating_add(1);
                let _ = self
                    .bus
                    .publish_record(self.producer_id, seq, &subj, &framed)?;
                self.sync()?;
            }
            idx = idx.saturating_add(1);
        }
        let mut results = Vec::new();
        let mut r = 0usize;
        while r < self.total_steps {
            let item = match self.committed.get(r) {
                Some(Some(v)) => v.clone(),
                _ => Vec::new(),
            };
            results.push(item);
            r = r.saturating_add(1);
        }
        Ok(results)
    }
}

// ============================================================================
// Multi-Worker Distributed Step-DAG (`DistributedDag`)
// ============================================================================

/// Active broker-stamped lease state for an uncommitted DAG node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ActiveLease {
    /// Worker/producer identifier currently holding the lease.
    pub worker_id: u64,
    /// Broker offset of the winning `ADLS` lease claim record.
    pub offset: u64,
    /// Monotone broker-time (`bt=`, unix ms) at which this lease expires.
    pub expiry_bt_ms: u64,
}

/// Outcome of one [`DistributedDag::claim_and_step_next`] coordination round.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DistributedStepOutcome {
    /// This worker claimed `node_id`, executed it, and published its `ADAG` commit at `offset`.
    ClaimedAndCommitted {
        /// Executed DAG node ID.
        node_id: u64,
        /// Broker offset of this worker's commit record.
        offset: u64,
        /// Canonical committed output for `node_id` after syncing through `offset`.
        output: Vec<u8>,
    },
    /// Every node in the [`DagSpec`] is already committed on the bus.
    AlreadyComplete,
    /// Uncommitted nodes remain, but every currently ready node holds an unexpired lease
    /// owned by another worker (or awaits parent commits from those leased nodes).
    WaitingOnPeers {
        /// Number of nodes committed so far.
        committed_nodes: usize,
        /// Total nodes in [`DagSpec`].
        total_nodes: usize,
    },
}

/// Multi-worker distributed step-DAG coordinator over any [`WorkflowBus`].
#[derive(Debug)]
pub struct DistributedDag<B> {
    bus: B,
    spec: DagSpec,
    prefix: String,
    worker_id: u64,
    lease_ttl_ms: u64,
    next_seq: u64,
    scan_cursor: u64,
    latest_bt_ms: u64,
    readiness: DagReadiness,
    winner_offsets: Vec<u64>,
    outputs: Vec<Option<Vec<u8>>>,
    leases: Vec<Option<ActiveLease>>,
}

/// Monotone dependency state, updated once per node's first canonical commit.
/// Epochs preserve the candidate snapshot taken at the start of a claim call
/// without copying the entire ready frontier on every single-node execution.
#[derive(Debug)]
struct DagReadiness {
    completed: Vec<bool>,
    completed_nodes: usize,
    remaining: Vec<u64>,
    dependents: Vec<Vec<usize>>,
    ready: BTreeSet<usize>,
    ready_since: Vec<usize>,
    epoch: usize,
}

impl DagReadiness {
    fn new(spec: &DagSpec) -> Self {
        let n = spec.node_count();
        let mut remaining = Vec::with_capacity(n);
        let mut dependents: Vec<Vec<usize>> = (0..n).map(|_| Vec::new()).collect();
        let mut ready = BTreeSet::new();
        for (node, step) in spec.steps().iter().enumerate() {
            let degree = step.deps.len() as u64;
            remaining.push(degree);
            if dag_deps_satisfied(degree) {
                ready.insert(node);
            }
            for &parent in &step.deps {
                if let Some(children) = usize::try_from(parent)
                    .ok()
                    .and_then(|idx| dependents.get_mut(idx))
                {
                    children.push(node);
                }
            }
        }
        Self {
            completed: vec![false; n],
            completed_nodes: 0,
            remaining,
            dependents,
            ready,
            ready_since: vec![0; n],
            epoch: 0,
        }
    }

    fn complete(&mut self, node: usize) {
        let Some(done) = self.completed.get_mut(node) else {
            return;
        };
        if *done {
            return;
        }
        *done = true;
        self.completed_nodes = self.completed_nodes.saturating_add(1);
        self.ready.remove(&node);
        if let Some(children) = self.dependents.get(node) {
            for &child in children {
                #[cfg(test)]
                readiness_tally::edge();
                if let Some(degree) = self.remaining.get_mut(child) {
                    if *degree > 0 {
                        *degree = degree.saturating_sub(1);
                        if dag_deps_satisfied(*degree)
                            && !self.completed.get(child).copied().unwrap_or(true)
                        {
                            self.epoch = self.epoch.saturating_add(1);
                            if let Some(since) = self.ready_since.get_mut(child) {
                                *since = self.epoch;
                            }
                            self.ready.insert(child);
                        }
                    }
                }
            }
        }
    }

    fn next_candidate(&self, after: Option<usize>, snapshot: usize) -> Option<usize> {
        self.ready
            .range((after.map_or(Unbounded, Excluded), Unbounded))
            .find(|&&node| {
                #[cfg(test)]
                readiness_tally::candidate();
                self.ready_since
                    .get(node)
                    .is_some_and(|&since| since <= snapshot)
            })
            .copied()
    }
}

#[cfg(test)]
mod readiness_tally {
    use std::cell::Cell;
    thread_local! {
        static EDGES: Cell<usize> = const { Cell::new(0) };
        static CANDIDATES: Cell<usize> = const { Cell::new(0) };
    }
    pub(super) fn edge() {
        EDGES.with(|count| count.set(count.get().saturating_add(1)));
    }
    pub(super) fn candidate() {
        CANDIDATES.with(|count| count.set(count.get().saturating_add(1)));
    }
    pub(super) fn take() -> (usize, usize) {
        (
            EDGES.with(|count| count.replace(0)),
            CANDIDATES.with(|count| count.replace(0)),
        )
    }
}

impl<B: WorkflowBus> DistributedDag<B> {
    /// Open or attach a worker (`worker_id`) to the distributed DAG under `prefix`,
    /// replaying all lease and commit records currently on `bus`.
    pub fn open(
        bus: B,
        spec: DagSpec,
        prefix: impl Into<String>,
        worker_id: u64,
        lease_ttl_ms: u64,
    ) -> io::Result<Self> {
        let prefix = prefix.into();
        if let Err(e) = validate_workflow_prefix(&prefix) {
            return Err(e.into_io());
        }
        let n = spec.node_count();
        if n > MAX_DISTRIBUTED_STEPS {
            return Err(DistributedFault::TooManySteps { requested: n }.into_io());
        }
        if lease_ttl_ms == 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "distributed DAG lease_ttl_ms must be > 0",
            ));
        }
        let readiness = DagReadiness::new(&spec);
        let mut winner_offsets = Vec::new();
        let mut outputs = Vec::new();
        let mut leases = Vec::new();
        let mut i = 0usize;
        while i < n {
            winner_offsets.push(u64::MAX);
            outputs.push(None);
            leases.push(None);
            i = i.saturating_add(1);
        }
        let mut dag = Self {
            bus,
            spec,
            prefix,
            worker_id,
            lease_ttl_ms,
            next_seq: 1,
            scan_cursor: 0,
            latest_bt_ms: 0,
            readiness,
            winner_offsets,
            outputs,
            leases,
        };
        dag.sync()?;
        Ok(dag)
    }

    /// Borrow the underlying [`WorkflowBus`].
    #[must_use]
    pub const fn bus(&self) -> &B {
        &self.bus
    }

    /// Mutably borrow the underlying [`WorkflowBus`].
    pub fn bus_mut(&mut self) -> &mut B {
        &mut self.bus
    }

    /// Consume the coordinator and return the underlying [`WorkflowBus`].
    #[must_use]
    pub fn into_bus(self) -> B {
        self.bus
    }

    /// Borrow the validated [`DagSpec`].
    #[must_use]
    pub const fn spec(&self) -> &DagSpec {
        &self.spec
    }

    /// Worker identifier for this coordinator handle.
    #[must_use]
    pub const fn worker_id(&self) -> u64 {
        self.worker_id
    }

    /// Lease TTL in milliseconds.
    #[must_use]
    pub const fn lease_ttl_ms(&self) -> u64 {
        self.lease_ttl_ms
    }

    /// Highest broker-stamped wall time (`bt=`, unix ms) observed across synced records.
    #[must_use]
    pub const fn latest_bt_ms(&self) -> u64 {
        self.latest_bt_ms
    }

    /// Number of committed nodes in `0..spec.node_count()`.
    #[must_use]
    pub fn committed_count(&self) -> usize {
        self.readiness.completed_nodes
    }

    /// Whether every node in [`Self::spec`] has committed.
    #[must_use]
    pub fn is_complete(&self) -> bool {
        self.committed_count() == self.spec.node_count()
    }

    /// Canonical committed output bytes for `node_id` (earliest valid commit offset wins).
    #[must_use]
    pub fn committed_output(&self, node_id: u64) -> Option<&[u8]> {
        let Ok(idx) = usize::try_from(node_id) else {
            return None;
        };
        match self.outputs.get(idx) {
            Some(Some(buf)) => Some(buf.as_slice()),
            _ => None,
        }
    }

    /// Broker offset of the canonical winning commit record for `node_id`, if committed.
    #[must_use]
    pub fn winning_commit_offset(&self, node_id: u64) -> Option<u64> {
        let Ok(idx) = usize::try_from(node_id) else {
            return None;
        };
        if !self.readiness.completed.get(idx).copied().unwrap_or(false) {
            return None;
        }
        self.winner_offsets.get(idx).copied()
    }

    /// Active lease state for an uncommitted `node_id`, if any claim has been recorded.
    #[must_use]
    pub fn active_lease(&self, node_id: u64) -> Option<ActiveLease> {
        let Ok(idx) = usize::try_from(node_id) else {
            return None;
        };
        if self.readiness.completed.get(idx).copied().unwrap_or(false) {
            return None;
        }
        match self.leases.get(idx) {
            Some(Some(l)) => Some(*l),
            _ => None,
        }
    }

    /// Replay all newly appended `{prefix}/>` lease and commit records from the bus.
    pub fn sync(&mut self) -> io::Result<()> {
        let filter = format!("{}/>", self.prefix);
        let lease_prefix = format!("{}/lease/", self.prefix);
        let commit_prefix = format!("{}/commit/", self.prefix);
        let mut pages = 0usize;
        loop {
            if pages >= MAX_SYNC_PAGES {
                return Err(DistributedFault::ScanLimitExceeded.into_io());
            }
            pages = pages.saturating_add(1);
            let (rows, (next, head)) =
                self.bus
                    .fetch_records(self.scan_cursor, &filter, DEFAULT_FETCH_BATCH)?;
            for (offset, subject, body, bt_opt) in rows {
                let rec_bt = bt_opt.unwrap_or(0);
                if rec_bt > self.latest_bt_ms {
                    self.latest_bt_ms = rec_bt;
                }
                if let Some(suffix) = subject.strip_prefix(&lease_prefix) {
                    self.apply_lease_record(offset, suffix, &body, rec_bt)?;
                } else if let Some(suffix) = subject.strip_prefix(&commit_prefix) {
                    self.apply_commit_record(offset, suffix, &body)?;
                }
            }
            self.scan_cursor = next;
            if next >= head {
                break;
            }
        }
        Ok(())
    }

    fn apply_lease_record(
        &mut self,
        offset: u64,
        suffix: &str,
        body: &[u8],
        rec_bt_ms: u64,
    ) -> io::Result<()> {
        let Some(subj_node) = parse_u64_decimal(suffix) else {
            return Err(DistributedFault::MalformedLease { offset }.into_io());
        };
        let Some((node_id, worker_id, lease_ttl_ms, digest)) = decode_lease_record(body) else {
            return Err(DistributedFault::MalformedLease { offset }.into_io());
        };
        if node_id != subj_node {
            return Err(DistributedFault::UnknownNode { offset, node_id }.into_io());
        }
        let Some(expected_digest) = self.spec.node_digest(node_id) else {
            return Err(DistributedFault::UnknownNode { offset, node_id }.into_io());
        };
        if !ct_eq(&digest, expected_digest) {
            return Err(DistributedFault::SpecMismatch { offset, node_id }.into_io());
        }
        let Ok(idx) = usize::try_from(node_id) else {
            return Err(DistributedFault::UnknownNode { offset, node_id }.into_io());
        };
        if self.readiness.completed.get(idx).copied().unwrap_or(false) {
            return Ok(());
        }
        let proposed_exp = rec_bt_ms.saturating_add(lease_ttl_ms);
        let cur_lease = match self.leases.get(idx) {
            Some(Some(l)) => Some(*l),
            _ => None,
        };
        match cur_lease {
            None => {
                let exp = dist_lease_expiry_advance(0, proposed_exp);
                if let Some(slot) = self.leases.get_mut(idx) {
                    *slot = Some(ActiveLease {
                        worker_id,
                        offset,
                        expiry_bt_ms: exp,
                    });
                }
            }
            Some(holder) => {
                if holder.worker_id == worker_id
                    || dist_lease_expired(holder.expiry_bt_ms, rec_bt_ms)
                {
                    let exp = dist_lease_expiry_advance(holder.expiry_bt_ms, proposed_exp);
                    if let Some(slot) = self.leases.get_mut(idx) {
                        *slot = Some(ActiveLease {
                            worker_id,
                            offset,
                            expiry_bt_ms: exp,
                        });
                    }
                }
            }
        }
        Ok(())
    }

    fn apply_commit_record(&mut self, offset: u64, suffix: &str, body: &[u8]) -> io::Result<()> {
        let Some(subj_node) = parse_u64_decimal(suffix) else {
            return Err(DistributedFault::MalformedCommit { offset }.into_io());
        };
        if body.len() < DAG_RECORD_MAGIC.len() {
            return Err(DistributedFault::MalformedCommit { offset }.into_io());
        }
        let Some((node_id, digest, output)) = decode_dag_record(body) else {
            return Err(DistributedFault::MalformedCommit { offset }.into_io());
        };
        if node_id != subj_node {
            return Err(DistributedFault::UnknownNode { offset, node_id }.into_io());
        }
        let Some(expected_digest) = self.spec.node_digest(node_id) else {
            return Err(DistributedFault::UnknownNode { offset, node_id }.into_io());
        };
        if !ct_eq(&digest, expected_digest) {
            return Err(DistributedFault::SpecMismatch { offset, node_id }.into_io());
        }
        let Ok(idx) = usize::try_from(node_id) else {
            return Err(DistributedFault::UnknownNode { offset, node_id }.into_io());
        };
        let Some(step_decl) = self.spec.steps().get(idx) else {
            return Err(DistributedFault::UnknownNode { offset, node_id }.into_io());
        };
        for &dep in &step_decl.deps {
            let dep_done = match usize::try_from(dep) {
                Ok(d_idx) => self
                    .readiness
                    .completed
                    .get(d_idx)
                    .copied()
                    .unwrap_or(false),
                Err(_) => false,
            };
            if !dep_done {
                return Err(DistributedFault::TopologicalViolation {
                    offset,
                    node_id,
                    missing_dep: dep,
                }
                .into_io());
            }
        }
        let cur_win = self.winner_offsets.get(idx).copied().unwrap_or(u64::MAX);
        let next_win = dist_winner_offset_min(cur_win, offset);
        if next_win == offset && offset < cur_win {
            if let Some(w_slot) = self.winner_offsets.get_mut(idx) {
                *w_slot = next_win;
            }
            if let Some(o_slot) = self.outputs.get_mut(idx) {
                *o_slot = Some(output.to_vec());
            }
            self.readiness.complete(idx);
            if let Some(l_slot) = self.leases.get_mut(idx) {
                *l_slot = None;
            }
        }
        Ok(())
    }

    /// Attempt to claim and execute one ready DAG node:
    ///
    /// 1. Syncs the bus and snapshots the incrementally maintained ready frontier.
    /// 2. Skips any ready node whose lease is currently held by another worker and is
    ///    known to be unexpired at `latest_bt_ms` — except when no unclaimed node exists,
    ///    in which case it probes candidate ready nodes by publishing a broker-stamped
    ///    `ADLS` claim so the broker's real `bt=` clock decides expired-lease takeover!
    /// 3. Once a claim wins (`active_lease(u).offset == claim_offset && worker_id == self.worker_id`),
    ///    gathers canonical parent `(dep_id, output)` pairs, invokes `exec(node_id, &parent_outputs)`,
    ///    and publishes the `ADAG` commit record to `{prefix}/commit/{node_id}`.
    pub fn claim_and_step_next<F>(&mut self, mut exec: F) -> io::Result<DistributedStepOutcome>
    where
        F: FnMut(u64, &[(u64, &[u8])]) -> io::Result<Vec<u8>>,
    {
        self.sync()?;
        if self.is_complete() {
            return Ok(DistributedStepOutcome::AlreadyComplete);
        }
        let snapshot = self.readiness.epoch;

        // Two-pass candidate selection:
        // Pass 0 tries unclaimed ready nodes (or nodes already leased by `self.worker_id`,
        // or leases already expired relative to `self.latest_bt_ms`) so concurrent workers
        // fan out across independent ready branches without publishing redundant claims.
        // Pass 1 probes remaining ready nodes whose prior holder may have stalled while
        // the bus was idle (`latest_bt_ms` only advances when a new record lands).
        let mut pass = 0u8;
        while pass < 2 {
            let mut after = None;
            while let Some(node_usize) = self.readiness.next_candidate(after, snapshot) {
                after = Some(node_usize);
                let node_id = node_usize as u64;
                self.sync()?;
                if self
                    .readiness
                    .completed
                    .get(node_usize)
                    .copied()
                    .unwrap_or(false)
                {
                    continue;
                }
                // Readiness is monotone: the final parent transition admitted this
                // node, and replayed duplicate commits cannot decrement it twice.
                let unsat = self
                    .readiness
                    .remaining
                    .get(node_usize)
                    .copied()
                    .unwrap_or(1);
                if !dag_deps_satisfied(unsat) {
                    continue;
                }

                let cur_lease = match self.leases.get(node_usize) {
                    Some(Some(l)) => Some(*l),
                    _ => None,
                };
                let should_try = match cur_lease {
                    None => pass == 0,
                    Some(l) if l.worker_id == self.worker_id => pass == 0,
                    Some(l) if dist_lease_expired(l.expiry_bt_ms, self.latest_bt_ms) => pass == 0,
                    Some(_) => pass == 1,
                };
                if !should_try {
                    continue;
                }

                let Some(dep_digest) = self.spec.node_digest(node_id).copied() else {
                    continue;
                };
                let claim_bytes =
                    encode_lease_record(node_id, self.worker_id, self.lease_ttl_ms, &dep_digest);
                let lease_subj = format!("{}/lease/{node_id}", self.prefix);
                let claim_seq = self.next_seq;
                self.next_seq = self.next_seq.saturating_add(1);
                let (claim_off, _) = self.bus.publish_record(
                    self.worker_id,
                    claim_seq,
                    &lease_subj,
                    &claim_bytes,
                )?;
                self.sync()?;

                if self
                    .readiness
                    .completed
                    .get(node_usize)
                    .copied()
                    .unwrap_or(false)
                {
                    continue;
                }
                let won = match self.leases.get(node_usize) {
                    Some(Some(l)) => l.worker_id == self.worker_id && l.offset == claim_off,
                    _ => false,
                };
                if !won {
                    continue;
                }

                // Borrow canonical outputs in declaration order. The callback returns
                // owned bytes, so these borrows end before publishing or syncing again.
                let output = {
                    let mut parent_refs: Vec<(u64, &[u8])> = Vec::new();
                    if let Some(step) = self.spec.steps().get(node_usize) {
                        parent_refs.reserve(step.deps.len());
                        for &dep_id in &step.deps {
                            let bytes = self.committed_output(dep_id).ok_or_else(|| {
                                io::Error::other("distributed DAG parent missing committed output")
                            })?;
                            parent_refs.push((dep_id, bytes));
                        }
                    }
                    exec(node_id, &parent_refs)?
                };
                let commit_bytes = encode_dag_record(node_id, &dep_digest, &output);
                let commit_subj = format!("{}/commit/{node_id}", self.prefix);
                let commit_seq = self.next_seq;
                self.next_seq = self.next_seq.saturating_add(1);
                let (commit_off, _) = self.bus.publish_record(
                    self.worker_id,
                    commit_seq,
                    &commit_subj,
                    &commit_bytes,
                )?;
                self.sync()?;
                let canonical = match self.committed_output(node_id) {
                    Some(b) => b.to_vec(),
                    None => output,
                };
                return Ok(DistributedStepOutcome::ClaimedAndCommitted {
                    node_id,
                    offset: commit_off,
                    output: canonical,
                });
            }
            pass = pass.saturating_add(1);
        }

        if self.is_complete() {
            Ok(DistributedStepOutcome::AlreadyComplete)
        } else {
            Ok(DistributedStepOutcome::WaitingOnPeers {
                committed_nodes: self.committed_count(),
                total_nodes: self.spec.node_count(),
            })
        }
    }

    /// Execute all currently claimable ready nodes until either the DAG completes or all
    /// remaining uncommitted branches are actively leased by live peer workers.
    pub fn run_available<F>(&mut self, mut exec: F) -> io::Result<usize>
    where
        F: FnMut(u64, &[(u64, &[u8])]) -> io::Result<Vec<u8>>,
    {
        let mut ran = 0usize;
        let bound = self.spec.node_count().saturating_add(1);
        let mut iter = 0usize;
        while iter < bound {
            match self.claim_and_step_next(&mut exec)? {
                DistributedStepOutcome::ClaimedAndCommitted { .. } => {
                    ran = ran.saturating_add(1);
                }
                DistributedStepOutcome::AlreadyComplete
                | DistributedStepOutcome::WaitingOnPeers { .. } => break,
            }
            iter = iter.saturating_add(1);
        }
        Ok(ran)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dag::DagStep;

    fn diamond_spec() -> DagSpec {
        DagSpec::new(vec![
            DagStep::new(0, vec![]),
            DagStep::new(1, vec![0]),
            DagStep::new(2, vec![0]),
            DagStep::new(3, vec![1, 2]),
        ])
        .expect("valid diamond DAG")
    }

    #[test]
    fn linear_distributed_workflow_resumes_across_worker_crash() {
        let bus = InMemoryWorkflowBus::new(5_000);
        let mut calls_w1 = Vec::new();
        {
            let mut w1 = DistributedWorkflow::open(bus.clone(), "/wf/linear", 4, 101).unwrap();
            let err = w1
                .run(|idx, prev| {
                    calls_w1.push(idx);
                    if idx == 2 {
                        return Err(io::Error::other("simulated worker 1 crash at step 2"));
                    }
                    Ok(
                        format!("{prev_s}->s{idx}", prev_s = String::from_utf8_lossy(prev))
                            .into_bytes(),
                    )
                })
                .unwrap_err();
            assert!(err.to_string().contains("crash at step 2"));
        }
        assert_eq!(calls_w1, vec![0, 1, 2]);

        let mut calls_w2 = Vec::new();
        let mut w2 = DistributedWorkflow::open(bus, "/wf/linear", 4, 202).unwrap();
        assert_eq!(w2.committed_steps(), 2);
        let outputs = w2
            .run(|idx, prev| {
                calls_w2.push(idx);
                Ok(
                    format!("{prev_s}->s{idx}", prev_s = String::from_utf8_lossy(prev))
                        .into_bytes(),
                )
            })
            .unwrap();
        assert_eq!(calls_w2, vec![2, 3], "steps 0 and 1 must not re-run");
        assert_eq!(String::from_utf8_lossy(&outputs[3]), "->s0->s1->s2->s3");
    }

    #[test]
    fn multi_worker_dag_fans_out_without_duplicate_execution() {
        let bus = InMemoryWorkflowBus::new(10_000);
        let spec = diamond_spec();
        let mut w1 = DistributedDag::open(bus.clone(), spec.clone(), "/wf/diamond", 1, 5_000)
            .expect("open w1");
        let mut w2 =
            DistributedDag::open(bus.clone(), spec, "/wf/diamond", 2, 5_000).expect("open w2");

        // Worker 1 runs root node 0.
        let out0 = w1
            .claim_and_step_next(|id, parents| {
                assert_eq!(id, 0);
                assert!(parents.is_empty());
                Ok(b"root".to_vec())
            })
            .unwrap();
        assert!(matches!(
            out0,
            DistributedStepOutcome::ClaimedAndCommitted { node_id: 0, .. }
        ));

        // Now nodes 1 and 2 are both ready! Simulate w1 holding an active lease on node 1
        // while w2 steps concurrently: w1 claims node 1 manually via lease record, and w2
        // automatically skips node 1 and claims/commits node 2!
        let d1 = *w1.spec().node_digest(1).unwrap();
        let manual_claim = encode_lease_record(1, 99, 5_000, &d1);
        bus.clone()
            .publish_record(99, 1, "/wf/diamond/lease/1", &manual_claim)
            .unwrap();

        let out_w2 = w2
            .claim_and_step_next(|id, parents| {
                assert_eq!(
                    id, 2,
                    "w2 must skip live-leased node 1 and execute ready node 2"
                );
                assert_eq!(parents, &[(0, &b"root"[..])]);
                Ok(b"branch-2".to_vec())
            })
            .unwrap();
        assert!(matches!(
            out_w2,
            DistributedStepOutcome::ClaimedAndCommitted { node_id: 2, .. }
        ));

        // While worker 99's lease on node 1 is still unexpired (clock = 10_000 < 15_000),
        // w2 sees WaitingOnPeers!
        let wait = w2
            .claim_and_step_next(|_, _| panic!("must not steal unexpired lease"))
            .unwrap();
        assert_eq!(
            wait,
            DistributedStepOutcome::WaitingOnPeers {
                committed_nodes: 2,
                total_nodes: 4
            }
        );

        // Advance broker clock past lease_ttl_ms (10_000 + 5_000 = 15_000): w1 takes over
        // stalled worker 99's expired lease on node 1 and completes node 3!
        bus.advance_clock_ms(5_001);
        let ran = w1
            .run_available(|id, parents| match id {
                1 => {
                    assert_eq!(parents, &[(0, &b"root"[..])]);
                    Ok(b"branch-1-takeover".to_vec())
                }
                3 => {
                    assert_eq!(
                        parents,
                        &[(1, &b"branch-1-takeover"[..]), (2, &b"branch-2"[..])]
                    );
                    Ok(b"joined".to_vec())
                }
                other => panic!("unexpected node {other}"),
            })
            .unwrap();
        assert_eq!(ran, 2);
        assert!(w1.is_complete());
        w2.sync().unwrap();
        assert!(w2.is_complete());
        assert_eq!(w2.committed_output(3), Some(&b"joined"[..]));
    }

    #[test]
    fn zombie_worker_late_commit_never_overwrites_canonical_winner() {
        let bus = InMemoryWorkflowBus::new(1_000);
        let spec = DagSpec::new(vec![DagStep::new(0, vec![]), DagStep::new(1, vec![0])]).unwrap();
        let mut w1 =
            DistributedDag::open(bus.clone(), spec.clone(), "/wf/zombie", 1, 2_000).unwrap();

        let _ = w1
            .claim_and_step_next(|id, _| {
                assert_eq!(id, 0);
                Ok(b"canonical-winner".to_vec())
            })
            .unwrap();
        let win_off = w1.winning_commit_offset(0).unwrap();

        // Stale/zombie worker publishes a conflicting late commit for node 0 at a higher offset.
        let d0 = *w1.spec().node_digest(0).unwrap();
        let zombie_commit = encode_dag_record(0, &d0, b"zombie-overwrite");
        let (late_off, _) = bus
            .clone()
            .publish_record(777, 1, "/wf/zombie/commit/0", &zombie_commit)
            .unwrap();
        assert!(late_off > win_off);

        // Fresh worker opening the bus must still see `canonical-winner` and run node 1 with it!
        let mut w2 = DistributedDag::open(bus, spec, "/wf/zombie", 2, 2_000).unwrap();
        assert_eq!(w2.winning_commit_offset(0), Some(win_off));
        assert_eq!(w2.committed_output(0), Some(&b"canonical-winner"[..]));
        let _ = w2
            .claim_and_step_next(|id, parents| {
                assert_eq!(id, 1);
                assert_eq!(parents, &[(0, &b"canonical-winner"[..])]);
                Ok(b"child-ok".to_vec())
            })
            .unwrap();
        assert!(w2.is_complete());
    }

    #[test]
    fn spec_drift_on_bus_fails_closed_with_spec_mismatch() {
        let bus = InMemoryWorkflowBus::new(1_000);
        let spec_v1 =
            DagSpec::new(vec![DagStep::new(0, vec![]), DagStep::new(1, vec![0])]).unwrap();
        let mut w1 = DistributedDag::open(bus.clone(), spec_v1, "/wf/drift", 1, 2_000).unwrap();
        w1.run_available(|id, _| Ok(format!("out-{id}").into_bytes()))
            .unwrap();

        // Modified DAG where node 1 no longer depends on node 0 has a different SHA-256 digest!
        let spec_v2 = DagSpec::new(vec![DagStep::new(0, vec![]), DagStep::new(1, vec![])]).unwrap();
        let err = DistributedDag::open(bus, spec_v2, "/wf/drift", 2, 2_000).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
        assert!(err.to_string().contains("spec mismatch for node 1"));
    }
}

#[cfg(test)]
mod readiness_tests {
    use super::*;
    use crate::dag::DagStep;

    fn cached_ready(state: &DagReadiness, snapshot: usize) -> Vec<u64> {
        let mut found = Vec::new();
        let mut after = None;
        while let Some(node) = state.next_candidate(after, snapshot) {
            found.push(node as u64);
            after = Some(node);
        }
        found
    }

    #[test]
    fn readiness_matches_stateless_oracle_across_every_four_node_dag_and_completion_order() {
        const N: usize = 4;
        let edges: Vec<_> = (0..N)
            .flat_map(|child| {
                (0..N)
                    .filter(move |&parent| parent != child)
                    .map(move |parent| (parent, child))
            })
            .collect();
        for mask in 0usize..1usize << edges.len() {
            let mut steps: Vec<_> = (0..N)
                .map(|id| DagStep::new(id as u64, Vec::new()))
                .collect();
            for (bit, &(parent, child)) in edges.iter().enumerate() {
                if mask & (1 << bit) != 0 {
                    steps[child].deps.push(parent as u64);
                }
            }
            let Ok(spec) = DagSpec::new(steps) else {
                continue;
            };
            for a in 0..N {
                for b in 0..N {
                    for c in 0..N {
                        for d in 0..N {
                            let order = [a, b, c, d];
                            let mut unique = order;
                            unique.sort_unstable();
                            if unique != [0, 1, 2, 3] {
                                continue;
                            }
                            let mut state = DagReadiness::new(&spec);
                            let mut completed = vec![false; N];
                            for node in order {
                                let expected = spec.ready_nodes(&completed);
                                assert_eq!(cached_ready(&state, state.epoch), expected);
                                assert_eq!(
                                    state.completed_nodes,
                                    completed.iter().filter(|&&v| v).count()
                                );
                                if !expected.contains(&(node as u64)) {
                                    break;
                                }
                                state.complete(node);
                                completed[node] = true;
                                let epoch = state.epoch;
                                state.complete(node); // Replayed prefix/duplicate winner.
                                assert_eq!(state.epoch, epoch);
                                assert_eq!(state.completed, completed);
                                assert_eq!(
                                    cached_ready(&state, state.epoch),
                                    spec.ready_nodes(&completed)
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn candidate_epochs_preserve_initial_snapshot_when_sync_admits_lower_nodes() {
        let spec = DagSpec::new(vec![
            DagStep::new(0, vec![2]),
            DagStep::new(1, vec![]),
            DagStep::new(2, vec![]),
            DagStep::new(3, vec![0]),
        ])
        .unwrap();
        let mut state = DagReadiness::new(&spec);
        let first = state.epoch;
        assert_eq!(cached_ready(&state, first), vec![1, 2]);
        state.complete(2);
        assert_eq!(cached_ready(&state, first), vec![1]);
        let second = state.epoch;
        assert_eq!(cached_ready(&state, second), vec![0, 1]);
        state.complete(0);
        assert_eq!(cached_ready(&state, first), vec![1]);
        assert_eq!(cached_ready(&state, second), vec![1]);
        assert_eq!(cached_ready(&state, state.epoch), vec![1, 3]);
    }

    #[test]
    fn failed_sync_replays_do_not_double_release_dependencies_or_count_commits() {
        let mut bus = InMemoryWorkflowBus::new(100);
        let spec = DagSpec::new(vec![DagStep::new(0, vec![]), DagStep::new(1, vec![0])]).unwrap();
        let digest = *spec.node_digest(0).unwrap();
        let mut dag = DistributedDag::open(bus.clone(), spec, "/wf/replay-ready", 1, 500).unwrap();
        bus.publish_record(
            7,
            1,
            "/wf/replay-ready/commit/0",
            &encode_dag_record(0, &digest, b"root"),
        )
        .unwrap();
        bus.publish_record(7, 2, "/wf/replay-ready/commit/1", b"invalid commit")
            .unwrap();
        for _ in 0..3 {
            assert_eq!(dag.sync().unwrap_err().kind(), io::ErrorKind::InvalidData);
            assert_eq!(dag.committed_count(), 1);
            assert_eq!(
                dag.scan_cursor, 0,
                "page retries the valid prefix before its malformed tail"
            );
            assert_eq!(dag.readiness.remaining, vec![0, 0]);
            assert_eq!(dag.readiness.epoch, 1);
            assert_eq!(cached_ready(&dag.readiness, dag.readiness.epoch), vec![1]);
        }
    }

    #[test]
    fn callback_failure_and_panic_leave_the_node_ready_for_a_real_commit() {
        let spec = DagSpec::new(vec![DagStep::new(0, vec![]), DagStep::new(1, vec![0])]).unwrap();
        let mut dag = DistributedDag::open(
            InMemoryWorkflowBus::new(100),
            spec,
            "/wf/retry-ready",
            1,
            500,
        )
        .unwrap();
        let err = dag
            .claim_and_step_next(|node, _| {
                assert_eq!(node, 0);
                Err(io::Error::other("callback failed"))
            })
            .unwrap_err();
        assert_eq!(err.to_string(), "callback failed");
        assert_eq!(dag.committed_count(), 0);
        assert_eq!(cached_ready(&dag.readiness, dag.readiness.epoch), vec![0]);
        let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = dag.claim_and_step_next(|node, _| {
                assert_eq!(node, 0);
                panic!("callback panic")
            });
        }));
        assert!(panic.is_err());
        assert_eq!(dag.committed_count(), 0);
        assert_eq!(cached_ready(&dag.readiness, dag.readiness.epoch), vec![0]);
        let root = dag
            .claim_and_step_next(|node, _| {
                assert_eq!(node, 0);
                Ok(b"root".to_vec())
            })
            .unwrap();
        assert!(matches!(
            root,
            DistributedStepOutcome::ClaimedAndCommitted { node_id: 0, .. }
        ));
        assert_eq!(dag.committed_count(), 1);
        assert_eq!(cached_ready(&dag.readiness, dag.readiness.epoch), vec![1]);
        dag.claim_and_step_next(|node, parents| {
            assert_eq!(node, 1);
            assert_eq!(parents, &[(0, &b"root"[..])]);
            Ok(b"child".to_vec())
        })
        .unwrap();
        assert!(dag.is_complete());
    }

    #[test]
    fn durable_commit_publish_error_is_replayed_before_callback_retry() {
        struct FailAfterFirstCommit {
            inner: InMemoryWorkflowBus,
            fail_commit: bool,
        }

        impl WorkflowBus for FailAfterFirstCommit {
            fn publish_record(
                &mut self,
                producer_id: u64,
                producer_seq: u64,
                subject: &str,
                body: &[u8],
            ) -> io::Result<(u64, bool)> {
                let published =
                    self.inner
                        .publish_record(producer_id, producer_seq, subject, body)?;
                if self.fail_commit && subject == "/wf/ambiguous-publish/commit/0" {
                    self.fail_commit = false;
                    return Err(io::Error::other("commit persisted before publish failed"));
                }
                Ok(published)
            }

            fn fetch_records(
                &mut self,
                from_offset: u64,
                filter: &str,
                max: u32,
            ) -> io::Result<(Vec<BusRecord>, (u64, u64))> {
                self.inner.fetch_records(from_offset, filter, max)
            }
        }

        let mut bus = InMemoryWorkflowBus::new(100);
        let spec = DagSpec::new(vec![DagStep::new(0, vec![]), DagStep::new(1, vec![0])]).unwrap();
        let mut dag = DistributedDag::open(
            FailAfterFirstCommit {
                inner: bus.clone(),
                fail_commit: true,
            },
            spec,
            "/wf/ambiguous-publish",
            1,
            500,
        )
        .unwrap();
        let mut calls = Vec::new();
        let err = dag
            .claim_and_step_next(|node, parents| {
                calls.push(node);
                assert_eq!(node, 0);
                assert!(parents.is_empty());
                Ok(b"canonical root".to_vec())
            })
            .unwrap_err();
        assert_eq!(err.to_string(), "commit persisted before publish failed");
        assert_eq!(calls, vec![0]);
        assert_eq!(dag.committed_count(), 0);
        assert_eq!(dag.committed_output(0), None);

        // The transport returned an error after the real shared bus accepted the
        // commit. Read it through the public bus API before retrying the worker.
        let (rows, (next, head)) = bus.fetch_records(0, "/wf/ambiguous-publish/>", 8).unwrap();
        assert_eq!((next, head), (2, 2));
        assert_eq!(rows.len(), 2);
        assert_eq!(rows[1].1, "/wf/ambiguous-publish/commit/0");
        let (node, _, output) = decode_dag_record(&rows[1].2).unwrap();
        assert_eq!(node, 0);
        assert_eq!(output, b"canonical root");

        let outcome = dag
            .claim_and_step_next(|node, parents| {
                calls.push(node);
                assert_eq!(node, 1, "the persisted root callback must not repeat");
                assert_eq!(parents, &[(0, &b"canonical root"[..])]);
                Ok(b"child".to_vec())
            })
            .unwrap();
        assert_eq!(
            outcome,
            DistributedStepOutcome::ClaimedAndCommitted {
                node_id: 1,
                offset: 3,
                output: b"child".to_vec(),
            }
        );
        assert_eq!(calls, vec![0, 1]);
        assert_eq!(dag.winning_commit_offset(0), Some(1));
        assert_eq!(dag.committed_output(0), Some(&b"canonical root"[..]));
        assert_eq!(dag.committed_output(1), Some(&b"child"[..]));
        assert_eq!(dag.committed_count(), 2);
        assert!(dag.is_complete());
        assert_eq!(bus.head(), 4);
        assert_eq!(
            dag.claim_and_step_next(|_, _| panic!("complete DAG must not execute callbacks"))
                .unwrap(),
            DistributedStepOutcome::AlreadyComplete
        );
        assert_eq!(bus.head(), 4);
    }

    #[test]
    fn callback_borrows_canonical_parent_buffers_in_declared_order() {
        let mut bus = InMemoryWorkflowBus::new(100);
        let spec = DagSpec::new(vec![
            DagStep::new(0, vec![]),
            DagStep::new(1, vec![]),
            DagStep::new(2, vec![1, 0]),
        ])
        .unwrap();
        for node in 0..2 {
            let bytes = vec![node as u8; 1 << 20];
            let body = encode_dag_record(node, spec.node_digest(node).unwrap(), &bytes);
            bus.publish_record(8, node + 1, &format!("/wf/borrow/commit/{node}"), &body)
                .unwrap();
        }
        let mut dag = DistributedDag::open(bus, spec, "/wf/borrow", 1, 500).unwrap();
        let parent0 = dag.committed_output(0).unwrap().as_ptr();
        let parent1 = dag.committed_output(1).unwrap().as_ptr();
        let outcome = dag
            .claim_and_step_next(|node, parents| {
                assert_eq!(node, 2);
                assert_eq!(parents.len(), 2);
                assert_eq!(parents[0].0, 1);
                assert_eq!(parents[1].0, 0);
                assert_eq!(
                    parents[0].1.as_ptr(),
                    parent1,
                    "must not clone a megabyte parent"
                );
                assert_eq!(parents[1].1.as_ptr(), parent0);
                assert_eq!(parents[0].1, vec![1; 1 << 20]);
                assert_eq!(parents[1].1, vec![0; 1 << 20]);
                Ok(b"joined".to_vec())
            })
            .unwrap();
        assert!(matches!(
            outcome,
            DistributedStepOutcome::ClaimedAndCommitted { node_id: 2, .. }
        ));
        assert!(dag.is_complete());
        assert_eq!(dag.committed_count(), 3);
    }

    fn shape(n: usize, kind: &str) -> DagSpec {
        DagSpec::new(
            (0..n)
                .map(|node| {
                    let deps = match kind {
                        "chain" if node > 0 => vec![node as u64 - 1],
                        "fanout" if node > 0 => vec![0],
                        "fanin" if node + 1 == n => (0..node as u64).collect(),
                        _ => Vec::new(),
                    };
                    DagStep::new(node as u64, deps)
                })
                .collect(),
        )
        .unwrap()
    }

    #[test]
    fn dependency_transitions_and_candidate_visits_are_linear_in_nodes_and_edges() {
        for kind in ["independent", "chain", "fanout", "fanin"] {
            let spec = shape(MAX_DISTRIBUTED_STEPS, kind);
            let edges: usize = spec.steps().iter().map(|step| step.deps.len()).sum();
            let mut state = DagReadiness::new(&spec);
            let _ = readiness_tally::take();
            for _ in 0..spec.node_count() {
                let node = state.next_candidate(None, state.epoch).unwrap();
                state.complete(node);
                state.complete(node);
            }
            assert!(state.next_candidate(None, state.epoch).is_none());
            assert_eq!(state.completed_nodes, spec.node_count());
            assert_eq!(readiness_tally::take(), (edges, spec.node_count()));
        }
    }

    fn scan_execution(spec: &DagSpec) -> Vec<u64> {
        let mut completed = vec![false; spec.node_count()];
        let mut order = Vec::with_capacity(spec.node_count());
        while completed.iter().any(|&done| !done) {
            let node = spec.ready_nodes(&completed)[0];
            completed[node as usize] = true;
            order.push(node);
        }
        order
    }

    fn indexed_execution(spec: &DagSpec) -> Vec<u64> {
        let mut state = DagReadiness::new(spec);
        let mut order = Vec::with_capacity(spec.node_count());
        while state.completed_nodes < spec.node_count() {
            let node = state.next_candidate(None, state.epoch).unwrap();
            state.complete(node);
            order.push(node as u64);
        }
        order
    }

    #[test]
    #[ignore = "manual dependency-readiness CPU comparison, excluding bus and payload copying"]
    fn readiness_microbench() {
        use std::time::Instant;
        for kind in ["independent", "chain", "fanout", "fanin"] {
            for n in [256, 1024, MAX_DISTRIBUTED_STEPS] {
                let spec = shape(n, kind);
                let started = Instant::now();
                let old = scan_execution(&spec);
                let scan = started.elapsed();
                let started = Instant::now();
                let new = indexed_execution(&spec);
                let indexed = started.elapsed();
                assert_eq!(old, new);
                eprintln!(
                    "READINESS shape={kind} nodes={n} scan_ns={} indexed_ns={} speedup={:.2}",
                    scan.as_nanos(),
                    indexed.as_nanos(),
                    scan.as_secs_f64() / indexed.as_secs_f64()
                );
            }
        }
    }
}
