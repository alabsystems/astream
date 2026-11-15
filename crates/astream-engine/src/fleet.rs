//! Fleet consistent-cut replay (the fleet rung — a green slice of it).
//!
//! An agent fleet is a forest of independent single-writer logs. A global
//! checkpoint is a **consistent cut**: a vector of per-partition offsets such
//! that for every recorded cross-injection edge — an orchestrator's `Out` in one
//! log *caused* a child's injected `In` in another — if the cut admits the effect
//! it must also admit the cause. That is the condition a Chandy-Lamport snapshot
//! guarantees, but no snapshot protocol runs here (no markers, no channel
//! recording): a cut is any offset vector a caller names, judged after the fact
//! against the cross-edges recorded in the logs. Replaying each partition from
//! its first record up to and including its cut offset re-folds the exact screen
//! as of that cut.
//!
//! A [`CrossEdge`] is fleet-coordination metadata built **over** the logs from
//! the real [`Offset`]s the appends returned — never smuggled into `client_seq`
//! (a different numbering domain). It has two sources: the in-memory edge the
//! producers hold (the offsets their appends returned), and the **durable**
//! one: the envelope's `caused_by` pointer (`ENV_VERSION` 3), from which
//! [`cross_edges_from_logs`] rebuilds the same edges out of the stored bytes
//! alone after a crash/reconnect (claim `term.fleet.durable-watermark`).
//!
//! Every reader here goes through [`Log::read_bytes`], so the fleet functions
//! and `recover` agree on exactly which prefix of a log is intact: a corrupt,
//! unreadable, or out-of-sequence frame ends it for all of them.

use crate::log::{Log, ReadError};
use crate::session::StateSnapshot;
use astream_term::{Folder, Screen};
use astream_wire::{CausalCut, CausalEdge, CutViolation, Offset};
use std::collections::{BTreeMap, BTreeSet};

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "fleet_island.rs"]
mod fleet_island;
#[cfg(not(clean_islands))]
pub use crate::twins::fleet_clamp_to_cut;
#[cfg(clean_islands)]
pub use fleet_island::fleet_clamp_to_cut;

contract_fn! {
    /// Kernel-certified check that a record sequence number `seq` is admitted by a
    /// partition cut frontier `cut_off` (`seq <= cut_off`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `fleet_seq_within_cut_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn fleet_seq_within_cut(seq: u64, cut_off: u64) -> bool
    clauses [ensures result == (seq <= cut_off)]
    {
        seq <= cut_off
    }
}

/// A fleet partition id (which session log).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Partition(pub u64);

/// One recorded cross-injection: the `cause` `Out` (in one partition) produced
/// the `effect` injected `In` (in another). `cause.0 != effect.0`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CrossEdge {
    /// The producing partition and the offset of the `Out` that caused the inject.
    pub cause: (Partition, Offset),
    /// The receiving partition and the offset of the injected `In`.
    pub effect: (Partition, Offset),
}

impl From<CrossEdge> for CausalEdge<Partition> {
    fn from(e: CrossEdge) -> Self {
        Self {
            cause: e.cause,
            effect: e.effect,
        }
    }
}

impl From<CausalEdge<Partition>> for CrossEdge {
    fn from(e: CausalEdge<Partition>) -> Self {
        Self {
            cause: e.cause,
            effect: e.effect,
        }
    }
}

/// A global checkpoint: each partition's highest offset included in the cut.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Cut {
    /// Per-partition cut offsets (the highest offset the cut admits in each).
    /// If a partition is listed more than once, the first entry is the one that
    /// counts ([`offset_of`](Self::offset_of)).
    pub offsets: Vec<(Partition, Offset)>,
}

impl Cut {
    /// The cut offset for partition `p`, if the cut names it (first entry wins).
    pub fn offset_of(&self, p: Partition) -> Option<Offset> {
        self.offsets.iter().find(|(q, _)| *q == p).map(|(_, o)| *o)
    }

    /// Project this [`Cut`] onto the shared [`CausalCut`] frontier lattice in
    /// `astream-wire` (preserving first-entry-wins semantics on duplicate partitions).
    #[must_use]
    pub fn to_causal_cut(&self) -> CausalCut<Partition> {
        CausalCut::from_first_wins(self.offsets.iter().copied())
    }

    /// Build a [`Cut`] from a [`CausalCut<Partition>`].
    #[must_use]
    pub fn from_causal_cut(cut: &CausalCut<Partition>) -> Self {
        let len = cut.len();
        let cap = if len < 4096 { len } else { 4096 };
        let mut offsets = Vec::with_capacity(cap);
        for (&p, &off) in cut.iter() {
            offsets.push((p, off));
        }
        Self { offsets }
    }
}

fn causal_edges_of(edges: &[CrossEdge]) -> Vec<CausalEdge<Partition>> {
    let len = edges.len();
    let cap = if len < 4096 { len } else { 4096 };
    let mut causal_edges = Vec::with_capacity(cap);
    for &e in edges {
        causal_edges.push(CausalEdge::from(e));
    }
    causal_edges
}

/// Does the cut admit `at` in partition `p` (`at <= the cut offset for p`)? A
/// partition the cut does not name admits nothing.
pub fn cut_includes(cut: &Cut, p: Partition, at: Offset) -> bool {
    match cut.offset_of(p) {
        Some(o) => fleet_seq_within_cut(at.0, o.0),
        None => false,
    }
}

/// Cut consistency: for every cross-edge whose **effect** the cut
/// admits, it must also admit the **cause**. An effect-without-cause cut is an
/// orphaned injection (causally impossible) and is rejected; a cause-without-
/// effect cut is an in-flight (sent-not-yet-delivered) message and is admitted.
///
/// Unified with [`astream_wire::CausalCut::is_consistent`].
pub fn is_consistent(cut: &Cut, edges: &[CrossEdge]) -> bool {
    let causal_edges = causal_edges_of(edges);
    cut.to_causal_cut().is_consistent(&causal_edges)
}

/// Return the first edge in `edges` the cut violates, or `None` if `cut` is
/// consistent.
pub fn first_violation(cut: &Cut, edges: &[CrossEdge]) -> Option<CutViolation<Partition>> {
    let causal_edges = causal_edges_of(edges);
    cut.to_causal_cut().first_violation(&causal_edges)
}

/// Compute the minimal causal closure of `cut` over `edges`, advancing lagging
/// source partitions so every admitted effect's transitive cause is included.
pub fn heal_cut(cut: &Cut, edges: &[CrossEdge]) -> (Cut, usize) {
    let causal_edges = causal_edges_of(edges);
    let mut c = cut.to_causal_cut();
    let repairs = c.heal(&causal_edges);
    (Cut::from_causal_cut(&c), repairs)
}

/// Rebuild the fleet's cross-edges from the **stored log bytes alone** — the
/// durable path. For each partition's log, decode every envelope and, for every
/// record whose `caused_by` names a *different* partition, emit a [`CrossEdge`]
/// from that cross-log cause to this record. Unlike the in-memory [`CrossEdge`]s
/// the producers held, this survives crash/reconnect: the causality is on the log.
///
/// Decoding is [`Log::read_bytes`]'s: it stops at the first frame that is
/// malformed, unreadable, **or out of sequence** — the same boundary
/// [`crate::recover`] and [`replay_to_cut`] stop at — so no edge is ever emitted
/// for a record that a replay of the same bytes could not reach. Panic-free.
pub fn cross_edges_from_logs(logs: &[(Partition, &[u8])]) -> Vec<CrossEdge> {
    let mut edges = Vec::new();
    for (part, bytes) in logs {
        let mut reader = Log::read_bytes(bytes, Offset::ZERO);
        while let Some(item) = reader.next_metadata() {
            let Ok(env) = item else { break };
            if let Some(cb) = env.caused_by {
                if let Some(cause_part) = cb.partition {
                    if cause_part != part.0 {
                        edges.push(CrossEdge {
                            cause: (Partition(cause_part), Offset(cb.offset)),
                            effect: (*part, env.seq),
                        });
                    }
                }
            }
        }
    }
    edges
}

/// The result of replaying one partition to a cut.
#[derive(Debug, Clone)]
pub struct CutReplay {
    /// The screen folded from the records the cut admits.
    pub screen: Screen,
    /// The last offset actually folded — `None` if no record was (the cut does
    /// not name the partition, or the log is empty). Compare with the cut offset
    /// to know whether the log reached the cut or ended before it.
    pub folded_through: Option<Offset>,
}

/// Replay one partition up to the cut: a separate read-by-offset pass over its
/// stored bytes from offset 0, folding the prefix up to and including the cut
/// offset. (The
/// byte-identical replay path; a partition the cut does not name folds empty.)
///
/// A decode error **before** the cut offset is returned, never folded over: a
/// checkpoint restored from a damaged partition must not look like a valid,
/// shorter screen. Bytes after the cut offset are not read at all.
pub fn replay_to_cut(
    cut: &Cut,
    p: Partition,
    log_bytes: &[u8],
    cols: u16,
    rows: u16,
) -> Result<CutReplay, ReadError> {
    let mut folder = Folder::new(cols, rows);
    let mut folded_through = None;
    if let Some(cut_off) = cut.offset_of(p) {
        for item in Log::read_bytes(log_bytes, Offset::ZERO) {
            let env = item?;
            if !fleet_seq_within_cut(env.seq.0, cut_off.0) {
                break; // unreachable on a dense log (we stop AT the cut), kept as a guard
            }
            let seq = Offset(fleet_clamp_to_cut(env.seq.0, cut_off.0));
            folded_through = Some(seq);
            folder.apply(&env.record);
            if seq == cut_off {
                break; // the cut is folded: the reader is lazy, so nothing after it is decoded
            }
        }
    }
    Ok(CutReplay {
        screen: folder.into_screen(),
        folded_through,
    })
}

/// Why materializing or resuming a fleet-wide `/a/state` view over a cut failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FleetError {
    /// The cut violates causal consistency (it admits an injected
    /// effect without admitting its cause).
    InconsistentCut(CutViolation<Partition>),
    /// Decoding a partition's log failed.
    Read {
        /// The partition whose log failed to decode.
        partition: Partition,
        /// The underlying read/decode error.
        err: ReadError,
    },
}

impl std::fmt::Display for FleetError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FleetError::InconsistentCut(v) => write!(
                f,
                "inconsistent fleet cut: effect ({}, {}) admitted without cause ({}, {})",
                v.edge.effect.0 .0, v.edge.effect.1 .0, v.edge.cause.0 .0, v.edge.cause.1 .0
            ),
            FleetError::Read { partition, err } => {
                write!(f, "partition {} log error: {err}", partition.0)
            }
        }
    }
}

impl std::error::Error for FleetError {}

/// One partition's materialized `/a/state` view inside a [`FleetSnapshot`].
#[derive(Debug, Clone)]
pub struct FleetPartitionState {
    /// The partition id.
    pub partition: Partition,
    /// The materialized `/a/state` snapshot folded through the partition's cut offset.
    pub snapshot: StateSnapshot,
}

/// A fleet-wide `/a/state`-verb materialized view over a consistent cut.
///
/// Holds each partition's [`StateSnapshot`] (including parser state and
/// `folded_through` watermark) at its cut offset, together with the verified [`Cut`]
/// and durable [`CrossEdge`]s rebuilt from the logs. Resuming via
/// [`resume_fleet_cut`] folds only the tail records after each partition's
/// `folded_through` watermark.
#[derive(Debug, Clone)]
pub struct FleetSnapshot {
    /// The verified consistent cut this snapshot materializes.
    pub cut: Cut,
    /// The cross-partition causal edges rebuilt from the stored logs.
    pub edges: Vec<CrossEdge>,
    /// Per-partition materialized `/a/state` snapshots, in cut order.
    pub partitions: Vec<FleetPartitionState>,
}

impl FleetSnapshot {
    /// Look up partition `p`'s materialized [`StateSnapshot`] in this fleet view.
    #[must_use]
    pub fn partition(&self, p: Partition) -> Option<&StateSnapshot> {
        self.partitions
            .iter()
            .find(|ps| ps.partition == p)
            .map(|ps| &ps.snapshot)
    }

    /// Look up partition `p`'s screen as of this fleet cut.
    #[must_use]
    pub fn screen(&self, p: Partition) -> Option<&Screen> {
        self.partition(p).map(StateSnapshot::screen)
    }
}

// Below the measured directory crossover, preserve allocation-free scans.
const PARTITION_INDEX_MIN: usize = 128;

/// First-entry-wins log lookup. Larger calls index only as far as callers need:
/// every directory entry is visited at most once across all lookups, and an
/// early match does not index an otherwise unused suffix of the supplied logs.
/// Tiny calls retain linear scans without allocating index nodes.
struct PartitionLogs<'logs, 'bytes> {
    remaining: std::slice::Iter<'logs, (Partition, &'bytes [u8])>,
    first: BTreeMap<Partition, &'bytes [u8]>,
    indexed: bool,
    #[cfg(test)]
    visited: usize,
}

impl<'logs, 'bytes> PartitionLogs<'logs, 'bytes> {
    fn new(logs: &'logs [(Partition, &'bytes [u8])], lookups: usize) -> Self {
        #[cfg(test)]
        scaling_tests::note_lookup_hint(lookups);
        Self {
            remaining: logs.iter(),
            first: BTreeMap::new(),
            indexed: lookups >= PARTITION_INDEX_MIN,
            #[cfg(test)]
            visited: 0,
        }
    }

    fn get(&mut self, partition: Partition) -> &'bytes [u8] {
        if !self.indexed {
            return self
                .remaining
                .as_slice()
                .iter()
                .find(|&&(part, _)| part == partition)
                .map_or(&[][..], |&(_, bytes)| bytes);
        }
        if let Some(&bytes) = self.first.get(&partition) {
            return bytes;
        }
        for &(part, bytes) in self.remaining.by_ref() {
            #[cfg(test)]
            {
                self.visited = self.visited.saturating_add(1);
            }
            self.first.entry(part).or_insert(bytes);
            if part == partition {
                return bytes;
            }
        }
        &[]
    }
}

/// Materialize a fleet-wide `/a/state` view over `cut` from each partition's stored
/// log bytes.
///
/// Rebuilds the fleet's durable [`CrossEdge`]s via [`cross_edges_from_logs`] and
/// verifies the cut's causal consistency via [`CausalCut::first_violation`] **before**
/// folding: an orphaned-injection cut is refused with
/// [`FleetError::InconsistentCut`]. A decode error in any partition at or before its
/// cut offset is returned as [`FleetError::Read`].
pub fn materialize_fleet_cut(
    cut: &Cut,
    logs: &[(Partition, &[u8])],
    cols: u16,
    rows: u16,
) -> Result<FleetSnapshot, FleetError> {
    let edges = cross_edges_from_logs(logs);
    let distinct_partitions = {
        let causal_edges = causal_edges_of(&edges);
        let frontier = cut.to_causal_cut();
        if let Some(v) = frontier.first_violation(&causal_edges) {
            return Err(FleetError::InconsistentCut(v));
        }
        // Reuse the frontier needed by consistency validation: duplicates do
        // not justify indexing a large log directory for one actual lookup.
        frontier.len()
    };
    let mut partitions: Vec<FleetPartitionState> = Vec::new();
    let mut seen = (cut.offsets.len() >= PARTITION_INDEX_MIN).then(BTreeSet::new);
    let mut by_partition = PartitionLogs::new(logs, distinct_partitions);
    for &(part, cut_off) in &cut.offsets {
        let repeated = match &mut seen {
            Some(seen) => !seen.insert(part),
            None => partitions.iter().any(|ps| ps.partition == part),
        };
        if repeated {
            continue;
        }
        let log_bytes = by_partition.get(part);
        let mut folder = Folder::new(cols, rows);
        let mut folded_through = None;
        for item in Log::read_bytes(log_bytes, Offset::ZERO) {
            let env = item.map_err(|err| FleetError::Read {
                partition: part,
                err,
            })?;
            if !fleet_seq_within_cut(env.seq.0, cut_off.0) {
                break;
            }
            let seq = Offset(fleet_clamp_to_cut(env.seq.0, cut_off.0));
            folded_through = Some(seq);
            folder.apply(&env.record);
            if seq == cut_off {
                break;
            }
        }
        partitions.push(FleetPartitionState {
            partition: part,
            snapshot: StateSnapshot::from_parts(folded_through, folder),
        });
    }
    Ok(FleetSnapshot {
        cut: cut.clone(),
        edges,
        partitions,
    })
}

/// Resume every partition in `fleet` from its materialized cut watermark, folding
/// only the tail records at or after each partition's [`StateSnapshot::next_offset`]
/// to yield each partition's current [`Screen`].
pub fn resume_fleet_cut(
    fleet: &FleetSnapshot,
    logs: &[(Partition, &[u8])],
) -> Result<Vec<(Partition, Screen)>, FleetError> {
    let mut out = Vec::new();
    let mut by_partition = PartitionLogs::new(logs, fleet.partitions.len());
    for ps in &fleet.partitions {
        let log_bytes = by_partition.get(ps.partition);
        let mut folder = ps.snapshot.clone_folder();
        let start_off = ps.snapshot.next_offset();
        for item in Log::read_bytes(log_bytes, start_off) {
            let env = item.map_err(|err| FleetError::Read {
                partition: ps.partition,
                err,
            })?;
            if env.seq.0 >= start_off.0 {
                folder.apply(&env.record);
            }
        }
        out.push((ps.partition, folder.into_screen()));
    }
    Ok(out)
}

#[cfg(test)]
#[path = "fleet_scaling_tests.rs"]
mod scaling_tests;
