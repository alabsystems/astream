//! Fleet consistent-cut replay (the fleet rung — a green slice of it).
//!
//! An agent fleet is a forest of independent single-writer logs. A global
//! checkpoint is a **Chandy-Lamport consistent cut**: a vector of per-partition
//! offsets such that for every recorded cross-injection edge — an orchestrator's
//! `Out` in one log *caused* a child's injected `In` in another — if the cut
//! admits the effect it must also admit the cause. Replaying each partition from
//! its cut offset re-folds the exact screen as of that cut.
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
use astream_term::{screen, Record, Screen};
use astream_wire::Offset;

/// A fleet partition id (which session log).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
}

/// Does the cut admit `at` in partition `p` (`at <= the cut offset for p`)? A
/// partition the cut does not name admits nothing.
pub fn cut_includes(cut: &Cut, p: Partition, at: Offset) -> bool {
    match cut.offset_of(p) {
        Some(o) => at <= o,
        None => false,
    }
}

/// Chandy-Lamport consistency: for every cross-edge whose **effect** the cut
/// admits, it must also admit the **cause**. An effect-without-cause cut is an
/// orphaned injection (causally impossible) and is rejected; a cause-without-
/// effect cut is an in-flight (sent-not-yet-delivered) message and is admitted.
pub fn is_consistent(cut: &Cut, edges: &[CrossEdge]) -> bool {
    edges.iter().all(|e| {
        let effect_in = cut_includes(cut, e.effect.0, e.effect.1);
        let cause_in = cut_includes(cut, e.cause.0, e.cause.1);
        // effect_in IMPLIES cause_in
        !effect_in || cause_in
    })
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
        for item in Log::read_bytes(bytes, Offset::ZERO) {
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

/// Replay one partition from the cut: a separate read-by-offset pass over its
/// stored bytes, folding the prefix up to and including the cut offset. (The
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
    let mut records: Vec<Record> = Vec::new();
    let mut folded_through = None;
    if let Some(cut_off) = cut.offset_of(p) {
        for item in Log::read_bytes(log_bytes, Offset::ZERO) {
            let env = item?;
            if env.seq > cut_off {
                break; // unreachable on a dense log (we stop AT the cut), kept as a guard
            }
            let seq = env.seq;
            folded_through = Some(seq);
            records.push(env.record);
            if seq == cut_off {
                break; // the cut is folded: the reader is lazy, so nothing after it is decoded
            }
        }
    }
    Ok(CutReplay {
        screen: screen::fold(cols, rows, &records),
        folded_through,
    })
}
