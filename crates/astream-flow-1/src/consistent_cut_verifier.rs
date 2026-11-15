// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Transport-independent causal consistent-cut verifier over bus & engine streams
//! (`DESIGN-aterm-fabric.md` §10, `Astream.Engine.TlaBusConsistentCut`).
//!
//! Unifies `astream-engine` consistent cuts with `aterm-link` broker-record causal links:
//! given a map of exclusive stream frontiers `stream_id -> frontier_offset` and a slice of
//! causal edges `(effect_stream, effect_offset) --caused_by--> (cause_stream, cause_offset)`,
//! verifies Chandy-Lamport causal closure:
//! for every event inside the cut (`effect_offset < frontier[effect_stream]`), its causal
//! predecessor MUST also lie inside the cut (`cause_offset < frontier[cause_stream]`).

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

use std::collections::BTreeMap;

#[cfg(clean_islands)]
#[path = "consistent_cut_verifier_island.rs"]
mod consistent_cut_verifier_island;
#[cfg(clean_islands)]
pub use consistent_cut_verifier_island::{bus_cut_cause_clamp, bus_cut_verified_clamp};

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn bus_cut_cause_clamp(cause_off: u64, frontier: u64) -> u64 {
    if cause_off < frontier {
        cause_off
    } else {
        frontier
    }
}

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn bus_cut_verified_clamp(verified: u64, total: u64) -> u64 {
    if verified < total {
        verified
    } else {
        total
    }
}

contract_fn! {
    /// Verified check that `cause_offset` is included in an exclusive stream cut frontier
    /// (`cause_offset < stream_frontier_exclusive`), linked via `clean-kernel-defeq` to
    /// `bus_cut_includes_cause_isl`.
    #[must_use]
    pub const fn bus_cut_includes_cause(
        cause_offset: u64,
        stream_frontier_exclusive: u64,
    ) -> bool
    clauses [ensures result == (cause_offset < stream_frontier_exclusive)]
    {
        cause_offset < stream_frontier_exclusive
    }
}

/// Directed causal dependency: `(effect_stream, effect_offset)` was caused by
/// `(cause_stream, cause_offset)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BusCausalEdge {
    /// Stream/log identifier holding the dependent effect record.
    pub effect_stream: String,
    /// Offset of the dependent effect record within `effect_stream`.
    pub effect_offset: u64,
    /// Stream/log identifier holding the causal predecessor record.
    pub cause_stream: String,
    /// Offset of the causal predecessor record within `cause_stream`.
    pub cause_offset: u64,
}

/// Violation witness when a proposed [`BusConsistentCut`] omits a causal predecessor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CausalCutViolation {
    /// Stream containing the included effect record.
    pub effect_stream: String,
    /// Included effect offset (`< effect_frontier`).
    pub effect_offset: u64,
    /// Stream whose frontier omitted the cause.
    pub cause_stream: String,
    /// Missing cause offset (`>= cause_frontier`).
    pub cause_offset: u64,
    /// Exclusive frontier recorded in the cut for `cause_stream` (`0` if absent).
    pub cause_frontier: u64,
}

/// Summary returned by [`BusConsistentCut::verify_edges`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BusCutAudit {
    /// `true` iff every included effect's cause is also included in the cut.
    pub consistent: bool,
    /// Clamped highest included cause offset (`<= max_frontier`).
    pub max_cause_offset: u64,
    /// Highest exclusive frontier across all streams in the cut.
    pub max_frontier: u64,
    /// Clamped count of causal edges inside the cut that passed verification (`<= total_links`).
    pub verified_links: u64,
    /// Total causal edges inspected.
    pub total_links: u64,
    /// First causal violation encountered, if any.
    pub first_violation: Option<CausalCutViolation>,
}

/// Transport-independent exclusive offset cut across named bus logs or session streams.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct BusConsistentCut {
    frontiers: BTreeMap<String, u64>,
}

impl BusConsistentCut {
    /// Empty cut (all stream frontiers implicitly `0`).
    #[must_use]
    pub fn new() -> Self {
        Self {
            frontiers: BTreeMap::new(),
        }
    }

    /// Set the exclusive frontier `next_offset` (`[0..next_offset)`) for `stream_id`
    /// monotonically.
    #[allow(clippy::manual_unwrap_or, clippy::manual_unwrap_or_default)]
    pub fn advance_frontier(&mut self, stream_id: impl Into<String>, next_offset: u64) {
        let key = stream_id.into();
        let prev = match self.frontiers.get(&key) {
            Some(&v) => v,
            None => 0,
        };
        if next_offset > prev || !self.frontiers.contains_key(&key) {
            let next_val = if next_offset > prev {
                next_offset
            } else {
                prev
            };
            self.frontiers.insert(key, next_val);
        }
    }

    /// Exclusive frontier for `stream_id` (`0` when not present in the cut).
    #[must_use]
    #[allow(clippy::manual_unwrap_or, clippy::manual_unwrap_or_default)]
    pub fn frontier(&self, stream_id: &str) -> u64 {
        match self.frontiers.get(stream_id) {
            Some(&v) => v,
            None => 0,
        }
    }

    /// Maximum frontier offset across all streams in this cut.
    #[must_use]
    pub fn max_frontier(&self) -> u64 {
        let mut hi = 0u64;
        for &off in self.frontiers.values() {
            if off > hi {
                hi = off;
            }
        }
        hi
    }

    /// Verify Chandy-Lamport causal consistency of this cut over `edges`.
    #[must_use]
    pub fn verify_edges(&self, edges: &[BusCausalEdge]) -> BusCutAudit {
        let max_f = self.max_frontier();
        let total = edges.len() as u64;
        let mut raw_verified = 0u64;
        let mut raw_max_cause = 0u64;
        let mut first_violation: Option<CausalCutViolation> = None;

        let mut rest = edges;
        while let [e, tail @ ..] = rest {
            rest = tail;
            let eff_front = self.frontier(&e.effect_stream);
            if bus_cut_includes_cause(e.effect_offset, eff_front) {
                let cause_front = self.frontier(&e.cause_stream);
                if bus_cut_includes_cause(e.cause_offset, cause_front) {
                    raw_verified = raw_verified.saturating_add(1);
                    if e.cause_offset > raw_max_cause {
                        raw_max_cause = e.cause_offset;
                    }
                } else if first_violation.is_none() {
                    first_violation = Some(CausalCutViolation {
                        effect_stream: e.effect_stream.clone(),
                        effect_offset: e.effect_offset,
                        cause_stream: e.cause_stream.clone(),
                        cause_offset: e.cause_offset,
                        cause_frontier: cause_front,
                    });
                }
            }
        }

        BusCutAudit {
            consistent: first_violation.is_none(),
            max_cause_offset: bus_cut_cause_clamp(raw_max_cause, max_f),
            max_frontier: max_f,
            verified_links: bus_cut_verified_clamp(raw_verified, total),
            total_links: total,
            first_violation,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_orphan_effect_and_certifies_causally_closed_multi_bus_cut() {
        let mut cut = BusConsistentCut::new();
        cut.advance_frontier("bus.inbox", 5);
        cut.advance_frontier("bus.worker.s41", 10);

        let edges = vec![
            // Worker event 3 was caused by inbox message 2 (< 5: inside cut!).
            BusCausalEdge {
                effect_stream: "bus.worker.s41".to_string(),
                effect_offset: 3,
                cause_stream: "bus.inbox".to_string(),
                cause_offset: 2,
            },
            // Worker event 8 (< 10: inside cut!) was caused by inbox message 6 (>= 5: outside cut!).
            BusCausalEdge {
                effect_stream: "bus.worker.s41".to_string(),
                effect_offset: 8,
                cause_stream: "bus.inbox".to_string(),
                cause_offset: 6,
            },
        ];

        let bad = cut.verify_edges(&edges);
        assert!(!bad.consistent);
        assert_eq!(bad.verified_links, 1);
        assert_eq!(
            bad.first_violation,
            Some(CausalCutViolation {
                effect_stream: "bus.worker.s41".to_string(),
                effect_offset: 8,
                cause_stream: "bus.inbox".to_string(),
                cause_offset: 6,
                cause_frontier: 5,
            })
        );

        // Advance `bus.inbox` frontier to 7 -> cut becomes causally closed!
        cut.advance_frontier("bus.inbox", 7);
        let ok = cut.verify_edges(&edges);
        assert!(ok.consistent);
        assert_eq!(ok.verified_links, 2);
        assert!(ok.max_cause_offset <= ok.max_frontier);
    }
}
