// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Broker-bus causal cut consistency verifier (`Astream.Engine.TlaBusCutConsistencyFence`).
//!
//! Bridges `astream-engine` causal cuts directly to `astream-broker` / `aterm-link` multi-stream
//! bus records without requiring `astream-host` local envelope logs (`DESIGN-aterm-fabric.md` §10).
//! Tracks up to `MAX_CUT_STREAMS` stream frontiers on the stack and verifies that every observed
//! cross-stream dependency `(dep_stream, dep_offset)` is satisfied by the cut (`dep_offset <= cut[dep_stream]`).

#[cfg(clean_islands)]
#[path = "bus_cut_consistency_fence_island.rs"]
mod bus_cut_consistency_fence_island;
#[cfg(clean_islands)]
pub use bus_cut_consistency_fence_island::{bus_cut_dep_clamp, bus_cut_offset_advance};

#[cfg(not(clean_islands))]
/// Clamp a required dependency offset to a stream's committed cut frontier.
#[must_use]
pub const fn bus_cut_dep_clamp(dep_offset: u64, frontier_offset: u64) -> u64 {
    if dep_offset < frontier_offset {
        dep_offset
    } else {
        frontier_offset
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance a stream's cut frontier offset.
#[must_use]
pub const fn bus_cut_offset_advance(cur_frontier: u64, cand_frontier: u64) -> u64 {
    if cur_frontier < cand_frontier {
        cand_frontier
    } else {
        cur_frontier
    }
}

contract_fn! {
    /// True iff a cross-stream causal dependency `dep_offset` is included within `frontier_offset`.
    #[must_use]
    pub const fn bus_cut_dep_satisfied(dep_offset: u64, frontier_offset: u64) -> bool
    clauses [ensures result == (dep_offset <= frontier_offset)]
    {
        dep_offset <= frontier_offset
    }
}

/// Maximum number of concurrent fabric streams tracked in a stack-allocated bus cut.
pub const MAX_CUT_STREAMS: usize = 16;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct StreamCutSlot {
    active: bool,
    stream_id: u64,
    frontier_offset: u64,
}

impl StreamCutSlot {
    const EMPTY: Self = Self {
        active: false,
        stream_id: 0,
        frontier_offset: 0,
    };
}

/// Result of checking or extending a multi-stream bus cut.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BusCutVerdict {
    Consistent {
        active_streams: usize,
    },
    MissingDependencyStream {
        dep_stream_id: u64,
    },
    CausalGap {
        dep_stream_id: u64,
        dep_offset: u64,
        frontier_offset: u64,
    },
    StreamTableFull,
}

/// Zero-allocation causal cut tracker over `astream-broker` / `aterm-link` bus records.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BusCutConsistencyFence {
    slots: [StreamCutSlot; MAX_CUT_STREAMS],
    active_count: usize,
    violations: u64,
}

impl Default for BusCutConsistencyFence {
    fn default() -> Self {
        Self::new()
    }
}

impl BusCutConsistencyFence {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            slots: [StreamCutSlot::EMPTY; MAX_CUT_STREAMS],
            active_count: 0,
            violations: 0,
        }
    }

    #[must_use]
    pub const fn active_count(&self) -> usize {
        self.active_count
    }

    #[must_use]
    pub const fn violations(&self) -> u64 {
        self.violations
    }

    #[must_use]
    pub fn frontier_of(&self, stream_id: u64) -> Option<u64> {
        let mut rest: &[StreamCutSlot] = &self.slots;
        while let [slot, tail @ ..] = rest {
            if slot.active && slot.stream_id == stream_id {
                return Some(slot.frontier_offset);
            }
            rest = tail;
        }
        None
    }

    /// Record or monotonically advance `stream_id`'s included offset in the cut.
    pub fn include_stream_offset(&mut self, stream_id: u64, offset: u64) -> bool {
        let mut idx = 0usize;
        let mut free_idx: Option<usize> = None;
        while let Some(slot) = self.slots.get_mut(idx) {
            if slot.active {
                if slot.stream_id == stream_id {
                    slot.frontier_offset = bus_cut_offset_advance(slot.frontier_offset, offset);
                    return true;
                }
            } else if free_idx.is_none() {
                free_idx = Some(idx);
            }
            idx = idx.saturating_add(1);
        }
        if let Some(target) = free_idx {
            if let Some(slot) = self.slots.get_mut(target) {
                *slot = StreamCutSlot {
                    active: true,
                    stream_id,
                    frontier_offset: offset,
                };
                self.active_count = self.active_count.saturating_add(1);
                return true;
            }
        }
        false
    }

    /// Verify that a bus record's causal dependency `(dep_stream_id, dep_offset)` is satisfied
    /// by the cut, and if so, advance `record_stream_id` to `record_offset`.
    pub fn check_and_advance(
        &mut self,
        record_stream_id: u64,
        record_offset: u64,
        dep: Option<(u64, u64)>,
    ) -> BusCutVerdict {
        if let Some((dep_stream_id, dep_offset)) = dep {
            match self.frontier_of(dep_stream_id) {
                None => {
                    self.violations = self.violations.saturating_add(1);
                    return BusCutVerdict::MissingDependencyStream { dep_stream_id };
                }
                Some(frontier) => {
                    let clamped = bus_cut_dep_clamp(dep_offset, frontier);
                    if !bus_cut_dep_satisfied(dep_offset, frontier) || clamped != dep_offset {
                        self.violations = self.violations.saturating_add(1);
                        return BusCutVerdict::CausalGap {
                            dep_stream_id,
                            dep_offset,
                            frontier_offset: frontier,
                        };
                    }
                }
            }
        }
        if !self.include_stream_offset(record_stream_id, record_offset) {
            return BusCutVerdict::StreamTableFull;
        }
        BusCutVerdict::Consistent {
            active_streams: self.active_count,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_cross_stream_causal_consistency_on_bus_cut() {
        let mut cut = BusCutConsistencyFence::new();
        assert_eq!(
            cut.check_and_advance(1, 10, None),
            BusCutVerdict::Consistent { active_streams: 1 }
        );
        // Stream 2 depends on stream 1 @ offset 12 (not yet in cut -> CausalGap):
        assert_eq!(
            cut.check_and_advance(2, 5, Some((1, 12))),
            BusCutVerdict::CausalGap {
                dep_stream_id: 1,
                dep_offset: 12,
                frontier_offset: 10,
            }
        );
        assert_eq!(cut.violations(), 1);
        // Once stream 1 advances to 15, stream 2's dependency (1, 12) is satisfied:
        assert!(cut.include_stream_offset(1, 15));
        assert_eq!(
            cut.check_and_advance(2, 5, Some((1, 12))),
            BusCutVerdict::Consistent { active_streams: 2 }
        );
        assert_eq!(cut.frontier_of(2), Some(5));
    }
}
