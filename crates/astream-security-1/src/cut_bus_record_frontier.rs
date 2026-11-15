// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bus-record Chandy-Lamport causal cut frontier for `aterm-link` & `astream-engine`
//! (`DESIGN-aterm-fabric.md` §10; `Astream.Engine.TlaBusCutFrontier`).
//!
//! Unifies Chandy-Lamport consistent-cut checking directly over fabric bus records (`origin_id`,
//! `record_seq`, optional `(dep_origin_id, dep_seq)` causal parent) without requiring conversion
//! into `astream-host` envelope logs. Guarantees monotone per-origin frontier advancement via
//! [`bus_cut_advance_b121`] and orphan-free causal closure via [`bus_cut_dep_exceeds_b121`].

#[cfg(clean_islands)]
#[path = "cut_bus_record_frontier_island.rs"]
mod cut_bus_record_frontier_island;
#[cfg(clean_islands)]
pub use cut_bus_record_frontier_island::{bus_cut_advance_b121, bus_cut_slot_clamp_b121};

#[cfg(not(clean_islands))]
/// Clamp active origin slot count to `max_slots`.
#[must_use]
pub const fn bus_cut_slot_clamp_b121(cand_slots: u64, max_slots: u64) -> u64 {
    if cand_slots < max_slots {
        cand_slots
    } else {
        max_slots
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance an origin's bus-record frontier sequence.
#[must_use]
pub const fn bus_cut_advance_b121(cur_frontier: u64, cand_frontier: u64) -> u64 {
    if cur_frontier < cand_frontier {
        cand_frontier
    } else {
        cur_frontier
    }
}

contract_fn! {
    /// True iff causal dependency `dep_seq` exceeds `origin_frontier` (`origin_frontier < dep_seq`).
    #[must_use]
    pub const fn bus_cut_dep_exceeds_b121(origin_frontier: u64, dep_seq: u64) -> bool
    clauses [ensures result == (origin_frontier < dep_seq)]
    {
        origin_frontier < dep_seq
    }
}

pub const MAX_BUS_CUT_ORIGINS: usize = 16;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct OriginCutSlot {
    active: bool,
    origin_id: u64,
    frontier_seq: u64,
}

impl OriginCutSlot {
    const EMPTY: Self = Self {
        active: false,
        origin_id: 0,
        frontier_seq: 0,
    };
}

/// Result of admitting a causally-linked bus record into a [`BusCutFrontier`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BusCutAdmission {
    Admitted {
        origin_id: u64,
        frontier_seq: u64,
    },
    OrphanDependency {
        dep_origin_id: u64,
        dep_seq: u64,
        known_frontier: Option<u64>,
    },
    OriginCapacityExhausted,
}

/// Zero-allocation Chandy-Lamport causal cut tracker over fabric bus records.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BusCutFrontier {
    slots: [OriginCutSlot; MAX_BUS_CUT_ORIGINS],
    used_slots: u64,
}

impl Default for BusCutFrontier {
    fn default() -> Self {
        Self::new()
    }
}

impl BusCutFrontier {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            slots: [OriginCutSlot::EMPTY; MAX_BUS_CUT_ORIGINS],
            used_slots: 0,
        }
    }

    #[must_use]
    pub const fn used_origins(&self) -> u64 {
        self.used_slots
    }

    /// Look up the current frontier sequence for `origin_id`.
    #[must_use]
    pub fn frontier_of(&self, origin_id: u64) -> Option<u64> {
        let mut rest = self.slots.as_slice();
        while let &[slot, ref tail @ ..] = rest {
            if slot.active && slot.origin_id == origin_id {
                return Some(slot.frontier_seq);
            }
            rest = tail;
        }
        None
    }

    /// Check whether `(dep_origin_id, dep_seq)` is already causally closed in this cut.
    #[must_use]
    pub fn is_dep_consistent(&self, dep_origin_id: u64, dep_seq: u64) -> bool {
        match self.frontier_of(dep_origin_id) {
            Some(front) => !bus_cut_dep_exceeds_b121(front, dep_seq),
            None => false,
        }
    }

    /// Admit `(origin_id, record_seq)` iff optional `causal_dep` is already closed in the cut.
    pub fn observe_bus_record(
        &mut self,
        origin_id: u64,
        record_seq: u64,
        causal_dep: Option<(u64, u64)>,
    ) -> BusCutAdmission {
        if let Some((dep_origin, dep_seq)) = causal_dep {
            let known = self.frontier_of(dep_origin);
            let ok = match known {
                Some(front) => !bus_cut_dep_exceeds_b121(front, dep_seq),
                None => false,
            };
            if !ok {
                return BusCutAdmission::OrphanDependency {
                    dep_origin_id: dep_origin,
                    dep_seq,
                    known_frontier: known,
                };
            }
        }

        // Update existing origin slot if present.
        for slot in &mut self.slots {
            if slot.active && slot.origin_id == origin_id {
                slot.frontier_seq = bus_cut_advance_b121(slot.frontier_seq, record_seq);
                return BusCutAdmission::Admitted {
                    origin_id,
                    frontier_seq: slot.frontier_seq,
                };
            }
        }

        // Allocate first empty slot.
        for slot in &mut self.slots {
            if !slot.active {
                slot.active = true;
                slot.origin_id = origin_id;
                slot.frontier_seq = record_seq;
                self.used_slots = bus_cut_slot_clamp_b121(
                    self.used_slots.saturating_add(1),
                    MAX_BUS_CUT_ORIGINS as u64,
                );
                return BusCutAdmission::Admitted {
                    origin_id,
                    frontier_seq: slot.frontier_seq,
                };
            }
        }

        BusCutAdmission::OriginCapacityExhausted
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bus_cut_rejects_orphan_dep_and_admits_causally_closed_chain() {
        let mut cut = BusCutFrontier::new();
        assert_eq!(
            cut.observe_bus_record(10, 5, None),
            BusCutAdmission::Admitted {
                origin_id: 10,
                frontier_seq: 5
            }
        );
        // Orphan dep on origin 10 seq 6 (> 5) is rejected fail-closed!
        assert_eq!(
            cut.observe_bus_record(20, 1, Some((10, 6))),
            BusCutAdmission::OrphanDependency {
                dep_origin_id: 10,
                dep_seq: 6,
                known_frontier: Some(5),
            }
        );
        // Satisfied dep on origin 10 seq 5 is admitted!
        assert_eq!(
            cut.observe_bus_record(20, 1, Some((10, 5))),
            BusCutAdmission::Admitted {
                origin_id: 20,
                frontier_seq: 1
            }
        );
        // Out-of-order replay on origin 10 (seq 3 < 5) preserves monotone frontier 5.
        assert_eq!(
            cut.observe_bus_record(10, 3, None),
            BusCutAdmission::Admitted {
                origin_id: 10,
                frontier_seq: 5
            }
        );
        assert_eq!(cut.used_origins(), 2);
    }
}
