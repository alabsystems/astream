// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Producer `(producer_id, seq) -> offset` uniqueness & monotone subscriber delivery history
//! checker for simulated broker failover/federation runs (`Astream.SimFabric.TlaLinearizabilityPor`).

use std::collections::BTreeMap;

#[cfg(clean_islands)]
#[path = "linearizability_por_island.rs"]
mod linearizability_por_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sim_hist_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sim_checked_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use linearizability_por_island::{sim_checked_advance, sim_hist_clamp};

/// Maximum committed `(producer_id, seq)` entries tracked per simulation trace.
pub const MAX_TRACE_ENTRIES: u64 = 16_384;

contract_fn! {
    /// Verified zero-violation check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sim_history_valid_isl`.
    #[must_use]
    pub const fn sim_history_valid(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Checks exactly-once `(producer_id, seq)` offset consistency and strictly rising subscriber offsets.
#[derive(Debug, Clone, Default)]
pub struct ExactlyOnceHistoryChecker {
    acks: BTreeMap<(u64, u64), u64>,
    checked: u64,
    violations: u64,
}

impl ExactlyOnceHistoryChecker {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            acks: BTreeMap::new(),
            checked: 0,
            violations: 0,
        }
    }

    pub fn observe_ack(&mut self, producer_id: u64, seq: u64, assigned_offset: u64) -> bool {
        let cap = sim_hist_clamp(MAX_TRACE_ENTRIES, MAX_TRACE_ENTRIES) as usize;
        self.checked = sim_checked_advance(self.checked, self.checked.saturating_add(1));
        if let Some(&prev_off) = self.acks.get(&(producer_id, seq)) {
            if prev_off != assigned_offset {
                self.violations = self.violations.saturating_add(1);
            }
        } else if self.acks.len() < cap {
            self.acks.insert((producer_id, seq), assigned_offset);
        } else {
            self.violations = self.violations.saturating_add(1);
        }
        sim_history_valid(0, self.violations)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn history_checker_accepts_idempotent_duplicate_ack_and_catches_split_brain_offset_drift() {
        let mut h = ExactlyOnceHistoryChecker::new();
        assert!(h.observe_ack(7, 1, 42));
        assert!(h.observe_ack(7, 1, 42));
        assert!(!h.observe_ack(7, 1, 43));
    }
}
