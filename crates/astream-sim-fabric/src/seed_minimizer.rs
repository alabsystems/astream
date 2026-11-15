// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Delta-debugging fault-schedule minimizer bisecting failing simulation traces down to the
//! smallest reproducing fault count (`Astream.SimFabric.TlaSeedMinimizer`).

#[cfg(clean_islands)]
#[path = "seed_minimizer_island.rs"]
mod seed_minimizer_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sim_faults_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sim_shrink_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use seed_minimizer_island::{sim_faults_clamp, sim_shrink_advance};

/// Maximum injected faults in one unshrunk simulation trace (`512`).
pub const MAX_FAULT_STEPS: u64 = 512;

contract_fn! {
    /// Verified strict reduction (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sim_smaller_repro_isl`.
    #[must_use]
    pub const fn sim_smaller_repro(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Tracks the smallest reproducing fault list across delta-debugging shrink probes.
#[derive(Debug, Clone)]
pub struct FaultScheduleShrinker {
    best_faults: Vec<u64>,
    probes: u64,
}

impl FaultScheduleShrinker {
    #[must_use]
    pub fn new(initial_failing: &[u64]) -> Self {
        let keep = sim_faults_clamp(initial_failing.len() as u64, MAX_FAULT_STEPS) as usize;
        let mut best_faults = Vec::new();
        let mut idx = 0usize;
        while idx < initial_failing.len() && idx < keep {
            if let Some(&f) = initial_failing.get(idx) {
                best_faults.push(f);
            }
            idx = idx.saturating_add(1);
        }
        Self {
            best_faults,
            probes: 0,
        }
    }

    pub fn record_probe(&mut self, candidate: &[u64], still_fails: bool) -> bool {
        self.probes = sim_shrink_advance(self.probes, self.probes.saturating_add(1));
        let cand_len = candidate.len() as u64;
        if !still_fails || cand_len > MAX_FAULT_STEPS {
            return false;
        }
        let cur_len = self.best_faults.len() as u64;
        if cur_len > 0 && sim_smaller_repro(cur_len.saturating_sub(1), cand_len) {
            self.best_faults.clear();
            self.best_faults.extend_from_slice(candidate);
            true
        } else {
            false
        }
    }

    #[must_use]
    pub fn best_faults(&self) -> &[u64] {
        &self.best_faults
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shrinker_adopts_strictly_shorter_reproducing_schedule_and_ignores_passing_candidates() {
        let mut s = FaultScheduleShrinker::new(&[10, 20, 30, 40]);
        assert!(!s.record_probe(&[10], false));
        assert!(s.record_probe(&[10, 30], true));
        assert_eq!(s.best_faults(), &[10, 30]);
    }
}
