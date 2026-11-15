// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Retention gap-notice cut guard (`Response::Gap` / `ShardedEvent::Gap`) refusing to certify a
//! `BusCutFrontier` as whole when retention evicted unheld records inside the cut window
//! (`Astream.LinkCut.TlaHeldGapCutGuard`).

#[cfg(clean_islands)]
#[path = "held_gap_cut_guard_island.rs"]
mod held_gap_cut_guard_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lc_gaps_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lc_gap_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use held_gap_cut_guard_island::{lc_gap_advance, lc_gaps_clamp};

/// Maximum tracked retention gaps per cut sweep (`1_024`).
pub const MAX_CUT_GAPS: u64 = 1_024;

contract_fn! {
    /// Verified zero-gap completeness check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `lc_cut_gap_free_isl`.
    #[must_use]
    pub const fn lc_cut_gap_free(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct HeldGapCutGuard {
    gaps_in_window: u64,
    sweeps: u64,
}

impl HeldGapCutGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            gaps_in_window: 0,
            sweeps: 0,
        }
    }

    pub fn record_gap(&mut self, gap_from: u64, gap_to: u64, cut_exclusive: u64) {
        if gap_from < cut_exclusive && gap_to > gap_from {
            self.gaps_in_window =
                lc_gaps_clamp(self.gaps_in_window.saturating_add(1), MAX_CUT_GAPS);
        }
    }

    pub fn seal_sweep(&mut self) -> bool {
        self.sweeps = lc_gap_advance(self.sweeps, self.sweeps.saturating_add(1));
        lc_cut_gap_free(0, self.gaps_in_window)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn invalidates_cut_completeness_when_gap_overlaps_cut_range() {
        let mut g = HeldGapCutGuard::new();
        g.record_gap(20, 30, 15);
        assert!(g.seal_sweep());
        g.record_gap(5, 10, 15);
        assert!(!g.seal_sweep());
    }
}
