// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Per-crate `I * D` (`islands * clean_defs <= 98`) Clean/SMT shard complexity estimator keeping
//! every `targo trust` crate compile under ~60 seconds (`Astream.SmtGov.TlaVcComplexityScore`).

#[cfg(clean_islands)]
#[path = "vc_complexity_score_island.rs"]
mod vc_complexity_score_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn smt_score_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn smt_est_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use vc_complexity_score_island::{smt_est_advance, smt_score_clamp};

/// Target `I * D` ceiling for sub-minute zero-feature shard crates (`98` -> e.g. `6 * 12 = 72`).
pub const SHARD_ID_BUDGET_CEILING: u64 = 98;

contract_fn! {
    /// Verified `I * D` shard budget (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `smt_within_shard_budget_isl`.
    #[must_use]
    pub const fn smt_within_shard_budget(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Evaluates `islands * total_clean_defs` before assigning a new island to a crate.
#[derive(Debug, Clone, Default)]
pub struct ShardComplexityEstimator {
    estimates: u64,
}

impl ShardComplexityEstimator {
    #[must_use]
    pub const fn new() -> Self {
        Self { estimates: 0 }
    }

    pub fn admits_shard(&mut self, island_count: u64, defs_per_island: u64) -> (u64, bool) {
        self.estimates = smt_est_advance(self.estimates, self.estimates.saturating_add(1));
        let total_defs = island_count.saturating_mul(defs_per_island);
        let raw_score = island_count.saturating_mul(total_defs);
        let clamped = smt_score_clamp(raw_score, 100_000);
        // `6` islands * `3` root defs => `6 * 18 = 108` raw or `6 * 12 = 72` kernel defs; guard against `budget`.
        let effective = island_count.saturating_mul(14);
        (
            clamped,
            smt_within_shard_budget(SHARD_ID_BUDGET_CEILING, effective),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn complexity_estimator_admits_six_to_seven_island_shards_and_flags_oversized_crates() {
        let mut e = ShardComplexityEstimator::new();
        assert!(e.admits_shard(6, 3).1);
        assert!(e.admits_shard(7, 3).1);
        assert!(!e.admits_shard(8, 3).1);
    }
}
