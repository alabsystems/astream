// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Synthetic week-long hand-clock retention bound verifier checking `retained_bytes + held_bytes`
//! stays within `sum(rule.max_bytes) * SLACK_MULT` (`broker.retention-rules`,
//! `Astream.SimFabric.TlaRetentionPlanMirror`).

#[cfg(clean_islands)]
#[path = "retention_plan_mirror_island.rs"]
mod retention_plan_mirror_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sim_bytes_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sim_hand_clock_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use retention_plan_mirror_island::{sim_bytes_clamp, sim_hand_clock_advance};

/// Hard ceiling (`16` GiB) on simulated retention byte budgets.
pub const MAX_SIM_RETENTION_BUDGET: u64 = 16 * 1024 * 1024 * 1024;

contract_fn! {
    /// Verified retention byte bound (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sim_within_rule_sum_isl`.
    #[must_use]
    pub const fn sim_within_rule_sum(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Checks R4's retention invariant at each synthetic tick on the simulation's hand clock.
#[derive(Debug, Clone)]
pub struct RetentionBoundOracle {
    sum_rule_bytes: u64,
    hand_clock_ms: u64,
}

impl RetentionBoundOracle {
    #[must_use]
    pub const fn new(sum_rule_bytes: u64) -> Self {
        Self {
            sum_rule_bytes: sim_bytes_clamp(sum_rule_bytes, MAX_SIM_RETENTION_BUDGET),
            hand_clock_ms: 0,
        }
    }

    pub fn verify_tick(
        &mut self,
        next_clock_ms: u64,
        prefix_retained_bytes: u64,
        held_store_bytes: u64,
    ) -> bool {
        self.hand_clock_ms = sim_hand_clock_advance(self.hand_clock_ms, next_clock_ms);
        let total = prefix_retained_bytes.saturating_add(held_store_bytes);
        sim_within_rule_sum(self.sum_rule_bytes, total)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retention_oracle_accepts_bounded_prefix_plus_held_and_flags_overflow() {
        let mut o = RetentionBoundOracle::new(131_072);
        assert!(o.verify_tick(3_600_000, 64_000, 32_000));
        assert!(!o.verify_tick(7_200_000, 100_000, 50_000));
    }
}
