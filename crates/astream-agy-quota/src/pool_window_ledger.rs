// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Dual-horizon (`5-hour` rolling + `weekly`) model-pool quota ledger matching `aterm harness agy`
//! where Gemini is accounted independently from Claude and GPT (`Astream.AgyQuota.TlaPoolWindowLedger`).

#[cfg(clean_islands)]
#[path = "pool_window_ledger_island.rs"]
mod pool_window_ledger_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn aq_rem_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn aq_spend_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use pool_window_ledger_island::{aq_rem_clamp, aq_spend_advance};

/// Maximum quota units per pool horizon (`10_000_000` normalized credits).
pub const MAX_POOL_CREDITS: u64 = 10_000_000;

contract_fn! {
    /// Verified pool headroom predicate (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `aq_pool_has_quota_isl`.
    #[must_use]
    pub const fn aq_pool_has_quota(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModelPool {
    Gemini,
    Claude,
    Gpt,
}

#[derive(Debug, Clone)]
pub struct PoolLedger {
    pool: ModelPool,
    five_hour_left: u64,
    weekly_left: u64,
    cumulative_spent: u64,
}

impl PoolLedger {
    #[must_use]
    pub const fn new(pool: ModelPool, five_hour_cap: u64, weekly_cap: u64) -> Self {
        let fh = aq_rem_clamp(five_hour_cap, MAX_POOL_CREDITS);
        let wk = aq_rem_clamp(weekly_cap, MAX_POOL_CREDITS);
        Self {
            pool,
            five_hour_left: fh,
            weekly_left: wk,
            cumulative_spent: 0,
        }
    }

    #[must_use]
    pub const fn pool(&self) -> ModelPool {
        self.pool
    }

    #[must_use]
    pub const fn bottleneck_left(&self) -> u64 {
        if self.five_hour_left < self.weekly_left {
            self.five_hour_left
        } else {
            self.weekly_left
        }
    }

    pub fn try_debit(&mut self, cost: u64, reserve: u64) -> bool {
        let req = cost.saturating_add(reserve);
        if !aq_pool_has_quota(self.bottleneck_left(), req) {
            return false;
        }
        self.five_hour_left = self.five_hour_left.saturating_sub(cost);
        self.weekly_left = self.weekly_left.saturating_sub(cost);
        self.cumulative_spent = aq_spend_advance(
            self.cumulative_spent,
            self.cumulative_spent.saturating_add(cost),
        );
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn debit_honors_both_five_hour_and_weekly_bottlenecks_plus_reserve() {
        let mut g = PoolLedger::new(ModelPool::Gemini, 500, 2_000);
        assert!(g.try_debit(400, 50));
        assert_eq!(g.bottleneck_left(), 100);
        assert!(!g.try_debit(60, 50));
    }
}
