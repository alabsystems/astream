// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Independent 7-day rolling model-pool ledger separating `Gemini` from `Claude` and `GPT`
//! (`aterm harness agy`, `Astream.Quota.TlaPoolWindowWeekly`).

#[cfg(clean_islands)]
#[path = "pool_window_weekly_island.rs"]
mod pool_window_weekly_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn qwk_spend_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn qwk_epoch_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use pool_window_weekly_island::{qwk_epoch_advance, qwk_spend_clamp};

/// 7 days in milliseconds.
pub const WEEKLY_WINDOW_MS: u64 = 7 * 24 * 3_600 * 1_000;

contract_fn! {
    /// Verified weekly reserve check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `qwk_reserve_intact_isl`.
    #[must_use]
    pub const fn qwk_reserve_intact(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AgyPoolFamily {
    Gemini,
    Claude,
    Gpt,
}

impl AgyPoolFamily {
    #[must_use]
    pub const fn idx(self) -> usize {
        match self {
            Self::Gemini => 0,
            Self::Claude => 1,
            Self::Gpt => 2,
        }
    }
}

/// Separate weekly quota ledger across the 3 `agy` model pool families.
#[derive(Debug, Clone)]
pub struct WeeklyPoolLedger {
    caps_bps: [u64; 3],
    spent_bps: [u64; 3],
    week_epoch: u64,
}

impl Default for WeeklyPoolLedger {
    fn default() -> Self {
        Self::new()
    }
}

impl WeeklyPoolLedger {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            caps_bps: [10_000, 10_000, 10_000],
            spent_bps: [0, 0, 0],
            week_epoch: 0,
        }
    }

    pub fn record_spend_bps(&mut self, pool: AgyPoolFamily, delta_bps: u64) -> u64 {
        let [c0, c1, c2] = self.caps_bps;
        let [ref mut s0, ref mut s1, ref mut s2] = self.spent_bps;
        let (cap, spent_slot) = match pool {
            AgyPoolFamily::Gemini => (c0, s0),
            AgyPoolFamily::Claude => (c1, s1),
            AgyPoolFamily::Gpt => (c2, s2),
        };
        let next = spent_slot.saturating_add(delta_bps);
        *spent_slot = qwk_spend_clamp(next, cap);
        cap.saturating_sub(*spent_slot)
    }

    #[must_use]
    pub const fn remaining_bps(&self, pool: AgyPoolFamily) -> u64 {
        let [c0, c1, c2] = self.caps_bps;
        let [s0, s1, s2] = self.spent_bps;
        let (cap, spent) = match pool {
            AgyPoolFamily::Gemini => (c0, s0),
            AgyPoolFamily::Claude => (c1, s1),
            AgyPoolFamily::Gpt => (c2, s2),
        };
        cap.saturating_sub(spent)
    }

    #[must_use]
    pub const fn has_at_least_bps(&self, pool: AgyPoolFamily, floor_bps: u64) -> bool {
        qwk_reserve_intact(self.remaining_bps(pool), floor_bps)
    }

    pub fn advance_week_epoch(&mut self, new_epoch: u64) -> bool {
        let next = qwk_epoch_advance(self.week_epoch, new_epoch);
        if next > self.week_epoch {
            self.week_epoch = next;
            self.spent_bps = [0, 0, 0];
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn spending_claude_pool_leaves_gemini_weekly_pool_completely_untouched() {
        let mut wk = WeeklyPoolLedger::new();
        assert_eq!(wk.record_spend_bps(AgyPoolFamily::Claude, 9_500), 500);
        assert!(!wk.has_at_least_bps(AgyPoolFamily::Claude, 1_000));
        assert_eq!(wk.remaining_bps(AgyPoolFamily::Gemini), 10_000);
        assert!(wk.has_at_least_bps(AgyPoolFamily::Gemini, 9_000));
        assert!(wk.advance_week_epoch(1));
        assert_eq!(wk.remaining_bps(AgyPoolFamily::Claude), 10_000);
    }
}
