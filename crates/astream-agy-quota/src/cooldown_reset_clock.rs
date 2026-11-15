// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Monotone rolling-window reset clock for `5-hour` (`18_000_000 ms`) and `weekly`
//! (`604_800_000 ms`) `aterm harness agy` quota replenishments (`Astream.AgyQuota.TlaCooldownResetClock`).

#[cfg(clean_islands)]
#[path = "cooldown_reset_clock_island.rs"]
mod cooldown_reset_clock_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn aq_win_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn aq_epoch_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use cooldown_reset_clock_island::{aq_epoch_advance, aq_win_clamp};

/// Weekly horizon duration in milliseconds (`7 * 24 * 3600 * 1000`).
pub const MAX_WINDOW_MS: u64 = 604_800_000;

contract_fn! {
    /// Verified window-expiry predicate (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `aq_window_reset_due_isl`.
    #[must_use]
    pub const fn aq_window_reset_due(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct QuotaResetClock {
    window_ms: u64,
    next_reset_ms: u64,
    reset_epoch: u64,
}

impl QuotaResetClock {
    #[must_use]
    pub const fn new(start_ms: u64, window_ms: u64) -> Self {
        let win = aq_win_clamp(window_ms, MAX_WINDOW_MS);
        let safe_win = if win == 0 { 1 } else { win };
        Self {
            window_ms: safe_win,
            next_reset_ms: start_ms.saturating_add(safe_win),
            reset_epoch: 0,
        }
    }

    pub fn poll_reset(&mut self, now_ms: u64) -> bool {
        if aq_window_reset_due(now_ms, self.next_reset_ms) {
            self.next_reset_ms = now_ms.saturating_add(self.window_ms);
            self.reset_epoch =
                aq_epoch_advance(self.reset_epoch, self.reset_epoch.saturating_add(1));
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
    fn fires_reset_only_after_five_hour_deadline_and_advances_deadline() {
        let mut clk = QuotaResetClock::new(1_000, 18_000_000);
        assert!(!clk.poll_reset(18_000_999));
        assert!(clk.poll_reset(18_001_000));
        assert!(!clk.poll_reset(18_500_000));
    }
}
