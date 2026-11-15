// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Rolling 5-hour model-pool quota window (`aterm harness agy`, `Astream.Quota.TlaPoolWindow5h`).

#[cfg(clean_islands)]
#[path = "pool_window_5h_island.rs"]
mod pool_window_5h_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn q5h_spend_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn q5h_window_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use pool_window_5h_island::{q5h_spend_clamp, q5h_window_advance};

/// Rolling 5-hour quota window duration in milliseconds (`18_000_000` ms).
pub const FIVE_HOUR_WINDOW_MS: u64 = 5 * 3_600 * 1_000;

contract_fn! {
    /// Verified headroom predicate (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `q5h_has_headroom_isl`.
    #[must_use]
    pub const fn q5h_has_headroom(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// 5-hour quota tracker for a single provider pool (`Gemini`, `Claude`, or `GPT`).
#[derive(Debug, Clone)]
pub struct FiveHourPoolWindow {
    cap_units: u64,
    reserve_units: u64,
    spent_units: u64,
    reset_at_ms: u64,
}

impl FiveHourPoolWindow {
    #[must_use]
    pub const fn new(cap_units: u64, reserve_units: u64, start_ms: u64) -> Self {
        Self {
            cap_units,
            reserve_units: q5h_spend_clamp(reserve_units, cap_units),
            spent_units: 0,
            reset_at_ms: start_ms.saturating_add(FIVE_HOUR_WINDOW_MS),
        }
    }

    pub fn maybe_roll_window(&mut self, now_ms: u64) {
        if q5h_has_headroom(now_ms, self.reset_at_ms) {
            self.spent_units = 0;
            let next_reset = now_ms.saturating_add(FIVE_HOUR_WINDOW_MS);
            self.reset_at_ms = q5h_window_advance(self.reset_at_ms, next_reset);
        }
    }

    #[must_use]
    pub const fn available_for_workers(&self) -> u64 {
        self.cap_units
            .saturating_sub(self.reserve_units)
            .saturating_sub(self.spent_units)
    }

    pub fn charge(&mut self, units: u64, now_ms: u64, interactive_fg: bool) -> bool {
        self.maybe_roll_window(now_ms);
        let ceiling = if interactive_fg {
            self.cap_units
        } else {
            self.cap_units.saturating_sub(self.reserve_units)
        };
        let after = self.spent_units.saturating_add(units);
        if !q5h_has_headroom(ceiling, after) {
            return false;
        }
        self.spent_units = q5h_spend_clamp(after, self.cap_units);
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn five_hour_pool_protects_interactive_reserve_and_resets_after_5h() {
        let mut w = FiveHourPoolWindow::new(1_000, 200, 10_000);
        assert!(w.charge(750, 11_000, false));
        // Background worker cannot dip into 200-unit interactive reserve!
        assert!(!w.charge(100, 12_000, false));
        // Foreground human turn CAN use interactive reserve!
        assert!(w.charge(100, 12_000, true));
        // After 5h window elapses, full worker headroom returns!
        assert!(w.charge(800, 10_000 + FIVE_HOUR_WINDOW_MS, false));
    }
}
