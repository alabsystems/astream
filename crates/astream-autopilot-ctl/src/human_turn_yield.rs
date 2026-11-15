// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Human-input & 10-minute direct-question ownership guard (`aterm` primer: nothing is typed while
//! the person types or has input unsent, and under `land` a reply to a person's own message within
//! 10 minutes is theirs; `Astream.Autopilot.TlaHumanTurnYield`).

#[cfg(clean_islands)]
#[path = "human_turn_yield_island.rs"]
mod human_turn_yield_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ap_wait_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ap_yield_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use human_turn_yield_island::{ap_wait_clamp, ap_yield_advance};

/// Ten-minute human-turn ownership window in milliseconds (`600_000 ms`).
pub const HUMAN_REPLY_OWNERSHIP_MS: u64 = 600_000;

contract_fn! {
    /// Verified human-ownership window check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `ap_human_owns_turn_isl`.
    #[must_use]
    pub const fn ap_human_owns_turn(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Guards Autopilot keystroke injection against clobbering live human input or direct Q&A.
#[derive(Debug, Clone, Default)]
pub struct HumanTurnOwnershipGuard {
    yields: u64,
}

impl HumanTurnOwnershipGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self { yields: 0 }
    }

    pub fn must_hold_typing(
        &mut self,
        unsent_input_bytes: u64,
        human_typing_active: bool,
        land_mode_direct_human_prompt: bool,
        elapsed_since_human_ms: u64,
    ) -> bool {
        if unsent_input_bytes > 0 || human_typing_active {
            self.yields = ap_yield_advance(self.yields, self.yields.saturating_add(1));
            return true;
        }
        if land_mode_direct_human_prompt {
            let clamped = ap_wait_clamp(
                elapsed_since_human_ms,
                HUMAN_REPLY_OWNERSHIP_MS.saturating_add(1),
            );
            if ap_human_owns_turn(HUMAN_REPLY_OWNERSHIP_MS, clamped) {
                self.yields = ap_yield_advance(self.yields, self.yields.saturating_add(1));
                return true;
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn human_guard_yields_on_unsent_input_and_within_ten_minute_land_reply_window() {
        let mut g = HumanTurnOwnershipGuard::new();
        assert!(g.must_hold_typing(4, false, false, 999_999));
        assert!(g.must_hold_typing(0, false, true, 120_000));
        assert!(!g.must_hold_typing(0, false, true, 600_001));
    }
}
