// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! In-flight auto-repeat keystroke governor dropping excess synthetic key-repeats when unacked
//! remote input frames exceed cap so releasing `j`/`Backspace` stops immediately
//! (`Astream.KeyChord.TlaRepeatRateGovernor`).

#[cfg(clean_islands)]
#[path = "repeat_rate_governor_island.rs"]
mod repeat_rate_governor_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn kc_rep_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn kc_drop_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use repeat_rate_governor_island::{kc_drop_advance, kc_rep_clamp};

/// Maximum unacked auto-repeat keystrokes allowed in flight (`8`).
pub const MAX_UNACKED_REPEATS: u64 = 8;

contract_fn! {
    /// Verified repeat-queue headroom (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `kc_repeat_admitted_isl`.
    #[must_use]
    pub const fn kc_repeat_admitted(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct KeyRepeatGovernor {
    dropped_repeats: u64,
}

impl KeyRepeatGovernor {
    #[must_use]
    pub const fn new() -> Self {
        Self { dropped_repeats: 0 }
    }

    pub fn admit_keystroke(&mut self, is_repeat: bool, unacked_inputs: u64) -> bool {
        if !is_repeat {
            return true;
        }
        let clamped = kc_rep_clamp(unacked_inputs, 1_024);
        if kc_repeat_admitted(MAX_UNACKED_REPEATS, clamped.saturating_add(1)) {
            true
        } else {
            self.dropped_repeats =
                kc_drop_advance(self.dropped_repeats, self.dropped_repeats.saturating_add(1));
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn always_admits_initial_keydown_and_caps_unacked_auto_repeats() {
        let mut g = KeyRepeatGovernor::new();
        assert!(g.admit_keystroke(true, 4));
        assert!(!g.admit_keystroke(true, 8));
        assert!(g.admit_keystroke(false, 25));
    }
}
