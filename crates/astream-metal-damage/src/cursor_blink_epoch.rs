// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Battery-aware terminal cursor blink state machine keeping the cursor solid during typing and
//! automatically suspending blink wakeups after `10s` of user inactivity
//! (`Astream.MetalDmg.TlaCursorBlinkEpoch`).

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "cursor_blink_epoch_island.rs"]
mod cursor_blink_epoch_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn md_idle_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn md_blink_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use cursor_blink_epoch_island::{md_blink_advance, md_idle_clamp};

/// Idle threshold (`10_000 ms`) after which cursor blinking pauses to save GPU wakeups.
pub const MAX_BLINK_ACTIVE_MS: u64 = 10_000;

contract_fn! {
    /// Verified idle blink-suspension check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `md_blink_suspended_isl`.
    #[must_use]
    pub const fn md_blink_suspended(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct CursorBlinkTimer {
    last_keystroke_ms: u64,
    toggles: u64,
}

impl CursorBlinkTimer {
    #[must_use]
    pub const fn new(now_ms: u64) -> Self {
        Self {
            last_keystroke_ms: now_ms,
            toggles: 0,
        }
    }

    pub fn on_keystroke(&mut self, now_ms: u64) {
        if now_ms > self.last_keystroke_ms {
            self.last_keystroke_ms = now_ms;
        }
    }

    /// Returns `(cursor_visible, needs_next_timer)`.
    pub fn evaluate(&mut self, now_ms: u64) -> (bool, bool) {
        let idle = now_ms.saturating_sub(self.last_keystroke_ms);
        let _ = md_idle_clamp(idle, MAX_BLINK_ACTIVE_MS);
        if md_blink_suspended(idle, MAX_BLINK_ACTIVE_MS) {
            return (true, false);
        }
        if idle < 500 {
            return (true, true);
        }
        self.toggles = md_blink_advance(self.toggles, self.toggles.saturating_add(1));
        let phase_on = ((idle / 500) & 1) == 0;
        (phase_on, true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stays_solid_on_keystroke_blinks_while_active_and_suspends_after_ten_seconds() {
        let mut c = CursorBlinkTimer::new(1_000);
        assert_eq!(c.evaluate(1_200), (true, true));
        assert_eq!(c.evaluate(1_600), (false, true));
        assert_eq!(c.evaluate(12_000), (true, false));
    }
}
