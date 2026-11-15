// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! DEC `?1004` (`CSI I` / `CSI O`) window focus-event debouncer filtering sub-30ms macOS Stage
//! Manager / popover focus flicker so Neovim/tmux auto-save hooks do not thrash
//! (`Astream.KeyChord.TlaFocusEventDebouncer`).

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
#[path = "focus_event_debouncer_island.rs"]
mod focus_event_debouncer_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn kc_foc_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn kc_emit_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use focus_event_debouncer_island::{kc_emit_advance, kc_foc_clamp};

/// Maximum focus debounce interval (`250 ms`).
pub const MAX_DEBOUNCE_MS: u64 = 250;

contract_fn! {
    /// Verified settle-window check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `kc_debounce_settled_isl`.
    #[must_use]
    pub const fn kc_debounce_settled(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct FocusDebouncer {
    debounce_ms: u64,
    last_emit_ms: u64,
    emitted_focused: bool,
    emits: u64,
}

impl FocusDebouncer {
    #[must_use]
    pub const fn new(debounce_ms: u64) -> Self {
        Self {
            debounce_ms: kc_foc_clamp(debounce_ms, MAX_DEBOUNCE_MS),
            last_emit_ms: 0,
            emitted_focused: true,
            emits: 0,
        }
    }

    pub fn should_emit_transition(&mut self, focused: bool, now_ms: u64) -> bool {
        if focused == self.emitted_focused {
            return false;
        }
        let min_time = if self.emits == 0 {
            0
        } else {
            self.last_emit_ms.saturating_add(self.debounce_ms)
        };
        if kc_debounce_settled(now_ms, min_time) {
            self.emitted_focused = focused;
            self.last_emit_ms = now_ms;
            self.emits = kc_emit_advance(self.emits, self.emits.saturating_add(1));
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
    fn suppresses_sub_threshold_focus_flicker_and_emits_settled_transition() {
        let mut d = FocusDebouncer::new(40);
        assert!(d.should_emit_transition(false, 100));
        assert!(!d.should_emit_transition(true, 115));
        assert!(d.should_emit_transition(true, 150));
    }
}
