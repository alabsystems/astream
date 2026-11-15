// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bounded DEC private mode (`DECSET`/`DECRST` + `XTSAVE`/`XTRESTORE`) stack & crash sanitizer
//! (`Astream.Term.TlaDecsetModeRestoreFence`).
//!
//! Protects `astream-term` and `aterm` session restore against runaway `XTSAVE` (`CSI ? s`) stacks
//! and dangling TUI modes (`?1000..1006` mouse tracking, `?2004` bracketed paste, `?1004` focus,
//! `?2026` synchronized output, `?1049` alt-screen) when a foreground child exits abnormally.

#[cfg(clean_islands)]
#[path = "decset_mode_restore_fence_island.rs"]
mod decset_mode_restore_fence_island;
#[cfg(clean_islands)]
pub use decset_mode_restore_fence_island::{decset_epoch_advance, decset_save_depth_clamp};

#[cfg(not(clean_islands))]
/// Clamp `XTSAVE` mode stack depth to `max_depth`.
#[must_use]
pub const fn decset_save_depth_clamp(cand_depth: u64, max_depth: u64) -> u64 {
    if cand_depth < max_depth {
        cand_depth
    } else {
        max_depth
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the DECSET mode transition / sanitize epoch.
#[must_use]
pub const fn decset_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff the `XTSAVE` mode stack has room below `max_depth`.
    #[must_use]
    pub const fn decset_can_push_save(depth: u64, max_depth: u64) -> bool
    clauses [ensures result == (depth < max_depth)]
    {
        depth < max_depth
    }
}

/// Maximum `XTSAVE` snapshots retained per terminal screen.
pub const MAX_DECSET_SAVE_DEPTH: usize = 8;

/// Bitflags for common DEC private modes tracked across `XTSAVE`/`XTRESTORE` and crash cleanup.
pub const DEC_MODE_CURSOR_VISIBLE: u32 = 1 << 0; // ?25 (default ON)
pub const DEC_MODE_AUTOWRAP: u32 = 1 << 1; // ?7 (default ON)
pub const DEC_MODE_APP_CURSOR: u32 = 1 << 2; // ?1
pub const DEC_MODE_MOUSE_X10: u32 = 1 << 3; // ?1000
pub const DEC_MODE_MOUSE_BTN: u32 = 1 << 4; // ?1002
pub const DEC_MODE_MOUSE_ANY: u32 = 1 << 5; // ?1003
pub const DEC_MODE_MOUSE_SGR: u32 = 1 << 6; // ?1006
pub const DEC_MODE_FOCUS_EVENT: u32 = 1 << 7; // ?1004
pub const DEC_MODE_BRACKETED_PASTE: u32 = 1 << 8; // ?2004
pub const DEC_MODE_ALT_SCREEN: u32 = 1 << 9; // ?1049
pub const DEC_MODE_SYNC_OUTPUT: u32 = 1 << 10; // ?2026

/// Default clean shell mode mask (`?25` cursor visible + `?7` autowrap).
pub const DEC_DEFAULT_SHELL_MASK: u32 = DEC_MODE_CURSOR_VISIBLE | DEC_MODE_AUTOWRAP;

/// Volatile TUI modes cleared automatically when a foreground child crashes.
pub const DEC_VOLATILE_TUI_MASK: u32 = DEC_MODE_APP_CURSOR
    | DEC_MODE_MOUSE_X10
    | DEC_MODE_MOUSE_BTN
    | DEC_MODE_MOUSE_ANY
    | DEC_MODE_MOUSE_SGR
    | DEC_MODE_FOCUS_EVENT
    | DEC_MODE_BRACKETED_PASTE
    | DEC_MODE_ALT_SCREEN
    | DEC_MODE_SYNC_OUTPUT;

/// Bounded `DECSET` mode bitmask and `XTSAVE`/`XTRESTORE` fence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DecsetModeRestoreFence {
    active_mask: u32,
    save_stack: [u32; MAX_DECSET_SAVE_DEPTH],
    save_depth: u64,
    mode_epoch: u64,
}

impl Default for DecsetModeRestoreFence {
    fn default() -> Self {
        Self::new()
    }
}

impl DecsetModeRestoreFence {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            active_mask: DEC_DEFAULT_SHELL_MASK,
            save_stack: [DEC_DEFAULT_SHELL_MASK; MAX_DECSET_SAVE_DEPTH],
            save_depth: 0,
            mode_epoch: 0,
        }
    }

    #[must_use]
    pub const fn active_mask(&self) -> u32 {
        self.active_mask
    }

    #[must_use]
    pub const fn save_depth(&self) -> u64 {
        self.save_depth
    }

    #[must_use]
    pub const fn mode_epoch(&self) -> u64 {
        self.mode_epoch
    }

    pub fn set_mode_bits(&mut self, bits: u32) {
        self.active_mask |= bits;
        let next_ep = self.mode_epoch.saturating_add(1);
        self.mode_epoch = decset_epoch_advance(self.mode_epoch, next_ep);
    }

    pub fn clear_mode_bits(&mut self, bits: u32) {
        self.active_mask &= !bits;
        let next_ep = self.mode_epoch.saturating_add(1);
        self.mode_epoch = decset_epoch_advance(self.mode_epoch, next_ep);
    }

    /// Push current `active_mask` onto the bounded `XTSAVE` stack (evicting oldest if full).
    pub fn xtsave(&mut self) {
        let cap = MAX_DECSET_SAVE_DEPTH as u64;
        if decset_can_push_save(self.save_depth, cap) {
            if let Some(dst) = self.save_stack.get_mut(self.save_depth as usize) {
                *dst = self.active_mask;
            }
            let cand = self.save_depth.saturating_add(1);
            self.save_depth = decset_save_depth_clamp(cand, cap);
        } else {
            let mut idx = 0usize;
            while let Some(&next_val) = self.save_stack.get(idx.saturating_add(1)) {
                if let Some(dst) = self.save_stack.get_mut(idx) {
                    *dst = next_val;
                }
                idx = idx.saturating_add(1);
            }
            if let Some(last) = self.save_stack.last_mut() {
                *last = self.active_mask;
            }
        }
        let next_ep = self.mode_epoch.saturating_add(1);
        self.mode_epoch = decset_epoch_advance(self.mode_epoch, next_ep);
    }

    /// Restore `active_mask` from the top of the `XTSAVE` stack if non-empty.
    pub fn xtrestore(&mut self) -> bool {
        if self.save_depth == 0 {
            return false;
        }
        let clamped_cur = decset_save_depth_clamp(self.save_depth, MAX_DECSET_SAVE_DEPTH as u64);
        let next_depth = clamped_cur.saturating_sub(1);
        self.save_depth = next_depth;
        if let Some(&saved) = self.save_stack.get(next_depth as usize) {
            self.active_mask = saved;
        }
        let next_ep = self.mode_epoch.saturating_add(1);
        self.mode_epoch = decset_epoch_advance(self.mode_epoch, next_ep);
        true
    }

    /// Clear leaky TUI mouse/paste/sync/alt-screen modes and restore `?25` cursor visibility on crash.
    pub fn sanitize_on_child_crash(&mut self) -> u32 {
        self.active_mask = (self.active_mask & !DEC_VOLATILE_TUI_MASK) | DEC_MODE_CURSOR_VISIBLE;
        self.save_depth = 0;
        let next_ep = self.mode_epoch.saturating_add(1);
        self.mode_epoch = decset_epoch_advance(self.mode_epoch, next_ep);
        self.active_mask
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn xtsave_bounds_depth_and_crash_sanitize_clears_leaky_tui_modes() {
        let mut fence = DecsetModeRestoreFence::new();
        fence.xtsave();
        fence.set_mode_bits(DEC_MODE_MOUSE_SGR | DEC_MODE_BRACKETED_PASTE | DEC_MODE_SYNC_OUTPUT);
        fence.clear_mode_bits(DEC_MODE_CURSOR_VISIBLE);
        assert_eq!(fence.save_depth(), 1);
        let cleaned = fence.sanitize_on_child_crash();
        assert_eq!(cleaned, DEC_DEFAULT_SHELL_MASK);
        assert_eq!(fence.save_depth(), 0);
    }
}
