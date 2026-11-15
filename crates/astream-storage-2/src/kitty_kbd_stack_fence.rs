// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pure stack Kitty keyboard protocol (`CSI > flags u` / `CSI < count u`) 8-entry
//! mode stack fence (`Astream.Term.TlaKittyKbdStackFence`).
//!
//! Bounds main-screen and alternate-screen progressive enhancement stacks to 8
//! entries each, clamps flag masks to the 5 defined Kitty keyboard bits (`0x1F`),
//! and atomically clears alternate-screen flags when exiting `DECSET 1049` or on
//! `DECSTR`, preventing crashed TUIs from stranding raw key-event reporting in
//! parent shells.

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
#[path = "kitty_kbd_stack_fence_island.rs"]
mod kitty_kbd_stack_fence_island;
#[cfg(clean_islands)]
pub use kitty_kbd_stack_fence_island::{kitty_depth_clamp, kitty_epoch_advance, kitty_flags_clamp};

/// Maximum stack depth per screen buffer per Kitty keyboard specification (`8`).
pub const KITTY_KBD_STACK_CAP: usize = 8;

/// Defined 5-bit Kitty keyboard progressive enhancement mask (`0b1_1111 = 0x1F`).
pub const KITTY_KBD_MAX_FLAGS: u64 = 0x1F;

#[cfg(not(clean_islands))]
/// Clamp stack depth to `max_depth`.
#[must_use]
pub const fn kitty_depth_clamp(cand_depth: u64, max_depth: u64) -> u64 {
    if cand_depth < max_depth {
        cand_depth
    } else {
        max_depth
    }
}

#[cfg(not(clean_islands))]
/// Clamp progressive enhancement flags to `max_flags` (`0x1F`).
#[must_use]
pub const fn kitty_flags_clamp(raw_flags: u64, max_flags: u64) -> u64 {
    if raw_flags < max_flags {
        raw_flags
    } else {
        max_flags
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance transition counter across push/pop/reset events.
#[must_use]
pub const fn kitty_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ScreenKbdStack {
    slots: [u8; KITTY_KBD_STACK_CAP],
    depth: usize,
    active: u8,
}

impl ScreenKbdStack {
    const fn new() -> Self {
        Self {
            slots: [0u8; KITTY_KBD_STACK_CAP],
            depth: 0,
            active: 0,
        }
    }

    fn push(&mut self, raw_flags: u8) {
        let masked = raw_flags & (KITTY_KBD_MAX_FLAGS as u8);
        let max_u8 = KITTY_KBD_MAX_FLAGS as u8;
        let clamped = if masked < max_u8 { masked } else { max_u8 };
        let capped_flags = kitty_flags_clamp(clamped as u64, KITTY_KBD_MAX_FLAGS) as u8;
        if self.depth < KITTY_KBD_STACK_CAP {
            if let Some(slot) = self.slots.get_mut(self.depth) {
                *slot = self.active;
            }
            let cand_depth = (self.depth as u64).saturating_add(1);
            self.depth = kitty_depth_clamp(cand_depth, KITTY_KBD_STACK_CAP as u64) as usize;
        } else {
            // Shift down by 1 without dynamic `[i]` indexing so oldest entry is evicted.
            self.slots = [
                self.slots[1],
                self.slots[2],
                self.slots[3],
                self.slots[4],
                self.slots[5],
                self.slots[6],
                self.slots[7],
                self.active,
            ];
            self.depth =
                kitty_depth_clamp(KITTY_KBD_STACK_CAP as u64, KITTY_KBD_STACK_CAP as u64) as usize;
        }
        self.active = capped_flags;
    }

    fn pop(&mut self, count: usize) {
        let n = if count == 0 { 1 } else { count };
        let cap_plus = KITTY_KBD_STACK_CAP.saturating_add(1);
        let mut rem = if n < cap_plus { n } else { cap_plus };
        while rem > 0 {
            if self.depth == 0 {
                self.active = 0;
                break;
            }
            let prev_idx = self.depth.saturating_sub(1);
            self.active = match self.slots.get(prev_idx) {
                Some(&v) => kitty_flags_clamp(v as u64, KITTY_KBD_MAX_FLAGS) as u8,
                None => 0,
            };
            if let Some(slot) = self.slots.get_mut(prev_idx) {
                *slot = 0;
            }
            self.depth = kitty_depth_clamp(prev_idx as u64, KITTY_KBD_STACK_CAP as u64) as usize;
            rem = rem.saturating_sub(1);
        }
    }

    const fn reset(&mut self) {
        self.slots = [0u8; KITTY_KBD_STACK_CAP];
        self.depth = 0;
        self.active = 0;
    }
}

/// Dual-screen (`main` + `alt`) Kitty keyboard protocol stack fence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KittyKbdStackFence {
    main: ScreenKbdStack,
    alt: ScreenKbdStack,
    in_alt_screen: bool,
    transition_epoch: u64,
}

impl Default for KittyKbdStackFence {
    fn default() -> Self {
        Self::new()
    }
}

impl KittyKbdStackFence {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            main: ScreenKbdStack::new(),
            alt: ScreenKbdStack::new(),
            in_alt_screen: false,
            transition_epoch: 0,
        }
    }

    #[must_use]
    pub const fn active_flags(&self) -> u8 {
        if self.in_alt_screen {
            self.alt.active
        } else {
            self.main.active
        }
    }

    #[must_use]
    pub const fn active_depth(&self) -> usize {
        if self.in_alt_screen {
            self.alt.depth
        } else {
            self.main.depth
        }
    }

    #[must_use]
    pub const fn transition_epoch(&self) -> u64 {
        self.transition_epoch
    }

    fn bump_epoch(&mut self) {
        let cand = self.transition_epoch.saturating_add(1);
        self.transition_epoch = kitty_epoch_advance(self.transition_epoch, cand);
    }

    /// Handle `CSI > flags u`.
    pub fn push_flags(&mut self, raw_flags: u8) {
        if self.in_alt_screen {
            self.alt.push(raw_flags);
        } else {
            self.main.push(raw_flags);
        }
        self.bump_epoch();
    }

    /// Handle `CSI < count u`.
    pub fn pop_flags(&mut self, count: usize) {
        if self.in_alt_screen {
            self.alt.pop(count);
        } else {
            self.main.pop(count);
        }
        self.bump_epoch();
    }

    /// Enter or leave `DECSET 1049` alternate screen; leaving wipes `alt` stack!
    pub fn set_alt_screen(&mut self, in_alt: bool) {
        if self.in_alt_screen && !in_alt {
            self.alt.reset();
        }
        self.in_alt_screen = in_alt;
        self.bump_epoch();
    }

    /// Soft terminal reset (`DECSTR` / `RIS`) clears both stacks.
    pub fn reset_all(&mut self) {
        self.main.reset();
        self.alt.reset();
        self.in_alt_screen = false;
        self.bump_epoch();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alt_screen_crash_never_leaks_kitty_flags_to_main_shell() {
        let mut fence = KittyKbdStackFence::new();
        assert_eq!(fence.active_flags(), 0);

        fence.set_alt_screen(true);
        fence.push_flags(0b01011);
        fence.push_flags(0xFF); // masked & clamped to 0x1F
        assert_eq!(fence.active_flags(), 0x1F);
        assert_eq!(fence.active_depth(), 2);

        // Crashed TUI exits alt screen without `CSI < u`: main shell stays clean (`0`)!
        fence.set_alt_screen(false);
        assert_eq!(fence.active_flags(), 0);
        assert_eq!(fence.active_depth(), 0);

        // Overflow past 8 entries stays strictly bounded at 8:
        for i in 1..=12u8 {
            fence.push_flags(i);
        }
        assert_eq!(fence.active_depth(), KITTY_KBD_STACK_CAP);
        fence.pop_flags(1);
        assert_eq!(fence.active_flags(), 11);
    }
}
