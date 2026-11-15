// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Kitty Keyboard Protocol progressive-enhancement ring stack
//! (`Astream.Term.TlaKittyEnhancementRing`).
//!
//! Models primary and alternate-screen Kitty keyboard stacks (`CSI > flags u` push,
//! `CSI < count u` pop, `CSI = flags ; mode u` set, `CSI ? u` query -> `CSI ? flags u`)
//! with fixed-size zero-allocation ring eviction at [`MAX_KITTY_RING_STACK`] (`16`, matching
//! Kitty / `aterm` stack limits) and 5-bit flag masking (`0b1_1111 = 31`).

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
#[path = "kitty_enhancement_ring_island.rs"]
mod kitty_enhancement_ring_island;
#[cfg(clean_islands)]
pub use kitty_enhancement_ring_island::{kitty_ring_depth_clamp, kitty_ring_flags_clamp};

/// Mirror of Clean's `kitty_ring_depth_clamp` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn kitty_ring_depth_clamp(proposed_depth: u64, max_depth: u64) -> u64 {
    if proposed_depth < max_depth {
        proposed_depth
    } else {
        max_depth
    }
}

/// Mirror of Clean's `kitty_ring_flags_clamp` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn kitty_ring_flags_clamp(raw_flags: u64, max_flags: u64) -> u64 {
    if raw_flags < max_flags {
        raw_flags
    } else {
        max_flags
    }
}

contract_fn! {
    /// Kernel-certified check that `depth` is within `[0, max_depth]` (`depth <= max_depth`),
    /// linked via `clean-kernel-defeq` to `kitty_ring_depth_valid_isl`.
    #[must_use]
    pub const fn kitty_ring_depth_valid(depth: u64, max_depth: u64) -> bool
    clauses [ensures result == (depth <= max_depth)]
    {
        depth <= max_depth
    }
}

/// Maximum saved entries per screen buffer in [`KittyEnhancementRing`].
pub const MAX_KITTY_RING_STACK: usize = 16;

/// Mask of all 5 defined Kitty Keyboard progressive-enhancement flags (`0b1_1111 = 31`).
pub const KITTY_RING_ALL_FLAGS_MASK: u8 = 0b1_1111;

/// Flag 1 (`1 << 0`): Disambiguate escape codes.
pub const KITTY_RING_DISAMBIGUATE: u8 = 1 << 0;
/// Flag 2 (`1 << 1`): Report event types (press / repeat / release).
pub const KITTY_RING_REPORT_EVENTS: u8 = 1 << 1;
/// Flag 4 (`1 << 2`): Report alternate keys.
pub const KITTY_RING_REPORT_ALTERNATES: u8 = 1 << 2;
/// Flag 8 (`1 << 3`): Report all keys as escape codes.
pub const KITTY_RING_REPORT_ALL_KEYS: u8 = 1 << 3;
/// Flag 16 (`1 << 4`): Report associated text.
pub const KITTY_RING_REPORT_TEXT: u8 = 1 << 4;

/// Update mode parameter for `CSI = flags ; mode u`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KittyEnhancementSetMode {
    /// `mode = 1` (default): replace active flags with `flags`.
    Assign,
    /// `mode = 2`: bitwise-OR `flags` into active flags.
    BitwiseOr,
    /// `mode = 3`: clear `flags` bits from active flags (`active & !flags`).
    BitwiseAndNot,
}

impl KittyEnhancementSetMode {
    /// Parse `CSI = flags ; mode u`'s 1-based mode parameter (`0` or `1` -> `Assign`).
    #[must_use]
    pub const fn from_csi_param(param: u16) -> Option<Self> {
        match param {
            0 | 1 => Some(Self::Assign),
            2 => Some(Self::BitwiseOr),
            3 => Some(Self::BitwiseAndNot),
            _ => None,
        }
    }
}

const fn sanitize_flags(raw: u16) -> u8 {
    let masked = (raw as u64) & (KITTY_RING_ALL_FLAGS_MASK as u64);
    kitty_ring_flags_clamp(masked, KITTY_RING_ALL_FLAGS_MASK as u64) as u8
}

/// Zero-allocation single-screen Kitty keyboard mode stack (`<= MAX_KITTY_RING_STACK`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KittyEnhancementRing {
    entries: [u8; MAX_KITTY_RING_STACK],
    len: u8,
    active: u8,
}

impl Default for KittyEnhancementRing {
    fn default() -> Self {
        Self::new()
    }
}

impl KittyEnhancementRing {
    /// Construct an empty stack with legacy keyboard mode (`active == 0`).
    #[must_use]
    pub const fn new() -> Self {
        Self {
            entries: [0; MAX_KITTY_RING_STACK],
            len: 0,
            active: 0,
        }
    }

    /// Active 5-bit Kitty keyboard flags (`0..=31`).
    #[must_use]
    pub const fn active_flags(&self) -> u8 {
        self.active
    }

    /// Number of saved flag states on the stack (`0..=MAX_KITTY_RING_STACK`).
    #[must_use]
    pub const fn depth(&self) -> usize {
        let raw = self.len as usize;
        if raw < MAX_KITTY_RING_STACK {
            raw
        } else {
            MAX_KITTY_RING_STACK
        }
    }

    /// Handle `CSI > flags u`: push current `active_flags()` onto the bounded stack (evicting
    /// the oldest bottom entry when full) and set `active` to `sanitize_flags(flags)`.
    pub fn push(&mut self, flags: u16) {
        let cur_len = self.len as usize;
        let saved = self.active;
        if let Some(slot) = self.entries.get_mut(cur_len) {
            *slot = saved;
            let next_depth = kitty_ring_depth_clamp(
                (cur_len.saturating_add(1)) as u64,
                MAX_KITTY_RING_STACK as u64,
            ) as u8;
            let _ = kitty_ring_depth_valid(next_depth as u64, MAX_KITTY_RING_STACK as u64);
            self.len = next_depth;
        } else {
            let [_, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15] =
                self.entries;
            self.entries = [
                e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, saved,
            ];
            self.len = MAX_KITTY_RING_STACK as u8;
        }
        self.active = sanitize_flags(flags);
    }

    /// Handle `CSI < count u`: pop `max(count, 1)` entries; if the stack underflows,
    /// `active` resets to `0` (`legacy` mode) per the Kitty Keyboard specification.
    #[allow(clippy::manual_unwrap_or, clippy::manual_unwrap_or_default)]
    pub fn pop(&mut self, count: u16) {
        let pops = if count == 0 { 1usize } else { count as usize };
        let cur_len = self.depth();
        if pops > cur_len {
            self.len = 0;
            self.active = 0;
            self.entries = [0; MAX_KITTY_RING_STACK];
        } else {
            let new_len = cur_len.saturating_sub(pops);
            self.active = match self.entries.get(new_len) {
                Some(&v) => v,
                None => 0,
            };
            let mut k = new_len;
            while k < MAX_KITTY_RING_STACK {
                if let Some(slot) = self.entries.get_mut(k) {
                    *slot = 0;
                }
                k = k.saturating_add(1);
            }
            self.len = kitty_ring_depth_clamp(new_len as u64, MAX_KITTY_RING_STACK as u64) as u8;
        }
    }

    /// Handle `CSI = flags ; mode u`: update `active` without modifying the saved stack.
    pub const fn set(&mut self, flags: u16, mode: KittyEnhancementSetMode) {
        let clean = sanitize_flags(flags);
        let updated = match mode {
            KittyEnhancementSetMode::Assign => clean,
            KittyEnhancementSetMode::BitwiseOr => self.active | clean,
            KittyEnhancementSetMode::BitwiseAndNot => self.active & (!clean),
        };
        self.active =
            kitty_ring_flags_clamp(updated as u64, KITTY_RING_ALL_FLAGS_MASK as u64) as u8;
    }

    /// Reset stack and active flags (`RIS` or altscreen exit).
    pub const fn reset(&mut self) {
        *self = Self::new();
    }

    /// Format the `CSI ? flags u` reply emitted for `CSI ? u` without formatting panics.
    #[must_use]
    pub fn query_reply(&self) -> String {
        let (h, t, o) = u8_decimal_ascii(self.active);
        let mut out = String::new();
        out.push_str("\x1b[?");
        if let Some(d2) = h {
            out.push(d2 as char);
        }
        if let Some(d1) = t {
            out.push(d1 as char);
        }
        out.push(o as char);
        out.push('u');
        out
    }
}

const fn u8_decimal_ascii(v: u8) -> (Option<u8>, Option<u8>, u8) {
    let (h, rem100) = if v >= 200 {
        (Some(b'2'), v.saturating_sub(200))
    } else if v >= 100 {
        (Some(b'1'), v.saturating_sub(100))
    } else {
        (None, v)
    };
    let (tens_digit, ones_digit) = if rem100 >= 90 {
        (9u8, rem100.saturating_sub(90))
    } else if rem100 >= 80 {
        (8u8, rem100.saturating_sub(80))
    } else if rem100 >= 70 {
        (7u8, rem100.saturating_sub(70))
    } else if rem100 >= 60 {
        (6u8, rem100.saturating_sub(60))
    } else if rem100 >= 50 {
        (5u8, rem100.saturating_sub(50))
    } else if rem100 >= 40 {
        (4u8, rem100.saturating_sub(40))
    } else if rem100 >= 30 {
        (3u8, rem100.saturating_sub(30))
    } else if rem100 >= 20 {
        (2u8, rem100.saturating_sub(20))
    } else if rem100 >= 10 {
        (1u8, rem100.saturating_sub(10))
    } else {
        (0u8, rem100)
    };
    let t = if v >= 10 {
        Some(b'0'.saturating_add(tens_digit))
    } else {
        None
    };
    (h, t, b'0'.saturating_add(ones_digit))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn push_set_pop_and_ring_eviction_obey_kitty_spec() {
        let mut s = KittyEnhancementRing::new();
        assert_eq!(s.active_flags(), 0);
        assert_eq!(s.query_reply(), "\x1b[?0u");

        s.push(KITTY_RING_DISAMBIGUATE as u16);
        assert_eq!(s.active_flags(), 1);
        assert_eq!(s.depth(), 1);

        s.set(
            KITTY_RING_REPORT_EVENTS as u16,
            KittyEnhancementSetMode::BitwiseOr,
        );
        assert_eq!(s.active_flags(), 3);
        assert_eq!(s.query_reply(), "\x1b[?3u");

        // Push 20 entries: depth caps at 16 without panicking, evicting oldest entries.
        for i in 0..20u16 {
            s.push(i);
        }
        assert_eq!(s.depth(), MAX_KITTY_RING_STACK);
        assert!(s.active_flags() <= KITTY_RING_ALL_FLAGS_MASK);

        // Underflow pop resets active flags and stack to 0.
        s.pop(99);
        assert_eq!(s.depth(), 0);
        assert_eq!(s.active_flags(), 0);
    }
}
