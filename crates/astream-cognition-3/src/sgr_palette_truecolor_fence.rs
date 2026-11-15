// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bounded `OSC 4` / `OSC 104` 256-color dynamic palette override & reset fence
//! (`Astream.Term.TlaSgrPaletteTruecolorFence`).
//!
//! Tracks overridden 24-bit RGB entries in the 256-color terminal palette on the stack using a
//! 4x64-bit dirty bitmap (`dirty_count <= 256`) so `OSC 104` resets modified colors in O(1)
//! without heap allocation.

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
#[path = "sgr_palette_truecolor_fence_island.rs"]
mod sgr_palette_truecolor_fence_island;
#[cfg(clean_islands)]
pub use sgr_palette_truecolor_fence_island::{
    palette_dirty_clamp_b113, palette_epoch_advance_b113,
};

#[cfg(not(clean_islands))]
/// Clamp dirty custom palette entry count to `max_entries` (`256`).
#[must_use]
pub const fn palette_dirty_clamp_b113(cand_dirty: u64, max_entries: u64) -> u64 {
    if cand_dirty < max_entries {
        cand_dirty
    } else {
        max_entries
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the terminal palette mutation epoch.
#[must_use]
pub const fn palette_epoch_advance_b113(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `color_idx` is a valid 8-bit ANSI/xterm palette index (`< 256`).
    #[must_use]
    pub const fn palette_index_valid_b113(color_idx: u64) -> bool
    clauses [ensures result == (color_idx < 256)]
    {
        color_idx < 256
    }
}

/// Number of entries in the standard xterm indexed palette.
pub const PALETTE_LEN: usize = 256;

/// Stack-allocated `OSC 4` / `OSC 104` dynamic palette override fence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SgrPaletteTruecolorFence {
    rgb_overrides: [u32; PALETTE_LEN],
    dirty_bits: [u64; 4],
    dirty_count: u64,
    palette_epoch: u64,
}

impl Default for SgrPaletteTruecolorFence {
    fn default() -> Self {
        Self::new()
    }
}

impl SgrPaletteTruecolorFence {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            rgb_overrides: [0; PALETTE_LEN],
            dirty_bits: [0; 4],
            dirty_count: 0,
            palette_epoch: 0,
        }
    }

    #[must_use]
    pub const fn dirty_count(&self) -> u64 {
        self.dirty_count
    }

    #[must_use]
    pub const fn palette_epoch(&self) -> u64 {
        self.palette_epoch
    }

    /// Set `OSC 4` RGB override for `idx` (`0..256`).
    pub fn set_osc4_rgb(&mut self, idx: u16, r: u8, g: u8, b: u8) -> bool {
        if !palette_index_valid_b113(idx as u64) {
            return false;
        }
        let slot = idx as usize;
        let word = slot >> 6;
        let bit = 1u64 << (slot & 63);
        let Some(w_ref) = self.dirty_bits.get_mut(word) else {
            return false;
        };
        if (*w_ref & bit) == 0 {
            *w_ref |= bit;
            let cand = self.dirty_count.saturating_add(1);
            self.dirty_count = palette_dirty_clamp_b113(cand, PALETTE_LEN as u64);
        }
        if let Some(rgb_ref) = self.rgb_overrides.get_mut(slot) {
            *rgb_ref = ((r as u32) << 16) | ((g as u32) << 8) | (b as u32);
        }
        let next_ep = self.palette_epoch.saturating_add(1);
        self.palette_epoch = palette_epoch_advance_b113(self.palette_epoch, next_ep);
        true
    }

    /// Query custom RGB `(r, g, b)` for `idx`, if overridden via `OSC 4`.
    #[must_use]
    #[allow(clippy::question_mark)]
    pub fn get_override(&self, idx: u8) -> Option<(u8, u8, u8)> {
        let slot = idx as usize;
        let word = slot >> 6;
        let bit = 1u64 << (slot & 63);
        let Some(&bits) = self.dirty_bits.get(word) else {
            return None;
        };
        if (bits & bit) == 0 {
            None
        } else {
            let Some(&packed) = self.rgb_overrides.get(slot) else {
                return None;
            };
            Some((
                ((packed >> 16) & 0xFF) as u8,
                ((packed >> 8) & 0xFF) as u8,
                (packed & 0xFF) as u8,
            ))
        }
    }

    /// Handle `OSC 104` (reset all custom palette entries in O(1)).
    pub fn reset_all_osc104(&mut self) {
        self.dirty_bits = [0; 4];
        self.dirty_count = 0;
        let next_ep = self.palette_epoch.saturating_add(1);
        self.palette_epoch = palette_epoch_advance_b113(self.palette_epoch, next_ep);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tracks_osc4_overrides_and_resets_cleanly_on_osc104() {
        let mut p = SgrPaletteTruecolorFence::new();
        assert!(p.set_osc4_rgb(42, 0x12, 0x34, 0x56));
        assert!(!p.set_osc4_rgb(300, 1, 2, 3));
        assert_eq!(p.get_override(42), Some((0x12, 0x34, 0x56)));
        assert_eq!(p.dirty_count(), 1);
        p.reset_all_osc104();
        assert_eq!(p.get_override(42), None);
        assert_eq!(p.dirty_count(), 0);
    }
}
