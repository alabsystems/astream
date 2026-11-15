// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Perceptual foreground/background luminance contrast floor nudging low-contrast ANSI colors (such
//! as dark-blue-on-black or light-gray-on-white) above `min_delta_luma` so agent output is always
//! legible (`Astream.MetalDmg.TlaContrastApcaFloor`).

#[cfg(clean_islands)]
#[path = "contrast_apca_floor_island.rs"]
mod contrast_apca_floor_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn md_lum_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn md_adj_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use contrast_apca_floor_island::{md_adj_advance, md_lum_clamp};

/// Maximum scaled relative luminance (`1_000`).
pub const MAX_SCALED_LUMA: u64 = 1_000;

contract_fn! {
    /// Verified contrast legibility floor (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `md_contrast_legible_isl`.
    #[must_use]
    pub const fn md_contrast_legible(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct ContrastFloorGuard {
    min_delta: u64,
    nudges_applied: u64,
}

impl ContrastFloorGuard {
    #[must_use]
    pub const fn new(min_delta: u64) -> Self {
        Self {
            min_delta: md_lum_clamp(min_delta, MAX_SCALED_LUMA),
            nudges_applied: 0,
        }
    }

    pub fn ensure_fg_luma(&mut self, fg_luma: u64, bg_luma: u64) -> u64 {
        let fg = md_lum_clamp(fg_luma, MAX_SCALED_LUMA);
        let bg = md_lum_clamp(bg_luma, MAX_SCALED_LUMA);
        let delta = if fg >= bg {
            fg.saturating_sub(bg)
        } else {
            bg.saturating_sub(fg)
        };
        if md_contrast_legible(delta, self.min_delta) {
            return fg;
        }
        self.nudges_applied =
            md_adj_advance(self.nudges_applied, self.nudges_applied.saturating_add(1));
        if bg < 500 {
            md_lum_clamp(bg.saturating_add(self.min_delta), MAX_SCALED_LUMA)
        } else {
            bg.saturating_sub(self.min_delta)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn boosts_dark_foreground_on_dark_background_while_keeping_high_contrast_intact() {
        let mut g = ContrastFloorGuard::new(300);
        assert_eq!(g.ensure_fg_luma(850, 50), 850);
        assert_eq!(g.ensure_fg_luma(90, 50), 350);
    }
}
