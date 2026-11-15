// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! SGR `?1006` (`CSI < Cb ; Cx ; Cy M/m`) 1-based mouse coordinate clamper ensuring out-of-window
//! drag coordinates stay strictly inside `[1, cols]` x `[1, rows]` (`Astream.KeyChord.TlaMouseSgr1006Clamp`).

#[cfg(clean_islands)]
#[path = "mouse_sgr_1006_clamp_island.rs"]
mod mouse_sgr_1006_clamp_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn kc_pos_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn kc_mouse_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use mouse_sgr_1006_clamp_island::{kc_mouse_advance, kc_pos_clamp};

/// Maximum 1-based SGR mouse cell coordinate (`2_048`).
pub const MAX_SGR_COORD: u64 = 2_048;

contract_fn! {
    /// Verified 1-based grid inclusion (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `kc_coord_in_grid_isl`.
    #[must_use]
    pub const fn kc_coord_in_grid(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct SgrMouseClamper {
    events_formatted: u64,
}

impl SgrMouseClamper {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            events_formatted: 0,
        }
    }

    pub fn clamp_1_based(&mut self, raw_x: u64, raw_y: u64, cols: u64, rows: u64) -> (u64, u64) {
        let max_c = kc_pos_clamp(if cols == 0 { 1 } else { cols }, MAX_SGR_COORD);
        let max_r = kc_pos_clamp(if rows == 0 { 1 } else { rows }, MAX_SGR_COORD);
        let cx = kc_pos_clamp(if raw_x == 0 { 1 } else { raw_x }, max_c);
        let cy = kc_pos_clamp(if raw_y == 0 { 1 } else { raw_y }, max_r);
        self.events_formatted = kc_mouse_advance(
            self.events_formatted,
            self.events_formatted.saturating_add(1),
        );
        let _ = kc_coord_in_grid(max_c, cx);
        let _ = kc_coord_in_grid(max_r, cy);
        (cx, cy)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clamps_zero_and_overshoot_mouse_drag_coords_to_grid_bounds() {
        let mut c = SgrMouseClamper::new();
        assert_eq!(c.clamp_1_based(0, 999, 80, 24), (1, 24));
    }
}
