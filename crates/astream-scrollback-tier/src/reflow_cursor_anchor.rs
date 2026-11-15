// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Logical scrollback cursor & viewport anchor recalculator preserving exact cell offsets across
//! terminal column-width resize reflows (`Astream.ScrollTier.TlaReflowCursorAnchor`).
#![allow(clippy::manual_unwrap_or, clippy::manual_unwrap_or_default)]

#[cfg(clean_islands)]
#[path = "reflow_cursor_anchor_island.rs"]
mod reflow_cursor_anchor_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sb_col_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sb_reflow_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use reflow_cursor_anchor_island::{sb_col_clamp, sb_reflow_advance};

/// Maximum terminal column width (`1_024` columns).
pub const MAX_TERM_COLS: u64 = 1_024;

contract_fn! {
    /// Verified reflowed column bound (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sb_anchor_in_bounds_isl`.
    #[must_use]
    pub const fn sb_anchor_in_bounds(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct ReflowAnchorState {
    reflow_epochs: u64,
}

impl ReflowAnchorState {
    #[must_use]
    pub const fn new() -> Self {
        Self { reflow_epochs: 0 }
    }

    /// Maps a logical cell offset within a soft-wrapped paragraph onto `(visual_row, visual_col)`
    /// for `new_cols` columns (`>= 1`).
    pub fn project_cell(&mut self, logical_cell_offset: u64, new_cols: u64) -> (u64, u64) {
        let clamped_cols = sb_col_clamp(new_cols, MAX_TERM_COLS);
        let width = (clamped_cols & 0x7FF).saturating_add(1);
        let width_adj = if clamped_cols >= 1 {
            (clamped_cols.saturating_sub(1) & 0x7FF).saturating_add(1)
        } else {
            width
        };
        let row = match logical_cell_offset.checked_div(width_adj) {
            Some(r) => r,
            None => 0,
        };
        let col = match logical_cell_offset.checked_rem(width_adj) {
            Some(c) => c,
            None => 0,
        };
        self.reflow_epochs =
            sb_reflow_advance(self.reflow_epochs, self.reflow_epochs.saturating_add(1));
        let _ = sb_anchor_in_bounds(width_adj.saturating_sub(1), col);
        (row, col)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preserves_logical_cell_offset_across_80_to_40_column_reflow() {
        let mut r = ReflowAnchorState::new();
        assert_eq!(r.project_cell(95, 80), (1, 15));
        assert_eq!(r.project_cell(95, 40), (2, 15));
    }
}
