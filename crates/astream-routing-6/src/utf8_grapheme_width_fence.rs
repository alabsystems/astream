// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Multi-scalar ZWJ / VS16 grapheme cluster column-wrap fence
//! (`Astream.Term.TlaUtf8GraphemeWidthFence`).
//!
//! Complements single-scalar `char_display_width` without modifying its behavior:
//! evaluates multi-scalar ZWJ (`U+200D`), Variation Selector-16 (`U+FE0F` -> width 2),
//! and Variation Selector-15 (`U+FE0E` -> width 1) sequences and guarantees that a
//! width-2 cluster at `col == grid_cols - 1` wraps cleanly to column `0` of the
//! next row rather than overflowing `grid_cols`.

#[cfg(clean_islands)]
#[path = "utf8_grapheme_width_fence_island.rs"]
mod utf8_grapheme_width_fence_island;
#[cfg(clean_islands)]
pub use utf8_grapheme_width_fence_island::{grapheme_col_clamp, grapheme_seq_advance};

#[cfg(not(clean_islands))]
/// Monotonically advance the placed grapheme-cluster sequence counter.
#[must_use]
pub const fn grapheme_seq_advance(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}

#[cfg(not(clean_islands))]
/// Clamp cursor column position within `0..=grid_cols`.
#[must_use]
pub const fn grapheme_col_clamp(cand_col: u64, grid_cols: u64) -> u64 {
    if cand_col < grid_cols {
        cand_col
    } else {
        grid_cols
    }
}

contract_fn! {
    /// True iff `next_col <= grid_cols` (the cluster fits on the current row without wrapping).
    #[must_use]
    pub const fn grapheme_fits_row(next_col: u64, grid_cols: u64) -> bool
    clauses [ensures result == (next_col <= grid_cols)]
    {
        next_col <= grid_cols
    }
}

/// Evaluate the cell width (`0`, `1`, or `2`) of a single grapheme cluster's scalar sequence
/// given the base scalar's width (`base_width` in `0..=2`).
#[must_use]
pub fn cluster_cell_width(base_width: u8, scalars: &[u32]) -> u8 {
    if scalars.is_empty() {
        return 0;
    }
    let mut width = if base_width <= 2 { base_width } else { 2 };
    let mut saw_zwj = false;
    let mut rest = scalars;
    while let &[cp, ref tail @ ..] = rest {
        if cp == 0xFE0F && width > 0 {
            // Emoji presentation selector upgrades 1-column symbol to 2 columns
            width = 2;
        } else if cp == 0xFE0E && !saw_zwj && width > 1 {
            // Text presentation selector downgrades non-ZWJ symbol to 1 column
            width = 1;
        } else if cp == 0x200D {
            saw_zwj = true;
            if width == 1 {
                width = 2;
            }
        }
        rest = tail;
    }
    width
}

/// Placement outcome for a grapheme cluster on a row of `grid_cols` columns.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClusterPlacement {
    pub wrapped_to_next_row: bool,
    pub start_col: u64,
    pub next_cursor_col: u64,
    pub cell_width: u8,
}

/// Pure stack row-cursor fence for multi-scalar grapheme clusters.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Utf8GraphemeWidthFence {
    grid_cols: u64,
    cursor_col: u64,
    cluster_seq: u64,
}

impl Utf8GraphemeWidthFence {
    #[must_use]
    pub const fn new(grid_cols: u64) -> Self {
        let cols = if grid_cols < 2 { 2 } else { grid_cols };
        Self {
            grid_cols: cols,
            cursor_col: 0,
            cluster_seq: 0,
        }
    }

    #[must_use]
    pub const fn cursor_col(&self) -> u64 {
        self.cursor_col
    }

    #[must_use]
    pub const fn cluster_seq(&self) -> u64 {
        self.cluster_seq
    }

    pub fn carriage_return(&mut self) {
        self.cursor_col = 0;
    }

    /// Place a grapheme cluster with `base_width` and `scalars`, auto-wrapping if needed.
    pub fn place_cluster(&mut self, base_width: u8, scalars: &[u32]) -> ClusterPlacement {
        let cand_seq = self.cluster_seq.saturating_add(1);
        self.cluster_seq = grapheme_seq_advance(self.cluster_seq, cand_seq);

        let w = cluster_cell_width(base_width, scalars);
        if w == 0 {
            return ClusterPlacement {
                wrapped_to_next_row: false,
                start_col: self.cursor_col,
                next_cursor_col: self.cursor_col,
                cell_width: 0,
            };
        }

        let w64 = w as u64;
        let proposed_end = self.cursor_col.saturating_add(w64);
        if grapheme_fits_row(proposed_end, self.grid_cols) {
            let start = self.cursor_col;
            self.cursor_col = grapheme_col_clamp(proposed_end, self.grid_cols);
            ClusterPlacement {
                wrapped_to_next_row: false,
                start_col: start,
                next_cursor_col: self.cursor_col,
                cell_width: w,
            }
        } else {
            // Wrap to col 0 of the next row!
            self.cursor_col = grapheme_col_clamp(w64, self.grid_cols);
            ClusterPlacement {
                wrapped_to_next_row: true,
                start_col: 0,
                next_cursor_col: self.cursor_col,
                cell_width: w,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn upgrades_vs16_and_zwj_to_width_two_and_wraps_cleanly_at_right_margin() {
        let mut fence = Utf8GraphemeWidthFence::new(5);
        // Place 4 ASCII columns (0..4)
        for _ in 0..4 {
            let p = fence.place_cluster(1, &[b'a' as u32]);
            assert!(!p.wrapped_to_next_row);
        }
        assert_eq!(fence.cursor_col(), 4);

        // Warning sign U+26A0 (base width 1) + VS16 (U+FE0F) -> width 2; at col 4 of 5-col grid -> wraps to col 0..2!
        let p_emoji = fence.place_cluster(1, &[0x26A0, 0xFE0F]);
        assert_eq!(
            p_emoji,
            ClusterPlacement {
                wrapped_to_next_row: true,
                start_col: 0,
                next_cursor_col: 2,
                cell_width: 2,
            }
        );
    }
}
