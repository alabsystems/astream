// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Canonical edge-wrap vs DECSLRM right-margin pending-wrap arbiter
//! (`Astream.Term.TlaMarginWrapArbiter`).
//!
//! Preserves `Screen::serialize()` injectivity (`s1 == s2 <=> s1.serialize() == s2.serialize()`)
//! across `DECAWM` and `DECLRMM` (`?69` / `DECSLRM`) pending-wrap states:
//! - A wrap pending on the screen's rightmost column (`last_col = cols - 1`) is ALWAYS
//!   encoded as `(cursor_col = cols, margin_wrap = false)`.
//! - A wrap pending short of the screen's rightmost column (at a `DECSLRM` right margin
//!   `col < cols - 1`, or restored via `DECRC`) is ALWAYS encoded as
//!   `(cursor_col = col, margin_wrap = true)`.
//! - Consequently, no visual wrap state ever has two distinct struct encodings!

#[cfg(clean_islands)]
#[path = "margin_wrap_arbiter_island.rs"]
mod margin_wrap_arbiter_island;
#[cfg(clean_islands)]
pub use margin_wrap_arbiter_island::{wrap_col_clamp, wrap_margin_flag};

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn wrap_col_clamp(col: u64, screen_cols: u64) -> u64 {
    if col < screen_cols {
        col
    } else {
        screen_cols
    }
}

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn wrap_margin_flag(col: u64, last_col: u64) -> u64 {
    if col < last_col {
        1
    } else {
        0
    }
}

contract_fn! {
    /// Verified check that a pending wrap sits at the screen edge
    /// (`screen_cols <= cursor_col`), linked via `clean-kernel-defeq` to
    /// `wrap_at_edge_isl`.
    #[must_use]
    pub const fn wrap_at_edge(
        cursor_col: u64,
        screen_cols: u64,
    ) -> bool
    clauses [ensures result == (screen_cols <= cursor_col)]
    {
        screen_cols <= cursor_col
    }
}

/// Canonical `(col, margin_wrap)` cursor-wrap state on a terminal grid of width `cols`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CanonicalCursorWrap {
    /// Stored cursor column (`0..=cols`; equals `cols` iff an edge wrap is pending).
    pub cursor_col: u16,
    /// `true` iff a wrap is pending on `cursor_col < cols - 1`.
    pub margin_wrap: bool,
    /// Viewport width in columns (`>= 1`).
    pub screen_cols: u16,
}

impl CanonicalCursorWrap {
    /// Construct a non-wrapped cursor at column `0` on a viewport of width `cols` (`>= 1`).
    #[must_use]
    pub const fn new(cols: u16) -> Self {
        let c = if cols < 1 { 1 } else { cols };
        Self {
            cursor_col: 0,
            margin_wrap: false,
            screen_cols: c,
        }
    }

    /// Whether a wrap is pending (either edge wrap `cursor_col == screen_cols` or `margin_wrap`).
    #[must_use]
    pub const fn is_wrap_pending(&self) -> bool {
        wrap_at_edge(self.cursor_col as u64, self.screen_cols as u64) || self.margin_wrap
    }

    /// Physical grid column (`0..screen_cols`) currently occupied by the cursor.
    #[must_use]
    pub const fn grid_col(&self) -> u16 {
        let last = self.screen_cols.saturating_sub(1);
        if self.cursor_col < last {
            self.cursor_col
        } else {
            last
        }
    }

    /// Latch a canonical pending wrap at `col`:
    /// - if `col >= screen_cols - 1`, parks at `(screen_cols, false)` (edge wrap);
    /// - if `col < screen_cols - 1`, parks at `(col, true)` (interior margin wrap).
    pub fn set_wrap_at(&mut self, col: u16) {
        let cols64 = self.screen_cols as u64;
        let last64 = self.screen_cols.saturating_sub(1) as u64;
        let col64 = col as u64;
        let flag = wrap_margin_flag(col64, last64);
        if flag == 1 {
            self.cursor_col = wrap_col_clamp(col64, cols64) as u16;
            self.margin_wrap = true;
        } else {
            self.cursor_col = wrap_col_clamp(cols64, cols64) as u16;
            self.margin_wrap = false;
        }
    }

    /// Clear any pending wrap, clamping `cursor_col` back into `0..screen_cols`.
    pub const fn clear_wrap(&mut self) {
        self.cursor_col = self.grid_col();
        self.margin_wrap = false;
    }

    /// Re-canonicalize across a viewport width resize to `new_cols` (`>= 1`), matching
    /// xterm/`astream-term` resize semantics.
    pub fn resize_cols(&mut self, new_cols: u16) {
        let cols = if new_cols < 1 { 1 } else { new_cols };
        let old_edge_wrap = self.cursor_col >= self.screen_cols;
        self.screen_cols = cols;
        if self.margin_wrap {
            let target = if self.cursor_col < cols.saturating_sub(1) {
                self.cursor_col
            } else {
                cols.saturating_sub(1)
            };
            self.margin_wrap = false;
            self.set_wrap_at(target);
        } else if old_edge_wrap {
            self.cursor_col = wrap_col_clamp(self.cursor_col as u64, cols as u64) as u16;
        } else {
            let max_cell = cols.saturating_sub(1);
            if self.cursor_col > max_cell {
                self.cursor_col = max_cell;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonicalizes_edge_wrap_and_margin_wrap_uniquely_across_set_clear_and_resize() {
        let mut w = CanonicalCursorWrap::new(80);
        assert!(!w.is_wrap_pending());

        // Wrap at DECSLRM right margin col 39 -> `(39, true)`!
        w.set_wrap_at(39);
        assert_eq!((w.cursor_col, w.margin_wrap, w.grid_col()), (39, true, 39));
        assert!(w.is_wrap_pending());

        // Narrow screen from 80 -> 40 cols: col 39 IS now `last_col`, so it canonicalizes to `(40, false)`!
        w.resize_cols(40);
        assert_eq!((w.cursor_col, w.margin_wrap, w.grid_col()), (40, false, 39));
        assert!(w.is_wrap_pending());

        // Clear wrap -> `(39, false)`.
        w.clear_wrap();
        assert_eq!((w.cursor_col, w.margin_wrap), (39, false));
        assert!(!w.is_wrap_pending());
    }
}
