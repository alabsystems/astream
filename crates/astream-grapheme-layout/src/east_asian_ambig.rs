// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! UAX #11 East Asian Ambiguous (`A`) width policy & wide-glyph right-margin autowrap calculator
//! (`Astream.Grapheme.TlaEastAsianAmbig`).

#[cfg(clean_islands)]
#[path = "east_asian_ambig_island.rs"]
mod east_asian_ambig_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn gr_cols_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn gr_wrap_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use east_asian_ambig_island::{gr_cols_clamp, gr_wrap_advance};

/// Maximum viewport column count (`512`).
pub const MAX_TERMINAL_COLS: u64 = 512;

contract_fn! {
    /// Verified row-fit check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `gr_fits_row_isl`.
    #[must_use]
    pub const fn gr_fits_row(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Computes `(wrapped_to_next_row, new_cursor_col)` for `1`-col or `2`-col glyphs.
#[derive(Debug, Clone)]
pub struct AmbiguousWrapCursor {
    cols: u64,
    ambiguous_as_wide: bool,
    wraps: u64,
}

impl AmbiguousWrapCursor {
    #[must_use]
    pub const fn new(cols: u64, ambiguous_as_wide: bool) -> Self {
        let c = if cols < 2 { 2 } else { cols };
        Self {
            cols: gr_cols_clamp(c, MAX_TERMINAL_COLS),
            ambiguous_as_wide,
            wraps: 0,
        }
    }

    pub fn place_glyph(
        &mut self,
        cur_col: u64,
        is_ambiguous: bool,
        base_wide: bool,
    ) -> (bool, u64) {
        let w = if base_wide || (is_ambiguous && self.ambiguous_as_wide) {
            2u64
        } else {
            1u64
        };
        if gr_fits_row(self.cols, cur_col.saturating_add(w)) {
            (false, cur_col.saturating_add(w))
        } else {
            self.wraps = gr_wrap_advance(self.wraps, self.wraps.saturating_add(1));
            (true, w)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ambiguous_cursor_wraps_two_column_glyph_at_last_column_boundary() {
        let mut c = AmbiguousWrapCursor::new(80, true);
        assert_eq!(c.place_glyph(79, true, false), (true, 2));
        assert_eq!(c.place_glyph(78, true, false), (false, 80));
    }
}
