// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Speculative space-keystroke traversal confirmation & silent-prompt abstention judge
//! (`evidence/manifest.toml` `term.echo.predict-and-reconcile`;
//! `Astream.Term.TlaPredictedSpaceTraversalConfirm`).
//!
//! Prevents false `Confirmed` verdicts on dropped space keystrokes:
//! - Because an unpainted blank cell already looks like `' '`, a predicted space at `space_col`
//!   must NEVER be confirmed merely because `grid[row][space_col] == ' '`!
//! - It transitions to `Confirmed` ONLY once authoritative output proves the cell was traversed
//!   (`cursor_col > space_col` on the same row OR a non-blank glyph was painted at `col > space_col`
//!   while `grid[row][space_col]` remained blank/space), and transitions to `Contradicted` as soon
//!   as `grid[row][space_col]` is painted with any non-space glyph!

#[cfg(clean_islands)]
#[path = "predicted_space_traversal_confirm_island.rs"]
mod predicted_space_traversal_confirm_island;
#[cfg(clean_islands)]
pub use predicted_space_traversal_confirm_island::{
    space_col_clamp_b143, traversed_rightmost_advance_b143,
};

#[cfg(not(clean_islands))]
/// Clamp predicted space column to `row_cols`.
#[must_use]
pub const fn space_col_clamp_b143(cand_col: u64, row_cols: u64) -> u64 {
    if cand_col < row_cols {
        cand_col
    } else {
        row_cols
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the rightmost authoritative column traversed on the prediction's row.
#[must_use]
pub const fn traversed_rightmost_advance_b143(cur_rightmost: u64, cand_col: u64) -> u64 {
    if cur_rightmost < cand_col {
        cand_col
    } else {
        cur_rightmost
    }
}

contract_fn! {
    /// True iff the cell at `space_col` is still blank/space AND authoritative output traversed
    /// strictly past `space_col` (`cursor_passed_right || glyph_painted_right`).
    #[must_use]
    pub const fn predicted_space_traversed_b143(
        cell_blank_or_space: bool,
        cursor_passed_right: bool,
        glyph_painted_right: bool,
    ) -> bool
    clauses [ensures result == (cell_blank_or_space && (cursor_passed_right || glyph_painted_right))]
    {
        cell_blank_or_space && (cursor_passed_right || glyph_painted_right)
    }
}

/// Reconciliation verdict for a predicted `' '` cell.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpacePredictionVerdict {
    AbstainedSilentPrompt,
    PendingUntraversed,
    ConfirmedTraversed,
    ContradictedOverwritten,
}

/// Tracker for a single speculative `' '` cell at `(row, space_col)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PredictedSpaceJudge {
    space_col: u64,
    row_cols: u64,
    rightmost_traversed_col: u64,
}

impl PredictedSpaceJudge {
    #[must_use]
    pub const fn new(raw_space_col: u64, row_cols: u64) -> Self {
        let col = space_col_clamp_b143(raw_space_col, row_cols);
        Self {
            space_col: col,
            row_cols,
            rightmost_traversed_col: col,
        }
    }

    pub fn reconcile_row_observation(
        &mut self,
        silent_password_prompt: bool,
        cell_blank_or_space: bool,
        auth_cursor_on_same_row: bool,
        auth_cursor_col: u64,
        rightmost_nonblank_col_on_row: Option<u64>,
    ) -> SpacePredictionVerdict {
        if silent_password_prompt {
            return SpacePredictionVerdict::AbstainedSilentPrompt;
        }
        if !cell_blank_or_space {
            return SpacePredictionVerdict::ContradictedOverwritten;
        }
        if auth_cursor_on_same_row {
            self.rightmost_traversed_col = traversed_rightmost_advance_b143(
                self.rightmost_traversed_col,
                space_col_clamp_b143(auth_cursor_col, self.row_cols),
            );
        }
        let glyph_right = match rightmost_nonblank_col_on_row {
            Some(c) => {
                self.rightmost_traversed_col = traversed_rightmost_advance_b143(
                    self.rightmost_traversed_col,
                    space_col_clamp_b143(c, self.row_cols),
                );
                c > self.space_col
            }
            None => false,
        };
        let cursor_right = self.rightmost_traversed_col > self.space_col;
        if predicted_space_traversed_b143(cell_blank_or_space, cursor_right, glyph_right) {
            SpacePredictionVerdict::ConfirmedTraversed
        } else {
            SpacePredictionVerdict::PendingUntraversed
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dropped_space_stays_pending_until_cursor_or_glyph_traverses_past_column() {
        let mut j = PredictedSpaceJudge::new(4, 80);
        // Blank cell at col 4 with cursor still at col 4 -> NOT confirmed!
        assert_eq!(
            j.reconcile_row_observation(false, true, true, 4, None),
            SpacePredictionVerdict::PendingUntraversed
        );
        // Authoritative cursor advances to col 5 while col 4 stays space -> Confirmed!
        assert_eq!(
            j.reconcile_row_observation(false, true, true, 5, None),
            SpacePredictionVerdict::ConfirmedTraversed
        );
        // Non-space glyph painted at col 4 -> Contradicted!
        assert_eq!(
            j.reconcile_row_observation(false, false, true, 5, Some(4)),
            SpacePredictionVerdict::ContradictedOverwritten
        );
    }
}
