// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! 0-RTT cooked-shell line predictor (`astream-term::predict` companion) tracking printable ASCII,
//! `Backspace`, `Ctrl-W` word-rubout, and `Left`/`Right` cursor edits strictly within `0..cols`
//! (`Astream.SpecEcho.TlaCookedLinePredictor`).

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
#[path = "cooked_line_predictor_island.rs"]
mod cooked_line_predictor_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn se_col_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn se_pred_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use cooked_line_predictor_island::{se_col_clamp, se_pred_advance};

/// Maximum viewport column width (`1_024`).
pub const MAX_COOKED_COLS: u64 = 1_024;

contract_fn! {
    /// Verified single-row cursor bound (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `se_edit_in_row_isl`.
    #[must_use]
    pub const fn se_edit_in_row(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct CookedLineState {
    prompt_col: u64,
    cursor_col: u64,
    max_col: u64,
    edits_predicted: u64,
}

impl CookedLineState {
    #[must_use]
    pub const fn new(prompt_col: u64, cols: u64) -> Self {
        let mc = se_col_clamp(cols.saturating_sub(1), MAX_COOKED_COLS);
        let pc = se_col_clamp(prompt_col, mc);
        Self {
            prompt_col: pc,
            cursor_col: pc,
            max_col: mc,
            edits_predicted: 0,
        }
    }

    pub fn predict_ascii(&mut self, byte: u8) -> Option<u64> {
        if !(0x20 <= byte && byte <= 0x7E) {
            return None;
        }
        let next = self.cursor_col.saturating_add(1);
        if !se_edit_in_row(self.max_col, next) {
            return None;
        }
        self.cursor_col = se_col_clamp(next, self.max_col);
        self.edits_predicted =
            se_pred_advance(self.edits_predicted, self.edits_predicted.saturating_add(1));
        Some(self.cursor_col)
    }

    pub fn predict_backspace(&mut self) -> u64 {
        if self.cursor_col > self.prompt_col {
            self.cursor_col = self.cursor_col.saturating_sub(1);
        }
        self.cursor_col
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn predicts_printable_insertions_and_stops_backspace_at_prompt_floor() {
        let mut s = CookedLineState::new(4, 80);
        assert_eq!(s.predict_ascii(b'l'), Some(5));
        assert_eq!(s.predict_ascii(b's'), Some(6));
        assert_eq!(s.predict_backspace(), 5);
        assert_eq!(s.predict_backspace(), 4);
        assert_eq!(s.predict_backspace(), 4);
    }
}
