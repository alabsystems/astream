// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Twelve-row `scripts/stock-check.sh` 5-target cross-cell tracker (`host`, `x86_64-linux`,
//! `aarch64-linux`, `x86_64-darwin`, `x86_64-windows` across default & `--all-features`) requiring
//! `12 / 12` rows green (`Astream.CrossCell.TlaFiveCellMatrix`).

#[cfg(clean_islands)]
#[path = "five_cell_matrix_island.rs"]
mod five_cell_matrix_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cc_row_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cc_pass_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use five_cell_matrix_island::{cc_pass_advance, cc_row_clamp};

/// Exact number of `stock-check.sh` compile rows (`12`).
pub const REQUIRED_STOCK_ROWS: u64 = 12;

contract_fn! {
    /// Verified full-matrix completion (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `cc_all_rows_green_isl`.
    #[must_use]
    pub const fn cc_all_rows_green(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct StockCellMatrix {
    passed_rows: u64,
    failed_rows: u64,
}

impl StockCellMatrix {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            passed_rows: 0,
            failed_rows: 0,
        }
    }

    pub fn record_row(&mut self, ok: bool) {
        if ok {
            let next = cc_row_clamp(self.passed_rows.saturating_add(1), REQUIRED_STOCK_ROWS);
            self.passed_rows = cc_pass_advance(self.passed_rows, next);
        } else {
            self.failed_rows = self.failed_rows.saturating_add(1);
        }
    }

    #[must_use]
    pub const fn qualified(&self) -> bool {
        self.failed_rows == 0 && cc_all_rows_green(self.passed_rows, REQUIRED_STOCK_ROWS)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn qualifies_only_when_all_twelve_cross_rows_pass_with_zero_failures() {
        let mut m = StockCellMatrix::new();
        for _ in 0..11 {
            m.record_row(true);
        }
        assert!(!m.qualified());
        m.record_row(true);
        assert!(m.qualified());
    }
}
