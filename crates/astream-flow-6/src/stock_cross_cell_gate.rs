// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `scripts/stock-check.sh` 12-row cross-cell stock-compiler verdict aggregator
//! (`Astream.Evidence.TlaStockCrossCellGate`, Island #280).

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
#[path = "stock_cross_cell_gate_island.rs"]
mod stock_cross_cell_gate_island;
#[cfg(clean_islands)]
pub use stock_cross_cell_gate_island::{stock_cell_count_clamp, stock_exit_code_escalate};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn stock_exit_code_escalate(cur_code: u64, row_code: u64) -> u64 {
    if cur_code < row_code {
        row_code
    } else {
        cur_code
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn stock_cell_count_clamp(cells: u64, max_cells: u64) -> u64 {
    if cells < max_cells {
        cells
    } else {
        max_cells
    }
}

/// Exit code `0`: every cross-cell row compiled warning-free under stock `rustc`.
pub const EXIT_STOCK_PASS: u64 = 0;
/// Exit code `1`: at least one row had a compile error, warning, or `--locked` failure.
pub const EXIT_STOCK_REFUSED: u64 = 1;
/// Exit code `2`: preflight or cargo stopped before checking (e.g. `trust:` line in `-vV`).
pub const EXIT_STOCK_COULD_NOT_RUN: u64 = 2;

/// Expected number of cross-compilation check rows in `scripts/stock-check.sh` (`12`).
pub const EXPECTED_STOCK_CELL_ROWS: u64 = 12;

/// Hard cap on tracked cross-cell rows (`32`).
pub const MAX_STOCK_CELL_ROWS: u64 = 32;

contract_fn! {
    /// Verified check `cells_checked == expected_cells`, linked via `clean-kernel-defeq` to
    /// `stock_cells_all_checked_isl`.
    #[must_use]
    pub const fn stock_cells_all_checked(cells_checked: u64, expected_cells: u64) -> bool
    clauses [ensures result == (cells_checked == expected_cells)]
    {
        cells_checked == expected_cells
    }
}

/// Check `exit_code == 0 && cells_checked == expected_cells`.
#[inline]
#[must_use]
pub const fn stock_verdict_is_pass(
    exit_code: u64,
    cells_checked: u64,
    expected_cells: u64,
) -> bool {
    exit_code == 0 && stock_cells_all_checked(cells_checked, expected_cells)
}

const fn is_ascii_ws(b: u8) -> bool {
    matches!(b, b' ' | b'\t' | b'\r' | b'\n' | 0x0C)
}

const fn trim_ascii_ws(mut s: &[u8]) -> &[u8] {
    while let [head, rest @ ..] = s {
        if is_ascii_ws(*head) {
            s = rest;
        } else {
            break;
        }
    }
    while let [rest @ .., last] = s {
        if is_ascii_ws(*last) {
            s = rest;
        } else {
            break;
        }
    }
    s
}

const fn split_first_line(mut s: &[u8]) -> (&[u8], &[u8]) {
    let orig = s;
    let mut len = 0usize;
    while let [b, rest @ ..] = s {
        if *b == b'\n' {
            if len <= orig.len() {
                let (head, _) = orig.split_at(len);
                return (head, rest);
            }
            return (orig, &[]);
        }
        s = rest;
        len = len.saturating_add(1);
    }
    (orig, &[])
}

/// Inspect `rustc -vV` output and reject if any line starts with `trust:` (which would skip
/// the stock-compiler exception check by compiling `clean { ... }` islands).
#[allow(clippy::manual_unwrap_or)]
pub fn validate_stock_rustc_vv(vv_output: &str) -> Result<&str, &'static str> {
    let mut host_triple: Option<&[u8]> = None;
    let mut rem = vv_output.as_bytes();
    while !rem.is_empty() {
        let (raw_line, next_rem) = split_first_line(rem);
        rem = next_rem;
        let line = match raw_line.strip_suffix(b"\r") {
            Some(stripped) => stripped,
            None => raw_line,
        };
        if line.starts_with(b"trust:") {
            return Err("compiler is Trust (`trust:` line in -vV), not stock rustc");
        }
        if let Some(rest) = line.strip_prefix(b"host: ") {
            let trimmed = trim_ascii_ws(rest);
            if !trimmed.is_empty() {
                host_triple = Some(trimmed);
            }
        }
    }
    match host_triple {
        Some(h) => match core::str::from_utf8(h) {
            Ok(s) => Ok(s),
            Err(_) => Err("`rustc -vV` host triple is not valid UTF-8"),
        },
        None => Err("`rustc -vV` named no host triple"),
    }
}

/// Monotone cross-cell stock-check verdict accumulator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StockCrossCellGate {
    expected_cells: u64,
    cells_checked: u64,
    exit_code: u64,
}

impl Default for StockCrossCellGate {
    fn default() -> Self {
        Self::new(EXPECTED_STOCK_CELL_ROWS)
    }
}

impl StockCrossCellGate {
    #[must_use]
    pub const fn new(expected_cells: u64) -> Self {
        Self {
            expected_cells: stock_cell_count_clamp(expected_cells, MAX_STOCK_CELL_ROWS),
            cells_checked: 0,
            exit_code: EXIT_STOCK_PASS,
        }
    }

    #[must_use]
    pub const fn expected_cells(&self) -> u64 {
        self.expected_cells
    }

    #[must_use]
    pub const fn exit_code(&self) -> u64 {
        self.exit_code
    }

    #[must_use]
    pub const fn cells_checked(&self) -> u64 {
        self.cells_checked
    }

    /// Record a preflight failure (`COULD_NOT_RUN = 2`).
    pub fn record_could_not_run(&mut self) {
        self.exit_code = stock_exit_code_escalate(self.exit_code, EXIT_STOCK_COULD_NOT_RUN);
    }

    /// Record the result of one `cargo check` cell (`0 = ok`, `1 = compiler warning/error`, `2 = cargo stopped`).
    pub fn record_cell(&mut self, row_exit_code: u64) {
        let clamped_row = if row_exit_code >= EXIT_STOCK_COULD_NOT_RUN {
            EXIT_STOCK_COULD_NOT_RUN
        } else if row_exit_code == EXIT_STOCK_REFUSED {
            EXIT_STOCK_REFUSED
        } else {
            EXIT_STOCK_PASS
        };
        self.exit_code = stock_exit_code_escalate(self.exit_code, clamped_row);
        self.cells_checked =
            stock_cell_count_clamp(self.cells_checked.saturating_add(1), MAX_STOCK_CELL_ROWS);
    }

    /// Final shell exit code (`0` iff all expected cells ran and passed; `2` if incomplete).
    #[must_use]
    pub const fn finalize_exit_code(&self) -> u64 {
        if stock_verdict_is_pass(self.exit_code, self.cells_checked, self.expected_cells) {
            EXIT_STOCK_PASS
        } else if self.exit_code == EXIT_STOCK_PASS {
            EXIT_STOCK_COULD_NOT_RUN
        } else {
            self.exit_code
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trust_compiler_vv_is_rejected_and_could_not_run_dominates_refused_and_pass() {
        let trust_vv = "rustc 1.99.0-dev\nhost: aarch64-apple-darwin\ntrust: 20565c325\n";
        assert!(validate_stock_rustc_vv(trust_vv).is_err());

        let stock_vv = "rustc 1.86.0\nhost: aarch64-apple-darwin\nrelease: 1.86.0\n";
        assert_eq!(
            validate_stock_rustc_vv(stock_vv),
            Ok("aarch64-apple-darwin")
        );

        let mut g = StockCrossCellGate::new(3);
        assert_eq!(g.expected_cells(), 3);
        g.record_cell(EXIT_STOCK_PASS);
        assert_eq!(g.finalize_exit_code(), EXIT_STOCK_COULD_NOT_RUN);

        g.record_cell(EXIT_STOCK_PASS);
        g.record_cell(EXIT_STOCK_PASS);
        assert_eq!(g.finalize_exit_code(), EXIT_STOCK_PASS);

        g.record_cell(EXIT_STOCK_REFUSED);
        assert_eq!(g.exit_code(), EXIT_STOCK_REFUSED);
        g.record_cell(EXIT_STOCK_PASS);
        assert_eq!(g.exit_code(), EXIT_STOCK_REFUSED);
        g.record_could_not_run();
        assert_eq!(g.finalize_exit_code(), EXIT_STOCK_COULD_NOT_RUN);
    }
}
