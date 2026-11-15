// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Zero-warning release gate matching `aterm-verify`'s `cells.rs` (`is_cell_warning`), where any
//! single `rustc` warning on Linux, Linux-ARM, or x86_64 macOS blocks `ship release`
//! (`Astream.CrossCell.TlaZeroCellWarnings`).

#[cfg(clean_islands)]
#[path = "zero_cell_warnings_island.rs"]
mod zero_cell_warnings_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cc_warn_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cc_lint_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use zero_cell_warnings_island::{cc_lint_advance, cc_warn_clamp};

/// Maximum tracked warnings per cell run (`1_024`).
pub const MAX_CELL_WARNINGS: u64 = 1_024;

contract_fn! {
    /// Verified zero-warning ship check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `cc_ship_clean_isl`.
    #[must_use]
    pub const fn cc_ship_clean(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct CellWarningGate {
    warnings_seen: u64,
    runs_audited: u64,
}

impl CellWarningGate {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            warnings_seen: 0,
            runs_audited: 0,
        }
    }

    pub fn observe_cell_warnings(&mut self, count: u64) -> bool {
        self.warnings_seen =
            cc_warn_clamp(self.warnings_seen.saturating_add(count), MAX_CELL_WARNINGS);
        self.runs_audited = cc_lint_advance(self.runs_audited, self.runs_audited.saturating_add(1));
        cc_ship_clean(0, self.warnings_seen)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_dead_code_warning_in_cross_cell_refuses_ship_release() {
        let mut g = CellWarningGate::new();
        assert!(g.observe_cell_warnings(0));
        assert!(!g.observe_cell_warnings(1));
    }
}
