// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Stock-compiler identity check (`scripts/stock-check.sh`: refusing with exit `2` if `$RUSTC -vV`
//! contains a `trust:` line, which would compile `clean_islands` and make the stock check vacuous;
//! `Astream.CrossCell.TlaStockNotTrustGuard`).

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
#[path = "stock_not_trust_guard_island.rs"]
mod stock_not_trust_guard_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cc_tc_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cc_prb_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use stock_not_trust_guard_island::{cc_prb_advance, cc_tc_clamp};

/// Compiler probe score (`1 = genuine stock rustc`, `0 = Trust compiler or unreadable`).
pub const GENUINE_STOCK_SCORE: u64 = 1;

contract_fn! {
    /// Verified stock-compiler check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `cc_is_stock_rustc_isl`.
    #[must_use]
    pub const fn cc_is_stock_rustc(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct StockCompilerProbe {
    probes: u64,
}

impl StockCompilerProbe {
    #[must_use]
    pub const fn new() -> Self {
        Self { probes: 0 }
    }

    pub fn verify_vv_output(&mut self, vv_text: &str) -> bool {
        let mut has_host = false;
        let mut is_trust = false;
        for raw_line in vv_text.split('\n') {
            let line = raw_line.trim_end_matches('\r');
            if line.starts_with("host: ") && line.len() > 6 {
                has_host = true;
            }
            if line.starts_with("trust:") {
                is_trust = true;
            }
        }
        let score = cc_tc_clamp(
            if has_host && !is_trust { 1 } else { 0 },
            GENUINE_STOCK_SCORE,
        );
        self.probes = cc_prb_advance(self.probes, self.probes.saturating_add(1));
        cc_is_stock_rustc(score, GENUINE_STOCK_SCORE)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accepts_stable_rustc_and_refuses_trust_compiler_in_stock_lane() {
        let mut p = StockCompilerProbe::new();
        assert!(p.verify_vv_output("rustc 1.85.0\nhost: aarch64-apple-darwin\n"));
        assert!(
            !p.verify_vv_output("rustc 1.99.0-dev\nhost: aarch64-apple-darwin\ntrust: 0.11.0\n")
        );
    }
}
