// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Target-triple toolchain router parsing `aterm pkg which targo` output so hosts where Trust
//! reports `unavailable on <target>` fall back cleanly to stock `cargo`
//! (`Astream.AtpkgTc.TlaTargetAvailabilityGate`).

#[cfg(clean_islands)]
#[path = "target_availability_gate_island.rs"]
mod target_availability_gate_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tc_tgt_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tc_route_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use target_availability_gate_island::{tc_route_advance, tc_tgt_clamp};

/// Availability score (`1 = Trust build available`, `0 = fallback to stock cargo`).
pub const TRUST_AVAILABLE_SCORE: u64 = 1;

contract_fn! {
    /// Verified Trust availability check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `tc_has_trust_build_isl`.
    #[must_use]
    pub const fn tc_has_trust_build(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SelectedToolchain {
    TrustTargo,
    StockCargo,
}

#[derive(Debug, Clone, Default)]
pub struct TargetToolchainRouter {
    queries: u64,
}

fn contains_bytes(haystack: &[u8], needle: &[u8]) -> bool {
    if needle.is_empty() {
        return true;
    }
    let mut idx = 0usize;
    while idx.saturating_add(needle.len()) <= haystack.len() {
        if haystack.get(idx..idx.saturating_add(needle.len())) == Some(needle) {
            return true;
        }
        idx = idx.saturating_add(1);
    }
    false
}

impl TargetToolchainRouter {
    #[must_use]
    pub const fn new() -> Self {
        Self { queries: 0 }
    }

    pub fn select(&mut self, atpkg_bin_set: bool, pkg_which_output: &str) -> SelectedToolchain {
        let unavailable = contains_bytes(pkg_which_output.as_bytes(), b"unavailable on ");
        let raw = if atpkg_bin_set && !unavailable && !pkg_which_output.trim().is_empty() {
            1u64
        } else {
            0u64
        };
        let score = tc_tgt_clamp(raw, TRUST_AVAILABLE_SCORE);
        self.queries = tc_route_advance(self.queries, self.queries.saturating_add(1));
        if tc_has_trust_build(score, TRUST_AVAILABLE_SCORE) {
            SelectedToolchain::TrustTargo
        } else {
            SelectedToolchain::StockCargo
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn selects_trust_when_available_and_stock_cargo_when_unavailable_on_target() {
        let mut r = TargetToolchainRouter::new();
        assert_eq!(
            r.select(true, "/fixture-home/.atpkg/bin/targo"),
            SelectedToolchain::TrustTargo
        );
        assert_eq!(
            r.select(true, "unavailable on riscv64gc-unknown-linux-gnu"),
            SelectedToolchain::StockCargo
        );
    }
}
