// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Rust compiler & verification lane resolver (`aterm help rust` / `aterm pkg which targo`:
//! `targo trust`, `targo --unverified`, or stock `cargo` when `unavailable on <target>`;
//! `Astream.Abrew.TlaTargetLaneProbe`).

#[cfg(clean_islands)]
#[path = "target_lane_probe_island.rs"]
mod target_lane_probe_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pkg_targets_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pkg_probe_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use target_lane_probe_island::{pkg_probe_advance, pkg_targets_clamp};

/// Maximum target triples cached by the lane resolver.
pub const MAX_CACHED_TRIPLES: u64 = 32;

contract_fn! {
    /// Verified Trust availability (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `pkg_trust_available_isl`.
    #[must_use]
    pub const fn pkg_trust_available(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResolvedRustDriver {
    TargoTrust,
    TargoUnverified,
    StockCargoFallback,
}

/// Resolves which Rust driver + explicit lane applies to the active directory and target.
#[derive(Debug, Clone, Default)]
pub struct RustLaneResolver {
    probes: u64,
}

impl RustLaneResolver {
    #[must_use]
    pub const fn new() -> Self {
        Self { probes: 0 }
    }

    pub fn resolve(
        &mut self,
        atpkg_bin_set: bool,
        which_targo_output: &str,
        verify_requested: bool,
    ) -> ResolvedRustDriver {
        let _ = pkg_targets_clamp(4, MAX_CACHED_TRIPLES);
        self.probes = pkg_probe_advance(self.probes, self.probes.saturating_add(1));
        let unavailable = !atpkg_bin_set
            || which_targo_output.trim().is_empty()
            || which_targo_output.contains("unavailable on ");
        let avail_flag = if unavailable { 0u64 } else { 1u64 };
        if !pkg_trust_available(avail_flag, 1) {
            return ResolvedRustDriver::StockCargoFallback;
        }
        if verify_requested {
            ResolvedRustDriver::TargoTrust
        } else {
            ResolvedRustDriver::TargoUnverified
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lane_resolver_selects_explicit_targo_lane_or_stock_cargo_when_unavailable() {
        let mut r = RustLaneResolver::new();
        assert_eq!(
            r.resolve(true, "/store/trust/bin/targo", false),
            ResolvedRustDriver::TargoUnverified
        );
        assert_eq!(
            r.resolve(true, "/store/trust/bin/targo", true),
            ResolvedRustDriver::TargoTrust
        );
        assert_eq!(
            r.resolve(true, "unavailable on x86_64-pc-windows-msvc", false),
            ResolvedRustDriver::StockCargoFallback
        );
    }
}
