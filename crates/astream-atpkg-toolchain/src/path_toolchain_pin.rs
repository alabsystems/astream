// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `Makefile` `toolchain` target invariant verifier confirming `PATH` resolves `rustc` to the exact
//! same binary digest/path as `rustup which --toolchain trust rustc` (`Astream.AtpkgTc.TlaPathToolchainPin`).

use astream_digest::{ct_eq, Sha256};

#[cfg(clean_islands)]
#[path = "path_toolchain_pin_island.rs"]
mod path_toolchain_pin_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tc_pin_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tc_chk_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use path_toolchain_pin_island::{tc_chk_advance, tc_pin_clamp};

/// Exact match score (`1`).
pub const PIN_MATCH_SCORE: u64 = 1;

contract_fn! {
    /// Verified PATH-pin equality check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `tc_path_matches_pin_isl`.
    #[must_use]
    pub const fn tc_path_matches_pin(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct PathToolchainPin {
    verifications: u64,
}

impl PathToolchainPin {
    #[must_use]
    pub const fn new() -> Self {
        Self { verifications: 0 }
    }

    pub fn verify_rustc_paths(&mut self, path_rustc: &[u8], trust_rustc: &[u8]) -> bool {
        let d_path = Sha256::digest_slice(path_rustc);
        let d_trust = Sha256::digest_slice(trust_rustc);
        let eq = !path_rustc.is_empty() && ct_eq(&d_path, &d_trust);
        let score = tc_pin_clamp(if eq { 1 } else { 0 }, PIN_MATCH_SCORE);
        self.verifications =
            tc_chk_advance(self.verifications, self.verifications.saturating_add(1));
        tc_path_matches_pin(score, PIN_MATCH_SCORE)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accepts_identical_resolved_rustc_paths_and_rejects_drift() {
        let mut pin = PathToolchainPin::new();
        assert!(pin.verify_rustc_paths(
            b"/fixture-home/.atpkg/toolchains/trust/bin/rustc",
            b"/fixture-home/.atpkg/toolchains/trust/bin/rustc"
        ));
        assert!(!pin.verify_rustc_paths(
            b"/opt/homebrew/bin/rustc",
            b"/fixture-home/.atpkg/toolchains/trust/bin/rustc"
        ));
    }
}
