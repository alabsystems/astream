// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Windows cross-cell target filter (`scripts/stock-check.sh`: skipping only Unix-socket `asb` bin
//! and `astream-broker` `--lib` unit tests on `x86_64-pc-windows-msvc` while checking the broker
//! library, integration tests, examples, and every other crate; `Astream.CrossCell.TlaWinUnixTargetSkip`).

#[cfg(clean_islands)]
#[path = "win_unix_target_skip_island.rs"]
mod win_unix_target_skip_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cc_tgt_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cc_flt_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use win_unix_target_skip_island::{cc_flt_advance, cc_tgt_clamp};

/// Target inclusion score (`1 = must compile on Windows`, `0 = documented Unix-only skip`).
pub const WIN_MUST_CHECK: u64 = 1;

contract_fn! {
    /// Verified Windows-target inclusion (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `cc_target_checked_isl`.
    #[must_use]
    pub const fn cc_target_checked(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct WindowsCellTargetFilter {
    decisions: u64,
}

impl WindowsCellTargetFilter {
    #[must_use]
    pub const fn new() -> Self {
        Self { decisions: 0 }
    }

    pub fn should_compile_on_windows(&mut self, crate_name: &str, kind: &str) -> bool {
        let unix_only =
            crate_name == "astream-broker" && (kind == "bin:asb" || kind == "lib-unit-test");
        let score = cc_tgt_clamp(if unix_only { 0 } else { 1 }, WIN_MUST_CHECK);
        self.decisions = cc_flt_advance(self.decisions, self.decisions.saturating_add(1));
        cc_target_checked(score, WIN_MUST_CHECK)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn skips_only_asb_bin_and_broker_unit_tests_on_windows() {
        let mut f = WindowsCellTargetFilter::new();
        assert!(!f.should_compile_on_windows("astream-broker", "bin:asb"));
        assert!(!f.should_compile_on_windows("astream-broker", "lib-unit-test"));
        assert!(f.should_compile_on_windows("astream-broker", "lib"));
        assert!(f.should_compile_on_windows("astream-fabric", "lib-unit-test"));
    }
}
