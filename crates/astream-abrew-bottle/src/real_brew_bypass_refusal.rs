// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `atpkg-abrew` strict bypass refusal gate (`aterm` primer: *"`brew --real`, `brew --no-reroute`
//! and `ABREW_REAL` refuse rather than bypass it; it never installs, bundles or invokes real
//! Homebrew"* — `Astream.Abrew.TlaRealBrewBypassRefusal`).

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
#[path = "real_brew_bypass_refusal_island.rs"]
mod real_brew_bypass_refusal_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ab_flag_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ab_ref_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use real_brew_bypass_refusal_island::{ab_flag_clamp, ab_ref_advance};

/// Maximum bypass flags counted per invocation (`16`).
pub const MAX_BYPASS_FLAGS: u64 = 16;

contract_fn! {
    /// Verified zero-bypass check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ab_no_bypass_isl`.
    #[must_use]
    pub const fn ab_no_bypass(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct AbrewBypassGate {
    refusals: u64,
}

impl AbrewBypassGate {
    #[must_use]
    pub const fn new() -> Self {
        Self { refusals: 0 }
    }

    pub fn allow_invocation(&mut self, args: &[&str], abrew_real_env_set: bool) -> bool {
        let mut violations = if abrew_real_env_set { 1u64 } else { 0u64 };
        for &arg in args {
            if arg == "--real"
                || arg.starts_with("--real=")
                || arg == "--no-reroute"
                || arg.starts_with("--no-reroute=")
            {
                violations = violations.saturating_add(1);
            }
        }
        let clamped = ab_flag_clamp(violations, MAX_BYPASS_FLAGS);
        if ab_no_bypass(0, clamped) {
            true
        } else {
            self.refusals = ab_ref_advance(self.refusals, self.refusals.saturating_add(1));
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_real_and_no_reroute_flags_and_abrew_real_env() {
        let mut g = AbrewBypassGate::new();
        assert!(g.allow_invocation(&["install", "ripgrep"], false));
        assert!(!g.allow_invocation(&["--real", "install", "jq"], false));
        assert!(!g.allow_invocation(&["--no-reroute", "info"], false));
        assert!(!g.allow_invocation(&["install", "fd"], true));
    }
}
