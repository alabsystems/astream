// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `abrew bundle` subcommand policy router (`aterm` primer: *"Bare `abrew bundle` installs a native
//! Brewfile; `bundle status`/`remove` only inspect or explicitly remove an owned legacy bundle"*)
//! refusing unowned legacy bundle mutations (`Astream.Abrew.TlaBrewfileBundleMode`).

#[cfg(clean_islands)]
#[path = "brewfile_bundle_mode_island.rs"]
mod brewfile_bundle_mode_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ab_op_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ab_bun_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use brewfile_bundle_mode_island::{ab_bun_advance, ab_op_clamp};

/// Highest bundle action code (`3`).
pub const MAX_BUNDLE_OP: u64 = 3;

contract_fn! {
    /// Verified bundle operation authorization (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `ab_bundle_op_safe_isl`.
    #[must_use]
    pub const fn ab_bundle_op_safe(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct BrewfileBundlePolicy {
    ops_checked: u64,
}

impl BrewfileBundlePolicy {
    #[must_use]
    pub const fn new() -> Self {
        Self { ops_checked: 0 }
    }

    pub fn allow_subcommand(&mut self, subcmd: Option<&str>, legacy_owned: bool) -> bool {
        let code = match subcmd {
            None => 3u64,           // Bare `abrew bundle` -> native Brewfile install
            Some("status") => 2u64, // Inspect legacy bundle
            Some("remove") if legacy_owned => 1u64, // Explicitly remove owned legacy bundle
            _ => 0u64,
        };
        let clamped = ab_op_clamp(code, MAX_BUNDLE_OP);
        self.ops_checked = ab_bun_advance(self.ops_checked, self.ops_checked.saturating_add(1));
        ab_bundle_op_safe(clamped, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn allows_bare_bundle_and_owned_remove_while_refusing_unowned_remove_or_dump() {
        let mut p = BrewfileBundlePolicy::new();
        assert!(p.allow_subcommand(None, false));
        assert!(p.allow_subcommand(Some("status"), false));
        assert!(p.allow_subcommand(Some("remove"), true));
        assert!(!p.allow_subcommand(Some("remove"), false));
        assert!(!p.allow_subcommand(Some("exec"), true));
    }
}
