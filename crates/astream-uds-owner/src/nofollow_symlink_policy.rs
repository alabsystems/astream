// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `Links::Refuse` (`O_NOFOLLOW`) vs `Links::Follow` policy evaluator preventing symlink-swap
//! attacks on private broker logs, capability files, and Unix-socket directories
//! (`Astream.UdsOwn.TlaNofollowSymlinkPolicy`).

#[cfg(clean_islands)]
#[path = "nofollow_symlink_policy_island.rs"]
mod nofollow_symlink_policy_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn uo_lnk_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn uo_sym_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use nofollow_symlink_policy_island::{uo_lnk_clamp, uo_sym_advance};

/// Policy clearance ceiling (`1`).
pub const SYMLINK_ALLOWED_SCORE: u64 = 1;

contract_fn! {
    /// Verified symlink policy clearance (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `uo_link_allowed_isl`.
    #[must_use]
    pub const fn uo_link_allowed(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LinksPolicy {
    Refuse,
    Follow,
}

#[derive(Debug, Clone, Default)]
pub struct SymlinkGuard {
    checks: u64,
}

impl SymlinkGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self { checks: 0 }
    }

    pub fn allow_target(&mut self, policy: LinksPolicy, target_is_symlink: bool) -> bool {
        let ok = !target_is_symlink || matches!(policy, LinksPolicy::Follow);
        let score = uo_lnk_clamp(if ok { 1 } else { 0 }, SYMLINK_ALLOWED_SCORE);
        self.checks = uo_sym_advance(self.checks, self.checks.saturating_add(1));
        uo_link_allowed(score, SYMLINK_ALLOWED_SCORE)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_symlink_under_refuse_policy_and_opens_under_follow() {
        let mut g = SymlinkGuard::new();
        assert!(!g.allow_target(LinksPolicy::Refuse, true));
        assert!(g.allow_target(LinksPolicy::Follow, true));
        assert!(g.allow_target(LinksPolicy::Refuse, false));
    }
}
