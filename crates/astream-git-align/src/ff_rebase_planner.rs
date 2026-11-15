// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bidirectional `git fetch origin && git rebase origin/main` divergence planner classifying
//! `(local_ahead, remote_ahead)` into `AlreadyAligned`, `FastForwardLocal`, `PushReady`, or
//! `RebaseRequired` (`Astream.GitAlign.TlaFfRebasePlanner`).

#[cfg(clean_islands)]
#[path = "ff_rebase_planner_island.rs"]
mod ff_rebase_planner_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn git_commits_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn git_fetch_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use ff_rebase_planner_island::{git_commits_clamp, git_fetch_advance};

/// Maximum ahead/behind commit window tracked per alignment cycle.
pub const MAX_DIVERGENCE_COMMITS: u64 = 10_000;

contract_fn! {
    /// Verified fast-forward push readiness (`threshold <= observed`, i.e., `remote_ahead == 0`),
    /// linked via `clean-kernel-defeq` to `git_can_push_ff_isl`.
    #[must_use]
    pub const fn git_can_push_ff(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GitAlignAction {
    AlreadyAligned,
    FastForwardLocal,
    PushReady,
    RebaseRequired,
}

/// Plans safe bidirectional alignment with `origin/main` before `git push`.
#[derive(Debug, Clone, Default)]
pub struct BidirectionalGitPlanner {
    fetches: u64,
}

impl BidirectionalGitPlanner {
    #[must_use]
    pub const fn new() -> Self {
        Self { fetches: 0 }
    }

    pub fn plan(&mut self, local_ahead: u64, remote_ahead: u64) -> GitAlignAction {
        let la = git_commits_clamp(local_ahead, MAX_DIVERGENCE_COMMITS);
        let ra = git_commits_clamp(remote_ahead, MAX_DIVERGENCE_COMMITS);
        self.fetches = git_fetch_advance(self.fetches, self.fetches.saturating_add(1));
        if git_can_push_ff(0, ra) {
            if la == 0 {
                GitAlignAction::AlreadyAligned
            } else {
                GitAlignAction::PushReady
            }
        } else if la == 0 {
            GitAlignAction::FastForwardLocal
        } else {
            GitAlignAction::RebaseRequired
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn planner_distinguishes_push_ready_fast_forward_and_diverged_rebase() {
        let mut p = BidirectionalGitPlanner::new();
        assert_eq!(p.plan(0, 0), GitAlignAction::AlreadyAligned);
        assert_eq!(p.plan(4, 0), GitAlignAction::PushReady);
        assert_eq!(p.plan(0, 2), GitAlignAction::FastForwardLocal);
        assert_eq!(p.plan(4, 2), GitAlignAction::RebaseRequired);
    }
}
