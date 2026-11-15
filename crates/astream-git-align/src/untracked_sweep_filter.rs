// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Session-owned file staging filter (`autopilot=cruise` spoke 6: "landing what the session made
//! while leaving what it did not"; `Astream.GitAlign.TlaUntrackedSweepFilter`).

use std::collections::BTreeSet;

#[cfg(clean_islands)]
#[path = "untracked_sweep_filter_island.rs"]
mod untracked_sweep_filter_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn git_untracked_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn git_stage_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use untracked_sweep_filter_island::{git_stage_advance, git_untracked_clamp};

/// Maximum untracked/dirty paths classified per commit sweep.
pub const MAX_SWEEP_PATHS: u64 = 2_048;

contract_fn! {
    /// Verified zero-foreign-staging check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `git_owned_only_isl`.
    #[must_use]
    pub const fn git_owned_only(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Partition dirty/untracked paths into session-authored vs pre-existing/foreign paths.
#[derive(Debug, Clone, Default)]
pub struct SessionStagingFilter {
    authored: BTreeSet<String>,
    sweeps: u64,
}

impl SessionStagingFilter {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            authored: BTreeSet::new(),
            sweeps: 0,
        }
    }

    pub fn record_session_write(&mut self, rel_path: &str) {
        if rel_path.is_empty() {
            return;
        }
        let cap = git_untracked_clamp(MAX_SWEEP_PATHS, MAX_SWEEP_PATHS) as usize;
        if self.authored.len() < cap || self.authored.contains(rel_path) {
            let mut owned = String::new();
            owned.push_str(rel_path);
            self.authored.insert(owned);
        }
    }

    pub fn select_stageable<'a>(&mut self, git_status_paths: &[&'a str]) -> Vec<&'a str> {
        let lim = git_untracked_clamp(git_status_paths.len() as u64, MAX_SWEEP_PATHS) as usize;
        self.sweeps = git_stage_advance(self.sweeps, self.sweeps.saturating_add(1));
        let mut stage = Vec::new();
        let mut idx = 0usize;
        while idx < lim {
            if let Some(&p) = git_status_paths.get(idx) {
                if self.authored.contains(p) {
                    stage.push(p);
                }
            }
            idx = idx.saturating_add(1);
        }
        let mut foreign_staged = 0u64;
        let mut s_idx = 0usize;
        while s_idx < stage.len() {
            if let Some(&p) = stage.get(s_idx) {
                if !self.authored.contains(p) {
                    foreign_staged = foreign_staged.saturating_add(1);
                }
            }
            s_idx = s_idx.saturating_add(1);
        }
        let _ = git_owned_only(0, foreign_staged);
        stage
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn staging_filter_stages_only_session_authored_files_and_leaves_foreign_files_untouched() {
        let mut f = SessionStagingFilter::new();
        f.record_session_write("crates/astream-git-align/src/lib.rs");
        assert_eq!(
            f.select_stageable(&["notes.local.md", "crates/astream-git-align/src/lib.rs"]),
            vec!["crates/astream-git-align/src/lib.rs"]
        );
    }
}
