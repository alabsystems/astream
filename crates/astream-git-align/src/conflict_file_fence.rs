// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pre-rebase touched-path disjointness checker predicting clean vs conflicting rebases before
//! mutating a live working tree (`Astream.GitAlign.TlaConflictFileFence`).

use std::collections::BTreeSet;

#[cfg(clean_islands)]
#[path = "conflict_file_fence_island.rs"]
mod conflict_file_fence_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn git_paths_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn git_check_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use conflict_file_fence_island::{git_check_advance, git_paths_clamp};

/// Maximum changed paths compared per pre-rebase dry check.
pub const MAX_COMPARED_PATHS: u64 = 4_096;

contract_fn! {
    /// Verified zero-overlap check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `git_paths_disjoint_isl`.
    #[must_use]
    pub const fn git_paths_disjoint(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Checks whether local commits and upstream commits touch disjoint file sets.
#[derive(Debug, Clone, Default)]
pub struct PreRebasePathFence {
    checks: u64,
}

impl PreRebasePathFence {
    #[must_use]
    pub const fn new() -> Self {
        Self { checks: 0 }
    }

    pub fn overlapping_paths<'a>(
        &mut self,
        local_paths: &[&'a str],
        remote_paths: &[&'a str],
    ) -> (bool, Vec<&'a str>) {
        let cap = git_paths_clamp(MAX_COMPARED_PATHS, MAX_COMPARED_PATHS) as usize;
        self.checks = git_check_advance(self.checks, self.checks.saturating_add(1));
        let mut remote_set: BTreeSet<&str> = BTreeSet::new();
        let mut r_idx = 0usize;
        while r_idx < remote_paths.len() && r_idx < cap {
            if let Some(&rp) = remote_paths.get(r_idx) {
                remote_set.insert(rp);
            }
            r_idx = r_idx.saturating_add(1);
        }
        let mut overlaps = Vec::new();
        let mut l_idx = 0usize;
        while l_idx < local_paths.len() && l_idx < cap {
            if let Some(&lp) = local_paths.get(l_idx) {
                if remote_set.contains(lp) {
                    overlaps.push(lp);
                }
            }
            l_idx = l_idx.saturating_add(1);
        }
        let disjoint = git_paths_disjoint(0, overlaps.len() as u64);
        (disjoint, overlaps)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn path_fence_proves_disjoint_rebase_safety_and_pinpoints_overlapping_files() {
        let mut f = PreRebasePathFence::new();
        assert_eq!(
            f.overlapping_paths(&["crates/astream-vt-ext/src/lib.rs"], &["README.md"]),
            (true, vec![])
        );
        assert_eq!(
            f.overlapping_paths(&["Cargo.toml", "src/a.rs"], &["Cargo.toml"]),
            (false, vec!["Cargo.toml"])
        );
    }
}
