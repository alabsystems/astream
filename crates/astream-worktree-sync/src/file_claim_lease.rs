// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Advisory path-prefix edit leases across concurrent `aterm` agent worktrees preventing
//! conflicting simultaneous edits to the same module (`Astream.Worktree.TlaFileClaimLease`).

use std::collections::BTreeMap;

#[cfg(clean_islands)]
#[path = "file_claim_lease_island.rs"]
mod file_claim_lease_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn claim_paths_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn claim_lease_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use file_claim_lease_island::{claim_lease_advance, claim_paths_clamp};

/// Maximum active path leases across peer agent tabs.
pub const MAX_ACTIVE_FILE_CLAIMS: u64 = 256;

contract_fn! {
    /// Verified lease-active check (`threshold <= observed`, i.e. `now_ms <= until_ms`),
    /// linked via `clean-kernel-defeq` to `claim_lease_active_isl`.
    #[must_use]
    pub const fn claim_lease_active(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FileClaimEntry {
    pub owner_sid: String,
    pub until_ms: u64,
}

fn copy_str(s: &str) -> String {
    let mut out = String::new();
    out.push_str(s);
    out
}

fn strip_trailing_slashes(mut s: &str) -> &str {
    while let Some(rest) = s.strip_suffix('/') {
        s = rest;
    }
    s
}

fn is_dir_prefix_or_equal(ancestor: &str, child: &str) -> bool {
    if ancestor == child {
        return true;
    }
    if let Some(rem) = child.strip_prefix(ancestor) {
        return rem.starts_with('/');
    }
    false
}

fn prefixes_overlap(a: &str, b: &str) -> bool {
    let a_norm = strip_trailing_slashes(a);
    let b_norm = strip_trailing_slashes(b);
    if a_norm.is_empty() || b_norm.is_empty() {
        return true;
    }
    is_dir_prefix_or_equal(a_norm, b_norm) || is_dir_prefix_or_equal(b_norm, a_norm)
}

/// Multi-agent advisory file-tree lease coordinator.
#[derive(Debug, Clone, Default)]
pub struct WorktreeClaimRegistry {
    epoch: u64,
    claims: BTreeMap<String, FileClaimEntry>,
}

impl WorktreeClaimRegistry {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            epoch: 0,
            claims: BTreeMap::new(),
        }
    }

    pub fn try_acquire(
        &mut self,
        path_prefix: &str,
        owner_sid: &str,
        now_ms: u64,
        ttl_ms: u64,
    ) -> Result<u64, String> {
        let norm_key = strip_trailing_slashes(path_prefix.trim());
        if norm_key.is_empty() || owner_sid.trim().is_empty() || ttl_ms == 0 {
            return Err(copy_str("invalid claim parameters"));
        }
        let mut kept = BTreeMap::new();
        for (existing_path, entry) in &self.claims {
            if claim_lease_active(entry.until_ms, now_ms.saturating_add(1)) {
                kept.insert(existing_path.clone(), entry.clone());
            }
        }
        for (existing_path, entry) in &kept {
            if entry.owner_sid.as_str() != owner_sid && prefixes_overlap(existing_path, norm_key) {
                return Err(entry.owner_sid.clone());
            }
        }
        let cap = claim_paths_clamp(MAX_ACTIVE_FILE_CLAIMS, MAX_ACTIVE_FILE_CLAIMS) as usize;
        if !kept.contains_key(norm_key) && kept.len() >= cap {
            return Err(copy_str("claim table full"));
        }
        let until_ms = now_ms.saturating_add(ttl_ms);
        kept.insert(
            copy_str(norm_key),
            FileClaimEntry {
                owner_sid: copy_str(owner_sid),
                until_ms,
            },
        );
        self.claims = kept;
        self.epoch = claim_lease_advance(self.epoch, self.epoch.saturating_add(1));
        Ok(until_ms)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn overlapping_crate_prefix_blocks_second_agent_until_lease_expires() {
        let mut r = WorktreeClaimRegistry::new();
        assert!(r
            .try_acquire("crates/astream-broker/", "@s-1", 1_000, 5_000)
            .is_ok());
        assert_eq!(
            r.try_acquire("crates/astream-broker/src/store.rs", "@s-2", 2_000, 5_000),
            Err("@s-1".to_owned())
        );
        assert!(r
            .try_acquire("crates/astream-wire/", "@s-2", 2_000, 5_000)
            .is_ok());
        assert!(r
            .try_acquire("crates/astream-broker/src/store.rs", "@s-2", 6_000, 5_000)
            .is_ok());
    }
}
