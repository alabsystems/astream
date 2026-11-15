// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Fail-closed peer-identity allowlist reload tracker (`asb serve --allow-peer-file`) refusing
//! empty or malformed reloads while advancing monotonic allowlist epochs
//! (`Astream.ExtAuth.TlaAllowlistEpochReload`).

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
#[path = "allowlist_epoch_reload_island.rs"]
mod allowlist_epoch_reload_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ext_peers_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ext_reload_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use allowlist_epoch_reload_island::{ext_peers_clamp, ext_reload_advance};

/// Maximum pinned peers per allowlist reload (`4096`).
pub const MAX_ALLOWED_PEERS: u64 = 4096;

contract_fn! {
    /// Verified non-empty allowlist reload (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ext_allowlist_live_isl`.
    #[must_use]
    pub const fn ext_allowlist_live(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct AllowlistReloadGate {
    peer_hashes: Vec<u64>,
    epoch: u64,
}

impl AllowlistReloadGate {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            peer_hashes: Vec::new(),
            epoch: 0,
        }
    }

    pub fn reload(&mut self, candidate_hashes: &[u64], parse_clean: bool) -> bool {
        if !parse_clean || (candidate_hashes.len() as u64) > MAX_ALLOWED_PEERS {
            return false;
        }
        let n = ext_peers_clamp(candidate_hashes.len() as u64, MAX_ALLOWED_PEERS);
        if !ext_allowlist_live(n, 1) {
            return false;
        }
        let Some(next_epoch) = self.epoch.checked_add(1) else {
            return false;
        };
        self.peer_hashes.clear();
        self.peer_hashes.extend_from_slice(candidate_hashes);
        self.epoch = ext_reload_advance(self.epoch, next_epoch);
        true
    }

    #[must_use]
    pub fn contains(&self, peer_hash: u64) -> bool {
        let mut idx = 0usize;
        while idx < self.peer_hashes.len() {
            if let Some(&h) = self.peer_hashes.get(idx) {
                if h == peer_hash {
                    return true;
                }
            }
            idx = idx.saturating_add(1);
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preserves_prior_allowlist_on_malformed_or_empty_reload() {
        let mut g = AllowlistReloadGate::new();
        assert!(g.reload(&[0xAA11, 0xBB22], true));
        assert!(!g.reload(&[0xCC33], false));
        assert!(!g.reload(&[], true));
        assert!(g.contains(0xAA11));
        assert!(!g.contains(0xCC33));
    }
}
