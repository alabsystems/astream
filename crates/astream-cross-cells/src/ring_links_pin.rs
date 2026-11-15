// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `ring` `links` build-script override pin verifier (`RING_LINKS=ring_core_0_17_14_` in
//! `scripts/stock-check.sh` and `aterm`'s `tools/cross-cell-gate.tsv`) catching `ring` version
//! bumps before cross-target checks silently invoke missing C toolchains (`Astream.CrossCell.TlaRingLinksPin`).

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

use astream_digest::{ct_eq, Sha256};

#[cfg(clean_islands)]
#[path = "ring_links_pin_island.rs"]
mod ring_links_pin_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cc_ver_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cc_ring_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use ring_links_pin_island::{cc_ring_advance, cc_ver_clamp};

/// Maximum `links` identifier byte length (`64`).
pub const MAX_LINKS_NAME_LEN: u64 = 64;

contract_fn! {
    /// Verified `ring` `links` equality (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `cc_links_matched_isl`.
    #[must_use]
    pub const fn cc_links_matched(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct RingLinksGuard {
    checks: u64,
}

impl RingLinksGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self { checks: 0 }
    }

    pub fn verify_links_name(&mut self, override_links: &[u8], lockfile_links: &[u8]) -> bool {
        let ov_len = override_links.len() as u64;
        let lk_len = lockfile_links.len() as u64;
        let clamped = cc_ver_clamp(ov_len, MAX_LINKS_NAME_LEN);
        self.checks = cc_ring_advance(self.checks, self.checks.saturating_add(1));
        if ov_len == 0
            || lk_len == 0
            || clamped != ov_len
            || lk_len > MAX_LINKS_NAME_LEN
            || ov_len != lk_len
        {
            return false;
        }
        let d1 = Sha256::digest_slice(override_links);
        let d2 = Sha256::digest_slice(lockfile_links);
        let ok = ct_eq(&d1, &d2);
        cc_links_matched(if ok { 1 } else { 0 }, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_drift_between_stock_check_ring_links_and_cargo_lock() {
        let mut g = RingLinksGuard::new();
        assert!(g.verify_links_name(b"ring_core_0_17_14_", b"ring_core_0_17_14_"));
        assert!(!g.verify_links_name(b"ring_core_0_17_14_", b"ring_core_0_17_15_"));
    }
}
