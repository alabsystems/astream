// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Dual-slot overlapping Ed25519 host-key rollover state machine (`docs/ROADMAP.md` §1: *"and the
//! key operations around it: distribution and rotation"*) preserving handshake continuity during
//! overlap windows (`Astream.ExtAuth.TlaHostKeyRollover`).

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
#[path = "host_key_rollover_island.rs"]
mod host_key_rollover_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ext_slot_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ext_gen_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use host_key_rollover_island::{ext_gen_advance, ext_slot_clamp};

/// Maximum concurrent active host-key slots (`2`: current + retiring).
pub const MAX_KEY_SLOTS: u64 = 2;

contract_fn! {
    /// Verified rollover overlap window (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ext_overlap_intact_isl`.
    #[must_use]
    pub const fn ext_overlap_intact(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct HostKeyRollover {
    primary_digest: [u8; 32],
    retiring_digest: Option<([u8; 32], u64)>,
    generation: u64,
    valid: bool,
}

impl HostKeyRollover {
    #[must_use]
    pub fn new(initial_pubkey: &[u8]) -> Self {
        Self {
            primary_digest: Sha256::digest_slice(initial_pubkey),
            retiring_digest: None,
            generation: 1,
            valid: !initial_pubkey.is_empty(),
        }
    }

    pub fn rotate(&mut self, next_pubkey: &[u8], overlap_until_ms: u64, now_ms: u64) -> bool {
        if !self.valid || next_pubkey.is_empty() {
            return false;
        }
        let Some(min_until) = now_ms.checked_add(1) else {
            return false;
        };
        if !ext_overlap_intact(overlap_until_ms, min_until) {
            return false;
        }
        let next_d = Sha256::digest_slice(next_pubkey);
        if ct_eq(&next_d, &self.primary_digest) {
            return false;
        }
        let _slots = ext_slot_clamp(2, MAX_KEY_SLOTS);
        self.retiring_digest = Some((self.primary_digest, overlap_until_ms));
        self.primary_digest = next_d;
        self.generation = ext_gen_advance(self.generation, self.generation.saturating_add(1));
        true
    }

    #[must_use]
    pub fn accepts(&self, presented_pubkey: &[u8], now_ms: u64) -> bool {
        if !self.valid || presented_pubkey.is_empty() {
            return false;
        }
        let d = Sha256::digest_slice(presented_pubkey);
        if ct_eq(&d, &self.primary_digest) {
            return true;
        }
        match self.retiring_digest {
            Some((old, until_ms)) => ct_eq(&d, &old) && ext_overlap_intact(until_ms, now_ms),
            None => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accepts_retiring_host_key_only_during_overlap_window() {
        let mut r = HostKeyRollover::new(b"host-key-v1");
        assert!(r.rotate(b"host-key-v2", 5_000, 1_000));
        assert!(r.accepts(b"host-key-v1", 4_999));
        assert!(r.accepts(b"host-key-v2", 9_000));
        assert!(!r.accepts(b"host-key-v1", 5_001));
    }
}
