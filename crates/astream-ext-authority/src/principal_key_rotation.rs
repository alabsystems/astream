// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Principal-preserving node-key rotation ledger binding stable logical principal IDs across
//! signed key-rotation statements (`Astream.ExtAuth.TlaPrincipalKeyRotation`).

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
#[path = "principal_key_rotation_island.rs"]
mod principal_key_rotation_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ext_hist_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ext_rot_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use principal_key_rotation_island::{ext_hist_clamp, ext_rot_advance};

/// Maximum historical rotation links retained per principal (`64`).
pub const MAX_ROTATION_CHAIN: u64 = 64;

contract_fn! {
    /// Verified monotonic key rotation epoch (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ext_principal_bound_isl`.
    #[must_use]
    pub const fn ext_principal_bound(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct PrincipalRotationLedger {
    genesis_principal: [u8; 32],
    active_key_digest: [u8; 32],
    chain_len: u64,
    rotation_epoch: u64,
    valid: bool,
}

impl PrincipalRotationLedger {
    #[must_use]
    pub fn new(genesis_pubkey: &[u8]) -> Self {
        let d = Sha256::digest_slice(genesis_pubkey);
        Self {
            genesis_principal: d,
            active_key_digest: d,
            chain_len: 1,
            rotation_epoch: 1,
            valid: !genesis_pubkey.is_empty(),
        }
    }

    pub fn apply_rotation(&mut self, old_pubkey: &[u8], new_pubkey: &[u8], epoch: u64) -> bool {
        if !self.valid || old_pubkey.is_empty() || new_pubkey.is_empty() {
            return false;
        }
        let old_d = Sha256::digest_slice(old_pubkey);
        let new_d = Sha256::digest_slice(new_pubkey);
        if !ct_eq(&old_d, &self.active_key_digest) || ct_eq(&old_d, &new_d) {
            return false;
        }
        let Some(min_epoch) = self.rotation_epoch.checked_add(1) else {
            return false;
        };
        if !ext_principal_bound(epoch, min_epoch) {
            return false;
        }
        let next_len = ext_hist_clamp(self.chain_len.saturating_add(1), MAX_ROTATION_CHAIN);
        if next_len == self.chain_len {
            return false;
        }
        self.active_key_digest = new_d;
        self.chain_len = next_len;
        self.rotation_epoch = ext_rot_advance(self.rotation_epoch, epoch);
        true
    }

    #[must_use]
    pub const fn genesis_principal(&self) -> &[u8; 32] {
        &self.genesis_principal
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preserves_genesis_principal_across_verified_rotations() {
        let mut l = PrincipalRotationLedger::new(b"node-ed25519-k1");
        let p0 = *l.genesis_principal();
        assert!(l.apply_rotation(b"node-ed25519-k1", b"node-ed25519-k2", 2));
        assert!(!l.apply_rotation(b"node-ed25519-k1", b"node-ed25519-k3", 3));
        assert_eq!(*l.genesis_principal(), p0);
    }
}
