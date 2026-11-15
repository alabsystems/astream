// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `REQUIREMENTS R6` transport-identity-to-capability-principal binder verifying that an Ed25519
//! `identity` peer public key hashes to the exact `n-<16hex>` node principal claimed in `Attach`
//! (`Astream.SecVault.TlaPrincipalKeyPin`).

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
#[path = "principal_key_pin_island.rs"]
mod principal_key_pin_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sv_key_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sv_pin_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use principal_key_pin_island::{sv_key_clamp, sv_pin_advance};

/// Ed25519 public key byte size (`32`).
pub const ED25519_PUBKEY_LEN: u64 = 32;

contract_fn! {
    /// Verified principal-key match (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sv_principal_bound_isl`.
    #[must_use]
    pub const fn sv_principal_bound(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct PrincipalKeyBinder {
    bindings_checked: u64,
}

impl PrincipalKeyBinder {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            bindings_checked: 0,
        }
    }

    #[must_use]
    pub fn derive_principal_tag(ed25519_pubkey: &[u8; 32]) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update_slice(b"aterm-r6-principal-v1:");
        h.update_slice(ed25519_pubkey);
        h.finalize()
    }

    pub fn verify_attach_principal(
        &mut self,
        peer_pubkey: &[u8; 32],
        claimed_principal_tag: &[u8; 32],
    ) -> bool {
        let _ = sv_key_clamp(peer_pubkey.len() as u64, ED25519_PUBKEY_LEN);
        self.bindings_checked = sv_pin_advance(
            self.bindings_checked,
            self.bindings_checked.saturating_add(1),
        );
        if ct_eq(peer_pubkey, &[0u8; 32]) {
            return false;
        }
        let expected = Self::derive_principal_tag(peer_pubkey);
        let matched = ct_eq(&expected, claimed_principal_tag);
        sv_principal_bound(if matched { 1 } else { 0 }, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn binds_ed25519_identity_key_to_claimed_node_principal() {
        let pk = [0x42u8; 32];
        let tag = PrincipalKeyBinder::derive_principal_tag(&pk);
        let mut b = PrincipalKeyBinder::new();
        assert!(b.verify_attach_principal(&pk, &tag));
        assert!(!b.verify_attach_principal(&[0x99u8; 32], &tag));
    }
}
