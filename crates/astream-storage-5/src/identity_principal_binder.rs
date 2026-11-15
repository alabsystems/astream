// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Ed25519 SIGMA transport identity <-> `Attach` capability principal (`n-<hash>`) binder
//! (`Astream.Broker.TlaIdentityPrincipalBinder`).
//!
//! Enforces Fabric Operations Requirement R6 (`REQUIREMENTS-fabric-operations-2026-09-14.md`):
//! binds an authenticated transport `identity` key tag (`n-<hash>`) to the capability principal
//! presented in `Attach`, rejecting bearer capability replay across mismatched Ed25519 peers.

#[cfg(clean_islands)]
#[path = "identity_principal_binder_island.rs"]
mod identity_principal_binder_island;
#[cfg(clean_islands)]
pub use identity_principal_binder_island::{identity_bind_epoch_advance, identity_mismatch_clamp};

#[cfg(not(clean_islands))]
/// Clamp recorded R6 identity-principal mismatch count to `max_mismatches`.
#[must_use]
pub const fn identity_mismatch_clamp(cand_mismatches: u64, max_mismatches: u64) -> u64 {
    if cand_mismatches < max_mismatches {
        cand_mismatches
    } else {
        max_mismatches
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the R6 identity-binding epoch.
#[must_use]
pub const fn identity_bind_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `cap_principal_tag` matches the transport-authenticated `identity_key_tag`.
    #[must_use]
    pub const fn identity_matches_principal(identity_key_tag: u64, cap_principal_tag: u64) -> bool
    clauses [ensures result == (identity_key_tag == cap_principal_tag)]
    {
        identity_key_tag == cap_principal_tag
    }
}

/// Maximum concurrent authenticated connections tracked per R6 binder shard.
pub const MAX_IDENTITY_BINDINGS: usize = 16;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct IdentityBindingSlot {
    active: bool,
    conn_id: u64,
    identity_key_tag: u64,
    bind_epoch: u64,
}

impl IdentityBindingSlot {
    const EMPTY: Self = Self {
        active: false,
        conn_id: 0,
        identity_key_tag: 0,
        bind_epoch: 0,
    };
}

/// Outcome of verifying an `Attach` capability principal against a connection's SIGMA identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrincipalBindOutcome {
    Authorized {
        bind_epoch: u64,
    },
    UnauthenticatedConnection,
    PrincipalMismatch {
        expected_identity_tag: u64,
        presented_principal_tag: u64,
    },
}

/// R6 transport-identity to capability-principal binding table.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IdentityPrincipalBinder {
    slots: [IdentityBindingSlot; MAX_IDENTITY_BINDINGS],
    bind_epoch: u64,
    mismatch_count: u64,
    max_mismatch_cap: u64,
}

impl IdentityPrincipalBinder {
    #[must_use]
    pub const fn new(max_mismatch_cap: u64) -> Self {
        let cap = if max_mismatch_cap == 0 {
            1024
        } else {
            max_mismatch_cap
        };
        Self {
            slots: [IdentityBindingSlot::EMPTY; MAX_IDENTITY_BINDINGS],
            bind_epoch: 0,
            mismatch_count: 0,
            max_mismatch_cap: cap,
        }
    }

    #[must_use]
    pub const fn mismatch_count(&self) -> u64 {
        self.mismatch_count
    }

    /// Record the peer's verified Ed25519 SIGMA identity tag (`n-<hash>`) upon handshake completion.
    pub fn register_handshake_identity(&mut self, conn_id: u64, identity_key_tag: u64) -> bool {
        let next_ep = self.bind_epoch.saturating_add(1);
        self.bind_epoch = identity_bind_epoch_advance(self.bind_epoch, next_ep);
        let mut idx = 0usize;
        let mut free_idx: Option<usize> = None;
        while let Some(slot) = self.slots.get_mut(idx) {
            if slot.active {
                if slot.conn_id == conn_id {
                    slot.identity_key_tag = identity_key_tag;
                    slot.bind_epoch = self.bind_epoch;
                    return true;
                }
            } else if free_idx.is_none() {
                free_idx = Some(idx);
            }
            idx = idx.saturating_add(1);
        }
        if let Some(target) = free_idx {
            if let Some(slot) = self.slots.get_mut(target) {
                *slot = IdentityBindingSlot {
                    active: true,
                    conn_id,
                    identity_key_tag,
                    bind_epoch: self.bind_epoch,
                };
                return true;
            }
        }
        false
    }

    /// Remove binding state when `conn_id` closes.
    pub fn unregister_conn(&mut self, conn_id: u64) -> bool {
        let mut idx = 0usize;
        while let Some(slot) = self.slots.get_mut(idx) {
            if slot.active && slot.conn_id == conn_id {
                *slot = IdentityBindingSlot::EMPTY;
                return true;
            }
            idx = idx.saturating_add(1);
        }
        false
    }

    /// Verify that an `Attach` capability's `n-<hash>` principal matches `conn_id`'s transport identity.
    pub fn verify_attach_principal(
        &mut self,
        conn_id: u64,
        cap_principal_tag: u64,
    ) -> PrincipalBindOutcome {
        let mut rest: &[IdentityBindingSlot] = &self.slots;
        while let [slot, tail @ ..] = rest {
            if slot.active && slot.conn_id == conn_id {
                if identity_matches_principal(slot.identity_key_tag, cap_principal_tag) {
                    return PrincipalBindOutcome::Authorized {
                        bind_epoch: slot.bind_epoch,
                    };
                }
                let next_mm = self.mismatch_count.saturating_add(1);
                self.mismatch_count = identity_mismatch_clamp(next_mm, self.max_mismatch_cap);
                return PrincipalBindOutcome::PrincipalMismatch {
                    expected_identity_tag: slot.identity_key_tag,
                    presented_principal_tag: cap_principal_tag,
                };
            }
            rest = tail;
        }
        let next_mm = self.mismatch_count.saturating_add(1);
        self.mismatch_count = identity_mismatch_clamp(next_mm, self.max_mismatch_cap);
        PrincipalBindOutcome::UnauthenticatedConnection
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_r6_identity_to_principal_match_and_rejects_stolen_cap() {
        let mut binder = IdentityPrincipalBinder::new(16);
        assert!(binder.register_handshake_identity(7, 0xCAFE_1234));
        assert_eq!(
            binder.verify_attach_principal(7, 0xCAFE_1234),
            PrincipalBindOutcome::Authorized { bind_epoch: 1 }
        );
        assert_eq!(
            binder.verify_attach_principal(7, 0xDEAD_BEEF),
            PrincipalBindOutcome::PrincipalMismatch {
                expected_identity_tag: 0xCAFE_1234,
                presented_principal_tag: 0xDEAD_BEEF,
            }
        );
        assert_eq!(binder.mismatch_count(), 1);
    }
}
