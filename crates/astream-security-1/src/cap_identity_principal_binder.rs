// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Ed25519 transport-identity to capability-principal (`n-<hash>`) binder & revocation fence
//! (`REQUIREMENTS-fabric-operations` R6; `Astream.Cap.TlaIdentityPrincipalBinder`).
//!
//! Prevents capability substitution across mutually-authenticated Ed25519 (`identity`) channels:
//! - Binds each 32-byte Ed25519 client public key to its canonical 64-bit principal tag (`n-<hex>`)
//!   and minimum admissible capability epoch,
//! - Rejects `Attach` when the capability's principal tag mismatches the transport peer's bound tag
//!   ([`cap_id_hash_matches_b122`]),
//! - Monotonically advances per-principal revocation epochs via [`cap_id_rev_epoch_advance_b122`].

#[cfg(clean_islands)]
#[path = "cap_identity_principal_binder_island.rs"]
mod cap_identity_principal_binder_island;
#[cfg(clean_islands)]
pub use cap_identity_principal_binder_island::{
    cap_id_rev_epoch_advance_b122, cap_id_slots_clamp_b122,
};

#[cfg(not(clean_islands))]
/// Clamp active identity-binding slot count to `max_slots`.
#[must_use]
pub const fn cap_id_slots_clamp_b122(cand_slots: u64, max_slots: u64) -> u64 {
    if cand_slots < max_slots {
        cand_slots
    } else {
        max_slots
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance minimum non-revoked capability epoch.
#[must_use]
pub const fn cap_id_rev_epoch_advance_b122(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `expected_tag` matches `presented_tag`.
    #[must_use]
    pub const fn cap_id_hash_matches_b122(expected_tag: u64, presented_tag: u64) -> bool
    clauses [ensures result == (expected_tag == presented_tag)]
    {
        expected_tag == presented_tag
    }
}

pub const MAX_IDENTITY_BINDINGS: usize = 32;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct IdentityBindingSlot {
    active: bool,
    peer_pub: [u8; 32],
    principal_tag: u64,
    min_cap_epoch: u64,
}

impl IdentityBindingSlot {
    const EMPTY: Self = Self {
        active: false,
        peer_pub: [0u8; 32],
        principal_tag: 0,
        min_cap_epoch: 0,
    };
}

/// Verdict of verifying `(peer_pub, presented_principal_tag, presented_cap_epoch)` on `Attach`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IdentityPrincipalVerdict {
    Admitted {
        principal_tag: u64,
        min_cap_epoch: u64,
    },
    UnboundTransportIdentity,
    PrincipalMismatch {
        bound_tag: u64,
        presented_tag: u64,
    },
    RevokedCapabilityEpoch {
        min_cap_epoch: u64,
        presented_epoch: u64,
    },
}

/// Bounded registry binding Ed25519 transport public keys to `n-<hash>` capability principals.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CapIdentityPrincipalBinder {
    slots: [IdentityBindingSlot; MAX_IDENTITY_BINDINGS],
    bound_slots: u64,
    global_rev_epoch: u64,
}

impl Default for CapIdentityPrincipalBinder {
    fn default() -> Self {
        Self::new()
    }
}

impl CapIdentityPrincipalBinder {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            slots: [IdentityBindingSlot::EMPTY; MAX_IDENTITY_BINDINGS],
            bound_slots: 0,
            global_rev_epoch: 0,
        }
    }

    #[must_use]
    pub const fn bound_count(&self) -> u64 {
        self.bound_slots
    }

    /// Bind or update `peer_pub` -> `principal_tag`, advancing `min_cap_epoch` monotonically.
    pub fn bind_identity(
        &mut self,
        peer_pub: [u8; 32],
        principal_tag: u64,
        min_cap_epoch: u64,
    ) -> bool {
        for slot in &mut self.slots {
            if slot.active && slot.peer_pub == peer_pub {
                slot.principal_tag = principal_tag;
                slot.min_cap_epoch =
                    cap_id_rev_epoch_advance_b122(slot.min_cap_epoch, min_cap_epoch);
                self.global_rev_epoch =
                    cap_id_rev_epoch_advance_b122(self.global_rev_epoch, slot.min_cap_epoch);
                return true;
            }
        }
        for slot in &mut self.slots {
            if !slot.active {
                slot.active = true;
                slot.peer_pub = peer_pub;
                slot.principal_tag = principal_tag;
                slot.min_cap_epoch = min_cap_epoch;
                self.bound_slots = cap_id_slots_clamp_b122(
                    self.bound_slots.saturating_add(1),
                    MAX_IDENTITY_BINDINGS as u64,
                );
                self.global_rev_epoch =
                    cap_id_rev_epoch_advance_b122(self.global_rev_epoch, min_cap_epoch);
                return true;
            }
        }
        false
    }

    /// Verify a presented capability's `(presented_tag, presented_epoch)` against `peer_pub`.
    #[must_use]
    pub fn verify_attach_principal(
        &self,
        peer_pub: &[u8; 32],
        presented_tag: u64,
        presented_epoch: u64,
    ) -> IdentityPrincipalVerdict {
        let mut rest = self.slots.as_slice();
        while let &[slot, ref tail @ ..] = rest {
            if slot.active && &slot.peer_pub == peer_pub {
                if !cap_id_hash_matches_b122(slot.principal_tag, presented_tag) {
                    return IdentityPrincipalVerdict::PrincipalMismatch {
                        bound_tag: slot.principal_tag,
                        presented_tag,
                    };
                }
                if presented_epoch < slot.min_cap_epoch {
                    return IdentityPrincipalVerdict::RevokedCapabilityEpoch {
                        min_cap_epoch: slot.min_cap_epoch,
                        presented_epoch,
                    };
                }
                return IdentityPrincipalVerdict::Admitted {
                    principal_tag: slot.principal_tag,
                    min_cap_epoch: slot.min_cap_epoch,
                };
            }
            rest = tail;
        }
        IdentityPrincipalVerdict::UnboundTransportIdentity
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_cross_principal_capability_and_revoked_epoch() {
        let mut binder = CapIdentityPrincipalBinder::new();
        let pub_a = [0xAAu8; 32];
        assert!(binder.bind_identity(pub_a, 0x1111_2222, 3));

        // Wrong principal over pub_a's authenticated channel is rejected!
        assert_eq!(
            binder.verify_attach_principal(&pub_a, 0x9999_8888, 5),
            IdentityPrincipalVerdict::PrincipalMismatch {
                bound_tag: 0x1111_2222,
                presented_tag: 0x9999_8888
            }
        );
        // Revoked epoch (< 3) is rejected!
        assert_eq!(
            binder.verify_attach_principal(&pub_a, 0x1111_2222, 2),
            IdentityPrincipalVerdict::RevokedCapabilityEpoch {
                min_cap_epoch: 3,
                presented_epoch: 2
            }
        );
        // Matching principal + current epoch is admitted!
        assert_eq!(
            binder.verify_attach_principal(&pub_a, 0x1111_2222, 3),
            IdentityPrincipalVerdict::Admitted {
                principal_tag: 0x1111_2222,
                min_cap_epoch: 3
            }
        );
    }
}
