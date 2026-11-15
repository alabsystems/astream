// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Transport Ed25519 key <-> `n-<fingerprint>` principal binding & revocation guard
//! (`Astream.Cap.TlaPrincipalKeyBindingB88`, R6 in `REQUIREMENTS-fabric-operations`).
//!
//! Ensures a capability token naming principal `n-<16-byte-tag>` can only be
//! exercised over a transport session authenticated by the matching Ed25519
//! identity key, and enforces a monotonic per-principal `min_valid_epoch`
//! revocation floor.

#[cfg(clean_islands)]
#[path = "principal_key_binding_island.rs"]
mod principal_key_binding_island;
#[cfg(clean_islands)]
pub use principal_key_binding_island::{revocation_epoch_advance, revoked_count_clamp};

/// Hard upper bound on explicitly tracked per-principal revocation floors.
pub const MAX_REVOKED_PRINCIPALS: usize = 256;

#[cfg(not(clean_islands))]
/// Monotonically advance a principal's minimum valid capability epoch.
#[must_use]
pub const fn revocation_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

#[cfg(not(clean_islands))]
/// Clamp tracked per-principal revocation entries to `max_revoked`.
#[must_use]
pub const fn revoked_count_clamp(cand_count: u64, max_revoked: u64) -> u64 {
    if cand_count < max_revoked {
        cand_count
    } else {
        max_revoked
    }
}

contract_fn! {
    /// True iff `token_epoch` meets or exceeds `min_valid_epoch`.
    #[must_use]
    pub const fn token_epoch_admitted(min_valid_epoch: u64, token_epoch: u64) -> bool
    clauses [ensures result == (min_valid_epoch <= token_epoch)]
    {
        min_valid_epoch <= token_epoch
    }
}

/// Constant-time equality over two 16-byte principal key tags.
#[must_use]
pub const fn ct_tag16_eq(a: &[u8; 16], b: &[u8; 16]) -> bool {
    let d0 = (a[0] ^ b[0]) | (a[1] ^ b[1]) | (a[2] ^ b[2]) | (a[3] ^ b[3]);
    let d1 = (a[4] ^ b[4]) | (a[5] ^ b[5]) | (a[6] ^ b[6]) | (a[7] ^ b[7]);
    let d2 = (a[8] ^ b[8]) | (a[9] ^ b[9]) | (a[10] ^ b[10]) | (a[11] ^ b[11]);
    let d3 = (a[12] ^ b[12]) | (a[13] ^ b[13]) | (a[14] ^ b[14]) | (a[15] ^ b[15]);
    (d0 | d1 | d2 | d3) == 0
}

/// Refusal reasons when verifying transport-identity <-> capability-principal binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrincipalBindingError {
    MissingTransportIdentity,
    PrincipalKeyMismatch,
    TokenEpochRevoked {
        min_valid_epoch: u64,
        token_epoch: u64,
    },
    RevocationTableFull,
}

/// Per-principal minimum valid token epoch entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PrincipalRevocationFloor {
    pub principal_tag: [u8; 16],
    pub min_valid_epoch: u64,
}

/// Bounded transport-key binding & revocation registry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrincipalBindingRegistry {
    global_min_epoch: u64,
    floors: Vec<PrincipalRevocationFloor>,
}

impl Default for PrincipalBindingRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl PrincipalBindingRegistry {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            global_min_epoch: 0,
            floors: Vec::new(),
        }
    }

    #[must_use]
    pub const fn global_min_epoch(&self) -> u64 {
        self.global_min_epoch
    }

    #[must_use]
    pub fn tracked_principals(&self) -> usize {
        revoked_count_clamp(self.floors.len() as u64, MAX_REVOKED_PRINCIPALS as u64) as usize
    }

    /// Advance the global minimum valid capability epoch (fencing older fleet tokens).
    pub fn advance_global_floor(&mut self, min_epoch: u64) -> u64 {
        self.global_min_epoch = revocation_epoch_advance(self.global_min_epoch, min_epoch);
        self.global_min_epoch
    }

    /// Revoke all tokens for `principal_tag` issued strictly before `min_valid_epoch`.
    pub fn revoke_principal_before(
        &mut self,
        principal_tag: [u8; 16],
        min_valid_epoch: u64,
    ) -> Result<u64, PrincipalBindingError> {
        for entry in &mut self.floors {
            if ct_tag16_eq(&entry.principal_tag, &principal_tag) {
                entry.min_valid_epoch =
                    revocation_epoch_advance(entry.min_valid_epoch, min_valid_epoch);
                return Ok(entry.min_valid_epoch);
            }
        }
        if self.floors.len() >= MAX_REVOKED_PRINCIPALS {
            return Err(PrincipalBindingError::RevocationTableFull);
        }
        self.floors.push(PrincipalRevocationFloor {
            principal_tag,
            min_valid_epoch,
        });
        Ok(min_valid_epoch)
    }

    /// Verify that `transport_key_tag` matches `token_principal_tag` and `token_epoch` is unrevoked.
    pub fn verify_bound_token(
        &self,
        transport_key_tag: Option<&[u8; 16]>,
        token_principal_tag: &[u8; 16],
        token_epoch: u64,
    ) -> Result<(), PrincipalBindingError> {
        let Some(peer_tag) = transport_key_tag else {
            return Err(PrincipalBindingError::MissingTransportIdentity);
        };
        if !ct_tag16_eq(peer_tag, token_principal_tag) {
            return Err(PrincipalBindingError::PrincipalKeyMismatch);
        }
        if !token_epoch_admitted(self.global_min_epoch, token_epoch) {
            return Err(PrincipalBindingError::TokenEpochRevoked {
                min_valid_epoch: self.global_min_epoch,
                token_epoch,
            });
        }
        let mut rest = self.floors.as_slice();
        while let &[entry, ref tail @ ..] = rest {
            if ct_tag16_eq(&entry.principal_tag, token_principal_tag) {
                if !token_epoch_admitted(entry.min_valid_epoch, token_epoch) {
                    return Err(PrincipalBindingError::TokenEpochRevoked {
                        min_valid_epoch: entry.min_valid_epoch,
                        token_epoch,
                    });
                }
                break;
            }
            rest = tail;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_transport_key_match_and_monotonic_revocation() {
        let mut reg = PrincipalBindingRegistry::new();
        let alice = [0xA1u8; 16];
        let mallory = [0xEEu8; 16];

        assert_eq!(reg.verify_bound_token(Some(&alice), &alice, 1), Ok(()));
        assert_eq!(
            reg.verify_bound_token(None, &alice, 1),
            Err(PrincipalBindingError::MissingTransportIdentity)
        );
        assert_eq!(
            reg.verify_bound_token(Some(&mallory), &alice, 1),
            Err(PrincipalBindingError::PrincipalKeyMismatch)
        );

        assert_eq!(reg.revoke_principal_before(alice, 5), Ok(5));
        assert_eq!(reg.tracked_principals(), 1);
        assert_eq!(
            reg.verify_bound_token(Some(&alice), &alice, 4),
            Err(PrincipalBindingError::TokenEpochRevoked {
                min_valid_epoch: 5,
                token_epoch: 4,
            })
        );
        assert_eq!(reg.verify_bound_token(Some(&alice), &alice, 5), Ok(()));

        assert_eq!(reg.advance_global_floor(10), 10);
        assert_eq!(reg.global_min_epoch(), 10);
        assert_eq!(
            reg.verify_bound_token(Some(&alice), &alice, 9),
            Err(PrincipalBindingError::TokenEpochRevoked {
                min_valid_epoch: 10,
                token_epoch: 9,
            })
        );
    }
}
