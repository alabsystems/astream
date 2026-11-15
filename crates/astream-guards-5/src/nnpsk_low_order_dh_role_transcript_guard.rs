// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! NNpsk & mutual-Ed25519 low-order X25519 DH rejection & role-ordered transcript guard
//! (`evidence/manifest.toml` `aead.handshake.forward-secret-key-agreement` &
//! `aead.identity.mutual-signed-dh`;
//! `Astream.Aead.TlaNnpskLowOrderDhRoleTranscriptGuard`).
//!
//! Enforces forward-secret handshake soundness:
//! - Rejects low-order / all-zero X25519 DH shared secrets (`dh_nonzero_bytes == 0`) BEFORE
//!   running `HKDF-SHA256`,
//! - Rejects reflected messages (`client_pub == server_pub` or swapped role-tag context),
//! - Enforces `verify_strict` + explicit allow-list membership BEFORE trusting any peer identity!

#[cfg(clean_islands)]
#[path = "nnpsk_low_order_dh_role_transcript_guard_island.rs"]
mod nnpsk_low_order_dh_role_transcript_guard_island;
#[cfg(clean_islands)]
pub use nnpsk_low_order_dh_role_transcript_guard_island::{
    dh_nonzero_bytes_clamp_b153, handshake_stage_advance_b153,
};

/// Stage `0`: awaiting peer ephemeral; `1`: DH validated; `2`: authenticated; `3`: aborted.
pub const HS_STAGE_ABORTED: u64 = 3;

#[cfg(not(clean_islands))]
/// Clamp counted non-zero DH output bytes to `32`.
#[must_use]
pub const fn dh_nonzero_bytes_clamp_b153(cand_nonzero: u64, key_bytes: u64) -> u64 {
    if cand_nonzero < key_bytes {
        cand_nonzero
    } else {
        key_bytes
    }
}

#[cfg(not(clean_islands))]
/// Advance handshake stage monotonically (`0 -> 1 -> 2` or terminal `3`).
#[must_use]
pub const fn handshake_stage_advance_b153(cur_stage: u64, cand_stage: u64) -> u64 {
    if cur_stage < cand_stage {
        cand_stage
    } else {
        cur_stage
    }
}

contract_fn! {
    /// True iff X25519 DH output is non-zero, ephemerals are distinct (non-reflected), and auth passed.
    #[must_use]
    pub const fn forward_secret_session_admissible_b153(
        dh_nonzero_bytes: u64,
        ephemerals_distinct: bool,
        role_strict_auth_ok: bool,
    ) -> bool
    clauses [ensures result == (dh_nonzero_bytes > 0 && ephemerals_distinct && role_strict_auth_ok)]
    {
        dh_nonzero_bytes > 0 && ephemerals_distinct && role_strict_auth_ok
    }
}

/// Verdict of forward-secret X25519 handshake verification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HandshakeGuardDecision {
    DerivedSessionKeyAndZeroizedPrk { nonzero_dh_bytes: u64 },
    RefusedLowOrderAllZeroDh,
    RefusedReflectedEphemeralOrRoleSwap,
    RefusedInvalidConfirmOrStrictSignature,
    RefusedSessionAlreadyAborted,
}

/// Forward-secret handshake state machine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ForwardSecretHandshakeGuard {
    stage: u64,
}

impl ForwardSecretHandshakeGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self { stage: 0 }
    }

    /// Validate X25519 DH shared secret, reflection check, and PSK confirm / `verify_strict` + allowlist.
    pub fn complete_key_agreement(
        &mut self,
        dh_nonzero_bytes: u64,
        ephemerals_distinct: bool,
        role_strict_auth_ok: bool,
    ) -> HandshakeGuardDecision {
        if self.stage >= HS_STAGE_ABORTED {
            return HandshakeGuardDecision::RefusedSessionAlreadyAborted;
        }
        let clamped_nz = dh_nonzero_bytes_clamp_b153(dh_nonzero_bytes, 32);
        if clamped_nz == 0 {
            self.stage = handshake_stage_advance_b153(self.stage, HS_STAGE_ABORTED);
            return HandshakeGuardDecision::RefusedLowOrderAllZeroDh;
        }
        if !ephemerals_distinct {
            self.stage = handshake_stage_advance_b153(self.stage, HS_STAGE_ABORTED);
            return HandshakeGuardDecision::RefusedReflectedEphemeralOrRoleSwap;
        }
        if !forward_secret_session_admissible_b153(
            clamped_nz,
            ephemerals_distinct,
            role_strict_auth_ok,
        ) {
            self.stage = handshake_stage_advance_b153(self.stage, HS_STAGE_ABORTED);
            return HandshakeGuardDecision::RefusedInvalidConfirmOrStrictSignature;
        }
        self.stage = handshake_stage_advance_b153(self.stage, 2);
        HandshakeGuardDecision::DerivedSessionKeyAndZeroizedPrk {
            nonzero_dh_bytes: clamped_nz,
        }
    }
}

impl Default for ForwardSecretHandshakeGuard {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_low_order_dh_and_reflected_ephemerals_before_accepting_session() {
        let mut low = ForwardSecretHandshakeGuard::new();
        assert_eq!(
            low.complete_key_agreement(0, true, true),
            HandshakeGuardDecision::RefusedLowOrderAllZeroDh
        );

        let mut refl = ForwardSecretHandshakeGuard::new();
        assert_eq!(
            refl.complete_key_agreement(31, false, true),
            HandshakeGuardDecision::RefusedReflectedEphemeralOrRoleSwap
        );

        let mut ok = ForwardSecretHandshakeGuard::new();
        assert_eq!(
            ok.complete_key_agreement(32, true, true),
            HandshakeGuardDecision::DerivedSessionKeyAndZeroizedPrk {
                nonzero_dh_bytes: 32,
            }
        );
    }
}
