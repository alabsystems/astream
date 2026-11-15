// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pre-parse `Attach` proof-of-possession, non-empty secret, and `Hello->Attach` deadline gate
//! (`docs/AUDIT-2026-09.md` lines 31, 33, 37, 38; `Astream.Cap.TlaAttachProofPreparseGate`).
//!
//! Eliminates three denial-of-service & authentication bypass hazards from `AUDIT-2026-09.md`:
//! - Refuses guarded open/attach under an empty HMAC secret (`secret_len == 0`),
//! - Enforces a bounded `Hello -> Attach` handshake window (`attach_deadline_ms`) so an
//!   unauthenticated peer sending `Hello` cannot hold a `MAX_CONNS` slot forever,
//! - Enforces `raw_grant_wire_len <= MAX_ATTACH_GRANT_BYTES` (`4_096` B) AND verifies the
//!   constant-time HMAC proof over raw grant text BEFORE allocating or parsing grant rules
//!   (preventing an unauthenticated 16 MiB `Attach` from triggering ~590 MiB of allocations).

#[cfg(clean_islands)]
#[path = "attach_proof_preparse_gate_island.rs"]
mod attach_proof_preparse_gate_island;
#[cfg(clean_islands)]
pub use attach_proof_preparse_gate_island::{
    attach_deadline_clock_advance_b139, attach_grant_wire_clamp_b139,
};

/// Maximum raw wire length of a capability grant (`MAX_NAME_LEN = 4_096` bytes).
pub const MAX_ATTACH_GRANT_BYTES: u64 = 4_096;

#[cfg(not(clean_islands))]
/// Clamp an inspected grant wire length to `max_grant_bytes`.
#[must_use]
pub const fn attach_grant_wire_clamp_b139(cand_bytes: u64, max_grant_bytes: u64) -> u64 {
    if cand_bytes < max_grant_bytes {
        cand_bytes
    } else {
        max_grant_bytes
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the handshake clock reading (`ms`).
#[must_use]
pub const fn attach_deadline_clock_advance_b139(cur_ms: u64, cand_ms: u64) -> u64 {
    if cur_ms < cand_ms {
        cand_ms
    } else {
        cur_ms
    }
}

contract_fn! {
    /// True iff the broker secret is non-empty, the `Hello -> Attach` deadline has not expired,
    /// `raw_wire_len <= max_grant_bytes`, and the HMAC proof verified BEFORE grant rule parsing.
    #[must_use]
    pub const fn attach_preparse_admissible_b139(
        secret_non_empty: bool,
        within_deadline: bool,
        raw_wire_len: u64,
        max_grant_bytes: u64,
        hmac_verified_first: bool,
    ) -> bool
    clauses [ensures result == (secret_non_empty && within_deadline && raw_wire_len <= max_grant_bytes && hmac_verified_first)]
    {
        secret_non_empty
            && within_deadline
            && raw_wire_len <= max_grant_bytes
            && hmac_verified_first
    }
}

/// Pre-parse verdict for an inbound `Attach` handshake frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AttachPreparseVerdict {
    /// Guarded broker configured with an empty secret: fail closed immediately!
    RefusedEmptyBrokerSecret,
    /// Unauthenticated peer held the connection past `hello_at_ms + handshake_window_ms`.
    RefusedAttachDeadlineExpired,
    /// Raw grant string exceeds `MAX_ATTACH_GRANT_BYTES` (`4_096` B): rejected before HMAC/parse.
    RefusedOversizedRawGrant { raw_wire_len: u64 },
    /// HMAC proof over `(nonce || raw_grant)` failed before any rule allocation.
    RefusedInvalidProofBeforeParse,
    /// Proof verified over bounded raw grant: safe to parse grant rules (`bounded_wire_len`).
    AdmittedParseGrant { bounded_wire_len: u64 },
}

/// Stateful `Hello -> Attach` pre-parse gate for a guarded connection slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AttachPreparseGate {
    secret_non_empty: bool,
    hello_at_ms: u64,
    now_ms: u64,
    handshake_window_ms: u64,
}

impl AttachPreparseGate {
    #[must_use]
    pub const fn new(secret_len: usize, hello_at_ms: u64, handshake_window_ms: u64) -> Self {
        Self {
            secret_non_empty: secret_len > 0,
            hello_at_ms,
            now_ms: hello_at_ms,
            handshake_window_ms,
        }
    }

    /// Evaluate an inbound `Attach` frame BEFORE allocating or parsing `Grant` rules.
    pub fn check_before_parse(
        &mut self,
        cand_now_ms: u64,
        raw_grant_wire_len: u64,
        hmac_proof_verified_on_raw_bytes: bool,
    ) -> AttachPreparseVerdict {
        self.now_ms = attach_deadline_clock_advance_b139(self.now_ms, cand_now_ms);
        if !self.secret_non_empty {
            return AttachPreparseVerdict::RefusedEmptyBrokerSecret;
        }
        let elapsed_ms = self.now_ms.saturating_sub(self.hello_at_ms);
        let within_deadline = elapsed_ms <= self.handshake_window_ms;
        if !within_deadline {
            return AttachPreparseVerdict::RefusedAttachDeadlineExpired;
        }
        if raw_grant_wire_len > MAX_ATTACH_GRANT_BYTES {
            return AttachPreparseVerdict::RefusedOversizedRawGrant {
                raw_wire_len: raw_grant_wire_len,
            };
        }
        if !attach_preparse_admissible_b139(
            self.secret_non_empty,
            within_deadline,
            raw_grant_wire_len,
            MAX_ATTACH_GRANT_BYTES,
            hmac_proof_verified_on_raw_bytes,
        ) {
            return AttachPreparseVerdict::RefusedInvalidProofBeforeParse;
        }
        AttachPreparseVerdict::AdmittedParseGrant {
            bounded_wire_len: attach_grant_wire_clamp_b139(
                raw_grant_wire_len,
                MAX_ATTACH_GRANT_BYTES,
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_empty_secret_expired_hello_oversized_grant_and_bad_proof_before_parse() {
        let mut empty = AttachPreparseGate::new(0, 100, 5_000);
        assert_eq!(
            empty.check_before_parse(110, 64, true),
            AttachPreparseVerdict::RefusedEmptyBrokerSecret
        );

        let mut gate = AttachPreparseGate::new(32, 1_000, 5_000);
        // Unauthenticated 16 MiB grant rejected before any parse allocation:
        assert_eq!(
            gate.check_before_parse(1_050, 16 * 1024 * 1024, false),
            AttachPreparseVerdict::RefusedOversizedRawGrant {
                raw_wire_len: 16 * 1024 * 1024
            }
        );
        // Invalid proof rejected before parse:
        assert_eq!(
            gate.check_before_parse(1_100, 128, false),
            AttachPreparseVerdict::RefusedInvalidProofBeforeParse
        );
        // Valid bounded attach within window admitted:
        assert_eq!(
            gate.check_before_parse(2_000, 128, true),
            AttachPreparseVerdict::AdmittedParseGrant {
                bounded_wire_len: 128
            }
        );
        // After `1_000 + 5_000 = 6_000` ms, slow `Hello` squatter is evicted:
        assert_eq!(
            gate.check_before_parse(6_001, 128, true),
            AttachPreparseVerdict::RefusedAttachDeadlineExpired
        );
    }
}
