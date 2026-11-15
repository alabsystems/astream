// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Commitment-preserving secret-spill redaction tombstone (`H("ASTREAM-REDACT-V1\0" || salt || body)`)
//! allowing payload scrubbing while keeping outer Merkle/hash-chain commitments intact!
//! (`Astream.Audit.TlaRedactTombstone`).

use astream_digest::{ct_eq, Sha256};

#[cfg(clean_islands)]
#[path = "redact_tombstone_island.rs"]
mod redact_tombstone_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn redact_count_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn redact_seq_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use redact_tombstone_island::{redact_count_clamp, redact_seq_advance};

/// Maximum redaction tombstones tracked in one audit segment.
pub const MAX_SEGMENT_REDACTIONS: u64 = 1_024;

contract_fn! {
    /// Verified authorization rank check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `redact_authorized_isl`.
    #[must_use]
    pub const fn redact_authorized(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Live or redacted commitment envelope whose outer `commitment` digest never changes on scrub!
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RedactableAuditEnvelope {
    Live {
        salt: [u8; 32],
        payload: Vec<u8>,
        commitment: [u8; 32],
    },
    RedactedTombstone {
        commitment: [u8; 32],
        redacted_by: String,
        redact_seq: u64,
    },
}

fn compute_salted_commitment(salt: &[u8; 32], payload: &[u8]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update_slice(b"ASTREAM-REDACT-V1\0");
    h.update_slice(salt);
    h.update_slice(payload);
    h.finalize()
}

impl RedactableAuditEnvelope {
    #[must_use]
    pub fn seal_live(salt: [u8; 32], payload: Vec<u8>) -> Self {
        let commitment = compute_salted_commitment(&salt, &payload);
        Self::Live {
            salt,
            payload,
            commitment,
        }
    }

    #[must_use]
    pub const fn commitment(&self) -> &[u8; 32] {
        match self {
            Self::Live { commitment, .. } | Self::RedactedTombstone { commitment, .. } => {
                commitment
            }
        }
    }

    #[must_use]
    pub fn verify_integrity(&self) -> bool {
        match self {
            Self::Live {
                salt,
                payload,
                commitment,
            } => {
                let calc = compute_salted_commitment(salt, payload);
                ct_eq(&calc, commitment)
            }
            Self::RedactedTombstone { .. } => true,
        }
    }

    /// Wipes `salt` and `payload` in memory before replacing with a commitment-preserving tombstone.
    pub fn scrub_in_place(
        &mut self,
        actor_rank: u64,
        required_rank: u64,
        actor: &str,
        prev_seq: u64,
    ) -> Result<u64, &'static str> {
        if actor.is_empty() {
            return Err("empty redaction actor");
        }
        if !redact_authorized(actor_rank, required_rank) {
            return Err("insufficient authority to redact audit payload");
        }
        if prev_seq >= MAX_SEGMENT_REDACTIONS {
            return Err("segment redaction budget exhausted");
        }
        let comm = *self.commitment();
        match self {
            Self::Live { salt, payload, .. } => {
                salt.fill(0);
                core::hint::black_box(salt);
                payload.fill(0);
                core::hint::black_box(payload.as_slice());
            }
            Self::RedactedTombstone { .. } => {
                return Err("audit envelope already redacted");
            }
        }
        let next_seq = redact_seq_advance(
            prev_seq,
            redact_count_clamp(prev_seq.saturating_add(1), MAX_SEGMENT_REDACTIONS),
        );
        let mut actor_owned = String::new();
        actor_owned.push_str(actor);
        *self = Self::RedactedTombstone {
            commitment: comm,
            redacted_by: actor_owned,
            redact_seq: next_seq,
        };
        Ok(next_seq)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn redaction_tombstone_wipes_secret_while_preserving_exact_outer_commitment() {
        let mut env =
            RedactableAuditEnvelope::seal_live([0x77; 32], b" accidental-api-key ".to_vec());
        let before = *env.commitment();
        assert!(env.verify_integrity());
        assert!(env.scrub_in_place(1, 2, "a-worker", 0).is_err());
        assert_eq!(env.scrub_in_place(2, 2, "h-admin", 0).unwrap(), 1);
        assert_eq!(*env.commitment(), before);
        assert!(env.verify_integrity());
    }
}
