// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Zero-heap SASL `SCRAM-SHA-256` challenge nonce anti-replay ring
//! (`Astream.Kafka.TlaScramNonceReplayGuard`).
//!
//! Protects `astream-kafka` SASL `SCRAM-SHA-256` authentication against cross-connection challenge
//! replay using a fixed 16-slot stack ring (`scram_seen_clamp_b114 <= 16`) and monotonic
//! `scram_challenge_seq_advance_b114` without any heap allocation.

#[cfg(clean_islands)]
#[path = "scram_nonce_replay_guard_island.rs"]
mod scram_nonce_replay_guard_island;
#[cfg(clean_islands)]
pub use scram_nonce_replay_guard_island::{
    scram_challenge_seq_advance_b114, scram_seen_clamp_b114,
};

#[cfg(not(clean_islands))]
/// Clamp occupied SCRAM nonce ring slots to `max_slots`.
#[must_use]
pub const fn scram_seen_clamp_b114(cand_seen: u64, max_slots: u64) -> u64 {
    if cand_seen < max_slots {
        cand_seen
    } else {
        max_slots
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the SCRAM server challenge sequence number.
#[must_use]
pub const fn scram_challenge_seq_advance_b114(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}

contract_fn! {
    /// True iff `nonce_digest` is non-zero (valid hashed `client_nonce || server_nonce`).
    #[must_use]
    pub const fn scram_digest_nonzero_b114(nonce_digest: u64) -> bool
    clauses [ensures result == (0 < nonce_digest)]
    {
        0 < nonce_digest
    }
}

/// Number of recent SCRAM challenge digests retained on the stack.
pub const MAX_SCRAM_NONCE_RING: usize = 16;

/// Verdict when consuming a SCRAM `client-final-message` nonce digest.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScramNonceVerdict {
    AcceptedFresh { challenge_seq: u64 },
    RejectedZeroDigest,
    RejectedReplay,
}

/// Stack-allocated SCRAM nonce replay ring.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ScramNonceReplayGuard {
    ring: [u64; MAX_SCRAM_NONCE_RING],
    write_idx: usize,
    occupied: u64,
    challenge_seq: u64,
}

impl Default for ScramNonceReplayGuard {
    fn default() -> Self {
        Self::new()
    }
}

impl ScramNonceReplayGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            ring: [0; MAX_SCRAM_NONCE_RING],
            write_idx: 0,
            occupied: 0,
            challenge_seq: 0,
        }
    }

    #[must_use]
    pub const fn occupied(&self) -> u64 {
        self.occupied
    }

    /// Consume `nonce_digest` once; rejects `0` or any digest still present in the ring.
    pub fn check_and_record(&mut self, nonce_digest: u64) -> ScramNonceVerdict {
        if !scram_digest_nonzero_b114(nonce_digest) {
            return ScramNonceVerdict::RejectedZeroDigest;
        }
        let len = self.occupied as usize;
        let mut i = 0usize;
        while i < len {
            let Some(&existing) = self.ring.get(i) else {
                break;
            };
            if existing == nonce_digest {
                return ScramNonceVerdict::RejectedReplay;
            }
            i = i.saturating_add(1);
        }
        let slot = self.write_idx % MAX_SCRAM_NONCE_RING;
        if let Some(dst) = self.ring.get_mut(slot) {
            *dst = nonce_digest;
        }
        self.write_idx = slot.wrapping_add(1) % MAX_SCRAM_NONCE_RING;
        let cand_occ = self.occupied.saturating_add(1);
        self.occupied = scram_seen_clamp_b114(cand_occ, MAX_SCRAM_NONCE_RING as u64);

        let next_seq = self.challenge_seq.saturating_add(1);
        self.challenge_seq = scram_challenge_seq_advance_b114(self.challenge_seq, next_seq);
        ScramNonceVerdict::AcceptedFresh {
            challenge_seq: self.challenge_seq,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accepts_fresh_scram_nonce_and_rejects_replay() {
        let mut g = ScramNonceReplayGuard::new();
        assert_eq!(
            g.check_and_record(0x9988_7766),
            ScramNonceVerdict::AcceptedFresh { challenge_seq: 1 }
        );
        assert_eq!(
            g.check_and_record(0x9988_7766),
            ScramNonceVerdict::RejectedReplay
        );
    }
}
