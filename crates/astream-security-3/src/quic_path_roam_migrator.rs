// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! QUIC RFC 9000 §9 zero-gap connection migration & 3x anti-amplification path validator
//! (QUIC transport and connection migration;
//! `Astream.Aead.TlaQuicPathRoamMigrator`).
//!
//! Enables zero-gap roaming across IP/port transitions without tearing down the authenticated stream
//! or resetting in-flight byte offsets:
//! - Issues a 64-bit `PATH_CHALLENGE` token on a candidate peer tuple,
//! - Enforces RFC 9000 §8.1's 3x anti-amplification send cap (`sent_on_candidate <= 3 * rx_bytes`)
//!   until matching `PATH_RESPONSE` proves peer return-routability,
//! - Commits path migration under a monotonically advancing `roam_generation` while preserving
//!   `contiguous_stream_offset` across the switch.

#[cfg(clean_islands)]
#[path = "quic_path_roam_migrator_island.rs"]
mod quic_path_roam_migrator_island;
#[cfg(clean_islands)]
pub use quic_path_roam_migrator_island::{
    quic_anti_amp_clamp_b126, quic_roam_gen_advance_b126, quic_stream_off_advance_b126,
};

#[cfg(not(clean_islands))]
/// Clamp bytes sent on an unvalidated candidate path to `anti_amp_budget` (`3 * bytes_received`).
#[must_use]
pub const fn quic_anti_amp_clamp_b126(cand_tx_bytes: u64, anti_amp_budget: u64) -> u64 {
    if cand_tx_bytes < anti_amp_budget {
        cand_tx_bytes
    } else {
        anti_amp_budget
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the validated connection roam generation.
#[must_use]
pub const fn quic_roam_gen_advance_b126(cur_gen: u64, cand_gen: u64) -> u64 {
    if cur_gen < cand_gen {
        cand_gen
    } else {
        cur_gen
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the contiguous zero-gap stream offset across path migration.
#[must_use]
pub const fn quic_stream_off_advance_b126(cur_off: u64, cand_off: u64) -> u64 {
    if cur_off < cand_off {
        cand_off
    } else {
        cur_off
    }
}

contract_fn! {
    /// True iff `response_token` matches `expected_challenge` and `expected_challenge != 0`.
    #[must_use]
    pub const fn quic_challenge_matched_b126(response_token: u64, expected_challenge: u64) -> bool
    clauses [ensures result == (expected_challenge != 0 && response_token == expected_challenge)]
    {
        expected_challenge != 0 && response_token == expected_challenge
    }
}

/// Candidate network path awaiting `PATH_RESPONSE` validation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct PendingPathProbe {
    path_tuple_fp: u64,
    challenge_token: u64,
    bytes_received: u64,
    bytes_sent: u64,
}

/// Outcome of probing, sending on, or validating a roaming QUIC path.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuicRoamOutcome {
    ChallengeIssued {
        candidate_path_fp: u64,
        challenge_token: u64,
    },
    UnvalidatedSendBudgeted {
        admitted_bytes: u64,
        anti_amp_ceiling: u64,
    },
    MigratedZeroGap {
        active_path_fp: u64,
        roam_generation: u64,
        contiguous_stream_offset: u64,
    },
    RefusedChallengeMismatch,
    RefusedZeroChallengeToken,
}

/// Zero-gap QUIC connection migration & path-validation state machine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct QuicPathRoamMigrator {
    active_path_fp: u64,
    roam_generation: u64,
    contiguous_stream_offset: u64,
    pending_probe: Option<PendingPathProbe>,
}

impl QuicPathRoamMigrator {
    #[must_use]
    pub const fn new(initial_path_fp: u64, initial_stream_offset: u64) -> Self {
        Self {
            active_path_fp: initial_path_fp,
            roam_generation: 0,
            contiguous_stream_offset: initial_stream_offset,
            pending_probe: None,
        }
    }

    #[must_use]
    pub const fn active_path_fp(&self) -> u64 {
        self.active_path_fp
    }

    #[must_use]
    pub const fn contiguous_stream_offset(&self) -> u64 {
        self.contiguous_stream_offset
    }

    /// Observe packets from a new peer address tuple and initiate `PATH_CHALLENGE`.
    pub fn begin_path_probe(
        &mut self,
        candidate_path_fp: u64,
        challenge_token: u64,
        initial_rx_bytes: u64,
    ) -> QuicRoamOutcome {
        if challenge_token == 0 {
            return QuicRoamOutcome::RefusedZeroChallengeToken;
        }
        self.pending_probe = Some(PendingPathProbe {
            path_tuple_fp: candidate_path_fp,
            challenge_token,
            bytes_received: initial_rx_bytes,
            bytes_sent: 0,
        });
        QuicRoamOutcome::ChallengeIssued {
            candidate_path_fp,
            challenge_token,
        }
    }

    /// Budget outbound bytes on the unvalidated candidate path under RFC 9000's 3x amplification cap.
    pub fn budget_unvalidated_send(&mut self, requested_bytes: u64) -> QuicRoamOutcome {
        let Some(probe) = &mut self.pending_probe else {
            return QuicRoamOutcome::UnvalidatedSendBudgeted {
                admitted_bytes: 0,
                anti_amp_ceiling: 0,
            };
        };
        let ceiling = probe.bytes_received.saturating_mul(3);
        let desired_total = probe.bytes_sent.saturating_add(requested_bytes);
        let next_sent = quic_anti_amp_clamp_b126(desired_total, ceiling);
        let admitted = next_sent.saturating_sub(probe.bytes_sent);
        probe.bytes_sent = next_sent;
        QuicRoamOutcome::UnvalidatedSendBudgeted {
            admitted_bytes: admitted,
            anti_amp_ceiling: ceiling,
        }
    }

    /// Validate `PATH_RESPONSE` and atomically cut over to the new path with zero stream-offset gap.
    pub fn complete_path_response(
        &mut self,
        response_token: u64,
        stream_offset_at_cutover: u64,
    ) -> QuicRoamOutcome {
        let Some(probe) = self.pending_probe else {
            return QuicRoamOutcome::RefusedChallengeMismatch;
        };
        if !quic_challenge_matched_b126(response_token, probe.challenge_token) {
            return QuicRoamOutcome::RefusedChallengeMismatch;
        }
        self.active_path_fp = probe.path_tuple_fp;
        self.roam_generation = quic_roam_gen_advance_b126(
            self.roam_generation,
            self.roam_generation.saturating_add(1),
        );
        self.contiguous_stream_offset =
            quic_stream_off_advance_b126(self.contiguous_stream_offset, stream_offset_at_cutover);
        self.pending_probe = None;
        QuicRoamOutcome::MigratedZeroGap {
            active_path_fp: self.active_path_fp,
            roam_generation: self.roam_generation,
            contiguous_stream_offset: self.contiguous_stream_offset,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_three_times_anti_amplification_before_validation_and_migrates_with_zero_gap() {
        let mut mig = QuicPathRoamMigrator::new(0x0A00_0001, 4_096);
        assert_eq!(
            mig.begin_path_probe(0xAC10_0009, 0x9988_7766_5544_3322, 1_200),
            QuicRoamOutcome::ChallengeIssued {
                candidate_path_fp: 0xAC10_0009,
                challenge_token: 0x9988_7766_5544_3322,
            }
        );

        // 1_200 rx bytes -> 3_600 tx anti-amplification ceiling!
        assert_eq!(
            mig.budget_unvalidated_send(2_500),
            QuicRoamOutcome::UnvalidatedSendBudgeted {
                admitted_bytes: 2_500,
                anti_amp_ceiling: 3_600,
            }
        );
        assert_eq!(
            mig.budget_unvalidated_send(2_500),
            QuicRoamOutcome::UnvalidatedSendBudgeted {
                admitted_bytes: 1_100,
                anti_amp_ceiling: 3_600,
            }
        );

        // Wrong token rejected; active path unchanged.
        assert_eq!(
            mig.complete_path_response(0x1111, 8_192),
            QuicRoamOutcome::RefusedChallengeMismatch
        );
        assert_eq!(mig.active_path_fp(), 0x0A00_0001);

        // Matching PATH_RESPONSE completes zero-gap migration at stream offset 8_192.
        assert_eq!(
            mig.complete_path_response(0x9988_7766_5544_3322, 8_192),
            QuicRoamOutcome::MigratedZeroGap {
                active_path_fp: 0xAC10_0009,
                roam_generation: 1,
                contiguous_stream_offset: 8_192,
            }
        );
    }
}
