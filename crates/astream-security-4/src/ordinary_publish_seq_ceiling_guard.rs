// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Library-enforced `2^63` ordinary-publish sequence ceiling & will/ack namespace partition guard
//! (`docs/DESIGN-aterm-fabric.md` §11.1 boundary 3, §14 lines 3908–3910;
//! `Astream.Broker.TlaOrdinaryPublishSeqCeilingGuard`).
//!
//! Closes the library-caller obligation noted in §14:
//! - Partition `[0, 2^63 - 1]` is reserved for ordinary `Publish` sequences AND incarnation-fenced
//!   `Will` sequences (`(inc << 32) | 0xFFFF_FFFF < 2^63`),
//! - Partition `[2^63, 2^64 - 1]` (`ACK_SEQ_BASE | target_offset`) is reserved exclusively for
//!   correlation acks (`RETIRE_PRODUCER_SEQ = u64::MAX` is also excluded from ordinary publishes),
//! - Refuses any `Client::publish` call whose `producer_seq >= ACK_SEQ_BASE` before wire send so an
//!   embedder can never pollute the ack keyspace or disable will high-watermarks!

#[cfg(clean_islands)]
#[path = "ordinary_publish_seq_ceiling_guard_island.rs"]
mod ordinary_publish_seq_ceiling_guard_island;
#[cfg(clean_islands)]
pub use ordinary_publish_seq_ceiling_guard_island::{
    ordinary_seq_clamp_b127, ordinary_will_hw_advance_b127,
};

#[cfg(not(clean_islands))]
/// Clamp an ordinary publish sequence into `[0, max_ordinary_seq]` (`2^63 - 1`).
#[must_use]
pub const fn ordinary_seq_clamp_b127(cand_seq: u64, max_ordinary_seq: u64) -> u64 {
    if cand_seq < max_ordinary_seq {
        cand_seq
    } else {
        max_ordinary_seq
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the producer's lower-half high-watermark read by the will fence.
#[must_use]
pub const fn ordinary_will_hw_advance_b127(cur_hw: u64, cand_seq: u64) -> u64 {
    if cur_hw < cand_seq {
        cand_seq
    } else {
        cur_hw
    }
}

contract_fn! {
    /// True iff `seq` lies strictly below `ACK_SEQ_BASE` (`seq < (1u64 << 63)`).
    #[must_use]
    pub const fn ordinary_seq_in_lower_half_b127(seq: u64, ack_seq_base: u64) -> bool
    clauses [ensures result == (seq < ack_seq_base)]
    {
        seq < ack_seq_base
    }
}

pub const ACK_SEQ_NAMESPACE_BASE: u64 = 1u64 << 63;
pub const MAX_ORDINARY_PRODUCER_SEQ: u64 = ACK_SEQ_NAMESPACE_BASE - 1;

/// Admission verdict for an embedder/library sequence key.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProducerSeqVerdict {
    AdmittedOrdinary {
        seq: u64,
        will_high_water: u64,
    },
    AdmittedAckKey {
        ack_seq: u64,
        correlated_offset: u64,
        will_high_water: u64,
    },
    RefusedOrdinaryInReservedUpperHalf {
        attempted_seq: u64,
    },
    RefusedAckTargetOverflow {
        target_offset: u64,
    },
}

/// Per-producer sequence-partition guard enforcing `< 2^63` on ordinary publishes and wills.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OrdinaryPublishSeqCeilingGuard {
    will_high_water: u64,
    max_ordinary_seq: u64,
}

impl OrdinaryPublishSeqCeilingGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            will_high_water: 0,
            max_ordinary_seq: MAX_ORDINARY_PRODUCER_SEQ,
        }
    }

    #[must_use]
    pub const fn will_high_water(&self) -> u64 {
        self.will_high_water
    }

    /// Validate an ordinary `Client::publish` or `Will` sequence (`must be < 2^63`).
    pub fn check_ordinary_publish(&mut self, seq: u64) -> ProducerSeqVerdict {
        if !ordinary_seq_in_lower_half_b127(seq, ACK_SEQ_NAMESPACE_BASE) {
            return ProducerSeqVerdict::RefusedOrdinaryInReservedUpperHalf { attempted_seq: seq };
        }
        let clamped = ordinary_seq_clamp_b127(seq, self.max_ordinary_seq);
        self.will_high_water = ordinary_will_hw_advance_b127(self.will_high_water, clamped);
        ProducerSeqVerdict::AdmittedOrdinary {
            seq: clamped,
            will_high_water: self.will_high_water,
        }
    }

    /// Derive and validate a reserved upper-half ack sequence (`ACK_SEQ_BASE | target_offset`)
    /// without advancing `will_high_water` (§14 lines 3903–3908)!
    #[must_use]
    pub const fn derive_ack_seq(&self, target_offset: u64) -> ProducerSeqVerdict {
        if !ordinary_seq_in_lower_half_b127(target_offset, ACK_SEQ_NAMESPACE_BASE) {
            return ProducerSeqVerdict::RefusedAckTargetOverflow { target_offset };
        }
        let ack_seq = ACK_SEQ_NAMESPACE_BASE | target_offset;
        if ack_seq == u64::MAX {
            return ProducerSeqVerdict::RefusedAckTargetOverflow { target_offset };
        }
        ProducerSeqVerdict::AdmittedAckKey {
            ack_seq,
            correlated_offset: target_offset,
            will_high_water: self.will_high_water,
        }
    }
}

impl Default for OrdinaryPublishSeqCeilingGuard {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_upper_half_ordinary_publishes_and_keeps_acks_out_of_will_high_water() {
        let mut guard = OrdinaryPublishSeqCeilingGuard::new();

        // Ordinary publish at incarnation `(1 << 32) | 1` advances `will_high_water`.
        let inc1_live = (1u64 << 32) | 1;
        assert_eq!(
            guard.check_ordinary_publish(inc1_live),
            ProducerSeqVerdict::AdmittedOrdinary {
                seq: inc1_live,
                will_high_water: inc1_live,
            }
        );

        // Ordinary publish at or above `2^63` is refused at the library boundary!
        assert_eq!(
            guard.check_ordinary_publish(ACK_SEQ_NAMESPACE_BASE),
            ProducerSeqVerdict::RefusedOrdinaryInReservedUpperHalf {
                attempted_seq: ACK_SEQ_NAMESPACE_BASE,
            }
        );
        assert_eq!(
            guard.check_ordinary_publish(u64::MAX),
            ProducerSeqVerdict::RefusedOrdinaryInReservedUpperHalf {
                attempted_seq: u64::MAX,
            }
        );

        // Ack derivation sits in upper half and NEVER raises `will_high_water`!
        assert_eq!(
            guard.derive_ack_seq(777),
            ProducerSeqVerdict::AdmittedAckKey {
                ack_seq: ACK_SEQ_NAMESPACE_BASE | 777,
                correlated_offset: 777,
                will_high_water: inc1_live,
            }
        );
        // Incarnation 1's will `(1 << 32) | 0xFFFF_FFFF` is STILL `> will_high_water` and fires!
        let inc1_will = (1u64 << 32) | 0xFFFF_FFFF;
        assert!(inc1_will > guard.will_high_water());
    }
}
