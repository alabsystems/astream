// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Cross-face `ACK_SEQ_BASE` (`1 << 63`) producer-sequence namespace partition guard
//! (`evidence/manifest.toml` `broker.ack-key-is-one-wire-contract`,
//! `DESIGN-aterm-fabric.md` §14; `Astream.Wire.TlaAckSeqBaseNamespaceGuard`).
//!
//! Enforces strict disjointness between ordinary producer sequences (`0 .. ACK_SEQ_BASE`)
//! and cross-face `client::ack` / `asb ack` / `ProcessAndProduce` sequences
//! (`ACK_SEQ_BASE | input_offset`):
//! - Ordinary `publish` / `retire` sequences `>= ACK_SEQ_BASE` (`0x8000_0000_0000_0000`)
//!   are refused before touching the wire so a hand-picked producer sequence can never
//!   collide with an ack of input offset `seq & !ACK_SEQ_BASE`.
//! - Cross-face ack derivation accepts only `input_offset < ACK_SEQ_BASE` and produces
//!   `ACK_SEQ_BASE | input_offset >= ACK_SEQ_BASE`.
//!
//! Zero heap allocations, zero loops, zero `Display`/`Hash` impls — preserves `astream-wire`
//! `unknown == 0` and `runtime_checked <= 110`.

#[cfg(clean_islands)]
#[path = "ack_seq_base_namespace_guard_island.rs"]
mod ack_seq_base_namespace_guard_island;
#[cfg(clean_islands)]
pub use ack_seq_base_namespace_guard_island::{
    ack_input_offset_clamp_b147, ordinary_seq_advance_b147,
};

/// High-bit namespace separator reserving `[2^63, 2^64)` for cross-face acks.
pub const ACK_SEQ_BASE_GUARD: u64 = 1u64 << 63;

/// Maximum legal ordinary publish/retire sequence (`(1 << 63) - 1`).
pub const MAX_ORDINARY_PRODUCER_SEQ: u64 = ACK_SEQ_BASE_GUARD - 1;

#[cfg(not(clean_islands))]
/// Clamp an input offset to `max_input_offset` (`MAX_ORDINARY_PRODUCER_SEQ`).
#[must_use]
pub const fn ack_input_offset_clamp_b147(cand_offset: u64, max_input_offset: u64) -> u64 {
    if cand_offset < max_input_offset {
        cand_offset
    } else {
        max_input_offset
    }
}

#[cfg(not(clean_islands))]
/// Advance highest admitted ordinary producer sequence monotonically.
#[must_use]
pub const fn ordinary_seq_advance_b147(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}

contract_fn! {
    /// True iff `seq` lies strictly inside the ordinary producer namespace `[0, ACK_SEQ_BASE)`.
    #[must_use]
    pub const fn is_ordinary_producer_seq_b147(seq: u64, ack_seq_base: u64) -> bool
    clauses [ensures result == (seq < ack_seq_base)]
    {
        seq < ack_seq_base
    }
}

/// Verdict when checking an ordinary publish sequence or deriving a cross-face ack sequence.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum AckSeqNamespaceDecision {
    AdmittedOrdinaryPublish {
        producer_seq: u64,
        high_ordinary_seq: u64,
    },
    DerivedCrossFaceAckSeq {
        input_offset: u64,
        ack_producer_seq: u64,
    },
    RefusedOrdinarySeqInAckNamespace {
        rejected_seq: u64,
    },
    RefusedInputOffsetOverflow {
        rejected_offset: u64,
    },
}

/// Tracks ordinary publish sequence watermark while guarding the `ACK_SEQ_BASE` boundary.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct AckSeqNamespaceGuard {
    high_ordinary_seq: u64,
}

impl AckSeqNamespaceGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            high_ordinary_seq: 0,
        }
    }

    #[must_use]
    pub const fn high_ordinary_seq(&self) -> u64 {
        ack_input_offset_clamp_b147(self.high_ordinary_seq, MAX_ORDINARY_PRODUCER_SEQ)
    }

    /// Gate an ordinary `Publish` / `Retire` sequence before writing to the wire.
    pub fn check_ordinary_publish_seq(&mut self, seq: u64) -> AckSeqNamespaceDecision {
        if !is_ordinary_producer_seq_b147(seq, ACK_SEQ_BASE_GUARD) {
            return AckSeqNamespaceDecision::RefusedOrdinarySeqInAckNamespace { rejected_seq: seq };
        }
        let clamped = ack_input_offset_clamp_b147(seq, MAX_ORDINARY_PRODUCER_SEQ);
        self.high_ordinary_seq = ordinary_seq_advance_b147(self.high_ordinary_seq, clamped);
        AckSeqNamespaceDecision::AdmittedOrdinaryPublish {
            producer_seq: clamped,
            high_ordinary_seq: self.high_ordinary_seq,
        }
    }

    /// Derive the canonical cross-face ack sequence `ACK_SEQ_BASE | input_offset`.
    #[must_use]
    pub const fn derive_cross_face_ack_seq(&self, input_offset: u64) -> AckSeqNamespaceDecision {
        if !is_ordinary_producer_seq_b147(input_offset, ACK_SEQ_BASE_GUARD) {
            return AckSeqNamespaceDecision::RefusedInputOffsetOverflow {
                rejected_offset: input_offset,
            };
        }
        let safe_off = ack_input_offset_clamp_b147(input_offset, MAX_ORDINARY_PRODUCER_SEQ);
        AckSeqNamespaceDecision::DerivedCrossFaceAckSeq {
            input_offset: safe_off,
            ack_producer_seq: ACK_SEQ_BASE_GUARD | safe_off,
        }
    }
}

impl Default for AckSeqNamespaceGuard {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn partitions_ordinary_publishes_from_cross_face_ack_sequences() {
        let mut g = AckSeqNamespaceGuard::new();
        assert_eq!(
            g.check_ordinary_publish_seq(5),
            AckSeqNamespaceDecision::AdmittedOrdinaryPublish {
                producer_seq: 5,
                high_ordinary_seq: 5,
            }
        );
        assert_eq!(
            g.derive_cross_face_ack_seq(5),
            AckSeqNamespaceDecision::DerivedCrossFaceAckSeq {
                input_offset: 5,
                ack_producer_seq: ACK_SEQ_BASE_GUARD | 5,
            }
        );
        assert_eq!(
            g.check_ordinary_publish_seq(ACK_SEQ_BASE_GUARD | 5),
            AckSeqNamespaceDecision::RefusedOrdinarySeqInAckNamespace {
                rejected_seq: ACK_SEQ_BASE_GUARD | 5,
            }
        );
    }
}
