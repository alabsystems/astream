// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! At-rest AEAD log-position & `LogIdentity` AAD binder
//! (`Astream.Aead.TlaAtRestSegmentAadBinder`).
//!
//! Closes the at-rest encryption AAD log-binding gap (`docs/AUDIT-2026-09.md`): binds every
//! encrypted WAL frame's AEAD Additional Authenticated Data (`[u8; 32]`) to `(lineage_tag,
//! segment_base_offset, frame_seq, payload_len)`, rejecting out-of-order, replayed, or
//! cross-segment spliced ciphertext frames before plaintext release.

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "at_rest_segment_aad_binder_island.rs"]
mod at_rest_segment_aad_binder_island;
#[cfg(clean_islands)]
pub use at_rest_segment_aad_binder_island::{
    aad_frame_seq_advance_b118, aad_payload_len_clamp_b118,
};

#[cfg(not(clean_islands))]
/// Clamp authenticated frame payload length to `max_frame_bytes`.
#[must_use]
pub const fn aad_payload_len_clamp_b118(payload_len: u64, max_frame_bytes: u64) -> u64 {
    if payload_len < max_frame_bytes {
        payload_len
    } else {
        max_frame_bytes
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `next_frame_seq`.
#[must_use]
pub const fn aad_frame_seq_advance_b118(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}

contract_fn! {
    /// True iff `frame_seq` is at or above `segment_base_offset`.
    #[must_use]
    pub const fn aad_seq_in_segment_b118(frame_seq: u64, segment_base_offset: u64) -> bool
    clauses [ensures result == (segment_base_offset <= frame_seq)]
    {
        segment_base_offset <= frame_seq
    }
}

/// Canonical 32-byte AAD block binding a ciphertext frame to its exact log lineage & offset.
#[must_use]
pub fn encode_segment_frame_aad(
    lineage_tag: u64,
    segment_base_offset: u64,
    frame_seq: u64,
    clamped_payload_len: u64,
) -> [u8; 32] {
    let a = lineage_tag.to_le_bytes();
    let b = segment_base_offset.to_le_bytes();
    let c = frame_seq.to_le_bytes();
    let d = clamped_payload_len.to_le_bytes();
    [
        a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], b[0], b[1], b[2], b[3], b[4], b[5], b[6],
        b[7], c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7], d[0], d[1], d[2], d[3], d[4], d[5],
        d[6], d[7],
    ]
}

/// Verification outcome before AEAD decryption of an at-rest WAL frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AtRestAadVerdict {
    BoundAad {
        aad: [u8; 32],
        next_seq: u64,
    },
    RejectedCrossLineage,
    RejectedOutOfOrderSeq {
        expected_seq: u64,
        found_seq: u64,
    },
    RejectedOversizedFrame {
        payload_len: u64,
        max_frame_bytes: u64,
    },
}

/// Stateful at-rest segment AAD binder tracking expected `frame_seq` progression.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AtRestSegmentAadBinder {
    lineage_tag: u64,
    segment_base_offset: u64,
    next_frame_seq: u64,
    max_frame_bytes: u64,
}

impl AtRestSegmentAadBinder {
    #[must_use]
    pub const fn new(lineage_tag: u64, segment_base_offset: u64, max_frame_bytes: u64) -> Self {
        let cap = if max_frame_bytes == 0 {
            16 * 1024 * 1024
        } else {
            max_frame_bytes
        };
        Self {
            lineage_tag,
            segment_base_offset,
            next_frame_seq: segment_base_offset,
            max_frame_bytes: cap,
        }
    }

    #[must_use]
    pub const fn next_frame_seq(&self) -> u64 {
        self.next_frame_seq
    }

    /// Derive the exact 32-byte AAD for `frame_seq` and advance `next_frame_seq`.
    pub fn bind_next_frame(
        &mut self,
        presented_lineage_tag: u64,
        frame_seq: u64,
        payload_len: u64,
    ) -> AtRestAadVerdict {
        if presented_lineage_tag != self.lineage_tag {
            return AtRestAadVerdict::RejectedCrossLineage;
        }
        if !aad_seq_in_segment_b118(frame_seq, self.segment_base_offset)
            || frame_seq != self.next_frame_seq
        {
            return AtRestAadVerdict::RejectedOutOfOrderSeq {
                expected_seq: self.next_frame_seq,
                found_seq: frame_seq,
            };
        }
        if payload_len > self.max_frame_bytes {
            return AtRestAadVerdict::RejectedOversizedFrame {
                payload_len,
                max_frame_bytes: self.max_frame_bytes,
            };
        }
        let clamped_len = aad_payload_len_clamp_b118(payload_len, self.max_frame_bytes);
        let aad = encode_segment_frame_aad(
            self.lineage_tag,
            self.segment_base_offset,
            frame_seq,
            clamped_len,
        );
        let cand_next = self.next_frame_seq.saturating_add(1);
        self.next_frame_seq = aad_frame_seq_advance_b118(self.next_frame_seq, cand_next);
        AtRestAadVerdict::BoundAad {
            aad,
            next_seq: self.next_frame_seq,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn binds_lineage_and_rejects_reordered_or_cross_log_frames() {
        let mut b = AtRestSegmentAadBinder::new(0xABCD_1234, 100, 4096);
        assert!(matches!(
            b.bind_next_frame(0xABCD_1234, 100, 512),
            AtRestAadVerdict::BoundAad { next_seq: 101, .. }
        ));
        assert_eq!(
            b.bind_next_frame(0xABCD_1234, 100, 512),
            AtRestAadVerdict::RejectedOutOfOrderSeq {
                expected_seq: 101,
                found_seq: 100,
            }
        );
        assert_eq!(
            b.bind_next_frame(0xDEAD_BEEF, 101, 512),
            AtRestAadVerdict::RejectedCrossLineage
        );
    }
}
