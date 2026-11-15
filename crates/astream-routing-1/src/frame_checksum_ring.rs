// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pure stack 8-slot rolling frame checksum continuity ring (`Astream.Wire.TlaFrameChecksumRing`).
//!
//! Designed for `aterm-restore` and WAN stream splicing: tracks a monotonic
//! frame sequence and cumulative FNV-1a chain digest over `(frame_seq, payload_crc)`
//! in a fixed stack ring (`[ChecksumSlot; 8]`) with **zero heap allocations**.

#[cfg(clean_islands)]
#[path = "frame_checksum_ring_island.rs"]
mod frame_checksum_ring_island;
#[cfg(clean_islands)]
pub use frame_checksum_ring_island::{checksum_seq_advance, checksum_slot_clamp};

/// Fixed capacity of the stack frame-checksum continuity ring.
pub const FRAME_RING_CAP: usize = 8;

/// 16-byte fixed wire bookmark magic (`"AFCR"`).
pub const FRAME_RING_MAGIC: [u8; 4] = *b"AFCR";

const FNV_OFFSET_BASIS: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

#[cfg(not(clean_islands))]
/// Monotonically advance the expected next frame sequence.
#[must_use]
pub const fn checksum_seq_advance(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}

#[cfg(not(clean_islands))]
/// Clamp occupied ring slot count to `ring_cap`.
#[must_use]
pub const fn checksum_slot_clamp(cand_count: u64, ring_cap: u64) -> u64 {
    if cand_count < ring_cap {
        cand_count
    } else {
        ring_cap
    }
}

contract_fn! {
    /// True iff `observed_seq` matches `expected_seq` with no gap or duplicate.
    #[must_use]
    pub const fn checksum_seq_contiguous(expected_seq: u64, observed_seq: u64) -> bool
    clauses [ensures result == (expected_seq == observed_seq)]
    {
        expected_seq == observed_seq
    }
}

/// One stack-resident frame continuity checkpoint.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ChecksumSlot {
    pub seq: u64,
    pub payload_crc: u32,
    pub chain_digest: u64,
}

impl ChecksumSlot {
    pub const EMPTY: Self = Self {
        seq: 0,
        payload_crc: 0,
        chain_digest: FNV_OFFSET_BASIS,
    };
}

/// Refusal reasons when verifying or splicing frame continuity.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum FrameContinuityError {
    SequenceMismatch { expected: u64, observed: u64 },
    AnchorNotFound { seq: u64 },
    ChainDigestMismatch { seq: u64 },
    InvalidBookmarkMagic,
}

const fn mix_u64(mut h: u64, v: u64) -> u64 {
    let [b0, b1, b2, b3, b4, b5, b6, b7] = v.to_le_bytes();
    h = (h ^ (b0 as u64)).wrapping_mul(FNV_PRIME);
    h = (h ^ (b1 as u64)).wrapping_mul(FNV_PRIME);
    h = (h ^ (b2 as u64)).wrapping_mul(FNV_PRIME);
    h = (h ^ (b3 as u64)).wrapping_mul(FNV_PRIME);
    h = (h ^ (b4 as u64)).wrapping_mul(FNV_PRIME);
    h = (h ^ (b5 as u64)).wrapping_mul(FNV_PRIME);
    h = (h ^ (b6 as u64)).wrapping_mul(FNV_PRIME);
    h = (h ^ (b7 as u64)).wrapping_mul(FNV_PRIME);
    h
}

/// Pure stack 8-slot rolling checksum ring.
#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub struct FrameChecksumRing {
    slots: [ChecksumSlot; FRAME_RING_CAP],
    head: usize,
    occupied: u64,
    next_seq: u64,
    chain_digest: u64,
}

impl Default for FrameChecksumRing {
    fn default() -> Self {
        Self::new()
    }
}

impl FrameChecksumRing {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            slots: [ChecksumSlot::EMPTY; FRAME_RING_CAP],
            head: 0,
            occupied: 0,
            next_seq: 0,
            chain_digest: FNV_OFFSET_BASIS,
        }
    }

    #[must_use]
    pub const fn next_seq(&self) -> u64 {
        self.next_seq
    }

    #[must_use]
    pub const fn occupied(&self) -> u64 {
        self.occupied
    }

    #[must_use]
    pub const fn chain_digest(&self) -> u64 {
        self.chain_digest
    }

    /// Append the next contiguous frame `(seq, payload_crc)` and return its chain digest.
    pub fn record_frame(
        &mut self,
        seq: u64,
        payload_crc: u32,
    ) -> Result<u64, FrameContinuityError> {
        if !checksum_seq_contiguous(self.next_seq, seq) {
            return Err(FrameContinuityError::SequenceMismatch {
                expected: self.next_seq,
                observed: seq,
            });
        }
        let next_digest = mix_u64(mix_u64(self.chain_digest, seq), payload_crc as u64);
        let slot_idx = self.head & (FRAME_RING_CAP - 1);
        if let Some(slot) = self.slots.get_mut(slot_idx) {
            *slot = ChecksumSlot {
                seq,
                payload_crc,
                chain_digest: next_digest,
            };
        }
        self.head = self.head.wrapping_add(1) & (FRAME_RING_CAP - 1);
        let cand_occ = self.occupied.saturating_add(1);
        self.occupied = checksum_slot_clamp(cand_occ, FRAME_RING_CAP as u64);
        let cand_seq = seq.saturating_add(1);
        self.next_seq = checksum_seq_advance(self.next_seq, cand_seq);
        self.chain_digest = next_digest;
        Ok(next_digest)
    }

    /// Verify that a peer's reconnect anchor `(anchor_seq, anchor_digest)` matches our retained ring.
    pub fn verify_splice_anchor(
        &self,
        anchor_seq: u64,
        anchor_digest: u64,
    ) -> Result<(), FrameContinuityError> {
        let max_scan = self.occupied as usize;
        let mut scanned = 0usize;
        let mut rest = self.slots.as_slice();
        while let &[slot, ref tail @ ..] = rest {
            if scanned >= max_scan {
                break;
            }
            if slot.seq == anchor_seq {
                if slot.chain_digest == anchor_digest {
                    return Ok(());
                }
                return Err(FrameContinuityError::ChainDigestMismatch { seq: anchor_seq });
            }
            scanned = scanned.saturating_add(1);
            rest = tail;
        }
        Err(FrameContinuityError::AnchorNotFound { seq: anchor_seq })
    }

    /// Encode the latest continuity tip as a 20-byte fixed wire bookmark (`magic[4] || next_seq[8] || digest[8]`).
    #[must_use]
    pub const fn encode_tip_bookmark(&self) -> [u8; 20] {
        let [m0, m1, m2, m3] = FRAME_RING_MAGIC;
        let [s0, s1, s2, s3, s4, s5, s6, s7] = self.next_seq.to_le_bytes();
        let [d0, d1, d2, d3, d4, d5, d6, d7] = self.chain_digest.to_le_bytes();
        [
            m0, m1, m2, m3, s0, s1, s2, s3, s4, s5, s6, s7, d0, d1, d2, d3, d4, d5, d6, d7,
        ]
    }

    /// Decode a 20-byte fixed wire continuity tip bookmark into `(next_seq, chain_digest)`.
    pub const fn decode_tip_bookmark(buf: &[u8; 20]) -> Result<(u64, u64), FrameContinuityError> {
        let &[m0, m1, m2, m3, s0, s1, s2, s3, s4, s5, s6, s7, d0, d1, d2, d3, d4, d5, d6, d7] = buf;
        let [em0, em1, em2, em3] = FRAME_RING_MAGIC;
        if m0 != em0 || m1 != em1 || m2 != em2 || m3 != em3 {
            return Err(FrameContinuityError::InvalidBookmarkMagic);
        }
        let seq = u64::from_le_bytes([s0, s1, s2, s3, s4, s5, s6, s7]);
        let digest = u64::from_le_bytes([d0, d1, d2, d3, d4, d5, d6, d7]);
        Ok((seq, digest))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ring_tracks_contiguous_frames_and_verifies_splice_anchor() {
        let mut ring = FrameChecksumRing::new();
        let mut d3 = 0u64;
        for seq in 0..10u64 {
            let d = ring
                .record_frame(seq, (seq as u32).wrapping_mul(17))
                .unwrap();
            if seq == 5 {
                d3 = d;
            }
        }
        assert_eq!(ring.next_seq(), 10);
        assert_eq!(ring.occupied(), FRAME_RING_CAP as u64);
        // Seq 5 is within the latest 8 frames (2..=9)
        assert_eq!(ring.verify_splice_anchor(5, d3), Ok(()));
        assert_eq!(
            ring.verify_splice_anchor(5, d3 ^ 1),
            Err(FrameContinuityError::ChainDigestMismatch { seq: 5 })
        );
        // Seq 1 was evicted by the 8-slot ring
        assert_eq!(
            ring.verify_splice_anchor(1, d3),
            Err(FrameContinuityError::AnchorNotFound { seq: 1 })
        );
        // Gap frame is rejected
        assert_eq!(
            ring.record_frame(11, 0),
            Err(FrameContinuityError::SequenceMismatch {
                expected: 10,
                observed: 11,
            })
        );

        let bm = ring.encode_tip_bookmark();
        assert_eq!(
            FrameChecksumRing::decode_tip_bookmark(&bm),
            Ok((10, ring.chain_digest()))
        );
    }
}
