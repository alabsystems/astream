// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Domain-separated at-rest log-extent AAD binder & torn-zero tail classifier
//! (`Astream.Aead.TlaAtRestExtentAad`).
//!
//! Binds every at-rest encrypted log record's AEAD tag to a canonical 36-byte
//! Additional Authenticated Data block (`"ASA1" || log_id[16] || generation_le[8] || record_offset_le[8]`)
//! so cross-log block splicing, generation rollback, and intra-log record reordering
//! fail AEAD tag authentication immediately.
//!
//! Also classifies trailing bytes after the last authenticated record on crash recovery:
//! distinguishing power-loss preallocated zero extents (`AtRestTailKind::ZeroedPreallocTail`)
//! from non-zero torn frames or tampered ciphertext without depending on `astream-digest`
//! (compiling cleanly in base `astream-aead` with default features disabled, and `0 mandated`).

#[cfg(clean_islands)]
#[path = "extent_aad_island.rs"]
mod extent_aad_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn extent_offset_advance(cur_off: u64, cand_off: u64) -> u64 {
    if cur_off < cand_off {
        cand_off
    } else {
        cur_off
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn extent_gen_advance(cur_gen: u64, cand_gen: u64) -> u64 {
    if cur_gen < cand_gen {
        cand_gen
    } else {
        cur_gen
    }
}
#[cfg(clean_islands)]
pub use extent_aad_island::{extent_gen_advance, extent_offset_advance};

/// 4-byte domain-separation magic (`"ASA1"`) for at-rest log-extent AAD blocks.
pub const EXTENT_AAD_MAGIC: [u8; 4] = *b"ASA1";

/// Fixed length of an encoded [`ExtentAad`] block (`4 + 16 + 8 + 8 = 36` bytes).
pub const EXTENT_AAD_LEN: usize = 36;

contract_fn! {
    /// Kernel-certified strict offset progression check (`prev_off < cand_off`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `extent_offset_strictly_next_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn extent_offset_strictly_next(prev_off: u64, cand_off: u64) -> bool
    clauses [ensures result == (prev_off < cand_off)]
    {
        prev_off < cand_off
    }
}

/// Canonical 36-byte Additional Authenticated Data binding a sealed record to a
/// specific `(log_id, generation, record_offset)` coordinate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExtentAad {
    pub log_id: [u8; 16],
    pub generation: u64,
    pub record_offset: u64,
}

impl ExtentAad {
    /// Construct an extent AAD descriptor.
    #[must_use]
    pub const fn new(log_id: [u8; 16], generation: u64, record_offset: u64) -> Self {
        Self {
            log_id,
            generation,
            record_offset,
        }
    }

    /// Serialize into canonical 36-byte `"ASA1"` AAD bytes.
    #[must_use]
    pub const fn to_bytes(&self) -> [u8; EXTENT_AAD_LEN] {
        let l = self.log_id;
        let g = self.generation.to_le_bytes();
        let o = self.record_offset.to_le_bytes();
        [
            EXTENT_AAD_MAGIC[0],
            EXTENT_AAD_MAGIC[1],
            EXTENT_AAD_MAGIC[2],
            EXTENT_AAD_MAGIC[3],
            l[0],
            l[1],
            l[2],
            l[3],
            l[4],
            l[5],
            l[6],
            l[7],
            l[8],
            l[9],
            l[10],
            l[11],
            l[12],
            l[13],
            l[14],
            l[15],
            g[0],
            g[1],
            g[2],
            g[3],
            g[4],
            g[5],
            g[6],
            g[7],
            o[0],
            o[1],
            o[2],
            o[3],
            o[4],
            o[5],
            o[6],
            o[7],
        ]
    }

    /// Decode a 36-byte `"ASA1"` AAD block, rejecting bad length or magic.
    pub fn from_bytes(buf: &[u8]) -> Result<Self, &'static str> {
        let &[m0, m1, m2, m3, l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, g0, g1, g2, g3, g4, g5, g6, g7, o0, o1, o2, o3, o4, o5, o6, o7] =
            buf
        else {
            return Err("invalid ExtentAad length");
        };
        if [m0, m1, m2, m3] != EXTENT_AAD_MAGIC {
            return Err("invalid ExtentAad magic");
        }
        Ok(Self {
            log_id: [
                l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15,
            ],
            generation: u64::from_le_bytes([g0, g1, g2, g3, g4, g5, g6, g7]),
            record_offset: u64::from_le_bytes([o0, o1, o2, o3, o4, o5, o6, o7]),
        })
    }
}

/// Monotone cursor guarding sequential at-rest sealing for one `(log_id, generation)` stream.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExtentSealCursor {
    log_id: [u8; 16],
    generation: u64,
    last_offset: Option<u64>,
}

impl ExtentSealCursor {
    /// Initialize a seal cursor for `log_id` at `generation`.
    #[must_use]
    pub const fn new(log_id: [u8; 16], generation: u64) -> Self {
        Self {
            log_id,
            generation,
            last_offset: None,
        }
    }

    /// Current generation bound into emitted AAD blocks.
    #[must_use]
    pub const fn generation(&self) -> u64 {
        self.generation
    }

    /// Last sealed record offset, if at least one record has been sealed.
    #[must_use]
    pub const fn last_offset(&self) -> Option<u64> {
        self.last_offset
    }

    /// Advance `generation` monotonically (`cand_gen >= self.generation`), rejecting rollbacks.
    pub fn advance_generation(&mut self, cand_gen: u64) -> Result<u64, &'static str> {
        if cand_gen < self.generation {
            return Err("extent generation rollback refused");
        }
        self.generation = extent_gen_advance(self.generation, cand_gen);
        Ok(self.generation)
    }

    /// Produce the 36-byte AAD for `cand_offset`, enforcing strict monotonic progression
    /// (`cand_offset > prev_offset`).
    pub fn next_aad(&mut self, cand_offset: u64) -> Result<[u8; EXTENT_AAD_LEN], &'static str> {
        if let Some(prev) = self.last_offset {
            if !extent_offset_strictly_next(prev, cand_offset) {
                return Err("non-monotonic extent record_offset refused");
            }
            let adv = extent_offset_advance(prev, cand_offset);
            self.last_offset = Some(adv);
        } else {
            self.last_offset = Some(cand_offset);
        }
        Ok(ExtentAad::new(self.log_id, self.generation, cand_offset).to_bytes())
    }
}

/// Classification of trailing unauthenticated bytes at the end of an at-rest sealed file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AtRestTailKind {
    /// Exact EOF (`0` trailing bytes).
    CleanEof,
    /// Every trailing byte is `0x00` (unwritten preallocated extent after power loss).
    ZeroedPreallocTail { zero_bytes: usize },
    /// Non-zero trailing bytes shorter than `declared_frame_len` (torn write mid-append).
    TornFramePrefix { present_bytes: usize },
    /// Full-length non-zero frame whose AEAD authentication failed (corruption or tampering).
    CorruptOrTamperedFrame,
}

/// Classify `tail` bytes at the end of a sealed log file given an optional `declared_frame_len`
/// parsed from its length prefix (folding all bytes without data-dependent early exit on zeros).
#[must_use]
pub fn classify_at_rest_tail(tail: &[u8], declared_frame_len: Option<usize>) -> AtRestTailKind {
    if tail.is_empty() {
        return AtRestTailKind::CleanEof;
    }
    let mut all_zero = true;
    let mut i = 0usize;
    while i < tail.len() {
        if let Some(&b) = tail.get(i) {
            all_zero = if b != 0 { false } else { all_zero };
        }
        i = i.saturating_add(1);
    }
    if all_zero {
        return AtRestTailKind::ZeroedPreallocTail {
            zero_bytes: tail.len(),
        };
    }
    match declared_frame_len {
        Some(expected) if tail.len() >= expected => AtRestTailKind::CorruptOrTamperedFrame,
        _ => AtRestTailKind::TornFramePrefix {
            present_bytes: tail.len(),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn aad_binds_log_generation_and_monotonic_offsets_and_classifies_tails() {
        let log_id = [0x7Au8; 16];
        let mut cur = ExtentSealCursor::new(log_id, 2);

        let aad0 = cur.next_aad(0).unwrap();
        let aad1 = cur.next_aad(1).unwrap();
        assert_ne!(aad0, aad1);
        assert!(cur.next_aad(1).is_err());
        assert!(cur.next_aad(0).is_err());
        assert!(cur.advance_generation(1).is_err());
        assert_eq!(cur.advance_generation(3).unwrap(), 3);

        let parsed = ExtentAad::from_bytes(&aad1).unwrap();
        assert_eq!(parsed, ExtentAad::new(log_id, 2, 1));

        assert_eq!(classify_at_rest_tail(&[], None), AtRestTailKind::CleanEof);
        assert_eq!(
            classify_at_rest_tail(&[0u8; 4096], Some(64)),
            AtRestTailKind::ZeroedPreallocTail { zero_bytes: 4096 }
        );
        assert_eq!(
            classify_at_rest_tail(&[0x12, 0x34, 0x00], Some(64)),
            AtRestTailKind::TornFramePrefix { present_bytes: 3 }
        );
        assert_eq!(
            classify_at_rest_tail(&[0x12; 64], Some(64)),
            AtRestTailKind::CorruptOrTamperedFrame
        );
    }
}
