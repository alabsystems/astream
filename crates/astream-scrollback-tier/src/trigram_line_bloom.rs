// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! 64-bit ASCII trigram Bloom filter per cold scrollback block enabling instant `Cmd+F` search
//! skipping over non-matching compressed blocks without decompression (`Astream.ScrollTier.TlaTrigramLineBloom`).

#[cfg(clean_islands)]
#[path = "trigram_line_bloom_island.rs"]
mod trigram_line_bloom_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sb_hits_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sb_idx_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use trigram_line_bloom_island::{sb_hits_clamp, sb_idx_advance};

/// Maximum indexed trigrams per query (`4_096`).
pub const MAX_QUERY_TRIGRAMS: u64 = 4_096;

contract_fn! {
    /// Verified Bloom bitmask inclusion check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `sb_bloom_may_match_isl`.
    #[must_use]
    pub const fn sb_bloom_may_match(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct TrigramBloom64 {
    bits: u64,
    lines_indexed: u64,
}

impl TrigramBloom64 {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            bits: 0,
            lines_indexed: 0,
        }
    }

    #[must_use]
    const fn trigram_mask(a: u8, b: u8, c: u8) -> u64 {
        let h1 = ((a as u64)
            .wrapping_mul(31)
            .wrapping_add(b as u64)
            .wrapping_mul(31)
            .wrapping_add(c as u64))
            & 63;
        let h2 = ((c as u64)
            .wrapping_mul(131)
            .wrapping_add(a as u64)
            .wrapping_add(b as u64))
            & 63;
        (1u64 << (h1 & 63)) | (1u64 << (h2 & 63))
    }

    #[must_use]
    pub fn mask_for_bytes(text: &[u8]) -> u64 {
        let mut mask = 0u64;
        let mut w0: Option<u8> = None;
        let mut w1: Option<u8> = None;
        let mut count = 0u64;
        for &byte in text {
            let fold = byte.to_ascii_lowercase();
            if let (Some(a), Some(b)) = (w0, w1) {
                if count < MAX_QUERY_TRIGRAMS {
                    mask |= Self::trigram_mask(a, b, fold);
                    count = count.saturating_add(1);
                }
            }
            w0 = w1;
            w1 = Some(fold);
        }
        let _ = sb_hits_clamp(count, MAX_QUERY_TRIGRAMS);
        mask
    }

    pub fn index_line(&mut self, line: &[u8]) {
        self.bits |= Self::mask_for_bytes(line);
        self.lines_indexed =
            sb_idx_advance(self.lines_indexed, self.lines_indexed.saturating_add(1));
    }

    #[must_use]
    pub fn may_contain(&self, needle: &[u8]) -> bool {
        let qmask = Self::mask_for_bytes(needle);
        let overlap = (self.bits & qmask) == qmask;
        sb_bloom_may_match(if overlap { 1 } else { 0 }, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bloom_filter_matches_indexed_substrings_and_skips_disjoint_queries() {
        let mut b = TrigramBloom64::new();
        b.index_line(b"error[E0502]: cannot borrow self as mutable");
        assert!(b.may_contain(b"borrow"));
        assert!(b.may_contain(b"E0502"));
        assert!(!b.may_contain(b"panicked at"));
    }
}
