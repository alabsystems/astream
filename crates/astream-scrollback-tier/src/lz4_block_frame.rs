// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Cold scrollback block frame header verifier checking compressed vs uncompressed byte bounds so
//! incompressible output falls back to raw storage without expansion (`Astream.ScrollTier.TlaLz4BlockFrame`).

#[cfg(clean_islands)]
#[path = "lz4_block_frame_island.rs"]
mod lz4_block_frame_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sb_blk_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sb_pack_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use lz4_block_frame_island::{sb_blk_clamp, sb_pack_advance};

/// Fixed cold scrollback uncompressed block ceiling (`65_536` bytes).
pub const MAX_COLD_BLOCK_BYTES: u64 = 65_536;

contract_fn! {
    /// Verified non-expanding compression check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `sb_frame_valid_isl`.
    #[must_use]
    pub const fn sb_frame_valid(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ColdBlockEncoding {
    Compressed,
    RawUncompressed,
}

#[derive(Debug, Clone, Default)]
pub struct ColdBlockPacker {
    blocks_sealed: u64,
}

impl ColdBlockPacker {
    #[must_use]
    pub const fn new() -> Self {
        Self { blocks_sealed: 0 }
    }

    pub fn choose_encoding(&mut self, raw_bytes: u64, compressed_bytes: u64) -> ColdBlockEncoding {
        self.blocks_sealed =
            sb_pack_advance(self.blocks_sealed, self.blocks_sealed.saturating_add(1));
        if raw_bytes == 0 || raw_bytes > MAX_COLD_BLOCK_BYTES {
            return ColdBlockEncoding::RawUncompressed;
        }
        let raw = sb_blk_clamp(raw_bytes, MAX_COLD_BLOCK_BYTES);
        if compressed_bytes > 0 && sb_frame_valid(raw, compressed_bytes.saturating_add(1)) {
            ColdBlockEncoding::Compressed
        } else {
            ColdBlockEncoding::RawUncompressed
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stores_raw_block_when_compression_does_not_shrink_payload() {
        let mut p = ColdBlockPacker::new();
        assert_eq!(
            p.choose_encoding(4_096, 1_120),
            ColdBlockEncoding::Compressed
        );
        assert_eq!(
            p.choose_encoding(4_096, 4_096),
            ColdBlockEncoding::RawUncompressed
        );
    }
}
