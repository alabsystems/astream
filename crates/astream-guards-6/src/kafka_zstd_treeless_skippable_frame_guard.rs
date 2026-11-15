// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! RFC 8878 Zstandard `Treeless` repeat-Huffman, skippable-frame, & `xxhash64` checksum guard
//! (`evidence/manifest.toml` `kafka.handshake-and-metadata`;
//! `Astream.Kafka.TlaKafkaZstdTreelessSkippableFrameGuard`).
//!
//! Enforces RFC 8878 Zstandard decompression safety on Kafka `RecordBatch v2` (`codec = 4`):
//! - Skippable frames (`0x184D_2A50 ..= 0x184D_2A5F`) advance the input cursor cleanly without
//!   carrying Huffman state across frame boundaries,
//! - Within a Zstandard frame (`0xFD2F_B528`), a `Treeless_Literals_Block` (`block_type == 3`)
//!   is admissible ONLY after an earlier `Compressed_Literals_Block` (`block_type == 2`) in the
//!   SAME frame populated `has_huffman_table == true`,
//! - Total decompressed output across concatenated frames is capped at `MAX_ZSTD_BATCH_BYTES`
//!   (`16 MiB`), and when `has_content_checksum` is set, the low 32 bits of `xxhash64` must match!

#[cfg(clean_islands)]
#[path = "kafka_zstd_treeless_skippable_frame_guard_island.rs"]
mod kafka_zstd_treeless_skippable_frame_guard_island;
#[cfg(clean_islands)]
pub use kafka_zstd_treeless_skippable_frame_guard_island::{
    zstd_blocks_decoded_advance_b155, zstd_output_bytes_clamp_b155,
};

/// Standard Zstandard frame magic (`0xFD2F_B528`).
pub const ZSTD_FRAME_MAGIC: u64 = 0xFD2F_B528;
/// Skippable frame magic range (`0x184D_2A50 ..= 0x184D_2A5F`).
pub const ZSTD_SKIPPABLE_MIN: u64 = 0x184D_2A50;
pub const ZSTD_SKIPPABLE_MAX: u64 = 0x184D_2A5F;
/// Decompressed batch byte ceiling (`16 MiB`).
pub const MAX_ZSTD_BATCH_BYTES: u64 = 16 * 1024 * 1024;

#[cfg(not(clean_islands))]
/// Clamp decompressed Zstd output byte total to `MAX_ZSTD_BATCH_BYTES`.
#[must_use]
pub const fn zstd_output_bytes_clamp_b155(cand_bytes: u64, max_bytes: u64) -> u64 {
    if cand_bytes < max_bytes {
        cand_bytes
    } else {
        max_bytes
    }
}

#[cfg(not(clean_islands))]
/// Advance decoded Zstandard block counter monotonically.
#[must_use]
pub const fn zstd_blocks_decoded_advance_b155(cur_blocks: u64, cand_blocks: u64) -> u64 {
    if cur_blocks < cand_blocks {
        cand_blocks
    } else {
        cur_blocks
    }
}

contract_fn! {
    /// True iff `magic` lies in the 16-value RFC 8878 skippable frame range.
    #[must_use]
    pub const fn is_zstd_skippable_magic_b155(magic: u64) -> bool
    clauses [ensures result == (magic >= 0x184D_2A50 && magic <= 0x184D_2A5F)]
    {
        magic >= ZSTD_SKIPPABLE_MIN && magic <= ZSTD_SKIPPABLE_MAX
    }
}

/// Decision for RFC 8878 Zstandard frame headers, `Treeless` literal blocks, and trailers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ZstdFrameGuardDecision {
    SkippedMetadataFrame,
    BeganStandardFrameResetHuffman,
    AdmittedLiteralBlock {
        has_huffman_table: bool,
        decompressed_bytes: u64,
        blocks_decoded: u64,
    },
    CompletedFrameVerifiedChecksum {
        decompressed_bytes: u64,
    },
    RefusedUnknownFrameMagic {
        magic: u64,
    },
    RefusedTreelessWithoutPriorHuffmanTable,
    RefusedDecompressedSizeExceeded {
        max_bytes: u64,
    },
    RefusedContentChecksumMismatch,
}

/// Stateful RFC 8878 Zstandard multi-frame & `Treeless` Huffman state guard.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KafkaZstdFrameGuard {
    has_huffman_table: bool,
    decompressed_bytes: u64,
    blocks_decoded: u64,
}

impl KafkaZstdFrameGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            has_huffman_table: false,
            decompressed_bytes: 0,
            blocks_decoded: 0,
        }
    }

    /// Inspect a 32-bit frame magic header across concatenated streams.
    pub fn on_frame_magic(&mut self, magic: u64) -> ZstdFrameGuardDecision {
        self.has_huffman_table = false;
        if is_zstd_skippable_magic_b155(magic) {
            ZstdFrameGuardDecision::SkippedMetadataFrame
        } else if magic == ZSTD_FRAME_MAGIC {
            ZstdFrameGuardDecision::BeganStandardFrameResetHuffman
        } else {
            ZstdFrameGuardDecision::RefusedUnknownFrameMagic { magic }
        }
    }

    /// Validate literal block (`is_compressed_new_table`, `is_treeless_repeat`) and output budget.
    pub fn on_literal_block(
        &mut self,
        is_compressed_new_table: bool,
        is_treeless_repeat: bool,
        block_out_bytes: u64,
    ) -> ZstdFrameGuardDecision {
        if is_treeless_repeat && !self.has_huffman_table {
            return ZstdFrameGuardDecision::RefusedTreelessWithoutPriorHuffmanTable;
        }
        let next_bytes = self.decompressed_bytes.saturating_add(block_out_bytes);
        if next_bytes > MAX_ZSTD_BATCH_BYTES {
            return ZstdFrameGuardDecision::RefusedDecompressedSizeExceeded {
                max_bytes: MAX_ZSTD_BATCH_BYTES,
            };
        }
        if is_compressed_new_table {
            self.has_huffman_table = true;
        }
        self.decompressed_bytes = zstd_output_bytes_clamp_b155(next_bytes, MAX_ZSTD_BATCH_BYTES);
        let next_blks = self.blocks_decoded.saturating_add(1);
        self.blocks_decoded = zstd_blocks_decoded_advance_b155(self.blocks_decoded, next_blks);
        ZstdFrameGuardDecision::AdmittedLiteralBlock {
            has_huffman_table: self.has_huffman_table,
            decompressed_bytes: self.decompressed_bytes,
            blocks_decoded: self.blocks_decoded,
        }
    }

    /// Verify optional 32-bit `xxhash64` content checksum at end of frame.
    #[must_use]
    pub const fn finish_frame(
        &self,
        has_checksum_flag: bool,
        expected_xxh32: u32,
        computed_xxh32: u32,
    ) -> ZstdFrameGuardDecision {
        if has_checksum_flag && expected_xxh32 != computed_xxh32 {
            ZstdFrameGuardDecision::RefusedContentChecksumMismatch
        } else {
            ZstdFrameGuardDecision::CompletedFrameVerifiedChecksum {
                decompressed_bytes: self.decompressed_bytes,
            }
        }
    }
}

impl Default for KafkaZstdFrameGuard {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn skips_skippable_frames_requires_prior_huffman_for_treeless_and_resets_per_frame() {
        let mut g = KafkaZstdFrameGuard::new();
        assert_eq!(
            g.on_frame_magic(0x184D_2A55),
            ZstdFrameGuardDecision::SkippedMetadataFrame
        );
        assert_eq!(
            g.on_frame_magic(ZSTD_FRAME_MAGIC),
            ZstdFrameGuardDecision::BeganStandardFrameResetHuffman
        );
        // Treeless block #1 before any Compressed Huffman table -> refused!
        assert_eq!(
            g.on_literal_block(false, true, 1024),
            ZstdFrameGuardDecision::RefusedTreelessWithoutPriorHuffmanTable
        );
        // Block #1 populates Huffman table, Block #2 (>128 KiB multi-block) reuses Treeless!
        g.on_literal_block(true, false, 131_072);
        assert_eq!(
            g.on_literal_block(false, true, 32_768),
            ZstdFrameGuardDecision::AdmittedLiteralBlock {
                has_huffman_table: true,
                decompressed_bytes: 163_840,
                blocks_decoded: 2,
            }
        );
        // Next concatenated frame resets `has_huffman_table`!
        g.on_frame_magic(ZSTD_FRAME_MAGIC);
        assert_eq!(
            g.on_literal_block(false, true, 512),
            ZstdFrameGuardDecision::RefusedTreelessWithoutPriorHuffmanTable
        );
    }
}
