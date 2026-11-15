// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pure-Rust RFC 8878 Zstandard (`COMPRESSION_ZSTD = 4`) frame codec and 64-bit `xxHash64`
//! (`XXH64`) checksum implementation for Kafka `RecordBatch` v2 (`magic = 2`), with zero
//! third-party dependencies and `#![forbid(unsafe_code)]`.
//!
//! Decompression (`zstd_decompress`) is fail-closed and strictly bounded by
//! [`crate::compress::MAX_DECOMPRESSED_BATCH_BYTES`] (clamped via Clean-origin
//! [`crate::compress::kafka_decompress_cap_clamp`]), supporting:
//! - Multi-frame concatenation and skippable metadata frames (`0x184D2A50..=0x184D2A5F`),
//! - RFC 8878 Frame Header Descriptors (`Single_Segment_Flag`, `Window_Descriptor`,
//!   `Frame_Content_Size`, and `Content_Checksum_Flag` 32-bit `xxhash64(content, 0)` verification;
//!   external `Dictionary_ID` frames fail closed),
//! - `Raw_Block`, `RLE_Block`, and `Compressed_Block` payloads (`<= 128 KiB` per block),
//! - `Raw`, `RLE`, `Compressed` (1-stream & 4-stream canonical Huffman with direct 4-bit or
//!   interleaved two-state FSE-compressed weights), and `Treeless` (repeat Huffman) literals,
//! - Sequences section with `Predefined`, `RLE`, `FSE_Compressed`, and `Repeat` symbol modes and
//!   3-entry repeat-offset history (`[1, 4, 8]`).
//!
//! Compression (`zstd_compress`) emits standard RFC 8878 Zstandard frames carrying exact
//! `Frame_Content_Size`, `Content_Checksum_Flag = 1` (`xxhash64` low 32 bits), and LZ77 +
//! RFC 8878 `Predefined_Mode` ANS/FSE sequence-compressed blocks (with automatic `RLE_Block`
//! and `Raw_Block` fallback on uniform or incompressible inputs).

use crate::compress::{kafka_decompress_cap_clamp, DecompressError, MAX_DECOMPRESSED_BATCH_BYTES};

/// Standard RFC 8878 Zstandard 4-byte little-endian magic (`0xFD2FB528`).
pub const ZSTD_MAGIC_LE: [u8; 4] = [0x28, 0xB5, 0x2F, 0xFD];

const ZSTD_MAGIC_U32: u32 = 0xFD2F_B528;
const ZSTD_SKIPPABLE_MIN: u32 = 0x184D_2A50;
const ZSTD_SKIPPABLE_MAX: u32 = 0x184D_2A5F;

const MAX_ZSTD_BLOCK_SIZE: usize = 128 * 1024;
const MAX_ZSTD_WINDOW_BYTES: u64 = 32 * 1024 * 1024;

const PRIME64_1: u64 = 0x9E37_79B1_85EB_CA87;
const PRIME64_2: u64 = 0xC2B2_AE3D_27D4_EB4F;
const PRIME64_3: u64 = 0x1656_67B1_9E37_79F9;
const PRIME64_4: u64 = 0x85EB_CA77_C2B2_AE63;
const PRIME64_5: u64 = 0x27D4_EB2F_1656_67C5;

const LL_BITS: [u8; 36] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 3, 3, 4, 6, 7, 8, 9, 10, 11,
    12, 13, 14, 15, 16,
];

const LL_BASE: [u32; 36] = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 28, 32, 40, 48, 64,
    128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
];

const ML_BITS: [u8; 53] = [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1, 1, 1, 1, 2, 2, 3, 3, 4, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
];

const ML_BASE: [u32; 53] = [
    3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27,
    28, 29, 30, 31, 32, 33, 34, 35, 37, 39, 41, 43, 47, 51, 59, 67, 83, 99, 131, 259, 515, 1027,
    2051, 4099, 8195, 16387, 32771, 65539,
];

const LL_DEFAULT_NORM: [i16; 36] = [
    4, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 1, 1, 1, 1, 1,
    -1, -1, -1, -1,
];

const OF_DEFAULT_NORM: [i16; 29] = [
    1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1,
];

const ML_DEFAULT_NORM: [i16; 53] = [
    1, 4, 3, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1,
];

#[inline]
const fn u16_le(b0: u8, b1: u8) -> u16 {
    (b0 as u16) | ((b1 as u16) << 8)
}

#[inline]
const fn u32_le(b0: u8, b1: u8, b2: u8, b3: u8) -> u32 {
    (b0 as u32) | ((b1 as u32) << 8) | ((b2 as u32) << 16) | ((b3 as u32) << 24)
}

#[inline]
const fn u64_le(b: [u8; 8]) -> u64 {
    (b[0] as u64)
        | ((b[1] as u64) << 8)
        | ((b[2] as u64) << 16)
        | ((b[3] as u64) << 24)
        | ((b[4] as u64) << 32)
        | ((b[5] as u64) << 40)
        | ((b[6] as u64) << 48)
        | ((b[7] as u64) << 56)
}

#[inline]
const fn xxh64_round(acc: u64, lane: u64) -> u64 {
    acc.wrapping_add(lane.wrapping_mul(PRIME64_2))
        .rotate_left(31)
        .wrapping_mul(PRIME64_1)
}

#[inline]
const fn xxh64_merge_round(acc: u64, val: u64) -> u64 {
    (acc ^ xxh64_round(0, val))
        .wrapping_mul(PRIME64_1)
        .wrapping_add(PRIME64_4)
}

/// Compute the 64-bit `xxHash` (`XXH64`) digest of `data` with `seed` (RFC 8878 §3.1.1 uses
/// the low 32 bits of `xxhash64(content, 0)` as the Zstandard `Content_Checksum`).
#[must_use]
pub const fn xxhash64(data: &[u8], seed: u64) -> u64 {
    let total_len = data.len() as u64;
    let mut rest = data;
    let mut h64 = if data.len() >= 32 {
        let mut v1 = seed.wrapping_add(PRIME64_1).wrapping_add(PRIME64_2);
        let mut v2 = seed.wrapping_add(PRIME64_2);
        let mut v3 = seed;
        let mut v4 = seed.wrapping_sub(PRIME64_1);
        while let &[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, ref tail @ ..] =
            rest
        {
            v1 = xxh64_round(v1, u64_le([b0, b1, b2, b3, b4, b5, b6, b7]));
            v2 = xxh64_round(v2, u64_le([b8, b9, b10, b11, b12, b13, b14, b15]));
            v3 = xxh64_round(v3, u64_le([b16, b17, b18, b19, b20, b21, b22, b23]));
            v4 = xxh64_round(v4, u64_le([b24, b25, b26, b27, b28, b29, b30, b31]));
            rest = tail;
        }
        let mut merged = v1
            .rotate_left(1)
            .wrapping_add(v2.rotate_left(7))
            .wrapping_add(v3.rotate_left(12))
            .wrapping_add(v4.rotate_left(18));
        merged = xxh64_merge_round(merged, v1);
        merged = xxh64_merge_round(merged, v2);
        merged = xxh64_merge_round(merged, v3);
        xxh64_merge_round(merged, v4)
    } else {
        seed.wrapping_add(PRIME64_5)
    };

    h64 = h64.wrapping_add(total_len);

    while let &[b0, b1, b2, b3, b4, b5, b6, b7, ref tail @ ..] = rest {
        let k1 = xxh64_round(0, u64_le([b0, b1, b2, b3, b4, b5, b6, b7]));
        h64 = (h64 ^ k1)
            .rotate_left(27)
            .wrapping_mul(PRIME64_1)
            .wrapping_add(PRIME64_4);
        rest = tail;
    }

    if let &[b0, b1, b2, b3, ref tail @ ..] = rest {
        let k1 = (u32_le(b0, b1, b2, b3) as u64).wrapping_mul(PRIME64_1);
        h64 = (h64 ^ k1)
            .rotate_left(23)
            .wrapping_mul(PRIME64_2)
            .wrapping_add(PRIME64_3);
        rest = tail;
    }

    while let &[b0, ref tail @ ..] = rest {
        let k1 = (b0 as u64).wrapping_mul(PRIME64_5);
        h64 = (h64 ^ k1).rotate_left(11).wrapping_mul(PRIME64_1);
        rest = tail;
    }

    h64 ^= h64 >> 33;
    h64 = h64.wrapping_mul(PRIME64_2);
    h64 ^= h64 >> 29;
    h64 = h64.wrapping_mul(PRIME64_3);
    h64 ^ (h64 >> 32)
}

// ============================================================================
// Forward & Backward Bitstream Readers (RFC 8878 §4.1.1 & §4.2.2)
// ============================================================================

struct FwdBitReader<'a> {
    src: &'a [u8],
    bit_pos: usize,
}

impl<'a> FwdBitReader<'a> {
    const fn new(src: &'a [u8]) -> Self {
        Self { src, bit_pos: 0 }
    }

    fn peek_bits(&self, n: u32) -> Result<u32, DecompressError> {
        if n == 0 {
            return Ok(0);
        }
        if n > 24 {
            return Err(DecompressError::Corrupt);
        }
        let byte_idx = self.bit_pos >> 3;
        if byte_idx >= self.src.len() {
            return Err(DecompressError::Truncated);
        }
        let mut raw = 0u64;
        let mut k = 0usize;
        while k < 4 {
            if let Some(&b) = self.src.get(byte_idx.saturating_add(k)) {
                raw |= (b as u64) << (((k & 7) << 3) & 63);
            }
            k = k.saturating_add(1);
        }
        let shift = (self.bit_pos & 7) as u32;
        let mask = (1u64 << (n & 31)).wrapping_sub(1);
        Ok(((raw >> shift) & mask) as u32)
    }

    fn consume(&mut self, n: u32) -> Result<(), DecompressError> {
        let next = self.bit_pos.saturating_add(n as usize);
        if next > self.src.len().saturating_mul(8) {
            return Err(DecompressError::Truncated);
        }
        self.bit_pos = next;
        Ok(())
    }

    fn read_bits(&mut self, n: u32) -> Result<u32, DecompressError> {
        let v = self.peek_bits(n)?;
        self.consume(n)?;
        Ok(v)
    }

    const fn bytes_consumed(&self) -> usize {
        self.bit_pos.saturating_add(7) >> 3
    }
}

struct BackBitReader<'a> {
    src: &'a [u8],
    bits_left: usize,
}

impl<'a> BackBitReader<'a> {
    fn new(src: &'a [u8]) -> Result<Self, DecompressError> {
        let Some(&last) = src.last() else {
            return Err(DecompressError::Truncated);
        };
        if last == 0 {
            return Err(DecompressError::Corrupt);
        }
        let sentinel = 7usize.saturating_sub(last.leading_zeros() as usize);
        let full_bytes = src.len().saturating_sub(1);
        let bits_left = full_bytes.saturating_mul(8).saturating_add(sentinel);
        Ok(Self { src, bits_left })
    }

    const fn bits_left(&self) -> usize {
        self.bits_left
    }

    fn extract_at(&self, low_bit: usize, count: u32) -> u32 {
        if count == 0 {
            return 0;
        }
        let byte_idx = low_bit >> 3;
        let bit_off = (low_bit & 7) as u32;
        let mut raw = 0u64;
        let mut k = 0usize;
        while k < 5 {
            if let Some(&b) = self.src.get(byte_idx.saturating_add(k)) {
                raw |= (b as u64) << (((k & 7) << 3) & 63);
            }
            k = k.saturating_add(1);
        }
        let mask = if count >= 32 {
            u32::MAX as u64
        } else {
            (1u64 << (count & 31)).wrapping_sub(1)
        };
        ((raw >> bit_off) & mask) as u32
    }

    fn read_bits(&mut self, count: u32) -> Result<u32, DecompressError> {
        if count == 0 {
            return Ok(0);
        }
        if count > 31 || (count as usize) > self.bits_left {
            return Err(DecompressError::Corrupt);
        }
        let next = self.bits_left.saturating_sub(count as usize);
        let val = self.extract_at(next, count);
        self.bits_left = next;
        Ok(val)
    }

    fn peek_huf(&self, max_bits: u8) -> u32 {
        let mb = max_bits as usize;
        if self.bits_left >= mb {
            self.extract_at(self.bits_left.saturating_sub(mb), max_bits as u32)
        } else {
            let avail = self.bits_left as u32;
            let v = self.extract_at(0, avail);
            let pad = mb.saturating_sub(self.bits_left) as u32;
            v << (pad & 31)
        }
    }
}

// ============================================================================
// FSE Table Construction & Decoding (RFC 8878 §4.1.1)
// ============================================================================

#[derive(Clone, Copy)]
struct FseEntry {
    symbol: u8,
    num_bits: u8,
    baseline: u16,
}

#[derive(Clone)]
struct FseTable {
    acc_log: u8,
    entries: Vec<FseEntry>,
}

impl FseTable {
    fn from_rle(symbol: u8) -> Self {
        Self {
            acc_log: 0,
            entries: vec![FseEntry {
                symbol,
                num_bits: 0,
                baseline: 0,
            }],
        }
    }

    fn from_norm(acc_log: u8, norm: &[i16]) -> Result<Self, DecompressError> {
        if !matches!(acc_log, 5..=9) || norm.is_empty() || norm.len() > 256 {
            return Err(DecompressError::Corrupt);
        }
        let table_size = 1usize << (acc_log & 15);
        let mut sym_table = vec![0u8; table_size];
        let mut next_state = vec![0u16; norm.len()];
        let mut high = table_size;

        let mut s = 0usize;
        while s < norm.len() {
            let c = *norm.get(s).unwrap_or(&0);
            if c == -1 {
                if high == 0 {
                    return Err(DecompressError::Corrupt);
                }
                high = high.saturating_sub(1);
                if let Some(slot) = sym_table.get_mut(high) {
                    *slot = s as u8;
                }
                if let Some(ns) = next_state.get_mut(s) {
                    *ns = 1;
                }
            } else if c > 0 {
                if let Some(ns) = next_state.get_mut(s) {
                    *ns = c as u16;
                }
            }
            s = s.saturating_add(1);
        }

        let step = (table_size >> 1)
            .saturating_add(table_size >> 3)
            .saturating_add(3);
        let mask = table_size.saturating_sub(1);
        let mut pos = 0usize;
        let mut placed = 0usize;

        s = 0;
        while s < norm.len() {
            let c = *norm.get(s).unwrap_or(&0);
            if c > 0 {
                let mut k = 0i16;
                while k < c {
                    if placed >= high {
                        return Err(DecompressError::Corrupt);
                    }
                    if let Some(slot) = sym_table.get_mut(pos) {
                        *slot = s as u8;
                    }
                    placed = placed.saturating_add(1);
                    let mut guard = 0usize;
                    loop {
                        pos = pos.saturating_add(step) & mask;
                        if pos < high {
                            break;
                        }
                        guard = guard.saturating_add(1);
                        if guard > table_size {
                            return Err(DecompressError::Corrupt);
                        }
                    }
                    k = k.saturating_add(1);
                }
            }
            s = s.saturating_add(1);
        }
        if placed != high || pos != 0 || table_size > 512 {
            return Err(DecompressError::Corrupt);
        }

        let mut entries = Vec::with_capacity(table_size);
        let mut st = 0usize;
        while st < table_size {
            let sym = *sym_table.get(st).unwrap_or(&0);
            let cnt = *norm.get(sym as usize).unwrap_or(&0);
            if cnt == -1 {
                entries.push(FseEntry {
                    symbol: sym,
                    num_bits: acc_log,
                    baseline: 0,
                });
            } else {
                let x = *next_state
                    .get(sym as usize)
                    .ok_or(DecompressError::Corrupt)?;
                if x == 0 {
                    return Err(DecompressError::Corrupt);
                }
                if let Some(ns) = next_state.get_mut(sym as usize) {
                    *ns = x.saturating_add(1);
                }
                let highest_bit = 15u8.saturating_sub(x.leading_zeros() as u8);
                if highest_bit > acc_log {
                    return Err(DecompressError::Corrupt);
                }
                let nb = acc_log.saturating_sub(highest_bit);
                let base_usize = ((x as usize) << (nb & 15)).saturating_sub(table_size);
                entries.push(FseEntry {
                    symbol: sym,
                    num_bits: nb,
                    baseline: base_usize as u16,
                });
            }
            st = st.saturating_add(1);
        }

        Ok(Self { acc_log, entries })
    }

    fn decode_header(
        src: &[u8],
        max_sym: usize,
        max_acc_log: u8,
    ) -> Result<(Self, usize), DecompressError> {
        let mut r = FwdBitReader::new(src);
        let acc_log = (r.read_bits(4)? as u8).saturating_add(5);
        if acc_log > max_acc_log || acc_log > 9 {
            return Err(DecompressError::Corrupt);
        }
        let table_size = 1i32 << (acc_log & 15);
        let mut remaining = table_size.saturating_add(1);
        let mut norm = vec![0i16; max_sym.saturating_add(1)];
        let mut sym = 0usize;

        while remaining > 1 && sym <= max_sym {
            let rem_u32 = remaining as u32;
            let nb = 32u32.saturating_sub(rem_u32.leading_zeros());
            let thresh = ((1i32 << (nb & 15)).saturating_sub(1)).saturating_sub(remaining);
            let low = r.peek_bits(nb.saturating_sub(1))? as i32;
            let val = if low < thresh {
                r.consume(nb.saturating_sub(1))?;
                low
            } else {
                let full = r.read_bits(nb)? as i32;
                let half = 1i32 << (nb.saturating_sub(1) & 15);
                if full >= half {
                    full.saturating_sub(thresh)
                } else {
                    full
                }
            };
            let count = val.saturating_sub(1);
            if count < -1 || count >= table_size {
                return Err(DecompressError::Corrupt);
            }
            if let Some(slot) = norm.get_mut(sym) {
                *slot = count as i16;
            }
            sym = sym.saturating_add(1);
            let sub = if count == -1 { 1 } else { count };
            if sub >= remaining {
                return Err(DecompressError::Corrupt);
            }
            remaining = remaining.saturating_sub(sub);

            if count == 0 {
                loop {
                    let rep = r.read_bits(2)? as usize;
                    sym = sym.saturating_add(rep);
                    if rep < 3 || sym > max_sym.saturating_add(3) {
                        break;
                    }
                }
            }
        }

        if remaining != 1 || sym > max_sym.saturating_add(1) {
            return Err(DecompressError::Corrupt);
        }
        let used = r.bytes_consumed();
        let table = Self::from_norm(acc_log, &norm)?;
        Ok((table, used))
    }

    fn get(&self, state: usize) -> Result<FseEntry, DecompressError> {
        self.entries
            .get(state)
            .copied()
            .ok_or(DecompressError::Corrupt)
    }
}

// ============================================================================
// Zstandard Canonical Huffman Table (RFC 8878 §4.2.1)
// ============================================================================

#[derive(Clone, Copy)]
struct ZstdHufEntry {
    symbol: u8,
    num_bits: u8,
}

#[derive(Clone)]
struct ZstdHufTable {
    max_bits: u8,
    entries: Vec<ZstdHufEntry>,
}

impl ZstdHufTable {
    fn from_weights(weights_prefix: &[u8]) -> Result<Self, DecompressError> {
        if weights_prefix.is_empty() || weights_prefix.len() >= 256 {
            return Err(DecompressError::Corrupt);
        }
        let mut weight_sum = 0u32;
        for &w in weights_prefix {
            if w > 11 {
                return Err(DecompressError::Corrupt);
            }
            if w > 0 {
                weight_sum = weight_sum.saturating_add(1u32 << ((w - 1) & 15));
            }
        }
        if weight_sum == 0 {
            return Err(DecompressError::Corrupt);
        }
        let max_bits = 32u8.saturating_sub(weight_sum.leading_zeros() as u8);
        if max_bits == 0 || max_bits > 11 {
            return Err(DecompressError::Corrupt);
        }
        let total_cap = 1u32 << (max_bits & 15);
        if weight_sum >= total_cap {
            return Err(DecompressError::Corrupt);
        }
        let left_over = total_cap.saturating_sub(weight_sum);
        if !left_over.is_power_of_two() {
            return Err(DecompressError::Corrupt);
        }
        let last_weight = (left_over.trailing_zeros() as u8).saturating_add(1);
        if last_weight > max_bits {
            return Err(DecompressError::Corrupt);
        }

        let weights_cap = weights_prefix.len().saturating_add(1);
        if weights_cap > 256 {
            return Err(DecompressError::Corrupt);
        }
        let mut weights = Vec::with_capacity(weights_cap);
        weights.extend_from_slice(weights_prefix);
        weights.push(last_weight);

        let mut rank_count = [0usize; 12];
        for &w in &weights {
            if let Some(rc) = rank_count.get_mut(w as usize) {
                *rc = rc.saturating_add(1);
            }
        }

        let mut rank_idx = [0usize; 12];
        let mut cur = 0usize;
        let mut w = 1usize;
        while w <= (max_bits as usize) {
            let cnt = *rank_count.get(w).unwrap_or(&0);
            if let Some(ri) = rank_idx.get_mut(w) {
                *ri = cur;
            }
            let span = 1usize << (w.saturating_sub(1) & 15);
            cur = cur.saturating_add(cnt.saturating_mul(span));
            w = w.saturating_add(1);
        }
        let table_len = 1usize << (max_bits & 15);
        if cur != table_len || table_len > 2048 {
            return Err(DecompressError::Corrupt);
        }

        let mut entries = vec![
            ZstdHufEntry {
                symbol: 0,
                num_bits: 0
            };
            table_len
        ];
        for (sym, &sw) in weights.iter().enumerate() {
            if sw > 0 {
                let nb = max_bits.saturating_add(1).saturating_sub(sw);
                let span = 1usize << ((sw - 1) & 15);
                let start = *rank_idx.get(sw as usize).ok_or(DecompressError::Corrupt)?;
                let mut j = 0usize;
                while j < span {
                    let slot = entries
                        .get_mut(start.saturating_add(j))
                        .ok_or(DecompressError::Corrupt)?;
                    *slot = ZstdHufEntry {
                        symbol: sym as u8,
                        num_bits: nb,
                    };
                    j = j.saturating_add(1);
                }
                if let Some(ri) = rank_idx.get_mut(sw as usize) {
                    *ri = start.saturating_add(span);
                }
            }
        }

        Ok(Self { max_bits, entries })
    }

    fn decode_header(src: &[u8]) -> Result<(Self, usize), DecompressError> {
        let &[hdr, ref rest @ ..] = src else {
            return Err(DecompressError::Truncated);
        };
        if hdr >= 128 {
            let num_weights = (hdr - 127) as usize;
            let byte_len = num_weights.saturating_add(1) >> 1;
            let weight_bytes = rest.get(..byte_len).ok_or(DecompressError::Truncated)?;
            let mut weights = Vec::with_capacity(num_weights);
            let mut i = 0usize;
            while i < num_weights {
                let b = *weight_bytes.get(i >> 1).ok_or(DecompressError::Truncated)?;
                if (i & 1) == 0 {
                    weights.push(b >> 4);
                } else {
                    weights.push(b & 0x0F);
                }
                i = i.saturating_add(1);
            }
            let table = Self::from_weights(&weights)?;
            Ok((table, 1usize.saturating_add(byte_len)))
        } else {
            let comp_len = hdr as usize;
            if comp_len == 0 {
                return Err(DecompressError::Corrupt);
            }
            let body = rest.get(..comp_len).ok_or(DecompressError::Truncated)?;
            let (fse, used) = FseTable::decode_header(body, 12, 6)?;
            let stream = body.get(used..).ok_or(DecompressError::Corrupt)?;
            let mut br = BackBitReader::new(stream)?;
            let mut s1 = br.read_bits(fse.acc_log as u32)? as usize;
            let mut s2 = br.read_bits(fse.acc_log as u32)? as usize;
            let mut weights = Vec::new();
            loop {
                if weights.len() >= 255 {
                    return Err(DecompressError::Corrupt);
                }
                let e1 = fse.get(s1)?;
                weights.push(e1.symbol);
                if br.bits_left() < (e1.num_bits as usize) {
                    let e2 = fse.get(s2)?;
                    if weights.len() >= 255 {
                        return Err(DecompressError::Corrupt);
                    }
                    weights.push(e2.symbol);
                    break;
                }
                s1 = (e1.baseline as usize)
                    .saturating_add(br.read_bits(e1.num_bits as u32)? as usize);

                let e2 = fse.get(s2)?;
                if weights.len() >= 255 {
                    return Err(DecompressError::Corrupt);
                }
                weights.push(e2.symbol);
                if br.bits_left() < (e2.num_bits as usize) {
                    let e1_end = fse.get(s1)?;
                    if weights.len() >= 255 {
                        return Err(DecompressError::Corrupt);
                    }
                    weights.push(e1_end.symbol);
                    break;
                }
                s2 = (e2.baseline as usize)
                    .saturating_add(br.read_bits(e2.num_bits as u32)? as usize);
            }
            let table = Self::from_weights(&weights)?;
            Ok((table, 1usize.saturating_add(comp_len)))
        }
    }

    fn decode_stream(
        &self,
        stream: &[u8],
        expected_len: usize,
        out: &mut Vec<u8>,
    ) -> Result<(), DecompressError> {
        if expected_len == 0 {
            if !stream.is_empty() {
                return Err(DecompressError::Corrupt);
            }
            return Ok(());
        }
        let mut br = BackBitReader::new(stream)?;
        let start_len = out.len();
        while br.bits_left() > 0 {
            if out.len().saturating_sub(start_len) >= expected_len {
                return Err(DecompressError::Corrupt);
            }
            let idx = br.peek_huf(self.max_bits) as usize;
            let entry = self
                .entries
                .get(idx)
                .copied()
                .ok_or(DecompressError::Corrupt)?;
            if entry.num_bits == 0 || (entry.num_bits as usize) > br.bits_left() {
                return Err(DecompressError::Corrupt);
            }
            let _ = br.read_bits(entry.num_bits as u32)?;
            out.push(entry.symbol);
        }
        if out.len().saturating_sub(start_len) != expected_len {
            return Err(DecompressError::Corrupt);
        }
        Ok(())
    }
}

// ============================================================================
// Frame State & Block Decompression (RFC 8878 §3.1.1.3)
// ============================================================================

struct FrameState {
    rep: [usize; 3],
    huf: Option<ZstdHufTable>,
    ll_fse: Option<FseTable>,
    of_fse: Option<FseTable>,
    ml_fse: Option<FseTable>,
}

impl FrameState {
    const fn new() -> Self {
        Self {
            rep: [1, 4, 8],
            huf: None,
            ll_fse: None,
            of_fse: None,
            ml_fse: None,
        }
    }
}

#[inline]
fn zstd_peek_n<const N: usize>(buf: &[u8]) -> Result<[u8; N], DecompressError> {
    let head = buf.get(..N).ok_or(DecompressError::Truncated)?;
    let mut out = [0u8; N];
    out.copy_from_slice(head);
    Ok(out)
}

#[inline]
fn zstd_take_u8(buf: &[u8]) -> Result<(u8, &[u8]), DecompressError> {
    let b = *buf.first().ok_or(DecompressError::Truncated)?;
    let rest = buf.get(1..).ok_or(DecompressError::Truncated)?;
    Ok((b, rest))
}

#[inline]
fn zstd_take_u16_le(buf: &[u8]) -> Result<(u16, &[u8]), DecompressError> {
    let b = zstd_peek_n::<2>(buf)?;
    let rest = buf.get(2..).ok_or(DecompressError::Truncated)?;
    Ok((u16::from_le_bytes(b), rest))
}

#[inline]
fn zstd_take_u24_le(buf: &[u8]) -> Result<(u32, &[u8]), DecompressError> {
    let b = zstd_peek_n::<3>(buf)?;
    let rest = buf.get(3..).ok_or(DecompressError::Truncated)?;
    let v = (b[0] as u32) | ((b[1] as u32) << 8) | ((b[2] as u32) << 16);
    Ok((v, rest))
}

#[inline]
fn zstd_take_u32_le(buf: &[u8]) -> Result<(u32, &[u8]), DecompressError> {
    let b = zstd_peek_n::<4>(buf)?;
    let rest = buf.get(4..).ok_or(DecompressError::Truncated)?;
    Ok((u32::from_le_bytes(b), rest))
}

#[inline]
fn zstd_take_u64_le(buf: &[u8]) -> Result<(u64, &[u8]), DecompressError> {
    let b = zstd_peek_n::<8>(buf)?;
    let rest = buf.get(8..).ok_or(DecompressError::Truncated)?;
    Ok((u64::from_le_bytes(b), rest))
}

fn decode_raw_or_rle_literals(
    block: &[u8],
    b0: u8,
    lit_type: u8,
    size_fmt: u8,
) -> Result<(Vec<u8>, &[u8]), DecompressError> {
    let (hdr_len, regen_size) = if (size_fmt & 1) == 0 {
        (1usize, (b0 >> 3) as usize)
    } else if size_fmt == 1 {
        let h = zstd_peek_n::<2>(block)?;
        (2usize, ((h[0] >> 4) as usize) | ((h[1] as usize) << 4))
    } else {
        let h = zstd_peek_n::<3>(block)?;
        (
            3usize,
            ((h[0] >> 4) as usize) | ((h[1] as usize) << 4) | ((h[2] as usize) << 12),
        )
    };
    if regen_size > MAX_ZSTD_BLOCK_SIZE {
        return Err(DecompressError::Corrupt);
    }
    let after_hdr = block.get(hdr_len..).ok_or(DecompressError::Truncated)?;
    if lit_type == 0 {
        let raw = after_hdr
            .get(..regen_size)
            .ok_or(DecompressError::Truncated)?;
        let rest = after_hdr
            .get(regen_size..)
            .ok_or(DecompressError::Truncated)?;
        return Ok((raw.to_vec(), rest));
    }
    let (val, rest) = zstd_take_u8(after_hdr)?;
    Ok((vec![val; regen_size], rest))
}

fn parse_huf_literals_header(
    block: &[u8],
    size_fmt: u8,
) -> Result<(usize, usize, usize, usize), DecompressError> {
    if size_fmt == 0 || size_fmt == 1 {
        let h = zstd_peek_n::<3>(block)?;
        let u24 = (h[0] as usize) | ((h[1] as usize) << 8) | ((h[2] as usize) << 16);
        let streams = if size_fmt == 0 { 1usize } else { 4usize };
        Ok((3usize, streams, (u24 >> 4) & 0x3FF, u24 >> 14))
    } else if size_fmt == 2 {
        let h = zstd_peek_n::<4>(block)?;
        let u32v = u32::from_le_bytes(h) as usize;
        Ok((4usize, 4usize, (u32v >> 4) & 0x3FFF, u32v >> 18))
    } else {
        let h = zstd_peek_n::<5>(block)?;
        let u32_lo = u32::from_le_bytes([h[0], h[1], h[2], h[3]]) as u64;
        let u40 = u32_lo | ((h[4] as u64) << 32);
        Ok((
            5usize,
            4usize,
            ((u40 >> 4) & 0x3FFFF) as usize,
            ((u40 >> 22) & 0x3FFFF) as usize,
        ))
    }
}

fn decode_huf_four_streams(
    huf: &ZstdHufTable,
    streams_payload: &[u8],
    regen_size: usize,
    out: &mut Vec<u8>,
) -> Result<(), DecompressError> {
    if regen_size < 6 {
        return Err(DecompressError::Corrupt);
    }
    let (sz1_u16, c1) = zstd_take_u16_le(streams_payload)?;
    let (sz2_u16, c2) = zstd_take_u16_le(c1)?;
    let (sz3_u16, s_body) = zstd_take_u16_le(c2)?;
    let end1 = sz1_u16 as usize;
    let end2 = end1.saturating_add(sz2_u16 as usize);
    let end3 = end2.saturating_add(sz3_u16 as usize);
    if end3 > s_body.len() {
        return Err(DecompressError::Corrupt);
    }
    let s1 = s_body.get(..end1).ok_or(DecompressError::Corrupt)?;
    let s2 = s_body.get(end1..end2).ok_or(DecompressError::Corrupt)?;
    let s3 = s_body.get(end2..end3).ok_or(DecompressError::Corrupt)?;
    let s4 = s_body.get(end3..).ok_or(DecompressError::Corrupt)?;

    let chunk_len = regen_size.saturating_add(3) >> 2;
    let tail_len = regen_size.saturating_sub(chunk_len.saturating_mul(3));
    if chunk_len.saturating_mul(3).saturating_add(tail_len) != regen_size {
        return Err(DecompressError::Corrupt);
    }
    huf.decode_stream(s1, chunk_len, out)?;
    huf.decode_stream(s2, chunk_len, out)?;
    huf.decode_stream(s3, chunk_len, out)?;
    huf.decode_stream(s4, tail_len, out)
}

fn decode_literals_section<'a>(
    block: &'a [u8],
    state: &mut FrameState,
) -> Result<(Vec<u8>, &'a [u8]), DecompressError> {
    let b0 = *block.first().ok_or(DecompressError::Truncated)?;
    let lit_type = b0 & 3;
    let size_fmt = (b0 >> 2) & 3;

    if lit_type == 0 || lit_type == 1 {
        return decode_raw_or_rle_literals(block, b0, lit_type, size_fmt);
    }

    let (hdr_len, num_streams, regen_size, comp_size) = parse_huf_literals_header(block, size_fmt)?;
    if regen_size > MAX_ZSTD_BLOCK_SIZE {
        return Err(DecompressError::Corrupt);
    }
    let after_hdr = block.get(hdr_len..).ok_or(DecompressError::Truncated)?;
    let lit_payload = after_hdr
        .get(..comp_size)
        .ok_or(DecompressError::Truncated)?;
    let after_lit = after_hdr
        .get(comp_size..)
        .ok_or(DecompressError::Truncated)?;

    let streams_payload = if lit_type == 2 {
        let (table, used) = ZstdHufTable::decode_header(lit_payload)?;
        state.huf = Some(table);
        lit_payload.get(used..).ok_or(DecompressError::Corrupt)?
    } else {
        lit_payload
    };

    let Some(huf) = state.huf.as_ref() else {
        return Err(DecompressError::Corrupt);
    };

    let mut out = Vec::with_capacity(regen_size.min(MAX_ZSTD_BLOCK_SIZE));
    if num_streams == 1 {
        huf.decode_stream(streams_payload, regen_size, &mut out)?;
    } else {
        decode_huf_four_streams(huf, streams_payload, regen_size, &mut out)?;
    }

    Ok((out, after_lit))
}

fn select_seq_fse<'a>(
    mode: u8,
    src: &'a [u8],
    default_acc: u8,
    default_norm: &[i16],
    max_sym: usize,
    max_acc: u8,
    slot: &mut Option<FseTable>,
) -> Result<(FseTable, &'a [u8]), DecompressError> {
    match mode {
        0 => {
            let t = FseTable::from_norm(default_acc, default_norm)?;
            *slot = Some(t.clone());
            Ok((t, src))
        }
        1 => {
            let &[sym, ref rest @ ..] = src else {
                return Err(DecompressError::Truncated);
            };
            if (sym as usize) > max_sym {
                return Err(DecompressError::Corrupt);
            }
            let t = FseTable::from_rle(sym);
            *slot = Some(t.clone());
            Ok((t, rest))
        }
        2 => {
            let (t, used) = FseTable::decode_header(src, max_sym, max_acc)?;
            let rest = src.get(used..).ok_or(DecompressError::Truncated)?;
            *slot = Some(t.clone());
            Ok((t, rest))
        }
        3 => {
            let Some(prev) = slot.as_ref() else {
                return Err(DecompressError::Corrupt);
            };
            Ok((prev.clone(), src))
        }
        _ => Err(DecompressError::Corrupt),
    }
}

fn resolve_repeat_offset(
    offset_value: usize,
    literals_len: usize,
    rep: &mut [usize; 3],
) -> Result<usize, DecompressError> {
    if offset_value == 0 {
        return Err(DecompressError::Corrupt);
    }
    if offset_value > 3 {
        let actual = offset_value.saturating_sub(3);
        *rep = [actual, rep[0], rep[1]];
        return Ok(actual);
    }
    if literals_len == 0 {
        if offset_value == 1 {
            let actual = rep[1];
            *rep = [actual, rep[0], rep[2]];
            Ok(actual)
        } else if offset_value == 2 {
            let actual = rep[2];
            *rep = [actual, rep[0], rep[1]];
            Ok(actual)
        } else {
            if rep[0] <= 1 {
                return Err(DecompressError::Corrupt);
            }
            let actual = rep[0].saturating_sub(1);
            *rep = [actual, rep[0], rep[1]];
            Ok(actual)
        }
    } else if offset_value == 1 {
        Ok(rep[0])
    } else if offset_value == 2 {
        let actual = rep[1];
        *rep = [actual, rep[0], rep[2]];
        Ok(actual)
    } else {
        let actual = rep[2];
        *rep = [actual, rep[0], rep[1]];
        Ok(actual)
    }
}

fn decode_compressed_block(
    block: &[u8],
    state: &mut FrameState,
    out: &mut Vec<u8>,
    frame_start: usize,
    window_limit: usize,
    budget: usize,
) -> Result<(), DecompressError> {
    let block_out_start = out.len();
    let (literals, seq_src) = decode_literals_section(block, state)?;
    let &[s0, ref after_s0 @ ..] = seq_src else {
        return Err(DecompressError::Truncated);
    };

    let (num_seq, after_cnt) = if s0 == 0 {
        if !after_s0.is_empty() {
            return Err(DecompressError::Corrupt);
        }
        let next_len = out
            .len()
            .checked_add(literals.len())
            .ok_or(DecompressError::OutputTooLarge)?;
        if next_len > budget {
            return Err(DecompressError::OutputTooLarge);
        }
        out.extend_from_slice(&literals);
        return Ok(());
    } else if s0 < 128 {
        (s0 as usize, after_s0)
    } else if s0 < 255 {
        let &[s1, ref rest @ ..] = after_s0 else {
            return Err(DecompressError::Truncated);
        };
        ((((s0 - 128) as usize) << 8) | (s1 as usize), rest)
    } else {
        let &[s1, s2, ref rest @ ..] = after_s0 else {
            return Err(DecompressError::Truncated);
        };
        ((u16_le(s1, s2) as usize).saturating_add(0x7F00), rest)
    };

    let &[modes, ref after_modes @ ..] = after_cnt else {
        return Err(DecompressError::Truncated);
    };
    if (modes & 3) != 0 {
        return Err(DecompressError::Corrupt);
    }
    let ll_mode = (modes >> 6) & 3;
    let of_mode = (modes >> 4) & 3;
    let ml_mode = (modes >> 2) & 3;

    let (ll_fse, r1) = select_seq_fse(
        ll_mode,
        after_modes,
        6,
        &LL_DEFAULT_NORM,
        35,
        9,
        &mut state.ll_fse,
    )?;
    let (of_fse, r2) = select_seq_fse(of_mode, r1, 5, &OF_DEFAULT_NORM, 31, 8, &mut state.of_fse)?;
    let (ml_fse, seq_bits) =
        select_seq_fse(ml_mode, r2, 6, &ML_DEFAULT_NORM, 52, 9, &mut state.ml_fse)?;

    let mut br = BackBitReader::new(seq_bits)?;
    let mut ll_state = br.read_bits(ll_fse.acc_log as u32)? as usize;
    let mut of_state = br.read_bits(of_fse.acc_log as u32)? as usize;
    let mut ml_state = br.read_bits(ml_fse.acc_log as u32)? as usize;

    let mut lit_pos = 0usize;
    let mut seq_idx = 0usize;
    while seq_idx < num_seq {
        let ll_e = ll_fse.get(ll_state)?;
        let of_e = of_fse.get(of_state)?;
        let ml_e = ml_fse.get(ml_state)?;

        let of_code = of_e.symbol;
        if of_code > 31 {
            return Err(DecompressError::Corrupt);
        }
        let of_extra = br.read_bits(of_code as u32)? as usize;
        let offset_val = (1usize << (of_code & 31)).saturating_add(of_extra);

        let ml_code = ml_e.symbol as usize;
        let ml_nb = *ML_BITS.get(ml_code).ok_or(DecompressError::Corrupt)?;
        let ml_base = *ML_BASE.get(ml_code).ok_or(DecompressError::Corrupt)? as usize;
        let match_len = ml_base.saturating_add(br.read_bits(ml_nb as u32)? as usize);

        let ll_code = ll_e.symbol as usize;
        let ll_nb = *LL_BITS.get(ll_code).ok_or(DecompressError::Corrupt)?;
        let ll_base = *LL_BASE.get(ll_code).ok_or(DecompressError::Corrupt)? as usize;
        let lit_len = ll_base.saturating_add(br.read_bits(ll_nb as u32)? as usize);

        if seq_idx.saturating_add(1) < num_seq {
            ll_state = (ll_e.baseline as usize)
                .saturating_add(br.read_bits(ll_e.num_bits as u32)? as usize);
            ml_state = (ml_e.baseline as usize)
                .saturating_add(br.read_bits(ml_e.num_bits as u32)? as usize);
            of_state = (of_e.baseline as usize)
                .saturating_add(br.read_bits(of_e.num_bits as u32)? as usize);
        }

        let lit_end = lit_pos
            .checked_add(lit_len)
            .ok_or(DecompressError::Corrupt)?;
        let lit_slice = literals
            .get(lit_pos..lit_end)
            .ok_or(DecompressError::Corrupt)?;
        lit_pos = lit_end;

        let total_step = lit_len
            .checked_add(match_len)
            .ok_or(DecompressError::OutputTooLarge)?;
        let next_out_len = out
            .len()
            .checked_add(total_step)
            .ok_or(DecompressError::OutputTooLarge)?;
        if next_out_len > budget {
            return Err(DecompressError::OutputTooLarge);
        }
        if next_out_len.saturating_sub(block_out_start) > MAX_ZSTD_BLOCK_SIZE {
            return Err(DecompressError::Corrupt);
        }

        out.extend_from_slice(lit_slice);

        let actual_offset = resolve_repeat_offset(offset_val, lit_len, &mut state.rep)?;
        let frame_produced = out.len().saturating_sub(frame_start);
        if actual_offset == 0 || actual_offset > frame_produced || actual_offset > window_limit {
            return Err(DecompressError::Corrupt);
        }

        let mut copied = 0usize;
        while copied < match_len {
            let src_idx = out
                .len()
                .checked_sub(actual_offset)
                .ok_or(DecompressError::Corrupt)?;
            let b = *out.get(src_idx).ok_or(DecompressError::Corrupt)?;
            out.push(b);
            copied = copied.saturating_add(1);
        }

        seq_idx = seq_idx.saturating_add(1);
    }

    if br.bits_left() != 0 {
        return Err(DecompressError::Corrupt);
    }

    if let Some(rem_lit) = literals.get(lit_pos..) {
        let final_len = out
            .len()
            .checked_add(rem_lit.len())
            .ok_or(DecompressError::OutputTooLarge)?;
        if final_len > budget {
            return Err(DecompressError::OutputTooLarge);
        }
        if final_len.saturating_sub(block_out_start) > MAX_ZSTD_BLOCK_SIZE {
            return Err(DecompressError::Corrupt);
        }
        out.extend_from_slice(rem_lit);
    }

    Ok(())
}

struct ZstdParsedFrameHeader {
    has_checksum: bool,
    expected_fcs: Option<u64>,
    window_limit: usize,
}

fn parse_zstd_frame_header(
    after_magic: &[u8],
    cur_out_len: usize,
    budget: usize,
) -> Result<(ZstdParsedFrameHeader, &[u8]), DecompressError> {
    let (fhd, mut cur) = zstd_take_u8(after_magic)?;
    let dict_id_flag = fhd & 0x03;
    let has_checksum = (fhd & 0x04) != 0;
    let reserved_or_unused = (fhd & 0x18) != 0;
    let single_segment = (fhd & 0x20) != 0;
    let fcs_flag = (fhd >> 6) & 0x03;

    if reserved_or_unused {
        return Err(DecompressError::Corrupt);
    }

    let mut window_size = if !single_segment {
        let (wd, tail) = zstd_take_u8(cur)?;
        cur = tail;
        let exp = (wd >> 3) as u32;
        let mant = (wd & 7) as u64;
        let shift = 10u32.saturating_add(exp);
        if shift >= 60 {
            return Err(DecompressError::Corrupt);
        }
        let base = 1u64 << shift;
        base.saturating_add((base >> 3).saturating_mul(mant))
    } else {
        0u64
    };

    // External dictionaries are unsupported on Kafka RecordBatch v2 frames: fail closed
    // if a non-zero Dictionary_ID is present.
    let dict_id = match dict_id_flag {
        0 => 0u32,
        1 => {
            let (d0, tail) = zstd_take_u8(cur)?;
            cur = tail;
            d0 as u32
        }
        2 => {
            let (d16, tail) = zstd_take_u16_le(cur)?;
            cur = tail;
            d16 as u32
        }
        _ => {
            let (d32, tail) = zstd_take_u32_le(cur)?;
            cur = tail;
            d32
        }
    };
    if dict_id != 0 {
        return Err(DecompressError::Corrupt);
    }

    let expected_fcs: Option<u64> = match (fcs_flag, single_segment) {
        (0, false) => None,
        (0, true) => {
            let (c0, tail) = zstd_take_u8(cur)?;
            cur = tail;
            Some(c0 as u64)
        }
        (1, _) => {
            let (c16, tail) = zstd_take_u16_le(cur)?;
            cur = tail;
            Some((c16 as u64).saturating_add(256))
        }
        (2, _) => {
            let (c32, tail) = zstd_take_u32_le(cur)?;
            cur = tail;
            Some(c32 as u64)
        }
        _ => {
            let (c64, tail) = zstd_take_u64_le(cur)?;
            cur = tail;
            Some(c64)
        }
    };

    if let Some(fcs) = expected_fcs {
        if single_segment {
            window_size = fcs;
        }
        let needed = (cur_out_len as u64).saturating_add(fcs);
        if needed > (budget as u64) {
            return Err(DecompressError::OutputTooLarge);
        }
    }
    if window_size > MAX_ZSTD_WINDOW_BYTES {
        return Err(DecompressError::OutputTooLarge);
    }
    let window_limit = (window_size as usize).min(budget);

    Ok((
        ZstdParsedFrameHeader {
            has_checksum,
            expected_fcs,
            window_limit,
        },
        cur,
    ))
}

fn decode_zstd_frame_blocks<'a>(
    mut cur: &'a [u8],
    out: &mut Vec<u8>,
    frame_start: usize,
    window_limit: usize,
    budget: usize,
) -> Result<&'a [u8], DecompressError> {
    let mut state = FrameState::new();
    loop {
        let (bh, after_bh) = zstd_take_u24_le(cur)?;
        let last_block = (bh & 1) != 0;
        let block_type = (bh >> 1) & 3;
        let block_size = (bh >> 3) as usize;
        if block_size > MAX_ZSTD_BLOCK_SIZE {
            return Err(DecompressError::Corrupt);
        }

        if block_type == 0 {
            let raw = after_bh
                .get(..block_size)
                .ok_or(DecompressError::Truncated)?;
            let next_len = out
                .len()
                .checked_add(block_size)
                .ok_or(DecompressError::OutputTooLarge)?;
            if next_len > budget {
                return Err(DecompressError::OutputTooLarge);
            }
            out.extend_from_slice(raw);
            cur = after_bh
                .get(block_size..)
                .ok_or(DecompressError::Truncated)?;
        } else if block_type == 1 {
            let (val, tail) = zstd_take_u8(after_bh)?;
            let next_len = out
                .len()
                .checked_add(block_size)
                .ok_or(DecompressError::OutputTooLarge)?;
            if next_len > budget {
                return Err(DecompressError::OutputTooLarge);
            }
            let bounded_budget = MAX_DECOMPRESSED_BATCH_BYTES;
            if next_len > bounded_budget {
                return Err(DecompressError::OutputTooLarge);
            }
            let mut written = 0usize;
            while written < block_size {
                out.push(val);
                written = written.saturating_add(1);
            }
            cur = tail;
        } else if block_type == 2 {
            let comp = after_bh
                .get(..block_size)
                .ok_or(DecompressError::Truncated)?;
            decode_compressed_block(comp, &mut state, out, frame_start, window_limit, budget)?;
            cur = after_bh
                .get(block_size..)
                .ok_or(DecompressError::Truncated)?;
        } else {
            return Err(DecompressError::Corrupt);
        }

        if last_block {
            break;
        }
    }
    Ok(cur)
}

fn verify_zstd_frame_trailer<'a>(
    mut cur: &'a [u8],
    frame_slice: &[u8],
    hdr: &ZstdParsedFrameHeader,
) -> Result<&'a [u8], DecompressError> {
    if let Some(fcs) = hdr.expected_fcs {
        if (frame_slice.len() as u64) != fcs {
            return Err(DecompressError::Corrupt);
        }
    }
    if hdr.has_checksum {
        let (expected_csum, tail) = zstd_take_u32_le(cur)?;
        cur = tail;
        let actual_csum = xxhash64(frame_slice, 0) as u32;
        if expected_csum != actual_csum {
            return Err(DecompressError::Corrupt);
        }
    }
    Ok(cur)
}

/// Decompress one or more concatenated RFC 8878 Zstandard frames (and skippable metadata
/// frames) up to `min(max_out, MAX_DECOMPRESSED_BATCH_BYTES)` uncompressed bytes.
pub fn zstd_decompress(input: &[u8], max_out: usize) -> Result<Vec<u8>, DecompressError> {
    if input.is_empty() {
        return Err(DecompressError::Truncated);
    }
    let budget =
        kafka_decompress_cap_clamp(max_out as u64, MAX_DECOMPRESSED_BATCH_BYTES as u64) as usize;
    let mut rest = input;
    let mut out = Vec::new();
    let mut saw_data_frame = false;

    while !rest.is_empty() {
        let (magic, after_magic) = zstd_take_u32_le(rest)?;
        if matches!(magic, ZSTD_SKIPPABLE_MIN..=ZSTD_SKIPPABLE_MAX) {
            let (skip_u32, after_size) = zstd_take_u32_le(after_magic)?;
            rest = after_size
                .get(skip_u32 as usize..)
                .ok_or(DecompressError::Truncated)?;
            continue;
        }
        if magic != ZSTD_MAGIC_U32 {
            return Err(DecompressError::Corrupt);
        }
        saw_data_frame = true;

        let (hdr, cur_blocks) = parse_zstd_frame_header(after_magic, out.len(), budget)?;
        let frame_start = out.len();
        let after_blocks =
            decode_zstd_frame_blocks(cur_blocks, &mut out, frame_start, hdr.window_limit, budget)?;
        let frame_slice = out.get(frame_start..).ok_or(DecompressError::Corrupt)?;
        rest = verify_zstd_frame_trailer(after_blocks, frame_slice, &hdr)?;
    }

    if !saw_data_frame {
        return Err(DecompressError::Corrupt);
    }
    Ok(out)
}

// ============================================================================
// Pure-Rust RFC 8878 Zstandard Compressor (`zstd_compress`)
// ============================================================================

struct FwdBitWriter {
    bytes: Vec<u8>,
    bit_buf: u64,
    bit_cnt: u32,
}

impl FwdBitWriter {
    fn new() -> Self {
        Self {
            bytes: Vec::new(),
            bit_buf: 0,
            bit_cnt: 0,
        }
    }

    fn write_bits(&mut self, val: u32, count: u8) {
        if count == 0 {
            return;
        }
        let mask = if count >= 32 {
            u32::MAX as u64
        } else {
            (1u64 << (count & 31)).wrapping_sub(1)
        };
        self.bit_buf |= ((val as u64) & mask) << (self.bit_cnt & 63);
        self.bit_cnt = self.bit_cnt.saturating_add(count as u32);
        while self.bit_cnt >= 8 {
            self.bytes.push(self.bit_buf as u8);
            self.bit_buf >>= 8;
            self.bit_cnt = self.bit_cnt.saturating_sub(8);
        }
    }

    /// Finish a backward Zstandard bitstream by appending the mandatory sentinel `1` bit.
    fn finish_backward(mut self) -> Vec<u8> {
        self.write_bits(1, 1);
        if self.bit_cnt > 0 {
            self.bytes.push(self.bit_buf as u8);
        }
        self.bytes
    }
}

#[derive(Clone, Copy)]
struct ZstdSeq {
    lit_len: u32,
    offset_val: u32,
    match_len: u32,
}

fn ll_code_of(lit_len: u32) -> (u8, u8, u32) {
    let mut code = 35usize;
    loop {
        let base = *LL_BASE.get(code).unwrap_or(&0);
        if lit_len >= base {
            let nb = *LL_BITS.get(code).unwrap_or(&0);
            return (code as u8, nb, lit_len.saturating_sub(base));
        }
        if code == 0 {
            return (0, 0, 0);
        }
        code = code.saturating_sub(1);
    }
}

fn ml_code_of(match_len: u32) -> (u8, u8, u32) {
    let mut code = 52usize;
    loop {
        let base = *ML_BASE.get(code).unwrap_or(&3);
        if match_len >= base {
            let nb = *ML_BITS.get(code).unwrap_or(&0);
            return (code as u8, nb, match_len.saturating_sub(base));
        }
        if code == 0 {
            return (0, 0, 0);
        }
        code = code.saturating_sub(1);
    }
}

const fn of_code_of(offset_val: u32) -> (u8, u8, u32) {
    if offset_val <= 1 {
        return (0, 0, 0);
    }
    let code = 31u8.saturating_sub(offset_val.leading_zeros() as u8);
    let base = 1u32 << (code & 31);
    (code, code, offset_val.saturating_sub(base))
}

fn fse_initial_state(table: &FseTable, symbol: u8) -> Option<usize> {
    for (idx, e) in table.entries.iter().enumerate() {
        if e.symbol == symbol {
            return Some(idx);
        }
    }
    None
}

fn fse_prev_state(table: &FseTable, symbol: u8, target_state: usize) -> Option<(usize, u32, u8)> {
    for (idx, e) in table.entries.iter().enumerate() {
        if e.symbol == symbol {
            let span = 1usize << (e.num_bits & 15);
            let lo = e.baseline as usize;
            let hi = lo.saturating_add(span);
            if target_state >= lo && target_state < hi {
                return Some((idx, target_state.saturating_sub(lo) as u32, e.num_bits));
            }
        }
    }
    None
}

fn append_literals_header_raw_or_rle(out: &mut Vec<u8>, lit_type: u8, size: usize) {
    if size < 32 {
        out.push((lit_type & 3) | ((size as u8) << 3));
    } else if size < 4096 {
        let v = ((lit_type & 3) as usize) | (1usize << 2) | (size << 4);
        out.push(v as u8);
        out.push((v >> 8) as u8);
    } else {
        let v = ((lit_type & 3) as usize) | (3usize << 2) | (size << 4);
        out.push(v as u8);
        out.push((v >> 8) as u8);
        out.push((v >> 16) as u8);
    }
}

fn is_uniform_slice(bytes: &[u8]) -> Option<u8> {
    let &[first, ref rest @ ..] = bytes else {
        return None;
    };
    for &b in rest {
        if b != first {
            return None;
        }
    }
    Some(first)
}

#[inline]
const fn lz_hash4(b0: u8, b1: u8, b2: u8, b3: u8) -> usize {
    let v = u32_le(b0, b1, b2, b3);
    (v.wrapping_mul(0x9E37_79B1) >> 20) as usize
}

fn try_encode_compressed_block(chunk: &[u8]) -> Option<Vec<u8>> {
    if chunk.len() < 16 || chunk.len() > MAX_ZSTD_BLOCK_SIZE {
        return None;
    }
    let mut htab = vec![usize::MAX; 4096];
    let mut literals = Vec::new();
    let mut seqs: Vec<ZstdSeq> = Vec::new();

    let len = chunk.len();
    let limit = len.saturating_sub(4);
    let mut anchor = 0usize;
    let mut ip = 0usize;

    while ip < limit {
        let b0 = *chunk.get(ip)?;
        let b1 = *chunk.get(ip.saturating_add(1))?;
        let b2 = *chunk.get(ip.saturating_add(2))?;
        let b3 = *chunk.get(ip.saturating_add(3))?;
        let h = lz_hash4(b0, b1, b2, b3) & 4095;
        let cand = *htab.get(h)?;
        if let Some(slot) = htab.get_mut(h) {
            *slot = ip;
        }

        if cand < ip
            && chunk.get(cand) == Some(&b0)
            && chunk.get(cand.saturating_add(1)) == Some(&b1)
            && chunk.get(cand.saturating_add(2)) == Some(&b2)
            && chunk.get(cand.saturating_add(3)) == Some(&b3)
        {
            let mut mlen = 4usize;
            while ip.saturating_add(mlen) < len {
                let ca = chunk.get(cand.saturating_add(mlen));
                let cb = chunk.get(ip.saturating_add(mlen));
                if ca.is_some() && ca == cb {
                    mlen = mlen.saturating_add(1);
                } else {
                    break;
                }
            }
            let lit_slice = chunk.get(anchor..ip)?;
            literals.extend_from_slice(lit_slice);
            let actual_off = ip.saturating_sub(cand);
            // Offset_Value > 3 encodes `actual_offset + 3` with zero repeat-offset ambiguity.
            let offset_val = (actual_off as u32).saturating_add(3);
            if offset_val < (1u32 << 29) {
                seqs.push(ZstdSeq {
                    lit_len: lit_slice.len() as u32,
                    offset_val,
                    match_len: mlen as u32,
                });
                ip = ip.saturating_add(mlen);
                anchor = ip;
                continue;
            }
            // Undo literal append if offset exceeded Predefined OF table range (`<= 28`).
            literals.truncate(literals.len().saturating_sub(lit_slice.len()));
        }
        ip = ip.saturating_add(1);
    }

    if seqs.is_empty() || seqs.len() > 0xFFFF {
        return None;
    }
    if let Some(tail) = chunk.get(anchor..) {
        literals.extend_from_slice(tail);
    }

    let ll_fse = FseTable::from_norm(6, &LL_DEFAULT_NORM).ok()?;
    let of_fse = FseTable::from_norm(5, &OF_DEFAULT_NORM).ok()?;
    let ml_fse = FseTable::from_norm(6, &ML_DEFAULT_NORM).ok()?;

    // Encode sequences in reverse so the backward reader sees them in forward order!
    #[derive(Clone, Copy)]
    struct EncStep {
        ll_extra: (u32, u8),
        ml_extra: (u32, u8),
        of_extra: (u32, u8),
        ll_upd: (u32, u8),
        ml_upd: (u32, u8),
        of_upd: (u32, u8),
    }

    let n = seqs.len();
    let last_seq = *seqs.get(n.saturating_sub(1))?;
    let (last_ll_c, last_ll_nb, last_ll_ex) = ll_code_of(last_seq.lit_len);
    let (last_of_c, last_of_nb, last_of_ex) = of_code_of(last_seq.offset_val);
    let (last_ml_c, last_ml_nb, last_ml_ex) = ml_code_of(last_seq.match_len);

    let mut cur_ll_st = fse_initial_state(&ll_fse, last_ll_c)?;
    let mut cur_of_st = fse_initial_state(&of_fse, last_of_c)?;
    let mut cur_ml_st = fse_initial_state(&ml_fse, last_ml_c)?;

    let mut rev_steps = if n <= 131_072 {
        Vec::with_capacity(n)
    } else {
        Vec::new()
    };
    rev_steps.push(EncStep {
        ll_extra: (last_ll_ex, last_ll_nb),
        ml_extra: (last_ml_ex, last_ml_nb),
        of_extra: (last_of_ex, last_of_nb),
        ll_upd: (0, 0),
        ml_upd: (0, 0),
        of_upd: (0, 0),
    });

    let mut rev_i = n.saturating_sub(1);
    while rev_i > 0 {
        rev_i = rev_i.saturating_sub(1);
        let sq = *seqs.get(rev_i)?;
        let (llc, llnb, llex) = ll_code_of(sq.lit_len);
        let (ofc, ofnb, ofex) = of_code_of(sq.offset_val);
        let (mlc, mlnb, mlex) = ml_code_of(sq.match_len);

        let (prev_ll, ll_bits, ll_cnt) = fse_prev_state(&ll_fse, llc, cur_ll_st)?;
        let (prev_of, of_bits, of_cnt) = fse_prev_state(&of_fse, ofc, cur_of_st)?;
        let (prev_ml, ml_bits, ml_cnt) = fse_prev_state(&ml_fse, mlc, cur_ml_st)?;

        cur_ll_st = prev_ll;
        cur_of_st = prev_of;
        cur_ml_st = prev_ml;

        rev_steps.push(EncStep {
            ll_extra: (llex, llnb),
            ml_extra: (mlex, mlnb),
            of_extra: (ofex, ofnb),
            ll_upd: (ll_bits, ll_cnt),
            ml_upd: (ml_bits, ml_cnt),
            of_upd: (of_bits, of_cnt),
        });
    }

    // Write bits into FwdBitWriter in exact reverse of BackBitReader's read order:
    // BackBitReader reads:
    //   init: ll_state, of_state, ml_state
    //   seq[i]: of_extra, ml_extra, ll_extra, [if i+1<n: ll_upd, ml_upd, of_upd]
    let mut bw = FwdBitWriter::new();
    let mut k = 0usize;
    while k < rev_steps.len() {
        let step = *rev_steps.get(k)?;
        if k > 0 {
            bw.write_bits(step.of_upd.0, step.of_upd.1);
            bw.write_bits(step.ml_upd.0, step.ml_upd.1);
            bw.write_bits(step.ll_upd.0, step.ll_upd.1);
        }
        bw.write_bits(step.ll_extra.0, step.ll_extra.1);
        bw.write_bits(step.ml_extra.0, step.ml_extra.1);
        bw.write_bits(step.of_extra.0, step.of_extra.1);
        k = k.saturating_add(1);
    }
    bw.write_bits(cur_ml_st as u32, ml_fse.acc_log);
    bw.write_bits(cur_of_st as u32, of_fse.acc_log);
    bw.write_bits(cur_ll_st as u32, ll_fse.acc_log);
    let bit_bytes = bw.finish_backward();

    let mut block_out = Vec::new();
    if let Some(uniform) = is_uniform_slice(&literals) {
        append_literals_header_raw_or_rle(&mut block_out, 1, literals.len());
        block_out.push(uniform);
    } else {
        append_literals_header_raw_or_rle(&mut block_out, 0, literals.len());
        block_out.extend_from_slice(&literals);
    }

    // Sequences_Section_Header: Number_of_Sequences + Modes byte (`0x00` = all Predefined).
    if n < 128 {
        block_out.push(n as u8);
    } else if n < 0x7F00 {
        block_out.push(((n >> 8) as u8).saturating_add(128));
        block_out.push((n & 0xFF) as u8);
    } else {
        let adj = n.saturating_sub(0x7F00);
        block_out.push(255);
        block_out.push((adj & 0xFF) as u8);
        block_out.push(((adj >> 8) & 0xFF) as u8);
    }
    block_out.push(0x00); // LL=Predefined(0), OF=Predefined(0), ML=Predefined(0)
    block_out.extend_from_slice(&bit_bytes);

    if block_out.len() < chunk.len() {
        Some(block_out)
    } else {
        None
    }
}

fn push_block_header(out: &mut Vec<u8>, last_block: bool, block_type: u8, block_size: usize) {
    let bh = (last_block as u32) | (((block_type & 3) as u32) << 1) | ((block_size as u32) << 3);
    out.push(bh as u8);
    out.push((bh >> 8) as u8);
    out.push((bh >> 16) as u8);
}

/// Compress `input` into a standard RFC 8878 Zstandard frame carrying exact
/// `Frame_Content_Size`, `Content_Checksum_Flag = 1` (low 32 bits of [`xxhash64`]),
/// and LZ77 + RFC 8878 `Predefined_Mode` ANS/FSE sequence-compressed blocks (with
/// automatic `RLE_Block` and `Raw_Block` fallback).
#[must_use]
pub fn zstd_compress(input: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&ZSTD_MAGIC_LE);

    // Frame_Header_Descriptor:
    // Single_Segment_Flag = 1 (0x20), Content_Checksum_Flag = 1 (0x04),
    // FCS_Field_Size = 2 (4-byte u32 LE -> 0x80) when <= u32::MAX, else 3 (8-byte u64 LE -> 0xC0).
    let len_u64 = input.len() as u64;
    if len_u64 <= (u32::MAX as u64) {
        out.push(0x80 | 0x20 | 0x04);
        out.extend_from_slice(&(len_u64 as u32).to_le_bytes());
    } else {
        out.push(0xC0 | 0x20 | 0x04);
        out.extend_from_slice(&len_u64.to_le_bytes());
    }

    if input.is_empty() {
        push_block_header(&mut out, true, 0, 0);
    } else {
        let mut offset = 0usize;
        while offset < input.len() {
            let rem = input.len().saturating_sub(offset);
            let take = rem.min(MAX_ZSTD_BLOCK_SIZE);
            let next_off = offset.saturating_add(take);
            let is_last = next_off >= input.len();
            if let Some(chunk) = input.get(offset..next_off) {
                if chunk.len() >= 4 {
                    if let Some(uniform) = is_uniform_slice(chunk) {
                        push_block_header(&mut out, is_last, 1, chunk.len());
                        out.push(uniform);
                        offset = next_off;
                        continue;
                    }
                }
                if let Some(comp) = try_encode_compressed_block(chunk) {
                    push_block_header(&mut out, is_last, 2, comp.len());
                    out.extend_from_slice(&comp);
                } else {
                    push_block_header(&mut out, is_last, 0, chunk.len());
                    out.extend_from_slice(chunk);
                }
            }
            offset = next_off;
        }
    }

    let csum = xxhash64(input, 0) as u32;
    out.extend_from_slice(&csum.to_le_bytes());
    out
}
