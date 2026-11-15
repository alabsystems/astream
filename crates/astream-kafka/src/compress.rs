// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pure-Rust Gzip (RFC 1952 + RFC 1951 DEFLATE + IEEE CRC-32), Snappy (raw + Xerial framing),
//! LZ4 Frame (v1.6.1 / Kafka KIP-57 + xxHash32), and Zstandard (RFC 8878 + xxHash64) codecs
//! for Kafka `RecordBatch` v2 (`magic = 2`), with zero third-party dependencies and
//! `#![forbid(unsafe_code)]`.
//!
//! Decompression is fail-closed and strictly bounded by [`MAX_DECOMPRESSED_BATCH_BYTES`]
//! (clamped via Clean-origin [`kafka_decompress_cap_clamp`]), defeating zip-bomb / RLE
//! amplification frames before allocation.

pub use crate::zstd::{xxhash64, zstd_compress, zstd_decompress, ZSTD_MAGIC_LE};

#[cfg(clean_islands)]
#[path = "compact_island.rs"]
mod compact_island;

#[cfg(not(clean_islands))]
pub use crate::twins::{kafka_compact_len_clamp, kafka_decompress_cap_clamp};
#[cfg(clean_islands)]
pub use compact_island::{kafka_compact_len_clamp, kafka_decompress_cap_clamp};

/// Hard ceiling (`16 MiB`, matching `MAX_KAFKA_FRAME_LEN`) on decompressed RecordBatch v2 bytes.
pub const MAX_DECOMPRESSED_BATCH_BYTES: usize = 16 * 1024 * 1024;

/// Standard RFC 1952 Gzip 2-byte identification header (`0x1f, 0x8b`).
pub const GZIP_MAGIC: [u8; 2] = [0x1f, 0x8b];

/// Xerial `snappy-java` 8-byte magic header emitted by JVM `kafka-clients` producers.
pub const XERIAL_SNAPPY_MAGIC: [u8; 8] = [0x82, b'S', b'N', b'A', b'P', b'P', b'Y', 0x00];

/// Standard LZ4 Frame v1.6.1 4-byte little-endian magic (`0x184D2204`).
pub const LZ4_FRAME_MAGIC_LE: [u8; 4] = [0x04, 0x22, 0x4D, 0x18];

const PRIME32_1: u32 = 0x9E37_79B1;
const PRIME32_2: u32 = 0x85EB_CA77;
const PRIME32_3: u32 = 0xC2B2_AE3D;
const PRIME32_4: u32 = 0x27D4_EB2F;
const PRIME32_5: u32 = 0x1656_67B1;

const LZ4_BLOCK_CHUNK: usize = 65_536;

contract_fn! {
    /// Kernel-certified check that a 3-bit Kafka RecordBatch v2 compression attribute
    /// lies in the defined Kafka codec range (`0..=4`: None, Gzip, Snappy, Lz4, Zstd),
    /// linked via `clean-kernel-defeq` to `compression_codec_in_spec_range_isl`.
    #[must_use]
    pub const fn compression_codec_in_spec_range(codec: u8) -> bool
    clauses [ensures result == (codec <= 4)]
    {
        codec <= 4
    }
}

/// Fail-closed decompression error for Gzip, Snappy, LZ4, and Zstandard RecordBatch v2 payloads.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DecompressError {
    /// Compressed stream ended mid-header, mid-token, or before declared uncompressed length.
    Truncated,
    /// Invalid backreference offset, bad CRC-32/xxHash32/xxHash64 checksum, or malformed framing.
    Corrupt,
    /// Claimed or actual uncompressed output exceeds the caller's byte budget.
    OutputTooLarge,
}

#[inline]
const fn xxh32_round(acc: u32, lane: u32) -> u32 {
    acc.wrapping_add(lane.wrapping_mul(PRIME32_2))
        .rotate_left(13)
        .wrapping_mul(PRIME32_1)
}

#[inline]
const fn read_u32_le(b0: u8, b1: u8, b2: u8, b3: u8) -> u32 {
    (b0 as u32) | ((b1 as u32) << 8) | ((b2 as u32) << 16) | ((b3 as u32) << 24)
}

#[inline]
const fn read_u32_be(b0: u8, b1: u8, b2: u8, b3: u8) -> u32 {
    ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32)
}

/// Compute the 32-bit xxHash (`XXH32`) of `data` with `seed` (used by LZ4 Frame header,
/// block, and content checksums).
#[must_use]
pub const fn xxhash32(data: &[u8], seed: u32) -> u32 {
    let total_len = data.len() as u32;
    let mut rest = data;
    let mut h32 = if data.len() >= 16 {
        let mut v1 = seed.wrapping_add(PRIME32_1).wrapping_add(PRIME32_2);
        let mut v2 = seed.wrapping_add(PRIME32_2);
        let mut v3 = seed;
        let mut v4 = seed.wrapping_sub(PRIME32_1);
        while let &[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, ref tail @ ..] =
            rest
        {
            v1 = xxh32_round(v1, read_u32_le(b0, b1, b2, b3));
            v2 = xxh32_round(v2, read_u32_le(b4, b5, b6, b7));
            v3 = xxh32_round(v3, read_u32_le(b8, b9, b10, b11));
            v4 = xxh32_round(v4, read_u32_le(b12, b13, b14, b15));
            rest = tail;
        }
        v1.rotate_left(1)
            .wrapping_add(v2.rotate_left(7))
            .wrapping_add(v3.rotate_left(12))
            .wrapping_add(v4.rotate_left(18))
    } else {
        seed.wrapping_add(PRIME32_5)
    };

    h32 = h32.wrapping_add(total_len);

    while let &[b0, b1, b2, b3, ref tail @ ..] = rest {
        let k1 = read_u32_le(b0, b1, b2, b3).wrapping_mul(PRIME32_3);
        h32 = h32.wrapping_add(k1);
        h32 = h32.rotate_left(17).wrapping_mul(PRIME32_4);
        rest = tail;
    }

    while let &[b0, ref tail @ ..] = rest {
        h32 = h32.wrapping_add((b0 as u32).wrapping_mul(PRIME32_5));
        h32 = h32.rotate_left(11).wrapping_mul(PRIME32_1);
        rest = tail;
    }

    h32 ^= h32 >> 15;
    h32 = h32.wrapping_mul(PRIME32_2);
    h32 ^= h32 >> 13;
    h32 = h32.wrapping_mul(PRIME32_3);
    h32 ^= h32 >> 16;
    h32
}

fn put_snappy_uvarint32(out: &mut Vec<u8>, mut v: u32) {
    while v >= 0x80 {
        out.push(((v as u8) & 0x7f) | 0x80);
        v >>= 7;
    }
    out.push(v as u8);
}

fn take_snappy_uvarint32(mut b: &[u8]) -> Result<(u32, &[u8]), DecompressError> {
    let mut acc = 0u32;
    let mut shift = 0u32;
    while shift <= 28 {
        let &[byte, ref rest @ ..] = b else {
            return Err(DecompressError::Truncated);
        };
        let low = (byte & 0x7f) as u32;
        if shift == 28 && low > 0x0f {
            return Err(DecompressError::Corrupt);
        }
        acc |= low << shift;
        if (byte & 0x80) == 0 {
            return Ok((acc, rest));
        }
        b = rest;
        shift += 7;
    }
    Err(DecompressError::Corrupt)
}

fn emit_snappy_literal(out: &mut Vec<u8>, lit: &[u8]) {
    if lit.is_empty() {
        return;
    }
    let n_minus_1 = lit.len() - 1;
    if n_minus_1 < 60 {
        out.push((n_minus_1 as u8) << 2);
    } else if n_minus_1 <= 0xff {
        out.push(60u8 << 2);
        out.push(n_minus_1 as u8);
    } else if n_minus_1 <= 0xffff {
        out.push(61u8 << 2);
        out.extend_from_slice(&(n_minus_1 as u16).to_le_bytes());
    } else if n_minus_1 <= 0xff_ffff {
        out.push(62u8 << 2);
        let le = (n_minus_1 as u32).to_le_bytes();
        out.push(le[0]);
        out.push(le[1]);
        out.push(le[2]);
    } else {
        out.push(63u8 << 2);
        out.extend_from_slice(&(n_minus_1 as u32).to_le_bytes());
    }
    out.extend_from_slice(lit);
}

fn emit_snappy_copy(out: &mut Vec<u8>, offset: usize, mut len: usize) {
    if len == 0 {
        return;
    }
    while len >= 68 {
        if offset <= 0xffff {
            out.push(0x02 | (63u8 << 2));
            out.extend_from_slice(&(offset as u16).to_le_bytes());
        } else {
            out.push(0x03 | (63u8 << 2));
            out.extend_from_slice(&(offset as u32).to_le_bytes());
        }
        len -= 64;
    }
    if len > 64 {
        if offset <= 0xffff {
            out.push(0x02 | (59u8 << 2));
            out.extend_from_slice(&(offset as u16).to_le_bytes());
        } else {
            out.push(0x03 | (59u8 << 2));
            out.extend_from_slice(&(offset as u32).to_le_bytes());
        }
        len -= 60;
    }
    if offset <= 2047 && len <= 11 {
        if let Some(len_m4) = len.checked_sub(4) {
            let tag = 0x01 | ((len_m4 as u8) << 2) | ((((offset >> 8) as u8) & 0x07) << 5);
            out.push(tag);
            out.push((offset & 0xff) as u8);
            return;
        }
    }
    let Some(len_m1) = len.checked_sub(1) else {
        return;
    };
    if offset <= 0xffff {
        out.push(0x02 | ((len_m1 as u8) << 2));
        out.extend_from_slice(&(offset as u16).to_le_bytes());
    } else {
        out.push(0x03 | ((len_m1 as u8) << 2));
        out.extend_from_slice(&(offset as u32).to_le_bytes());
    }
}

#[inline]
fn load_u32_at(buf: &[u8], pos: usize) -> Option<u32> {
    let s = buf.get(pos..pos.checked_add(4)?)?;
    let &[b0, b1, b2, b3] = s else {
        return None;
    };
    Some(read_u32_le(b0, b1, b2, b3))
}

#[inline]
const fn hash4_10bit(v: u32) -> usize {
    (v.wrapping_mul(0x1e35_a7bd) >> 22) as usize
}

const LZ_TABLE_EMPTY: u32 = u32::MAX;

fn lz_match_len(src: &[u8], cand: usize, ip: usize, limit_end: usize) -> usize {
    let mut mlen = 4usize;
    while ip.saturating_add(mlen) < limit_end {
        let a = src.get(cand.saturating_add(mlen));
        let b = src.get(ip.saturating_add(mlen));
        match (a, b) {
            (Some(&x), Some(&y)) if x == y => {
                mlen = mlen.saturating_add(1);
            }
            _ => break,
        }
    }
    mlen
}

/// Compress `input` into a raw Snappy stream (LEB128 uncompressed length + LZ77 tags).
#[must_use]
pub fn snappy_compress(input: &[u8]) -> Vec<u8> {
    let cap_hint = input
        .len()
        .saturating_add(16)
        .min(MAX_DECOMPRESSED_BATCH_BYTES);
    let mut out = Vec::with_capacity(cap_hint);
    let clamped_len = kafka_decompress_cap_clamp(input.len() as u64, u32::MAX as u64) as u32;
    put_snappy_uvarint32(&mut out, clamped_len);
    let src = match input.get(..(clamped_len as usize)) {
        Some(s) => s,
        None => input,
    };
    if src.len() < 16 {
        emit_snappy_literal(&mut out, src);
        return out;
    }

    let mut table = vec![LZ_TABLE_EMPTY; 1024];
    let mut anchor = 0usize;
    let mut ip = 0usize;
    let limit = src.len().saturating_sub(4);

    while ip <= limit {
        let Some(cur4) = load_u32_at(src, ip) else {
            break;
        };
        let h = hash4_10bit(cur4);
        let cand_raw = match table.get(h) {
            Some(&c) => c,
            None => LZ_TABLE_EMPTY,
        };
        if let Some(slot) = table.get_mut(h) {
            *slot = ip as u32;
        }

        if cand_raw != LZ_TABLE_EMPTY {
            let cand = cand_raw as usize;
            if cand < ip && ip.saturating_sub(cand) <= 65_535 {
                if let Some(cand4) = load_u32_at(src, cand) {
                    if cand4 == cur4 {
                        if let Some(lit) = src.get(anchor..ip) {
                            emit_snappy_literal(&mut out, lit);
                        }
                        let offset = ip.saturating_sub(cand);
                        let mlen = lz_match_len(src, cand, ip, src.len());
                        emit_snappy_copy(&mut out, offset, mlen);
                        ip = ip.saturating_add(mlen);
                        anchor = ip;
                        if ip <= limit {
                            if let Some(prev4) = load_u32_at(src, ip.saturating_sub(1)) {
                                let ph = hash4_10bit(prev4);
                                if let Some(slot) = table.get_mut(ph) {
                                    *slot = ip.saturating_sub(1) as u32;
                                }
                            }
                        }
                        continue;
                    }
                }
            }
        }
        ip = ip.saturating_add(1);
    }

    if anchor < src.len() {
        if let Some(tail_lit) = src.get(anchor..) {
            emit_snappy_literal(&mut out, tail_lit);
        }
    }
    out
}

/// Compress `input` using Xerial `snappy-java` chunk framing (`\x82SNAPPY\x00`, version `1`,
/// compat `1`, 32 KiB chunks), matching JVM `org.apache.kafka:kafka-clients` producers.
#[must_use]
pub fn snappy_compress_xerial(input: &[u8]) -> Vec<u8> {
    let cap_hint = input
        .len()
        .saturating_add(32)
        .min(MAX_DECOMPRESSED_BATCH_BYTES);
    let mut out = Vec::with_capacity(cap_hint);
    out.extend_from_slice(&XERIAL_SNAPPY_MAGIC);
    out.extend_from_slice(&1u32.to_be_bytes());
    out.extend_from_slice(&1u32.to_be_bytes());
    if input.is_empty() {
        return out;
    }
    let mut pos = 0usize;
    while pos < input.len() {
        let end = pos.saturating_add(32_768).min(input.len());
        if let Some(chunk) = input.get(pos..end) {
            let compressed = snappy_compress(chunk);
            out.extend_from_slice(&(compressed.len() as u32).to_be_bytes());
            out.extend_from_slice(&compressed);
        }
        pos = end;
    }
    out
}

fn copy_backref(
    out: &mut Vec<u8>,
    offset: usize,
    copy_len: usize,
    cap: usize,
) -> Result<(), DecompressError> {
    if offset == 0 || offset > out.len() {
        return Err(DecompressError::Corrupt);
    }
    let Some(end_len) = out.len().checked_add(copy_len) else {
        return Err(DecompressError::OutputTooLarge);
    };
    if end_len > cap {
        return Err(DecompressError::OutputTooLarge);
    }
    let mut rem = copy_len;
    while rem > 0 {
        let Some(src_idx) = out.len().checked_sub(offset) else {
            return Err(DecompressError::Corrupt);
        };
        let Some(&b) = out.get(src_idx) else {
            return Err(DecompressError::Corrupt);
        };
        out.push(b);
        rem = rem.saturating_sub(1);
    }
    Ok(())
}

fn decode_snappy_literal<'a>(
    code: usize,
    after_tag: &'a [u8],
    out: &mut Vec<u8>,
    target_end: usize,
) -> Result<&'a [u8], DecompressError> {
    let (raw, rest) = if code < 60 {
        (code, after_tag)
    } else if code == 60 {
        let &[b0, ref r @ ..] = after_tag else {
            return Err(DecompressError::Truncated);
        };
        (b0 as usize, r)
    } else if code == 61 {
        let &[b0, b1, ref r @ ..] = after_tag else {
            return Err(DecompressError::Truncated);
        };
        (u16::from_le_bytes([b0, b1]) as usize, r)
    } else if code == 62 {
        let &[b0, b1, b2, ref r @ ..] = after_tag else {
            return Err(DecompressError::Truncated);
        };
        (read_u32_le(b0, b1, b2, 0) as usize, r)
    } else {
        let &[b0, b1, b2, b3, ref r @ ..] = after_tag else {
            return Err(DecompressError::Truncated);
        };
        (read_u32_le(b0, b1, b2, b3) as usize, r)
    };
    let Some(lit_len) = raw.checked_add(1) else {
        return Err(DecompressError::OutputTooLarge);
    };
    let Some(next_out_len) = out.len().checked_add(lit_len) else {
        return Err(DecompressError::OutputTooLarge);
    };
    if next_out_len > target_end {
        return Err(DecompressError::Corrupt);
    }
    let Some(bytes) = rest.get(..lit_len) else {
        return Err(DecompressError::Truncated);
    };
    let Some(next_cur) = rest.get(lit_len..) else {
        return Err(DecompressError::Truncated);
    };
    out.extend_from_slice(bytes);
    Ok(next_cur)
}

fn snappy_decompress_raw_into(
    input: &[u8],
    out: &mut Vec<u8>,
    max_total: usize,
) -> Result<(), DecompressError> {
    let (decl_u32, mut cur) = take_snappy_uvarint32(input)?;
    let decl_len = decl_u32 as usize;
    let Some(target_end) = out.len().checked_add(decl_len) else {
        return Err(DecompressError::OutputTooLarge);
    };
    let clamped_end = kafka_decompress_cap_clamp(target_end as u64, max_total as u64) as usize;
    if target_end > clamped_end {
        return Err(DecompressError::OutputTooLarge);
    }
    out.reserve(decl_len.min(65_536));

    while let &[tag, ref after_tag @ ..] = cur {
        match tag & 0x03 {
            0x00 => {
                let code = (tag >> 2) as usize;
                cur = decode_snappy_literal(code, after_tag, out, target_end)?;
            }
            0x01 => {
                let &[b0, ref rest @ ..] = after_tag else {
                    return Err(DecompressError::Truncated);
                };
                let copy_len = (((tag >> 2) & 0x07) as usize) + 4;
                let offset = (((tag & 0xe0) as usize) << 3) | (b0 as usize);
                copy_backref(out, offset, copy_len, target_end)?;
                cur = rest;
            }
            0x02 => {
                let &[b0, b1, ref rest @ ..] = after_tag else {
                    return Err(DecompressError::Truncated);
                };
                let copy_len = ((tag >> 2) as usize) + 1;
                let offset = u16::from_le_bytes([b0, b1]) as usize;
                copy_backref(out, offset, copy_len, target_end)?;
                cur = rest;
            }
            _ => {
                let &[b0, b1, b2, b3, ref rest @ ..] = after_tag else {
                    return Err(DecompressError::Truncated);
                };
                let copy_len = ((tag >> 2) as usize) + 1;
                let offset = read_u32_le(b0, b1, b2, b3) as usize;
                copy_backref(out, offset, copy_len, target_end)?;
                cur = rest;
            }
        }
    }

    if out.len() != target_end {
        return Err(DecompressError::Corrupt);
    }
    Ok(())
}

/// Decompress a Snappy payload (supporting both raw Snappy from `librdkafka` / `franz-go`
/// and Xerial chunk framing from JVM `kafka-clients`), bounded by `max_out`.
pub fn snappy_decompress(input: &[u8], max_out: usize) -> Result<Vec<u8>, DecompressError> {
    let eff_cap =
        kafka_decompress_cap_clamp(max_out as u64, MAX_DECOMPRESSED_BATCH_BYTES as u64) as usize;
    if let Some(after_magic) = input.strip_prefix(&XERIAL_SNAPPY_MAGIC) {
        let &[v0, v1, v2, v3, c0, c1, c2, c3, ref init_chunks @ ..] = after_magic else {
            return Err(DecompressError::Truncated);
        };
        let mut chunks = init_chunks;
        let version = read_u32_be(v0, v1, v2, v3);
        let compat = read_u32_be(c0, c1, c2, c3);
        if version == 0 || compat == 0 {
            return Err(DecompressError::Corrupt);
        }
        let mut out = Vec::new();
        while !chunks.is_empty() {
            let &[l0, l1, l2, l3, ref after_len @ ..] = chunks else {
                return Err(DecompressError::Truncated);
            };
            let clen = read_u32_be(l0, l1, l2, l3) as usize;
            let Some(chunk_bytes) = after_len.get(..clen) else {
                return Err(DecompressError::Truncated);
            };
            let Some(next_chunks) = after_len.get(clen..) else {
                return Err(DecompressError::Truncated);
            };
            if clen > 0 {
                snappy_decompress_raw_into(chunk_bytes, &mut out, eff_cap)?;
            }
            chunks = next_chunks;
        }
        return Ok(out);
    }

    let mut out = Vec::new();
    snappy_decompress_raw_into(input, &mut out, eff_cap)?;
    Ok(out)
}

fn push_lz4_len_ext(out: &mut Vec<u8>, mut rem: usize) {
    while rem >= 255 {
        out.push(255);
        rem -= 255;
    }
    out.push(rem as u8);
}

fn lz4_compress_block(src: &[u8]) -> Vec<u8> {
    let cap_hint = src
        .len()
        .saturating_add(16)
        .min(MAX_DECOMPRESSED_BATCH_BYTES);
    let mut out = Vec::with_capacity(cap_hint);
    if src.len() < 13 {
        let lit_nib = if src.len() >= 15 {
            15u8
        } else {
            src.len() as u8
        };
        out.push(lit_nib << 4);
        if src.len() >= 15 {
            push_lz4_len_ext(&mut out, src.len() - 15);
        }
        out.extend_from_slice(src);
        return out;
    }

    let mut table = vec![LZ_TABLE_EMPTY; 1024];
    let mut anchor = 0usize;
    let mut ip = 0usize;
    let search_limit = src.len() - 12;
    let match_limit = src.len() - 5;

    while ip <= search_limit && ip < (LZ_TABLE_EMPTY as usize) {
        let Some(cur4) = load_u32_at(src, ip) else {
            break;
        };
        let h = hash4_10bit(cur4);
        let cand_raw = match table.get(h) {
            Some(&c) => c,
            None => LZ_TABLE_EMPTY,
        };
        if let Some(slot) = table.get_mut(h) {
            *slot = ip as u32;
        }

        if cand_raw != LZ_TABLE_EMPTY {
            let cand = cand_raw as usize;
            if cand < ip && ip.saturating_sub(cand) <= 65_535 {
                if let Some(cand4) = load_u32_at(src, cand) {
                    if cand4 == cur4 {
                        let lit_len = ip.saturating_sub(anchor);
                        let offset = ip.saturating_sub(cand);
                        let mlen = lz_match_len(src, cand, ip, match_limit);
                        let lit_nib = if lit_len >= 15 { 15u8 } else { lit_len as u8 };
                        let match_extra = mlen.saturating_sub(4);
                        let match_nib = if match_extra >= 15 {
                            15u8
                        } else {
                            match_extra as u8
                        };
                        out.push((lit_nib << 4) | match_nib);
                        if lit_len >= 15 {
                            push_lz4_len_ext(&mut out, lit_len.saturating_sub(15));
                        }
                        if let Some(lit_bytes) = src.get(anchor..ip) {
                            out.extend_from_slice(lit_bytes);
                        }
                        out.extend_from_slice(&(offset as u16).to_le_bytes());
                        if match_extra >= 15 {
                            push_lz4_len_ext(&mut out, match_extra.saturating_sub(15));
                        }
                        ip = ip.saturating_add(mlen);
                        anchor = ip;
                        continue;
                    }
                }
            }
        }
        ip = ip.saturating_add(1);
    }

    let tail_len = src.len().saturating_sub(anchor);
    let lit_nib = if tail_len >= 15 { 15u8 } else { tail_len as u8 };
    out.push(lit_nib << 4);
    if tail_len >= 15 {
        push_lz4_len_ext(&mut out, tail_len.saturating_sub(15));
    }
    if let Some(tail_bytes) = src.get(anchor..) {
        out.extend_from_slice(tail_bytes);
    }
    out
}

/// Compress `input` into a standard Kafka LZ4 Frame (`0x184D2204`, `FLG=0x64` independent
/// blocks + content xxHash32 checksum, `BD=0x70`).
#[must_use]
pub fn lz4_compress(input: &[u8]) -> Vec<u8> {
    let cap_hint = input
        .len()
        .saturating_add(24)
        .min(MAX_DECOMPRESSED_BATCH_BYTES);
    let mut out = Vec::with_capacity(cap_hint);
    out.extend_from_slice(&LZ4_FRAME_MAGIC_LE);
    let flg = 0x64u8; // version 01, block_indep=1, content_checksum=1
    let bd = 0x70u8; // 4 MiB block max size
    let hc = ((xxhash32(&[flg, bd], 0) >> 8) & 0xff) as u8;
    out.push(flg);
    out.push(bd);
    out.push(hc);

    let mut pos = 0usize;
    while pos < input.len() {
        let end = pos.saturating_add(LZ4_BLOCK_CHUNK).min(input.len());
        if let Some(chunk) = input.get(pos..end) {
            let compressed = lz4_compress_block(chunk);
            if compressed.len() < chunk.len() {
                out.extend_from_slice(&(compressed.len() as u32).to_le_bytes());
                out.extend_from_slice(&compressed);
            } else {
                let raw_hdr = 0x8000_0000u32 | (chunk.len() as u32);
                out.extend_from_slice(&raw_hdr.to_le_bytes());
                out.extend_from_slice(chunk);
            }
        }
        pos = end;
    }

    out.extend_from_slice(&0u32.to_le_bytes()); // EndMark
    out.extend_from_slice(&xxhash32(input, 0).to_le_bytes());
    out
}

fn take_lz4_ext_len(
    base: usize,
    mut cur: &[u8],
    cap: usize,
) -> Result<(usize, &[u8]), DecompressError> {
    let mut total = base;
    loop {
        let &[extra, ref rest @ ..] = cur else {
            return Err(DecompressError::Truncated);
        };
        let Some(next_total) = total.checked_add(extra as usize) else {
            return Err(DecompressError::OutputTooLarge);
        };
        if next_total > cap {
            return Err(DecompressError::OutputTooLarge);
        }
        total = next_total;
        cur = rest;
        if extra < 255 {
            return Ok((total, cur));
        }
    }
}

fn lz4_decompress_block_into(
    mut cur: &[u8],
    out: &mut Vec<u8>,
    block_indep: bool,
    max_total: usize,
) -> Result<(), DecompressError> {
    let block_start = out.len();
    while let &[token, ref after_tok @ ..] = cur {
        let lit_nib = (token >> 4) as usize;
        let (lit_len, after_lit_len) = if lit_nib == 15 {
            take_lz4_ext_len(15, after_tok, max_total)?
        } else {
            (lit_nib, after_tok)
        };
        let Some(after_lit_out) = out.len().checked_add(lit_len) else {
            return Err(DecompressError::OutputTooLarge);
        };
        if after_lit_out > max_total {
            return Err(DecompressError::OutputTooLarge);
        }
        let Some(lit_bytes) = after_lit_len.get(..lit_len) else {
            return Err(DecompressError::Truncated);
        };
        let Some(after_lit) = after_lit_len.get(lit_len..) else {
            return Err(DecompressError::Truncated);
        };
        out.extend_from_slice(lit_bytes);

        if after_lit.is_empty() {
            return Ok(());
        }

        let &[o0, o1, ref after_off @ ..] = after_lit else {
            return Err(DecompressError::Truncated);
        };
        let offset = u16::from_le_bytes([o0, o1]) as usize;
        let max_back = if block_indep {
            out.len().saturating_sub(block_start)
        } else {
            out.len()
        };
        if offset == 0 || offset > max_back {
            return Err(DecompressError::Corrupt);
        }

        let match_nib = (token & 0x0f) as usize;
        let (match_extra, next_cur) = if match_nib == 15 {
            take_lz4_ext_len(15, after_off, max_total)?
        } else {
            (match_nib, after_off)
        };
        let Some(match_len) = match_extra.checked_add(4) else {
            return Err(DecompressError::OutputTooLarge);
        };
        copy_backref(out, offset, match_len, max_total)?;
        cur = next_cur;
    }
    Ok(())
}

/// Decompress a standard LZ4 Frame (`0x184D2204`, Kafka KIP-57), verifying header, block,
/// and content xxHash32 checksums and enforcing `max_out`.
pub fn lz4_decompress(input: &[u8], max_out: usize) -> Result<Vec<u8>, DecompressError> {
    let eff_cap =
        kafka_decompress_cap_clamp(max_out as u64, MAX_DECOMPRESSED_BATCH_BYTES as u64) as usize;
    let Some(after_magic) = input.strip_prefix(&LZ4_FRAME_MAGIC_LE) else {
        return Err(DecompressError::Corrupt);
    };
    let &[flg, bd, ref after_fb @ ..] = after_magic else {
        return Err(DecompressError::Truncated);
    };
    if ((flg >> 6) & 0x03) != 0x01 || (flg & 0x02) != 0 {
        return Err(DecompressError::Corrupt);
    }
    if (bd & 0x8f) != 0 || ((bd >> 4) & 0x07) < 4 {
        return Err(DecompressError::Corrupt);
    }
    let block_indep = (flg & 0x20) != 0;
    let has_block_checksum = (flg & 0x10) != 0;
    let has_content_size = (flg & 0x08) != 0;
    let has_content_checksum = (flg & 0x04) != 0;
    let has_dict_id = (flg & 0x01) != 0;
    if has_dict_id {
        return Err(DecompressError::Corrupt);
    }

    let mut desc_len = 2usize;
    let (declared_size, after_csize) = if has_content_size {
        let &[s0, s1, s2, s3, s4, s5, s6, s7, ref r @ ..] = after_fb else {
            return Err(DecompressError::Truncated);
        };
        let sz = u64::from_le_bytes([s0, s1, s2, s3, s4, s5, s6, s7]);
        if sz > eff_cap as u64 {
            return Err(DecompressError::OutputTooLarge);
        }
        desc_len += 8;
        (Some(sz as usize), r)
    } else {
        (None, after_fb)
    };

    let &[hc, ref init_cur @ ..] = after_csize else {
        return Err(DecompressError::Truncated);
    };
    let mut cur = init_cur;
    let Some(desc_slice) = after_magic.get(..desc_len) else {
        return Err(DecompressError::Truncated);
    };
    let want_hc = ((xxhash32(desc_slice, 0) >> 8) & 0xff) as u8;
    if hc != want_hc {
        return Err(DecompressError::Corrupt);
    }

    let mut out = match declared_size {
        Some(sz) => Vec::with_capacity(sz.min(65_536)),
        None => Vec::new(),
    };

    let mut saw_end_mark = false;
    while let &[h0, h1, h2, h3, ref after_bhdr @ ..] = cur {
        let bhdr = read_u32_le(h0, h1, h2, h3);
        if bhdr == 0 {
            cur = after_bhdr;
            saw_end_mark = true;
            break;
        }
        let is_uncompressed = (bhdr & 0x8000_0000) != 0;
        let block_len = (bhdr & 0x7fff_ffff) as usize;
        let Some(block_data) = after_bhdr.get(..block_len) else {
            return Err(DecompressError::Truncated);
        };
        let Some(mut after_bdata) = after_bhdr.get(block_len..) else {
            return Err(DecompressError::Truncated);
        };
        if has_block_checksum {
            let &[c0, c1, c2, c3, ref r @ ..] = after_bdata else {
                return Err(DecompressError::Truncated);
            };
            if read_u32_le(c0, c1, c2, c3) != xxhash32(block_data, 0) {
                return Err(DecompressError::Corrupt);
            }
            after_bdata = r;
        }
        if is_uncompressed {
            let Some(next_len) = out.len().checked_add(block_len) else {
                return Err(DecompressError::OutputTooLarge);
            };
            if next_len > eff_cap {
                return Err(DecompressError::OutputTooLarge);
            }
            out.extend_from_slice(block_data);
        } else {
            lz4_decompress_block_into(block_data, &mut out, block_indep, eff_cap)?;
        }
        cur = after_bdata;
    }

    if !saw_end_mark {
        return Err(DecompressError::Truncated);
    }
    if let Some(sz) = declared_size {
        if out.len() != sz {
            return Err(DecompressError::Corrupt);
        }
    }
    if has_content_checksum {
        let &[c0, c1, c2, c3, ref after_cc @ ..] = cur else {
            return Err(DecompressError::Truncated);
        };
        if read_u32_le(c0, c1, c2, c3) != xxhash32(&out, 0) {
            return Err(DecompressError::Corrupt);
        }
        cur = after_cc;
    }
    if !cur.is_empty() {
        return Err(DecompressError::Corrupt);
    }
    Ok(out)
}

const GZIP_CRC32_POLY: u32 = 0xEDB8_8320;

#[inline(always)]
const fn crc32_ieee_table_at(row: &[u32; 256], idx: u8) -> u32 {
    row[idx as usize]
}

const fn crc32_ieee_entry(byte: u8) -> u32 {
    let mut crc = byte as u32;
    let mut step = 0usize;
    while step < 8 {
        if (crc & 1) != 0 {
            crc = (crc >> 1) ^ GZIP_CRC32_POLY;
        } else {
            crc >>= 1;
        }
        step = step.saturating_add(1);
    }
    crc
}

const fn crc32_ieee_table() -> [u32; 256] {
    let mut row = [0u32; 256];
    let mut i = 0u8;
    loop {
        row[i as usize] = crc32_ieee_entry(i);
        if i == u8::MAX {
            return row;
        }
        i = i.wrapping_add(1);
    }
}

const CRC32_IEEE_TABLE: [u32; 256] = crc32_ieee_table();

/// Compute the IEEE 802.3 CRC-32 checksum (`0xEDB8_8320`) used by RFC 1952 Gzip
/// headers (`FHCRC`) and trailers (`crc32_ieee(b"123456789") == 0xCBF4_3926`).
#[must_use]
pub const fn crc32_ieee(data: &[u8]) -> u32 {
    let mut state: u32 = !0u32;
    let mut rest = data;
    while let &[b, ref tail @ ..] = rest {
        state = (state >> 8) ^ crc32_ieee_table_at(&CRC32_IEEE_TABLE, (state as u8) ^ b);
        rest = tail;
    }
    !state
}

const DEFLATE_LEN_BASE: [u16; 29] = [
    3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131,
    163, 195, 227, 258,
];

const DEFLATE_LEN_EXTRA: [u8; 29] = [
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0,
];

const DEFLATE_DIST_BASE: [u16; 30] = [
    1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
    2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577,
];

const DEFLATE_DIST_EXTRA: [u8; 30] = [
    0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13,
    13,
];

const DEFLATE_CL_ORDER: [u8; 19] = [
    16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,
];

#[inline]
const fn reverse_bits_u16(mut code: u16, len: u8) -> u16 {
    let mut rev = 0u16;
    let mut rem = len;
    while rem > 0 {
        rev = (rev << 1) | (code & 1);
        code >>= 1;
        rem -= 1;
    }
    rev
}

struct DeflateBitReader<'a> {
    input: &'a [u8],
    pos: usize,
    bit_buf: u64,
    bit_count: u32,
}

impl<'a> DeflateBitReader<'a> {
    const fn new(input: &'a [u8]) -> Self {
        Self {
            input,
            pos: 0,
            bit_buf: 0,
            bit_count: 0,
        }
    }

    #[inline]
    fn fill_bits(&mut self) {
        while self.bit_count <= 56 {
            let Some(&b) = self.input.get(self.pos) else {
                break;
            };
            self.bit_buf |= (b as u64) << (self.bit_count & 63);
            self.bit_count = self.bit_count.saturating_add(8);
            self.pos = self.pos.saturating_add(1);
        }
    }

    #[inline]
    fn consume(&mut self, n: u32) {
        self.bit_buf >>= n & 63;
        self.bit_count = self.bit_count.saturating_sub(n);
    }

    #[inline]
    fn read_bits(&mut self, n: u32) -> Result<u32, DecompressError> {
        if n == 0 {
            return Ok(0);
        }
        self.fill_bits();
        if self.bit_count < n {
            return Err(DecompressError::Truncated);
        }
        let mask = (1u64 << (n & 31)).wrapping_sub(1);
        let val = (self.bit_buf & mask) as u32;
        self.consume(n);
        Ok(val)
    }

    fn align_and_rewind(&mut self) -> Result<(), DecompressError> {
        let rem = self.bit_count & 7;
        self.consume(rem);
        let unread_bytes = (self.bit_count / 8) as usize;
        let Some(new_pos) = self.pos.checked_sub(unread_bytes) else {
            return Err(DecompressError::Corrupt);
        };
        self.pos = new_pos;
        self.bit_buf = 0;
        self.bit_count = 0;
        Ok(())
    }
}

struct HuffTable {
    fast: [u16; 512],
    count: [u16; 16],
    first_code: [u16; 16],
    first_idx: [u16; 16],
    syms: [u16; 288],
    max_bits: u8,
}

impl HuffTable {
    fn from_lengths(lengths: &[u8], max_allowed_bits: u8) -> Result<Self, DecompressError> {
        if lengths.len() > 288 || max_allowed_bits > 15 {
            return Err(DecompressError::Corrupt);
        }
        let mut count = [0u16; 16];
        let mut max_bits = 0u8;
        let mut total_coded = 0u16;
        for &len in lengths {
            if len == 0 {
                continue;
            }
            if len > max_allowed_bits {
                return Err(DecompressError::Corrupt);
            }
            if len > max_bits {
                max_bits = len;
            }
            if let Some(slot) = count.get_mut(len as usize) {
                *slot = slot.saturating_add(1);
            }
            total_coded = total_coded.saturating_add(1);
        }

        let mut table = Self {
            fast: [0u16; 512],
            count,
            first_code: [0u16; 16],
            first_idx: [0u16; 16],
            syms: [0u16; 288],
            max_bits,
        };
        if total_coded == 0 {
            return Ok(table);
        }

        let mut left = 1i32;
        let mut b = 1usize;
        while b <= (max_allowed_bits as usize) {
            left <<= 1;
            let c = match table.count.get(b) {
                Some(&v) => v as i32,
                None => 0,
            };
            left = match left.checked_sub(c) {
                Some(v) if v >= 0 => v,
                _ => return Err(DecompressError::Corrupt),
            };
            b = b.saturating_add(1);
        }
        if left > 0 && !(total_coded == 1 && max_bits == 1) {
            return Err(DecompressError::Corrupt);
        }

        let mut next_code = [0u16; 16];
        let mut next_idx = [0u16; 16];
        let mut code = 0u32;
        let mut idx_acc = 0u16;
        let mut prev_count = 0u32;
        let mut bits = 1usize;
        while bits <= 15 {
            code = (code.saturating_add(prev_count)) << 1;
            if let Some(fc) = table.first_code.get_mut(bits) {
                *fc = code as u16;
            }
            if let Some(nc) = next_code.get_mut(bits) {
                *nc = code as u16;
            }
            if let Some(fi) = table.first_idx.get_mut(bits) {
                *fi = idx_acc;
            }
            if let Some(ni) = next_idx.get_mut(bits) {
                *ni = idx_acc;
            }
            let c = match table.count.get(bits) {
                Some(&v) => v,
                None => 0,
            };
            idx_acc = idx_acc.saturating_add(c);
            prev_count = c as u32;
            bits += 1;
        }

        for (sym_idx, &len) in lengths.iter().enumerate() {
            if len == 0 {
                continue;
            }
            let lb = len as usize;
            let cw = match next_code.get_mut(lb) {
                Some(slot) => {
                    let cur = *slot;
                    *slot = cur.wrapping_add(1);
                    cur
                }
                None => return Err(DecompressError::Corrupt),
            };
            let si = match next_idx.get_mut(lb) {
                Some(slot) => {
                    let cur = *slot as usize;
                    *slot = slot.wrapping_add(1);
                    cur
                }
                None => return Err(DecompressError::Corrupt),
            };
            if let Some(sym_slot) = table.syms.get_mut(si) {
                *sym_slot = sym_idx as u16;
            }
            if len <= 9 {
                let rev = reverse_bits_u16(cw, len) as usize;
                let step = 1usize << ((len as u32) & 15);
                let entry = (len as u16) | ((sym_idx as u16) << 4);
                let mut slot = rev;
                while slot < 512 {
                    if let Some(cell) = table.fast.get_mut(slot) {
                        *cell = entry;
                    }
                    slot = slot.saturating_add(step);
                }
            }
        }
        Ok(table)
    }

    #[inline]
    fn decode(&self, reader: &mut DeflateBitReader<'_>) -> Result<u16, DecompressError> {
        if self.max_bits == 0 {
            return Err(DecompressError::Corrupt);
        }
        reader.fill_bits();
        let fast_entry = self.fast[(reader.bit_buf as usize) & 0x1ff];
        let fast_len = (fast_entry & 0x0f) as u32;
        if fast_len != 0 && reader.bit_count >= fast_len {
            reader.consume(fast_len);
            return Ok(fast_entry >> 4);
        }

        let mut code = 0u32;
        let mut b = 1u32;
        let limit = self.max_bits as u32;
        while b <= limit {
            if reader.bit_count < b {
                return Err(DecompressError::Truncated);
            }
            let next_bit = ((reader.bit_buf >> (b.saturating_sub(1) & 63)) & 1) as u32;
            code = (code << 1) | next_bit;
            let cnt = match self.count.get(b as usize) {
                Some(&c) => c as u32,
                None => 0,
            };
            let first = match self.first_code.get(b as usize) {
                Some(&f) => f as u32,
                None => 0,
            };
            if cnt > 0 && code >= first && code.saturating_sub(first) < cnt {
                let base_idx = match self.first_idx.get(b as usize) {
                    Some(&i) => i as usize,
                    None => return Err(DecompressError::Corrupt),
                };
                let Some(&sym) = self
                    .syms
                    .get(base_idx.saturating_add(code.saturating_sub(first) as usize))
                else {
                    return Err(DecompressError::Corrupt);
                };
                reader.consume(b);
                return Ok(sym);
            }
            b = b.saturating_add(1);
        }
        Err(DecompressError::Corrupt)
    }
}

fn build_fixed_huff_tables() -> Result<(HuffTable, HuffTable), DecompressError> {
    let mut lit_lens = [0u8; 288];
    let mut i = 0usize;
    while i < 288 {
        let len = if i <= 143 {
            8u8
        } else if i <= 255 {
            9u8
        } else if i <= 279 {
            7u8
        } else {
            8u8
        };
        if let Some(slot) = lit_lens.get_mut(i) {
            *slot = len;
        }
        i += 1;
    }
    let dist_lens = [5u8; 32];
    Ok((
        HuffTable::from_lengths(&lit_lens, 15)?,
        HuffTable::from_lengths(&dist_lens, 15)?,
    ))
}

fn build_dynamic_huff_tables(
    reader: &mut DeflateBitReader<'_>,
) -> Result<(HuffTable, HuffTable), DecompressError> {
    let hlit = (reader.read_bits(5)? as usize).saturating_add(257);
    let hdist = (reader.read_bits(5)? as usize).saturating_add(1);
    let hclen = (reader.read_bits(4)? as usize).saturating_add(4);
    if hlit > 286 || hdist > 32 {
        return Err(DecompressError::Corrupt);
    }

    let mut cl_lens = [0u8; 19];
    let mut idx = 0usize;
    while idx < hclen {
        let len = reader.read_bits(3)? as u8;
        if let Some(&ord) = DEFLATE_CL_ORDER.get(idx) {
            if let Some(slot) = cl_lens.get_mut(ord as usize) {
                *slot = len;
            }
        }
        idx += 1;
    }
    let cl_table = HuffTable::from_lengths(&cl_lens, 7)?;

    let total = hlit.saturating_add(hdist);
    let mut lens = [0u8; 320];
    let mut pos = 0usize;
    while pos < total {
        let sym = cl_table.decode(reader)?;
        if sym <= 15 {
            if let Some(slot) = lens.get_mut(pos) {
                *slot = sym as u8;
            }
            pos = pos.saturating_add(1);
        } else if sym == 16 {
            let rep = (reader.read_bits(2)? as usize).saturating_add(3);
            if pos == 0 || pos.saturating_add(rep) > total {
                return Err(DecompressError::Corrupt);
            }
            let prev = match lens.get(pos.saturating_sub(1)) {
                Some(&p) => p,
                None => return Err(DecompressError::Corrupt),
            };
            let mut r = 0usize;
            while r < rep {
                if let Some(slot) = lens.get_mut(pos) {
                    *slot = prev;
                }
                pos = pos.saturating_add(1);
                r = r.saturating_add(1);
            }
        } else if sym == 17 {
            let rep = (reader.read_bits(3)? as usize).saturating_add(3);
            if pos.saturating_add(rep) > total {
                return Err(DecompressError::Corrupt);
            }
            pos = pos.saturating_add(rep);
        } else if sym == 18 {
            let rep = (reader.read_bits(7)? as usize).saturating_add(11);
            if pos.saturating_add(rep) > total {
                return Err(DecompressError::Corrupt);
            }
            pos = pos.saturating_add(rep);
        } else {
            return Err(DecompressError::Corrupt);
        }
    }

    let eob_len = match lens.get(256) {
        Some(&l) => l,
        None => 0,
    };
    if eob_len == 0 {
        return Err(DecompressError::Corrupt);
    }

    let Some(lit_slice) = lens.get(..hlit) else {
        return Err(DecompressError::Corrupt);
    };
    let Some(dist_slice) = lens.get(hlit..total) else {
        return Err(DecompressError::Corrupt);
    };
    Ok((
        HuffTable::from_lengths(lit_slice, 15)?,
        HuffTable::from_lengths(dist_slice, 15)?,
    ))
}

fn decode_huff_block_into(
    reader: &mut DeflateBitReader<'_>,
    lit_table: &HuffTable,
    dist_table: &HuffTable,
    out: &mut Vec<u8>,
    member_start: usize,
    eff_cap: usize,
) -> Result<(), DecompressError> {
    loop {
        let sym = lit_table.decode(reader)?;
        if sym < 256 {
            if out.len() >= eff_cap {
                return Err(DecompressError::OutputTooLarge);
            }
            out.push(sym as u8);
        } else if sym == 256 {
            return Ok(());
        } else {
            let lidx = (sym as usize).saturating_sub(257);
            let Some(&base_len) = DEFLATE_LEN_BASE.get(lidx) else {
                return Err(DecompressError::Corrupt);
            };
            let Some(&extra_bits) = DEFLATE_LEN_EXTRA.get(lidx) else {
                return Err(DecompressError::Corrupt);
            };
            let extra_len = reader.read_bits(extra_bits as u32)? as usize;
            let copy_len = (base_len as usize).saturating_add(extra_len);

            let dist_sym = dist_table.decode(reader)? as usize;
            let Some(&base_dist) = DEFLATE_DIST_BASE.get(dist_sym) else {
                return Err(DecompressError::Corrupt);
            };
            let Some(&dist_extra_bits) = DEFLATE_DIST_EXTRA.get(dist_sym) else {
                return Err(DecompressError::Corrupt);
            };
            let extra_dist = reader.read_bits(dist_extra_bits as u32)? as usize;
            let distance = (base_dist as usize).saturating_add(extra_dist);
            let window_avail = out.len().saturating_sub(member_start);
            if distance == 0 || distance > 32_768 || distance > window_avail {
                return Err(DecompressError::Corrupt);
            }
            copy_backref(out, distance, copy_len, eff_cap)?;
        }
    }
}

fn deflate_decompress_into(
    input: &[u8],
    out: &mut Vec<u8>,
    member_start: usize,
    eff_cap: usize,
) -> Result<usize, DecompressError> {
    let mut reader = DeflateBitReader::new(input);
    let mut fixed_cache: Option<(HuffTable, HuffTable)> = None;
    loop {
        let bfinal = reader.read_bits(1)?;
        let btype = reader.read_bits(2)?;
        match btype {
            0 => {
                reader.align_and_rewind()?;
                let Some(hdr_bytes) = reader.input.get(reader.pos..reader.pos.saturating_add(4))
                else {
                    return Err(DecompressError::Truncated);
                };
                let &[l0, l1, nl0, nl1] = hdr_bytes else {
                    return Err(DecompressError::Truncated);
                };
                let len = u16::from_le_bytes([l0, l1]);
                let nlen = u16::from_le_bytes([nl0, nl1]);
                if len != !nlen {
                    return Err(DecompressError::Corrupt);
                }
                let data_start = reader.pos.saturating_add(4);
                let data_end = data_start.saturating_add(len as usize);
                let Some(raw_slice) = reader.input.get(data_start..data_end) else {
                    return Err(DecompressError::Truncated);
                };
                let Some(next_out_len) = out.len().checked_add(len as usize) else {
                    return Err(DecompressError::OutputTooLarge);
                };
                if next_out_len > eff_cap {
                    return Err(DecompressError::OutputTooLarge);
                }
                out.extend_from_slice(raw_slice);
                reader.pos = data_end;
            }
            1 => {
                if fixed_cache.is_none() {
                    fixed_cache = Some(build_fixed_huff_tables()?);
                }
                let Some((ref lit_t, ref dist_t)) = fixed_cache else {
                    return Err(DecompressError::Corrupt);
                };
                decode_huff_block_into(&mut reader, lit_t, dist_t, out, member_start, eff_cap)?;
            }
            2 => {
                let (lit_t, dist_t) = build_dynamic_huff_tables(&mut reader)?;
                decode_huff_block_into(&mut reader, &lit_t, &dist_t, out, member_start, eff_cap)?;
            }
            _ => return Err(DecompressError::Corrupt),
        }
        if bfinal != 0 {
            reader.align_and_rewind()?;
            return Ok(reader.pos);
        }
    }
}

fn skip_gzip_cstring(input: &[u8], start: usize) -> Result<usize, DecompressError> {
    let mut pos = start;
    while let Some(&b) = input.get(pos) {
        pos = pos.saturating_add(1);
        if b == 0 {
            return Ok(pos);
        }
    }
    Err(DecompressError::Truncated)
}

/// Decompress an RFC 1952 Gzip stream (including optional `FEXTRA` / `FNAME` / `FCOMMENT` /
/// `FHCRC` header fields, stored/fixed/dynamic RFC 1951 DEFLATE blocks, concatenated
/// multi-member streams, and per-member IEEE CRC-32 + `ISIZE` trailer verification),
/// strictly bounded by `max_out`.
pub fn gzip_decompress(input: &[u8], max_out: usize) -> Result<Vec<u8>, DecompressError> {
    if input.is_empty() {
        return Err(DecompressError::Truncated);
    }
    let eff_cap =
        kafka_decompress_cap_clamp(max_out as u64, MAX_DECOMPRESSED_BATCH_BYTES as u64) as usize;
    let mut out = Vec::new();
    let mut cur = input;

    while !cur.is_empty() {
        if cur.len() < 10 {
            return Err(DecompressError::Truncated);
        }
        let Some(base_hdr) = cur.get(..10) else {
            return Err(DecompressError::Truncated);
        };
        let &[id1, id2, cm, flg, _mt0, _mt1, _mt2, _mt3, _xfl, _os] = base_hdr else {
            return Err(DecompressError::Truncated);
        };
        if [id1, id2] != GZIP_MAGIC || cm != 8 || (flg & 0xe0) != 0 {
            return Err(DecompressError::Corrupt);
        }

        let mut hdr_pos = 10usize;
        if (flg & 0x04) != 0 {
            let Some(xlen_bytes) = cur.get(hdr_pos..hdr_pos.saturating_add(2)) else {
                return Err(DecompressError::Truncated);
            };
            let &[x0, x1] = xlen_bytes else {
                return Err(DecompressError::Truncated);
            };
            let xlen = u16::from_le_bytes([x0, x1]) as usize;
            let after_x = hdr_pos.saturating_add(2).saturating_add(xlen);
            if cur.len() < after_x {
                return Err(DecompressError::Truncated);
            }
            hdr_pos = after_x;
        }
        if (flg & 0x08) != 0 {
            hdr_pos = skip_gzip_cstring(cur, hdr_pos)?;
        }
        if (flg & 0x10) != 0 {
            hdr_pos = skip_gzip_cstring(cur, hdr_pos)?;
        }
        if (flg & 0x02) != 0 {
            let Some(hdr_prefix) = cur.get(..hdr_pos) else {
                return Err(DecompressError::Truncated);
            };
            let Some(hcrc_bytes) = cur.get(hdr_pos..hdr_pos.saturating_add(2)) else {
                return Err(DecompressError::Truncated);
            };
            let &[c0, c1] = hcrc_bytes else {
                return Err(DecompressError::Truncated);
            };
            let want_crc16 = u16::from_le_bytes([c0, c1]);
            let got_crc16 = (crc32_ieee(hdr_prefix) & 0xffff) as u16;
            if want_crc16 != got_crc16 {
                return Err(DecompressError::Corrupt);
            }
            hdr_pos = hdr_pos.saturating_add(2);
        }

        let Some(after_hdr) = cur.get(hdr_pos..) else {
            return Err(DecompressError::Truncated);
        };
        let member_out_start = out.len();
        let deflate_consumed =
            deflate_decompress_into(after_hdr, &mut out, member_out_start, eff_cap)?;
        let Some(after_deflate) = after_hdr.get(deflate_consumed..) else {
            return Err(DecompressError::Truncated);
        };
        let &[c0, c1, c2, c3, s0, s1, s2, s3, ref next_member @ ..] = after_deflate else {
            return Err(DecompressError::Truncated);
        };
        let want_crc32 = read_u32_le(c0, c1, c2, c3);
        let want_isize = read_u32_le(s0, s1, s2, s3);
        let Some(member_out) = out.get(member_out_start..) else {
            return Err(DecompressError::Corrupt);
        };
        if crc32_ieee(member_out) != want_crc32 || (member_out.len() as u32) != want_isize {
            return Err(DecompressError::Corrupt);
        }
        cur = next_member;
    }

    Ok(out)
}

struct DeflateBitWriter {
    out: Vec<u8>,
    bit_buf: u64,
    bit_count: u32,
}

impl DeflateBitWriter {
    fn with_capacity(cap: usize) -> Self {
        Self {
            out: Vec::with_capacity(cap.min(MAX_DECOMPRESSED_BATCH_BYTES)),
            bit_buf: 0,
            bit_count: 0,
        }
    }

    #[inline]
    fn write_bits(&mut self, val: u32, n: u32) {
        if n == 0 {
            return;
        }
        let mask = (1u64 << (n & 31)).wrapping_sub(1);
        self.bit_buf |= ((val as u64) & mask) << (self.bit_count & 63);
        self.bit_count = self.bit_count.saturating_add(n);
        while self.bit_count >= 8 {
            self.out.push((self.bit_buf & 0xff) as u8);
            self.bit_buf >>= 8;
            self.bit_count = self.bit_count.saturating_sub(8);
        }
    }

    #[inline]
    fn write_fixed_sym(&mut self, sym: u16) {
        if sym <= 143 {
            let cw = 0x30u16.wrapping_add(sym);
            self.write_bits(reverse_bits_u16(cw, 8) as u32, 8);
        } else if sym <= 255 {
            let cw = 0x190u16.wrapping_add(sym - 144);
            self.write_bits(reverse_bits_u16(cw, 9) as u32, 9);
        } else if sym <= 279 {
            let cw = sym - 256;
            self.write_bits(reverse_bits_u16(cw, 7) as u32, 7);
        } else {
            let cw = 0xc0u16.wrapping_add(sym.saturating_sub(280));
            self.write_bits(reverse_bits_u16(cw, 8) as u32, 8);
        }
    }

    #[inline]
    fn write_fixed_dist(&mut self, dist_sym: u8) {
        self.write_bits(reverse_bits_u16(dist_sym as u16, 5) as u32, 5);
    }

    fn flush_to_byte(&mut self) {
        if self.bit_count > 0 {
            self.out.push((self.bit_buf & 0xff) as u8);
            self.bit_buf = 0;
            self.bit_count = 0;
        }
    }
}

#[inline]
fn encode_deflate_length(len: usize) -> (u16, u8, u32) {
    let mut i = 28usize;
    loop {
        let base = match DEFLATE_LEN_BASE.get(i) {
            Some(&b) => b as usize,
            None => 3,
        };
        if len >= base || i == 0 {
            let extra = match DEFLATE_LEN_EXTRA.get(i) {
                Some(&e) => e,
                None => 0,
            };
            return (
                257u16.saturating_add(i as u16),
                extra,
                len.saturating_sub(base) as u32,
            );
        }
        i = i.saturating_sub(1);
    }
}

#[inline]
fn encode_deflate_distance(dist: usize) -> (u8, u8, u32) {
    let mut i = 29usize;
    loop {
        let base = match DEFLATE_DIST_BASE.get(i) {
            Some(&b) => b as usize,
            None => 1,
        };
        if dist >= base || i == 0 {
            let extra = match DEFLATE_DIST_EXTRA.get(i) {
                Some(&e) => e,
                None => 0,
            };
            return (i as u8, extra, dist.saturating_sub(base) as u32);
        }
        i = i.saturating_sub(1);
    }
}

#[inline]
const fn hash4_12bit(v: u32) -> usize {
    (v.wrapping_mul(0x1e35_a7bd) >> 20) as usize
}

/// Compress `input` into a standard RFC 1952 Gzip stream (`0x1f 0x8b`, `CM=8` DEFLATE with
/// 32 KiB LZ77 matching + Fixed Huffman encoding + IEEE CRC-32 & `ISIZE` trailer).
#[must_use]
pub fn gzip_compress(input: &[u8]) -> Vec<u8> {
    let cap_hint = input
        .len()
        .saturating_add(24)
        .min(MAX_DECOMPRESSED_BATCH_BYTES);
    let mut bw = DeflateBitWriter::with_capacity(cap_hint);
    bw.out
        .extend_from_slice(&[0x1f, 0x8b, 0x08, 0x00, 0, 0, 0, 0, 0x00, 0xff]);

    bw.write_bits(1, 1); // BFINAL = 1
    bw.write_bits(1, 2); // BTYPE = 01 (Fixed Huffman)

    if input.len() < 4 {
        for &b in input {
            bw.write_fixed_sym(b as u16);
        }
    } else {
        let mut table = [0u32; 4096];
        let mut table_init = [false; 4096];
        let mut ip = 0usize;
        let limit = input.len() - 4;

        while ip <= limit {
            let Some(cur4) = load_u32_at(input, ip) else {
                break;
            };
            let h = hash4_12bit(cur4) & 0xfff;
            let cand = match table.get(h) {
                Some(&c) => c as usize,
                None => 0,
            };
            let valid_cand = match table_init.get(h) {
                Some(&f) => f,
                None => false,
            };
            if let Some(slot) = table.get_mut(h) {
                *slot = ip as u32;
            }
            if let Some(flag) = table_init.get(h).copied() {
                if !flag {
                    if let Some(fmut) = table_init.get_mut(h) {
                        *fmut = true;
                    }
                }
            }

            if valid_cand && cand < ip && ip.saturating_sub(cand) <= 32_768 {
                if let Some(cand4) = load_u32_at(input, cand) {
                    if cand4 == cur4 {
                        let dist = ip.saturating_sub(cand);
                        let max_mlen = input.len().saturating_sub(ip).min(258);
                        let mut mlen = 4usize;
                        while mlen < max_mlen {
                            let a = input.get(cand.saturating_add(mlen));
                            let b = input.get(ip.saturating_add(mlen));
                            match (a, b) {
                                (Some(&x), Some(&y)) if x == y => {
                                    mlen = mlen.saturating_add(1);
                                }
                                _ => break,
                            }
                        }
                        let (lsym, lextra_bits, lextra_val) = encode_deflate_length(mlen);
                        bw.write_fixed_sym(lsym);
                        bw.write_bits(lextra_val, lextra_bits as u32);
                        let (dsym, dextra_bits, dextra_val) = encode_deflate_distance(dist);
                        bw.write_fixed_dist(dsym);
                        bw.write_bits(dextra_val, dextra_bits as u32);

                        // Seed intermediate hash positions on short matches for better density.
                        if mlen <= 16 {
                            let mut step = 1usize;
                            while step < mlen && ip.saturating_add(step) <= limit {
                                if let Some(s4) = load_u32_at(input, ip.saturating_add(step)) {
                                    let sh = hash4_12bit(s4) & 0xfff;
                                    if let Some(slot) = table.get_mut(sh) {
                                        *slot = ip.saturating_add(step) as u32;
                                    }
                                    if let Some(fmut) = table_init.get_mut(sh) {
                                        *fmut = true;
                                    }
                                }
                                step = step.saturating_add(1);
                            }
                        }
                        ip = ip.saturating_add(mlen);
                        continue;
                    }
                }
            }

            if let Some(&lit_byte) = input.get(ip) {
                bw.write_fixed_sym(lit_byte as u16);
            }
            ip = ip.saturating_add(1);
        }

        while ip < input.len() {
            if let Some(&lit_byte) = input.get(ip) {
                bw.write_fixed_sym(lit_byte as u16);
            }
            ip = ip.saturating_add(1);
        }
    }

    bw.write_fixed_sym(256); // end-of-block
    bw.flush_to_byte();
    bw.out.extend_from_slice(&crc32_ieee(input).to_le_bytes());
    bw.out
        .extend_from_slice(&(input.len() as u32).to_le_bytes());
    bw.out
}
