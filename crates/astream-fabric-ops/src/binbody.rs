// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Lossless, line-safe binary-body chunk codec & whole-body CRC32 reassembler
//! (`DESIGN-aterm-fabric.md` §9.1 / §11.2 register 21 / line 4047 `inbox get --bytes`,
//! `Astream.Broker.TlaBinaryEnvelope`).
//!
//! Arbitrary binary payloads (`\0`, `\r`, `\n`, non-UTF-8 bytes, and multi-KiB blobs that
//! exceed a bridge's single `deliver` request line) encode into one or more ASCII-clean
//! `v=1` lines:
//! `v=1 bin_id=<u64> part=<idx>/<total> total_len=<bytes> crc32=<hex8> hex=<bytes>`
//! and reassemble losslessly with end-to-end IEEE CRC-32 verification, zero heap
//! over-allocation, `0 mandated`, and `0 runtime_checked` obligations.

#![allow(
    clippy::manual_is_ascii_check,
    clippy::manual_is_multiple_of,
    clippy::question_mark,
    clippy::vec_init_then_push
)]

use astream_wire::crc32_ieee;

#[cfg(clean_islands)]
#[path = "binbody_island.rs"]
mod binbody_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn binbody_chunk_idx_clamp(idx: u64, total: u64) -> u64 {
    if idx < total {
        idx
    } else {
        total
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn binbody_bytes_accum_clamp(accum: u64, max_bytes: u64) -> u64 {
    if accum < max_bytes {
        accum
    } else {
        max_bytes
    }
}
#[cfg(clean_islands)]
pub use binbody_island::{binbody_bytes_accum_clamp, binbody_chunk_idx_clamp};

/// Maximum raw binary payload bytes per encoded chunk (`512` raw bytes -> `1024` hex chars,
/// well below `deliver` single-line limits).
pub const MAX_BIN_CHUNK_RAW_BYTES: usize = 512;

/// Hard cap on total reassembled binary body size (`256 KiB`).
pub const MAX_BIN_TOTAL_BYTES: usize = 262_144;

/// Maximum number of chunks in one binary envelope (`MAX_BIN_TOTAL_BYTES / MAX_BIN_CHUNK_RAW_BYTES = 512`).
pub const MAX_BIN_CHUNKS: u64 = 512;

/// Maximum encoded byte length of one single-line `V1BinaryChunk`.
pub const MAX_BIN_LINE_BYTES: usize = 1200;

contract_fn! {
    /// Kernel-certified completion check (`received == total`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `binbody_complete_valid_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn binbody_complete_valid(received: u64, total: u64) -> bool
    clauses [ensures result == (received == total)]
    {
        received == total
    }
}

/// Errors returned when encoding, decoding, or reassembling a binary envelope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinBodyError {
    /// Payload or line exceeds bounded byte/chunk limits.
    Oversized,
    /// Malformed `v=1` header, missing field, or out-of-range `part=<i>/<n>`.
    MalformedChunk,
    /// Duplicate or conflicting metadata across chunks of the same `bin_id`.
    ConflictingMetadata,
    /// Whole-body IEEE CRC-32 or byte-length mismatch upon completion.
    IntegrityMismatch,
}

/// One decoded ASCII-safe `v=1` binary envelope chunk.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct V1BinaryChunk {
    /// Sender-assigned correlation id for this multi-part binary payload.
    pub bin_id: u64,
    /// Zero-based chunk index (`0..total_parts`).
    pub part_idx: u64,
    /// Total number of chunks (`1..=MAX_BIN_CHUNKS`).
    pub total_parts: u64,
    /// Declared total decoded byte length across all parts (`0..=MAX_BIN_TOTAL_BYTES`).
    pub total_len: u64,
    /// Whole-body IEEE CRC-32 over the complete unchunked binary payload.
    pub body_crc32: u32,
    /// Raw bytes carried in this part (`<= MAX_BIN_CHUNK_RAW_BYTES`).
    pub data: Vec<u8>,
}

const fn find_ascii_byte(mut rest: &[u8], needle: u8) -> Option<usize> {
    let mut idx = 0usize;
    while let &[b, ref tail @ ..] = rest {
        if b == needle {
            return Some(idx);
        }
        idx = idx.saturating_add(1);
        rest = tail;
    }
    None
}

fn split_byte_once(bytes: &[u8], delim: u8) -> Option<(&[u8], &[u8])> {
    let Some(i) = find_ascii_byte(bytes, delim) else {
        return None;
    };
    let Some(next) = i.checked_add(1) else {
        return None;
    };
    let Some(head) = bytes.get(..i) else {
        return None;
    };
    let Some(tail) = bytes.get(next..) else {
        return None;
    };
    Some((head, tail))
}

fn next_space_token(bytes: &[u8]) -> (&[u8], &[u8]) {
    let mut trimmed = bytes;
    while let &[b' ', ref tail @ ..] = trimmed {
        trimmed = tail;
    }
    match split_byte_once(trimmed, b' ') {
        Some((tok, rest)) => (tok, rest),
        None => (trimmed, &[]),
    }
}

impl V1BinaryChunk {
    /// Format this chunk as a single newline-free ASCII `v=1` line.
    #[must_use]
    pub fn encode_line(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(b"v=1 bin_id=");
        push_dec_u64(&mut out, self.bin_id);
        out.extend_from_slice(b" part=");
        let idx = binbody_chunk_idx_clamp(self.part_idx, self.total_parts);
        push_dec_u64(&mut out, idx);
        out.push(b'/');
        push_dec_u64(&mut out, self.total_parts);
        out.extend_from_slice(b" total_len=");
        push_dec_u64(&mut out, self.total_len);
        out.extend_from_slice(b" crc32=");
        push_hex_u32(&mut out, self.body_crc32);
        out.extend_from_slice(b" hex=");
        let mut rest = self.data.as_slice();
        while let &[b, ref tail @ ..] = rest {
            push_hex_byte(&mut out, b);
            rest = tail;
        }
        out
    }

    /// Decode and validate a single `v=1` binary chunk line.
    pub fn decode_line(raw: &[u8]) -> Result<Self, BinBodyError> {
        if raw.is_empty() || raw.len() > MAX_BIN_LINE_BYTES {
            return Err(BinBodyError::Oversized);
        }
        if core::str::from_utf8(raw).is_err() {
            return Err(BinBodyError::MalformedChunk);
        }
        let (first, mut rem_tokens) = next_space_token(raw);
        if first != b"v=1" {
            return Err(BinBodyError::MalformedChunk);
        }

        let mut bin_id: Option<u64> = None;
        let mut part_pair: Option<(u64, u64)> = None;
        let mut total_len: Option<u64> = None;
        let mut body_crc32: Option<u32> = None;
        let mut data: Option<Vec<u8>> = None;

        while !rem_tokens.is_empty() {
            let (tok, next_rem) = next_space_token(rem_tokens);
            rem_tokens = next_rem;
            if tok.is_empty() {
                continue;
            }
            let Some((k, v)) = split_byte_once(tok, b'=') else {
                return Err(BinBodyError::MalformedChunk);
            };
            if k == b"bin_id" {
                if bin_id.is_some() {
                    return Err(BinBodyError::MalformedChunk);
                }
                let val = match parse_u64_dec_bytes(v) {
                    Ok(n) => n,
                    Err(e) => return Err(e),
                };
                bin_id = Some(val);
            } else if k == b"part" {
                if part_pair.is_some() {
                    return Err(BinBodyError::MalformedChunk);
                }
                let Some((idx_b, tot_b)) = split_byte_once(v, b'/') else {
                    return Err(BinBodyError::MalformedChunk);
                };
                let idx = match parse_u64_dec_bytes(idx_b) {
                    Ok(n) => n,
                    Err(e) => return Err(e),
                };
                let tot = match parse_u64_dec_bytes(tot_b) {
                    Ok(n) => n,
                    Err(e) => return Err(e),
                };
                if tot == 0 || tot > MAX_BIN_CHUNKS || idx >= tot {
                    return Err(BinBodyError::MalformedChunk);
                }
                part_pair = Some((idx, tot));
            } else if k == b"total_len" {
                if total_len.is_some() {
                    return Err(BinBodyError::MalformedChunk);
                }
                let tl = match parse_u64_dec_bytes(v) {
                    Ok(n) => n,
                    Err(e) => return Err(e),
                };
                if tl > MAX_BIN_TOTAL_BYTES as u64 {
                    return Err(BinBodyError::Oversized);
                }
                total_len = Some(tl);
            } else if k == b"crc32" {
                if body_crc32.is_some() {
                    return Err(BinBodyError::MalformedChunk);
                }
                let crc = match parse_u32_hex8_bytes(v) {
                    Ok(n) => n,
                    Err(e) => return Err(e),
                };
                body_crc32 = Some(crc);
            } else if k == b"hex" {
                if data.is_some() {
                    return Err(BinBodyError::MalformedChunk);
                }
                let bytes_val = match decode_hex_bytes_slice(v) {
                    Ok(n) => n,
                    Err(e) => return Err(e),
                };
                data = Some(bytes_val);
            } else {
                return Err(BinBodyError::MalformedChunk);
            }
        }

        let (Some(id), Some((part_idx, total_parts)), Some(tlen), Some(crc), Some(bytes)) =
            (bin_id, part_pair, total_len, body_crc32, data)
        else {
            return Err(BinBodyError::MalformedChunk);
        };
        Ok(Self {
            bin_id: id,
            part_idx,
            total_parts,
            total_len: tlen,
            body_crc32: crc,
            data: bytes,
        })
    }
}

/// Split an arbitrary binary slice (`0..=MAX_BIN_TOTAL_BYTES`) into `1..=MAX_BIN_CHUNKS`
/// `V1BinaryChunk` records stamped with `bin_id` and whole-body IEEE CRC-32.
pub fn encode_binary_envelope(
    bin_id: u64,
    payload: &[u8],
) -> Result<Vec<V1BinaryChunk>, BinBodyError> {
    if payload.len() > MAX_BIN_TOTAL_BYTES {
        return Err(BinBodyError::Oversized);
    }
    let body_crc32 = crc32_ieee(payload);
    let total_len = payload.len() as u64;
    if payload.is_empty() {
        let mut single = Vec::new();
        single.push(V1BinaryChunk {
            bin_id,
            part_idx: 0,
            total_parts: 1,
            total_len: 0,
            body_crc32,
            data: Vec::new(),
        });
        return Ok(single);
    }

    let mut raw_slices: Vec<&[u8]> = Vec::new();
    let mut rem = payload;
    while !rem.is_empty() {
        let take = if rem.len() < MAX_BIN_CHUNK_RAW_BYTES {
            rem.len()
        } else {
            MAX_BIN_CHUNK_RAW_BYTES
        };
        let Some(head) = rem.get(..take) else {
            break;
        };
        let Some(tail) = rem.get(take..) else {
            break;
        };
        raw_slices.push(head);
        rem = tail;
    }
    let total_parts = raw_slices.len() as u64;
    let mut out = Vec::new();
    let mut idx = 0u64;
    let mut rest_slices = raw_slices.as_slice();
    while let &[chunk_bytes, ref tail @ ..] = rest_slices {
        let clamped_idx = binbody_chunk_idx_clamp(idx, total_parts);
        let mut data = Vec::new();
        data.extend_from_slice(chunk_bytes);
        out.push(V1BinaryChunk {
            bin_id,
            part_idx: clamped_idx,
            total_parts,
            total_len,
            body_crc32,
            data,
        });
        idx = idx.saturating_add(1);
        rest_slices = tail;
    }
    Ok(out)
}

/// Out-of-order / duplicate-tolerant bounded reassembler for a single `bin_id`.
#[derive(Debug, Clone)]
pub struct BinaryReassembler {
    bin_id: u64,
    total_parts: u64,
    total_len: u64,
    body_crc32: u32,
    slots: Vec<Option<Vec<u8>>>,
    received_parts: u64,
    accum_bytes: u64,
}

impl BinaryReassembler {
    /// Start reassembling from the first observed chunk.
    pub fn from_first_chunk(chunk: V1BinaryChunk) -> Result<Self, BinBodyError> {
        if chunk.total_parts == 0 || chunk.total_parts > MAX_BIN_CHUNKS {
            return Err(BinBodyError::MalformedChunk);
        }
        if chunk.total_len > MAX_BIN_TOTAL_BYTES as u64 {
            return Err(BinBodyError::Oversized);
        }
        let cap = if (chunk.total_parts as usize) < (MAX_BIN_CHUNKS as usize) {
            chunk.total_parts as usize
        } else {
            MAX_BIN_CHUNKS as usize
        };
        let mut slots = Vec::new();
        let mut k = 0usize;
        while k < cap {
            slots.push(None);
            k = k.saturating_add(1);
        }
        let mut r = Self {
            bin_id: chunk.bin_id,
            total_parts: chunk.total_parts,
            total_len: chunk.total_len,
            body_crc32: chunk.body_crc32,
            slots,
            received_parts: 0,
            accum_bytes: 0,
        };
        if let Err(e) = r.ingest(chunk) {
            return Err(e);
        }
        Ok(r)
    }

    /// Ingest one chunk (idempotent on exact duplicate retries).
    pub fn ingest(&mut self, chunk: V1BinaryChunk) -> Result<bool, BinBodyError> {
        if chunk.bin_id != self.bin_id
            || chunk.total_parts != self.total_parts
            || chunk.total_len != self.total_len
            || chunk.body_crc32 != self.body_crc32
        {
            return Err(BinBodyError::ConflictingMetadata);
        }
        let Some(slot) = self.slots.get_mut(chunk.part_idx as usize) else {
            return Err(BinBodyError::MalformedChunk);
        };
        if let Some(existing) = slot {
            if existing.as_slice() != chunk.data.as_slice() {
                return Err(BinBodyError::ConflictingMetadata);
            }
            return Ok(binbody_complete_valid(
                self.received_parts,
                self.total_parts,
            ));
        }
        let next_accum = self.accum_bytes.saturating_add(chunk.data.len() as u64);
        let clamped_accum = binbody_bytes_accum_clamp(next_accum, MAX_BIN_TOTAL_BYTES as u64);
        if next_accum > MAX_BIN_TOTAL_BYTES as u64 || next_accum > self.total_len {
            return Err(BinBodyError::Oversized);
        }
        *slot = Some(chunk.data);
        self.accum_bytes = clamped_accum;
        self.received_parts = self.received_parts.saturating_add(1);
        Ok(binbody_complete_valid(
            self.received_parts,
            self.total_parts,
        ))
    }

    /// Extract and CRC-verify the complete binary body once `binbody_complete_valid` holds.
    pub fn finish(&self) -> Result<Vec<u8>, BinBodyError> {
        if !binbody_complete_valid(self.received_parts, self.total_parts) {
            return Err(BinBodyError::MalformedChunk);
        }
        if self.accum_bytes != self.total_len {
            return Err(BinBodyError::IntegrityMismatch);
        }
        let mut out = Vec::new();
        let mut rest = self.slots.as_slice();
        while let &[ref opt, ref tail @ ..] = rest {
            let Some(part_bytes) = opt else {
                return Err(BinBodyError::MalformedChunk);
            };
            out.extend_from_slice(part_bytes);
            rest = tail;
        }
        if crc32_ieee(&out) != self.body_crc32 {
            return Err(BinBodyError::IntegrityMismatch);
        }
        Ok(out)
    }
}

fn push_dec_u64(out: &mut Vec<u8>, mut val: u64) {
    if val == 0 {
        out.push(b'0');
        return;
    }
    let mut rev = Vec::new();
    while val > 0 {
        let digit = (val % 10) as u8;
        rev.push(b'0'.wrapping_add(digit));
        val /= 10;
    }
    while let Some(b) = rev.pop() {
        out.push(b);
    }
}

fn hex_nibble_char(nib: u8) -> u8 {
    if nib < 10 {
        b'0'.wrapping_add(nib)
    } else {
        b'a'.wrapping_add(nib.saturating_sub(10))
    }
}

fn push_hex_byte(out: &mut Vec<u8>, b: u8) {
    out.push(hex_nibble_char(b >> 4));
    out.push(hex_nibble_char(b & 0x0F));
}

fn push_hex_u32(out: &mut Vec<u8>, v: u32) {
    push_hex_byte(out, ((v >> 24) & 0xFF) as u8);
    push_hex_byte(out, ((v >> 16) & 0xFF) as u8);
    push_hex_byte(out, ((v >> 8) & 0xFF) as u8);
    push_hex_byte(out, (v & 0xFF) as u8);
}

fn parse_u64_dec_bytes(bytes: &[u8]) -> Result<u64, BinBodyError> {
    if bytes.is_empty() || bytes.len() > 20 {
        return Err(BinBodyError::MalformedChunk);
    }
    let mut acc = 0u64;
    let mut rest = bytes;
    while let &[b, ref tail @ ..] = rest {
        if !matches!(b, b'0'..=b'9') {
            return Err(BinBodyError::MalformedChunk);
        }
        let d = b.saturating_sub(b'0') as u64;
        let Some(mul) = acc.checked_mul(10) else {
            return Err(BinBodyError::MalformedChunk);
        };
        let Some(next) = mul.checked_add(d) else {
            return Err(BinBodyError::MalformedChunk);
        };
        acc = next;
        rest = tail;
    }
    Ok(acc)
}

fn decode_nibble(b: u8) -> Result<u8, BinBodyError> {
    if matches!(b, b'0'..=b'9') {
        Ok(b.saturating_sub(b'0'))
    } else if matches!(b, b'a'..=b'f') {
        Ok(b.saturating_sub(b'a').wrapping_add(10))
    } else if matches!(b, b'A'..=b'F') {
        Ok(b.saturating_sub(b'A').wrapping_add(10))
    } else {
        Err(BinBodyError::MalformedChunk)
    }
}

fn decode_hex_pair(hi: u8, lo: u8) -> Result<u8, BinBodyError> {
    let h = match decode_nibble(hi) {
        Ok(v) => v,
        Err(e) => return Err(e),
    };
    let l = match decode_nibble(lo) {
        Ok(v) => v,
        Err(e) => return Err(e),
    };
    Ok((h << 4) | l)
}

fn parse_u32_hex8_bytes(bytes: &[u8]) -> Result<u32, BinBodyError> {
    let &[b0, b1, b2, b3, b4, b5, b6, b7] = bytes else {
        return Err(BinBodyError::MalformedChunk);
    };
    let h0 = match decode_hex_pair(b0, b1) {
        Ok(v) => v,
        Err(e) => return Err(e),
    };
    let h1 = match decode_hex_pair(b2, b3) {
        Ok(v) => v,
        Err(e) => return Err(e),
    };
    let h2 = match decode_hex_pair(b4, b5) {
        Ok(v) => v,
        Err(e) => return Err(e),
    };
    let h3 = match decode_hex_pair(b6, b7) {
        Ok(v) => v,
        Err(e) => return Err(e),
    };
    Ok(((h0 as u32) << 24) | ((h1 as u32) << 16) | ((h2 as u32) << 8) | (h3 as u32))
}

fn decode_hex_bytes_slice(bytes: &[u8]) -> Result<Vec<u8>, BinBodyError> {
    if bytes.len() % 2 != 0 {
        return Err(BinBodyError::MalformedChunk);
    }
    let out_len = bytes.len() / 2;
    if out_len > MAX_BIN_CHUNK_RAW_BYTES {
        return Err(BinBodyError::Oversized);
    }
    let mut out = Vec::new();
    let mut rest = bytes;
    while let &[hi, lo, ref tail @ ..] = rest {
        let byte = match decode_hex_pair(hi, lo) {
            Ok(v) => v,
            Err(e) => return Err(e),
        };
        out.push(byte);
        rest = tail;
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn binary_payload_with_nuls_newlines_and_non_utf8_round_trips_out_of_order() {
        let mut payload = Vec::new();
        for i in 0..1300usize {
            payload.push((i.wrapping_mul(37) & 0xFF) as u8);
        }
        payload[0] = 0x00;
        payload[1] = b'\n';
        payload[2] = b'\r';
        payload[3] = 0xFF;
        payload[4] = 0xFE;

        let chunks = encode_binary_envelope(9001, &payload).unwrap();
        assert_eq!(chunks.len(), 3);

        // Encode to wire lines and ensure no line contains `\n` or `\r`.
        let mut lines = Vec::new();
        for c in &chunks {
            let line = c.encode_line();
            assert!(!line.contains(&b'\n') && !line.contains(&b'\r'));
            lines.push(line);
        }

        // Reassemble out of order (2, 0, duplicate 2, 1).
        let c2 = V1BinaryChunk::decode_line(&lines[2]).unwrap();
        let c0 = V1BinaryChunk::decode_line(&lines[0]).unwrap();
        let c2_dup = V1BinaryChunk::decode_line(&lines[2]).unwrap();
        let c1 = V1BinaryChunk::decode_line(&lines[1]).unwrap();

        let mut reasm = BinaryReassembler::from_first_chunk(c2).unwrap();
        assert!(!reasm.ingest(c0).unwrap());
        assert!(!reasm.ingest(c2_dup).unwrap());
        assert!(reasm.ingest(c1).unwrap());

        let recovered = reasm.finish().unwrap();
        assert_eq!(recovered, payload);
    }

    #[test]
    fn corrupted_chunk_fails_crc32_verification() {
        let chunks = encode_binary_envelope(77, b"\x00\xffhello\nworld").unwrap();
        let mut bad = chunks[0].clone();
        bad.data[2] ^= 0x01;
        let r = BinaryReassembler::from_first_chunk(bad).unwrap();
        assert_eq!(r.finish(), Err(BinBodyError::IntegrityMismatch));
    }
}
