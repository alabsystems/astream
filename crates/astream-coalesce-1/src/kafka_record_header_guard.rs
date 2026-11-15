// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Kafka RecordBatch v2 zigzag-varint record header codec & budget guard (`astream-kafka`).
//!
//! Encodes and decodes Kafka v2 record header arrays (`count: varint`, followed by
//! `(key_len: varint, key_utf8, val_len: varint, optional_val_bytes)`) under strict
//! [`MAX_KAFKA_RECORD_HEADERS`] (`64`) and [`MAX_KAFKA_HEADER_BLOCK_BYTES`] (`16 KiB`)
//! limits so hostile giant varint counts on untrusted network frames fail closed without
//! pre-allocating memory. Zero closures (`0 mandated`), backed by Clean TLA+ island
//! `Astream.Kafka.TlaRecordHeaderBudget`.

#![allow(
    clippy::assign_op_pattern,
    clippy::question_mark,
    clippy::manual_map,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "kafka_record_header_guard_island.rs"]
mod kafka_record_header_guard_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn kafka_hdr_count_clamp(proposed_count: u64, max_headers: u64) -> u64 {
    if proposed_count < max_headers {
        proposed_count
    } else {
        max_headers
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn kafka_hdr_bytes_clamp(proposed_bytes: u64, max_bytes: u64) -> u64 {
    if proposed_bytes < max_bytes {
        proposed_bytes
    } else {
        max_bytes
    }
}
#[cfg(clean_islands)]
pub use kafka_record_header_guard_island::{kafka_hdr_bytes_clamp, kafka_hdr_count_clamp};

contract_fn! {
    /// Kernel-certified budget check (`used <= cap`), linked via `clean-kernel-defeq`
    /// to `kafka_hdr_fits_budget_isl`.
    #[must_use]
    pub const fn kafka_hdr_fits_budget(used: u64, cap: u64) -> bool
    clauses [ensures result == (used <= cap)]
    {
        used <= cap
    }
}

/// Maximum number of headers allowed on a single Kafka v2 record.
pub const MAX_KAFKA_RECORD_HEADERS: usize = 64;
/// Maximum total payload bytes (keys + values) allowed across a record's header block (`16 KiB`).
pub const MAX_KAFKA_HEADER_BLOCK_BYTES: usize = 16 * 1024;

/// Canonical bridge header key carrying the `astream` subject name.
pub const HEADER_ASTREAM_SUBJECT: &str = "astream.subject";
/// Canonical bridge header key carrying the 8-byte little-endian `bt=` broker timestamp.
pub const HEADER_ASTREAM_BT_MS: &str = "astream.bt_ms";

/// Single Kafka RecordBatch v2 header entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KafkaRecordHeader {
    /// UTF-8 header key.
    pub key: String,
    /// Optional binary header value (`None` = Kafka null `-1` varint length).
    pub value: Option<Vec<u8>>,
}

/// Error returned when encoding or decoding a Kafka v2 header block.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KafkaHeaderError {
    /// Truncated or overflowing signed zigzag varint.
    MalformedVarint,
    /// Negative header count or negative key length (`< 0`).
    NegativeLength,
    /// Header key is not valid UTF-8.
    InvalidUtf8Key,
    /// Header count exceeds [`MAX_KAFKA_RECORD_HEADERS`].
    TooManyHeaders,
    /// Total key+value byte length exceeds [`MAX_KAFKA_HEADER_BLOCK_BYTES`].
    ByteBudgetExceeded,
    /// Declared key or value slice extends past the input buffer.
    TruncatedPayload,
}

const fn encode_signed_varint_buf(v: i64) -> ([u8; 10], usize) {
    let u = v as u64;
    let sign_mask = if v < 0 { u64::MAX } else { 0 };
    let zz = (u << 1) ^ sign_mask;
    let mut buf = [0u8; 10];
    let r0 = zz;
    let r1 = r0 >> 7;
    if r1 == 0 {
        buf[0] = (r0 & 0x7F) as u8;
        return (buf, 1);
    }
    buf[0] = ((r0 & 0x7F) as u8) | 0x80;
    let r2 = r1 >> 7;
    if r2 == 0 {
        buf[1] = (r1 & 0x7F) as u8;
        return (buf, 2);
    }
    buf[1] = ((r1 & 0x7F) as u8) | 0x80;
    let r3 = r2 >> 7;
    if r3 == 0 {
        buf[2] = (r2 & 0x7F) as u8;
        return (buf, 3);
    }
    buf[2] = ((r2 & 0x7F) as u8) | 0x80;
    let r4 = r3 >> 7;
    if r4 == 0 {
        buf[3] = (r3 & 0x7F) as u8;
        return (buf, 4);
    }
    buf[3] = ((r3 & 0x7F) as u8) | 0x80;
    let r5 = r4 >> 7;
    if r5 == 0 {
        buf[4] = (r4 & 0x7F) as u8;
        return (buf, 5);
    }
    buf[4] = ((r4 & 0x7F) as u8) | 0x80;
    let r6 = r5 >> 7;
    if r6 == 0 {
        buf[5] = (r5 & 0x7F) as u8;
        return (buf, 6);
    }
    buf[5] = ((r5 & 0x7F) as u8) | 0x80;
    let r7 = r6 >> 7;
    if r7 == 0 {
        buf[6] = (r6 & 0x7F) as u8;
        return (buf, 7);
    }
    buf[6] = ((r6 & 0x7F) as u8) | 0x80;
    let r8 = r7 >> 7;
    if r8 == 0 {
        buf[7] = (r7 & 0x7F) as u8;
        return (buf, 8);
    }
    buf[7] = ((r7 & 0x7F) as u8) | 0x80;
    let r9 = r8 >> 7;
    if r9 == 0 {
        buf[8] = (r8 & 0x7F) as u8;
        return (buf, 9);
    }
    buf[8] = ((r8 & 0x7F) as u8) | 0x80;
    buf[9] = (r9 & 0x7F) as u8;
    (buf, 10)
}

fn push_signed_varint(v: i64, out: &mut Vec<u8>) {
    let (buf, len) = encode_signed_varint_buf(v);
    if let Some(prefix) = buf.get(..len) {
        out.extend_from_slice(prefix);
    }
}

fn read_signed_varint(buf: &[u8], pos: &mut usize) -> Result<i64, KafkaHeaderError> {
    let mut zz = 0u64;
    let mut shift = 0u32;
    loop {
        if shift > 63 {
            return Err(KafkaHeaderError::MalformedVarint);
        }
        let Some(&b) = buf.get(*pos) else {
            return Err(KafkaHeaderError::MalformedVarint);
        };
        *pos = pos.saturating_add(1);
        if shift == 63 && b > 1 {
            return Err(KafkaHeaderError::MalformedVarint);
        }
        zz = zz | (((b & 0x7F) as u64) << (shift & 63));
        if (b & 0x80) == 0 {
            let signed = ((zz >> 1) as i64) ^ (((zz & 1) as i64).wrapping_neg());
            return Ok(signed);
        }
        shift = shift.saturating_add(7);
    }
}

/// Budget-guarded collection of [`KafkaRecordHeader`] entries.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct KafkaHeaderBlock {
    headers: Vec<KafkaRecordHeader>,
    total_bytes: usize,
}

impl KafkaHeaderBlock {
    /// Construct an empty [`KafkaHeaderBlock`].
    #[must_use]
    pub const fn new() -> Self {
        Self {
            headers: Vec::new(),
            total_bytes: 0,
        }
    }

    /// Number of headers in this block (`<= MAX_KAFKA_RECORD_HEADERS`).
    #[must_use]
    pub fn len(&self) -> usize {
        self.headers.len()
    }

    /// True when the block holds zero headers.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.headers.is_empty()
    }

    /// Total key + value bytes stored in this block (`<= MAX_KAFKA_HEADER_BLOCK_BYTES`).
    #[must_use]
    pub const fn total_bytes(&self) -> usize {
        self.total_bytes
    }

    /// Borrow the underlying header slice.
    #[must_use]
    pub fn as_slice(&self) -> &[KafkaRecordHeader] {
        &self.headers
    }

    /// Append `(key, value)` if both count and byte budgets permit.
    pub fn push(&mut self, key: String, value: Option<Vec<u8>>) -> Result<(), KafkaHeaderError> {
        let next_count = self.headers.len().saturating_add(1) as u64;
        if !kafka_hdr_fits_budget(next_count, MAX_KAFKA_RECORD_HEADERS as u64) {
            return Err(KafkaHeaderError::TooManyHeaders);
        }
        let val_len = match &value {
            Some(v) => v.len(),
            None => 0,
        };
        let next_bytes = self
            .total_bytes
            .saturating_add(key.len())
            .saturating_add(val_len);
        if !kafka_hdr_fits_budget(next_bytes as u64, MAX_KAFKA_HEADER_BLOCK_BYTES as u64) {
            return Err(KafkaHeaderError::ByteBudgetExceeded);
        }
        let _clamped_c = kafka_hdr_count_clamp(next_count, MAX_KAFKA_RECORD_HEADERS as u64);
        self.total_bytes =
            kafka_hdr_bytes_clamp(next_bytes as u64, MAX_KAFKA_HEADER_BLOCK_BYTES as u64) as usize;
        self.headers.push(KafkaRecordHeader { key, value });
        Ok(())
    }

    /// Look up the last header matching `key` (Kafka header override semantics).
    #[must_use]
    pub fn get_last(&self, key: &str) -> Option<Option<&[u8]>> {
        let mut cur: &[KafkaRecordHeader] = &self.headers;
        while let [prefix @ .., hdr] = cur {
            if hdr.key == key {
                return Some(match &hdr.value {
                    Some(v) => Some(v.as_slice()),
                    None => None,
                });
            }
            cur = prefix;
        }
        None
    }

    /// Encode this header block into Kafka RecordBatch v2 wire format.
    pub fn encode_into(&self, out: &mut Vec<u8>) {
        push_signed_varint(self.headers.len() as i64, out);
        let mut cur: &[KafkaRecordHeader] = &self.headers;
        while let [hdr, rest @ ..] = cur {
            push_signed_varint(hdr.key.len() as i64, out);
            out.extend_from_slice(hdr.key.as_bytes());
            match &hdr.value {
                Some(v) => {
                    push_signed_varint(v.len() as i64, out);
                    out.extend_from_slice(v);
                }
                None => push_signed_varint(-1, out),
            }
            cur = rest;
        }
    }

    /// Decode a Kafka RecordBatch v2 header block from `buf[pos..]`, advancing `*pos`
    /// without pre-allocating untrusted `count` capacities!
    pub fn decode_from(buf: &[u8], pos: &mut usize) -> Result<Self, KafkaHeaderError> {
        let raw_count = match read_signed_varint(buf, pos) {
            Ok(v) => v,
            Err(e) => return Err(e),
        };
        if raw_count < 0 {
            return Err(KafkaHeaderError::NegativeLength);
        }
        if !kafka_hdr_fits_budget(raw_count as u64, MAX_KAFKA_RECORD_HEADERS as u64) {
            return Err(KafkaHeaderError::TooManyHeaders);
        }
        let count =
            kafka_hdr_count_clamp(raw_count as u64, MAX_KAFKA_RECORD_HEADERS as u64) as usize;
        let mut block = Self::new();
        let mut idx = 0usize;
        while idx < count {
            let key_len_i64 = match read_signed_varint(buf, pos) {
                Ok(v) => v,
                Err(e) => return Err(e),
            };
            if key_len_i64 < 0 {
                return Err(KafkaHeaderError::NegativeLength);
            }
            let key_len = key_len_i64 as usize;
            if !kafka_hdr_fits_budget(key_len as u64, MAX_KAFKA_HEADER_BLOCK_BYTES as u64) {
                return Err(KafkaHeaderError::ByteBudgetExceeded);
            }
            let Some(key_end) = pos.checked_add(key_len) else {
                return Err(KafkaHeaderError::TruncatedPayload);
            };
            let Some(key_slice) = buf.get(*pos..key_end) else {
                return Err(KafkaHeaderError::TruncatedPayload);
            };
            let Ok(key_str) = core::str::from_utf8(key_slice) else {
                return Err(KafkaHeaderError::InvalidUtf8Key);
            };
            *pos = key_end;

            let val_len_i64 = match read_signed_varint(buf, pos) {
                Ok(v) => v,
                Err(e) => return Err(e),
            };
            let val_opt = if val_len_i64 == -1 {
                None
            } else if val_len_i64 < -1 {
                return Err(KafkaHeaderError::NegativeLength);
            } else {
                let val_len = val_len_i64 as usize;
                if !kafka_hdr_fits_budget(val_len as u64, MAX_KAFKA_HEADER_BLOCK_BYTES as u64) {
                    return Err(KafkaHeaderError::ByteBudgetExceeded);
                }
                let Some(val_end) = pos.checked_add(val_len) else {
                    return Err(KafkaHeaderError::TruncatedPayload);
                };
                let Some(val_slice) = buf.get(*pos..val_end) else {
                    return Err(KafkaHeaderError::TruncatedPayload);
                };
                *pos = val_end;
                Some(copy_bytes(val_slice))
            };

            if let Err(e) = block.push(copy_str(key_str), val_opt) {
                return Err(e);
            }
            idx = idx.saturating_add(1);
        }
        Ok(block)
    }
}

fn copy_bytes(src: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(src);
    out
}

fn copy_str(src: &str) -> String {
    let mut out = String::new();
    out.push_str(src);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn kafka_headers_roundtrip_nulls_and_reject_hostile_varint_counts() {
        let mut blk = KafkaHeaderBlock::new();
        blk.push(
            HEADER_ASTREAM_SUBJECT.to_string(),
            Some(b"/a/session/42/out".to_vec()),
        )
        .unwrap();
        blk.push("nullable.tag".to_string(), None).unwrap();
        blk.push(
            HEADER_ASTREAM_BT_MS.to_string(),
            Some(1_730_000_000_000u64.to_le_bytes().to_vec()),
        )
        .unwrap();

        let mut wire = Vec::new();
        blk.encode_into(&mut wire);
        let mut pos = 0usize;
        let dec = KafkaHeaderBlock::decode_from(&wire, &mut pos).unwrap();
        assert_eq!(pos, wire.len());
        assert_eq!(dec, blk);
        assert_eq!(
            dec.get_last(HEADER_ASTREAM_SUBJECT),
            Some(Some(&b"/a/session/42/out"[..]))
        );
        assert_eq!(dec.get_last("nullable.tag"), Some(None));

        // Hostile varint header count = 1,000,000 -> rejected immediately without OOM!
        let mut hostile = Vec::new();
        push_signed_varint(1_000_000, &mut hostile);
        let mut hpos = 0usize;
        assert_eq!(
            KafkaHeaderBlock::decode_from(&hostile, &mut hpos),
            Err(KafkaHeaderError::TooManyHeaders)
        );
    }
}
