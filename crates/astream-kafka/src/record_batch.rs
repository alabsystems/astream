// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Kafka RecordBatch v2 (`magic = 2`, KIP-98) encoder and fail-closed CRC-32C decoder.
//!
//! Implements signed ZigZag `varint` / `varlong` framing, 61-byte RecordBatch v2 headers,
//! CRC-32C (Castagnoli) verification over `[attributes .. batch_end]`, record headers,
//! timestamp/offset deltas, and idempotent producer metadata (`producer_id`,
//! `producer_epoch`, `base_sequence`).

use crate::compress::{
    compression_codec_in_spec_range, gzip_compress, gzip_decompress, lz4_compress, lz4_decompress,
    snappy_compress, snappy_decompress, zstd_compress, zstd_decompress,
    MAX_DECOMPRESSED_BATCH_BYTES,
};
use crate::crc32c::crc32c;
use crate::{decode_i16_be, decode_i32_be, encode_i16_be, encode_i32_be};

#[cfg(clean_islands)]
#[path = "batch_island.rs"]
mod batch_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{kafka_batch_offset_advance, kafka_fetch_clamp_bytes};
#[cfg(clean_islands)]
pub use batch_island::{kafka_batch_offset_advance, kafka_fetch_clamp_bytes};

/// Kafka RecordBatch v2 magic byte (`2`).
pub const RECORD_BATCH_MAGIC_V2: u8 = 2;

/// Fixed byte length of a Kafka RecordBatch v2 header before the variable `records` array.
pub const RECORD_BATCH_HEADER_LEN: usize = 61;

/// Byte length from `partitionLeaderEpoch` through `recordsCount` (`61 - 12 = 49`).
const BATCH_BODY_PREFIX_LEN: usize = 49;

/// Compression codec mask in `RecordBatch.attributes` (`bits 0..=2`; `0` = uncompressed).
pub const COMPRESSION_MASK: i16 = 0x0007;
/// Uncompressed RecordBatch v2 records (`attributes & 0x07 == 0`).
pub const COMPRESSION_NONE: i16 = 0;
/// Pure-Rust Gzip compression codec (`1`, RFC 1952 + RFC 1951 DEFLATE + IEEE CRC-32).
pub const COMPRESSION_GZIP: i16 = 1;
/// Pure-Rust Snappy compression codec (`2`, raw + Xerial framing).
pub const COMPRESSION_SNAPPY: i16 = 2;
/// Pure-Rust LZ4 Frame compression codec (`3`, KIP-57 + xxHash32).
pub const COMPRESSION_LZ4: i16 = 3;
/// Pure-Rust Zstandard Frame compression codec (`4`, RFC 8878 + xxHash64).
pub const COMPRESSION_ZSTD: i16 = 4;

contract_fn! {
    /// Kernel-certified check that a RecordBatch magic byte is v2 (`magic == 2`),
    /// linked via `clean-kernel-defeq` to `record_batch_magic_v2_isl`.
    #[must_use]
    pub const fn record_batch_magic_v2(magic: u8) -> bool
    clauses [ensures result == (magic == 2)]
    {
        magic == 2
    }
}

/// Encode a big-endian `i64` into its 8-byte wire representation.
#[must_use]
pub const fn encode_i64_be(v: i64) -> [u8; 8] {
    let u = v as u64;
    [
        (u >> 56) as u8,
        (u >> 48) as u8,
        (u >> 40) as u8,
        (u >> 32) as u8,
        (u >> 24) as u8,
        (u >> 16) as u8,
        (u >> 8) as u8,
        u as u8,
    ]
}

/// Decode a big-endian `i64` from its 8-byte wire representation.
#[must_use]
pub const fn decode_i64_be(raw: &[u8; 8]) -> i64 {
    (((raw[0] as u64) << 56)
        | ((raw[1] as u64) << 48)
        | ((raw[2] as u64) << 40)
        | ((raw[3] as u64) << 32)
        | ((raw[4] as u64) << 24)
        | ((raw[5] as u64) << 16)
        | ((raw[6] as u64) << 8)
        | (raw[7] as u64)) as i64
}

/// Encode a signed 32-bit integer as a ZigZag base-128 `varint` (1..=5 bytes).
pub fn put_varint(out: &mut Vec<u8>, val: i32) {
    let mut zigzag = ((val << 1) ^ (val >> 31)) as u32;
    let mut steps = 0usize;
    while zigzag >= 0x80 && steps < 5 {
        out.push(((zigzag as u8) & 0x7f) | 0x80);
        zigzag >>= 7;
        steps = steps.saturating_add(1);
    }
    out.push(zigzag as u8);
}

/// Decode a signed 32-bit ZigZag `varint`, returning `(value, remaining)` or `None` on
/// truncation / 5-byte overflow.
#[must_use]
pub const fn take_varint(mut bytes: &[u8]) -> Option<(i32, &[u8])> {
    let mut acc: u32 = 0;
    let mut shift: u32 = 0;
    let mut idx = 0usize;
    while idx < 5 {
        let &[b, ref rest @ ..] = bytes else {
            return None;
        };
        bytes = rest;
        let payload = (b & 0x7f) as u32;
        if idx == 4 && (b & 0xf0) != 0 {
            return None; // > 32 bits in 5th byte
        }
        acc |= payload << (shift & 31);
        if (b & 0x80) == 0 {
            let mask = if (acc & 1) != 0 { -1i32 } else { 0 };
            let decoded = ((acc >> 1) as i32) ^ mask;
            return Some((decoded, bytes));
        }
        shift = shift.saturating_add(7);
        idx = idx.saturating_add(1);
    }
    None
}

/// Encode a signed 64-bit integer as a ZigZag base-128 `varlong` (1..=10 bytes).
pub fn put_varlong(out: &mut Vec<u8>, val: i64) {
    let mut zigzag = ((val << 1) ^ (val >> 63)) as u64;
    let mut steps = 0usize;
    while zigzag >= 0x80 && steps < 10 {
        out.push(((zigzag as u8) & 0x7f) | 0x80);
        zigzag >>= 7;
        steps = steps.saturating_add(1);
    }
    out.push(zigzag as u8);
}

/// Decode a signed 64-bit ZigZag `varlong`, returning `(value, remaining)` or `None` on
/// truncation / 10-byte overflow.
#[must_use]
pub const fn take_varlong(mut bytes: &[u8]) -> Option<(i64, &[u8])> {
    let mut acc: u64 = 0;
    let mut shift: u32 = 0;
    let mut idx = 0usize;
    while idx < 10 {
        let &[b, ref rest @ ..] = bytes else {
            return None;
        };
        bytes = rest;
        let payload = (b & 0x7f) as u64;
        if idx == 9 && (b & 0xfe) != 0 {
            return None; // > 64 bits in 10th byte
        }
        acc |= payload << (shift & 63);
        if (b & 0x80) == 0 {
            let mask = if (acc & 1) != 0 { -1i64 } else { 0 };
            let decoded = ((acc >> 1) as i64) ^ mask;
            return Some((decoded, bytes));
        }
        shift = shift.saturating_add(7);
        idx = idx.saturating_add(1);
    }
    None
}

/// One key/value header attached to a [`KafkaRecord`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KafkaHeader {
    pub key: String,
    pub value: Option<Vec<u8>>,
}

/// One logical Kafka v2 message inside a [`RecordBatchV2`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KafkaRecord {
    /// Absolute message timestamp in Unix milliseconds (`CreateTime`).
    pub timestamp_ms: i64,
    /// Optional record key (`None` = null key).
    pub key: Option<Vec<u8>>,
    /// Optional record payload (`None` = tombstone / null value).
    pub value: Option<Vec<u8>>,
    /// Record-level headers (KIP-82).
    pub headers: Vec<KafkaHeader>,
}

/// A Kafka RecordBatch v2 (`magic = 2`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordBatchV2 {
    pub base_offset: i64,
    pub partition_leader_epoch: i32,
    pub attributes: i16,
    pub producer_id: i64,
    pub producer_epoch: i16,
    pub base_sequence: i32,
    pub records: Vec<KafkaRecord>,
}

/// Why decoding a [`RecordBatchV2`] failed closed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BatchDecodeError {
    /// Input ended before the 61-byte header or declared `batchLength` completed.
    Truncated,
    /// `magic` byte was not [`RECORD_BATCH_MAGIC_V2`] (`2`).
    UnsupportedMagic(u8),
    /// Stored CRC-32C did not match the computed Castagnoli checksum over `[21..end]`.
    BadCrc { expected: u32, found: u32 },
    /// Non-zero compression codec in `attributes` (`0x0007`), unsupported by std-only codec.
    CompressedUnsupported(i16),
    /// Supported compression codec (`Gzip = 1`, `Snappy = 2`, or `Lz4 = 3`) failed closed on corrupt/oversized data.
    DecompressFailed(i16),
    /// Malformed varint, negative record count, invalid UTF-8 header key, or trailing garbage.
    MalformedRecord,
}

fn put_var_bytes(out: &mut Vec<u8>, opt: Option<&[u8]>) -> bool {
    match opt {
        None => {
            put_varint(out, -1);
            true
        }
        Some(bytes) => {
            let Ok(len) = i32::try_from(bytes.len()) else {
                return false;
            };
            put_varint(out, len);
            out.extend_from_slice(bytes);
            true
        }
    }
}

fn take_var_bytes(bytes: &[u8]) -> Option<(Option<Vec<u8>>, &[u8])> {
    let (len, rest) = take_varint(bytes)?;
    if len < -1 {
        return None;
    }
    if len == -1 {
        return Some((None, rest));
    }
    let ulen = len as usize;
    let slice = rest.get(..ulen)?;
    let tail = rest.get(ulen..)?;
    Some((Some(slice.to_vec()), tail))
}

/// Encode a [`RecordBatchV2`] to its exact Kafka v2 wire bytes (supporting uncompressed `0`,
/// Gzip `1`, Snappy `2`, and LZ4 Frame `3` in `batch.attributes & 0x07`), stamping `crc` with
/// [`crc32c`]. Returns `None` if `records` is empty, the codec is unsupported, or any field
/// exceeds `i32::MAX`.
#[must_use]
pub fn encode_record_batch_v2(batch: &RecordBatchV2) -> Option<Vec<u8>> {
    if batch.records.is_empty() {
        return None;
    }
    let codec = batch.attributes & COMPRESSION_MASK;
    if !compression_codec_in_spec_range(codec as u8) {
        return None;
    }
    let Ok(rec_count_i32) = i32::try_from(batch.records.len()) else {
        return None;
    };
    let last_offset_delta = rec_count_i32.checked_sub(1)?;
    let first_ts = batch.records.first()?.timestamp_ms;
    let mut max_ts = first_ts;

    let mut records_buf = Vec::new();
    for (idx, rec) in batch.records.iter().enumerate() {
        if rec.timestamp_ms > max_ts {
            max_ts = rec.timestamp_ms;
        }
        let ts_delta = rec.timestamp_ms.checked_sub(first_ts)?;
        let Ok(off_delta) = i32::try_from(idx) else {
            return None;
        };
        let Ok(hdr_count) = i32::try_from(rec.headers.len()) else {
            return None;
        };

        let mut body = Vec::new();
        body.push(0u8); // record attributes = 0
        put_varlong(&mut body, ts_delta);
        put_varint(&mut body, off_delta);
        if !put_var_bytes(&mut body, rec.key.as_deref()) {
            return None;
        }
        if !put_var_bytes(&mut body, rec.value.as_deref()) {
            return None;
        }
        put_varint(&mut body, hdr_count);
        for h in &rec.headers {
            let Ok(klen) = i32::try_from(h.key.len()) else {
                return None;
            };
            put_varint(&mut body, klen);
            body.extend_from_slice(h.key.as_bytes());
            if !put_var_bytes(&mut body, h.value.as_deref()) {
                return None;
            }
        }
        let Ok(rec_len) = i32::try_from(body.len()) else {
            return None;
        };
        put_varint(&mut records_buf, rec_len);
        records_buf.extend_from_slice(&body);
    }

    let wire_records = if codec == COMPRESSION_GZIP {
        gzip_compress(&records_buf)
    } else if codec == COMPRESSION_SNAPPY {
        snappy_compress(&records_buf)
    } else if codec == COMPRESSION_LZ4 {
        lz4_compress(&records_buf)
    } else if codec == COMPRESSION_ZSTD {
        zstd_compress(&records_buf)
    } else {
        records_buf
    };

    let batch_len_usize = BATCH_BODY_PREFIX_LEN.checked_add(wire_records.len())?;
    let Ok(batch_len_i32) = i32::try_from(batch_len_usize) else {
        return None;
    };

    // Build [attributes .. end] first so we compute CRC-32C in one pass.
    let mut crc_region = Vec::new();
    crc_region.extend_from_slice(&encode_i16_be(batch.attributes));
    crc_region.extend_from_slice(&encode_i32_be(last_offset_delta));
    crc_region.extend_from_slice(&encode_i64_be(first_ts));
    crc_region.extend_from_slice(&encode_i64_be(max_ts));
    crc_region.extend_from_slice(&encode_i64_be(batch.producer_id));
    crc_region.extend_from_slice(&encode_i16_be(batch.producer_epoch));
    crc_region.extend_from_slice(&encode_i32_be(batch.base_sequence));
    crc_region.extend_from_slice(&encode_i32_be(rec_count_i32));
    crc_region.extend_from_slice(&wire_records);

    let checksum = crc32c(&crc_region);
    let mut out = Vec::new();
    out.extend_from_slice(&encode_i64_be(batch.base_offset));
    out.extend_from_slice(&encode_i32_be(batch_len_i32));
    out.extend_from_slice(&encode_i32_be(batch.partition_leader_epoch));
    out.push(RECORD_BATCH_MAGIC_V2);
    out.extend_from_slice(&encode_i32_be(checksum as i32));
    out.extend_from_slice(&crc_region);
    Some(out)
}

struct BatchOuterPrefix {
    base_offset: i64,
    partition_leader_epoch: i32,
    magic: u8,
    expected_crc: u32,
    total_len: usize,
}

fn decode_batch_outer_prefix(bytes: &[u8]) -> Result<(BatchOuterPrefix, &[u8]), BatchDecodeError> {
    if bytes.len() < RECORD_BATCH_HEADER_LEN {
        return Err(BatchDecodeError::Truncated);
    }
    let &[o0, o1, o2, o3, o4, o5, o6, o7, l0, l1, l2, l3, e0, e1, e2, e3, magic, c0, c1, c2, c3, ref after_crc @ ..] =
        bytes
    else {
        return Err(BatchDecodeError::Truncated);
    };
    let base_offset = decode_i64_be(&[o0, o1, o2, o3, o4, o5, o6, o7]);
    let batch_length = decode_i32_be(&[l0, l1, l2, l3]);
    let partition_leader_epoch = decode_i32_be(&[e0, e1, e2, e3]);
    if batch_length < (BATCH_BODY_PREFIX_LEN as i32) {
        return Err(BatchDecodeError::MalformedRecord);
    }
    let Some(total_len) = 12usize.checked_add(batch_length as usize) else {
        return Err(BatchDecodeError::MalformedRecord);
    };
    if bytes.len() < total_len {
        return Err(BatchDecodeError::Truncated);
    }
    if !record_batch_magic_v2(magic) {
        return Err(BatchDecodeError::UnsupportedMagic(magic));
    }
    let expected_crc = decode_i32_be(&[c0, c1, c2, c3]) as u32;
    let Some(crc_len) = total_len.checked_sub(21) else {
        return Err(BatchDecodeError::MalformedRecord);
    };
    let Some(crc_slice) = after_crc.get(..crc_len) else {
        return Err(BatchDecodeError::Truncated);
    };
    Ok((
        BatchOuterPrefix {
            base_offset,
            partition_leader_epoch,
            magic,
            expected_crc,
            total_len,
        },
        crc_slice,
    ))
}

struct BatchBodyMeta {
    attributes: i16,
    base_timestamp: i64,
    producer_id: i64,
    producer_epoch: i16,
    base_sequence: i32,
    records_count: i32,
}

fn decode_batch_body_meta(crc_slice: &[u8]) -> Result<(BatchBodyMeta, &[u8]), BatchDecodeError> {
    let &[a0, a1, ld0, ld1, ld2, ld3, bt0, bt1, bt2, bt3, bt4, bt5, bt6, bt7, _mt0, _mt1, _mt2, _mt3, _mt4, _mt5, _mt6, _mt7, p0, p1, p2, p3, p4, p5, p6, p7, pe0, pe1, bs0, bs1, bs2, bs3, rc0, rc1, rc2, rc3, ref rec_bytes @ ..] =
        crc_slice
    else {
        return Err(BatchDecodeError::Truncated);
    };
    let attributes = decode_i16_be(&[a0, a1]);
    let codec = attributes & COMPRESSION_MASK;
    if !compression_codec_in_spec_range(codec as u8) {
        return Err(BatchDecodeError::CompressedUnsupported(codec));
    }
    let last_offset_delta = decode_i32_be(&[ld0, ld1, ld2, ld3]);
    let base_timestamp = decode_i64_be(&[bt0, bt1, bt2, bt3, bt4, bt5, bt6, bt7]);
    let producer_id = decode_i64_be(&[p0, p1, p2, p3, p4, p5, p6, p7]);
    let producer_epoch = decode_i16_be(&[pe0, pe1]);
    let base_sequence = decode_i32_be(&[bs0, bs1, bs2, bs3]);
    let records_count = decode_i32_be(&[rc0, rc1, rc2, rc3]);
    if records_count <= 0 || last_offset_delta < 0 {
        return Err(BatchDecodeError::MalformedRecord);
    }
    Ok((
        BatchBodyMeta {
            attributes,
            base_timestamp,
            producer_id,
            producer_epoch,
            base_sequence,
            records_count,
        },
        rec_bytes,
    ))
}

fn decode_record_headers_v2(
    mut h_cur: &[u8],
    hdr_count: i32,
) -> Result<Vec<KafkaHeader>, BatchDecodeError> {
    let mut headers = Vec::new();
    let mut h_idx = 0i32;
    while h_idx < hdr_count {
        let Some((klen, after_klen)) = take_varint(h_cur) else {
            return Err(BatchDecodeError::MalformedRecord);
        };
        if klen < 0 {
            return Err(BatchDecodeError::MalformedRecord);
        }
        let uklen = klen as usize;
        let Some(kbytes) = after_klen.get(..uklen) else {
            return Err(BatchDecodeError::MalformedRecord);
        };
        let Ok(kstr) = core::str::from_utf8(kbytes) else {
            return Err(BatchDecodeError::MalformedRecord);
        };
        let Some(after_key) = after_klen.get(uklen..) else {
            return Err(BatchDecodeError::MalformedRecord);
        };
        let Some((hval, next_h)) = take_var_bytes(after_key) else {
            return Err(BatchDecodeError::MalformedRecord);
        };
        headers.push(KafkaHeader {
            key: kstr.to_owned(),
            value: hval,
        });
        h_cur = next_h;
        h_idx = h_idx.saturating_add(1);
    }
    if !h_cur.is_empty() {
        return Err(BatchDecodeError::MalformedRecord);
    }
    Ok(headers)
}

fn decode_one_record_v2(
    cur: &[u8],
    idx: i32,
    base_timestamp: i64,
) -> Result<(KafkaRecord, &[u8]), BatchDecodeError> {
    let Some((rec_len, after_len)) = take_varint(cur) else {
        return Err(BatchDecodeError::MalformedRecord);
    };
    if rec_len <= 0 {
        return Err(BatchDecodeError::MalformedRecord);
    };
    let ulen = rec_len as usize;
    let Some(rec_body) = after_len.get(..ulen) else {
        return Err(BatchDecodeError::MalformedRecord);
    };
    let Some(next_cur) = after_len.get(ulen..) else {
        return Err(BatchDecodeError::MalformedRecord);
    };
    let &[_rec_attr, ref r_tail @ ..] = rec_body else {
        return Err(BatchDecodeError::MalformedRecord);
    };
    let Some((ts_delta, r_tail)) = take_varlong(r_tail) else {
        return Err(BatchDecodeError::MalformedRecord);
    };
    let Some((off_delta, r_tail)) = take_varint(r_tail) else {
        return Err(BatchDecodeError::MalformedRecord);
    };
    if off_delta != idx {
        return Err(BatchDecodeError::MalformedRecord);
    }
    let Some((key, r_tail)) = take_var_bytes(r_tail) else {
        return Err(BatchDecodeError::MalformedRecord);
    };
    let Some((value, r_tail)) = take_var_bytes(r_tail) else {
        return Err(BatchDecodeError::MalformedRecord);
    };
    let Some((hdr_count, h_cur)) = take_varint(r_tail) else {
        return Err(BatchDecodeError::MalformedRecord);
    };
    if hdr_count < 0 {
        return Err(BatchDecodeError::MalformedRecord);
    }
    let headers = decode_record_headers_v2(h_cur, hdr_count)?;
    let Some(timestamp_ms) = base_timestamp.checked_add(ts_delta) else {
        return Err(BatchDecodeError::MalformedRecord);
    };
    Ok((
        KafkaRecord {
            timestamp_ms,
            key,
            value,
            headers,
        },
        next_cur,
    ))
}

/// Decode one [`RecordBatchV2`] from the front of `bytes`, verifying its CRC-32C before
/// parsing any inner record. Returns `(batch, consumed_bytes)`.
pub fn decode_record_batch_v2(bytes: &[u8]) -> Result<(RecordBatchV2, usize), BatchDecodeError> {
    let (outer, crc_slice) = decode_batch_outer_prefix(bytes)?;
    let _ = outer.magic;
    let found_crc = crc32c(crc_slice);
    if outer.expected_crc != found_crc {
        return Err(BatchDecodeError::BadCrc {
            expected: outer.expected_crc,
            found: found_crc,
        });
    }
    let (meta, raw_rec_bytes) = decode_batch_body_meta(crc_slice)?;
    let codec = meta.attributes & COMPRESSION_MASK;
    let decompressed_holder: Vec<u8>;
    let mut cur: &[u8] = if codec == COMPRESSION_GZIP {
        match gzip_decompress(raw_rec_bytes, MAX_DECOMPRESSED_BATCH_BYTES) {
            Ok(v) => {
                decompressed_holder = v;
                &decompressed_holder
            }
            Err(_) => return Err(BatchDecodeError::DecompressFailed(codec)),
        }
    } else if codec == COMPRESSION_SNAPPY {
        match snappy_decompress(raw_rec_bytes, MAX_DECOMPRESSED_BATCH_BYTES) {
            Ok(v) => {
                decompressed_holder = v;
                &decompressed_holder
            }
            Err(_) => return Err(BatchDecodeError::DecompressFailed(codec)),
        }
    } else if codec == COMPRESSION_LZ4 {
        match lz4_decompress(raw_rec_bytes, MAX_DECOMPRESSED_BATCH_BYTES) {
            Ok(v) => {
                decompressed_holder = v;
                &decompressed_holder
            }
            Err(_) => return Err(BatchDecodeError::DecompressFailed(codec)),
        }
    } else if codec == COMPRESSION_ZSTD {
        match zstd_decompress(raw_rec_bytes, MAX_DECOMPRESSED_BATCH_BYTES) {
            Ok(v) => {
                decompressed_holder = v;
                &decompressed_holder
            }
            Err(_) => return Err(BatchDecodeError::DecompressFailed(codec)),
        }
    } else {
        raw_rec_bytes
    };
    let mut records = Vec::new();
    let mut idx = 0i32;
    while idx < meta.records_count {
        let (rec, next_cur) = decode_one_record_v2(cur, idx, meta.base_timestamp)?;
        records.push(rec);
        cur = next_cur;
        idx = idx.saturating_add(1);
    }
    if !cur.is_empty() {
        return Err(BatchDecodeError::MalformedRecord);
    }
    Ok((
        RecordBatchV2 {
            base_offset: outer.base_offset,
            partition_leader_epoch: outer.partition_leader_epoch,
            attributes: meta.attributes,
            producer_id: meta.producer_id,
            producer_epoch: meta.producer_epoch,
            base_sequence: meta.base_sequence,
            records,
        },
        outer.total_len,
    ))
}

/// Re-stamp the `baseOffset` (bytes `0..8`) of an already-encoded RecordBatch v2 buffer
/// without re-computing its CRC-32C (`baseOffset` sits outside `[21..end]`).
pub fn restamp_batch_base_offset(encoded: &mut [u8], new_base_offset: i64) -> bool {
    if encoded.len() < RECORD_BATCH_HEADER_LEN {
        return false;
    }
    let raw = encode_i64_be(new_base_offset);
    if let Some(dst) = encoded.get_mut(..8) {
        dst.copy_from_slice(&raw);
        true
    } else {
        false
    }
}
