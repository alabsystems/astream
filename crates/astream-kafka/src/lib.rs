#![forbid(unsafe_code)]
//! `astream-kafka` — pure-Rust Kafka wire-protocol codec, multi-partition RecordBatch v2 +
//! CRC-32C engine, consumer-group coordinator (`TlaConsumerGroup`), [`KafkaStore`],
//! optional `ShardedBroker`-backed `DurableKafkaStore`, and live TCP [`KafkaServer`] /
//! [`KafkaClient`].
//!
//! Answers the doctrine's ecosystem-maturity bridge: speak standard non-flexible Kafka
//! protocol frames byte-for-byte with zero third-party dependencies and `#![forbid(unsafe_code)]`.
//!
//! Supported API surface (12 APIs, non-flexible + KIP-482 flexible bootstrap/discovery):
//! - `ApiVersions` (key `18`, v0..=3 including KIP-482 flexible v3 + KIP-511 v0-framed downgrade via `error_code = 35` for v4+),
//! - `Metadata` (key `3`, v0..=9 including KIP-482 flexible v9 — single- and multi-partition topics via [`TopicMeta`]),
//! - `Produce` (key `0`, v3 — multi-partition RecordBatch v2 `magic = 2` with all five Kafka codecs: uncompressed, pure-Rust RFC 1952 Gzip / RFC 1951 DEFLATE, pure-Rust Snappy raw/Xerial, pure-Rust LZ4 Frame + xxHash32, and pure-Rust RFC 8878 Zstandard + xxHash64, plus Castagnoli CRC-32C verification and KIP-98 idempotent producer deduplication / epoch fencing),
//! - `Fetch` (key `1`, v4 — multi-partition RecordBatch v2 streaming with KIP-74 progress byte clamping),
//! - `ListOffsets` (key `2`, v1 — earliest `-2`, latest `-1`, and monotone timestamp lookup),
//! - `OffsetCommit` (key `8`, v2 — generation-fenced and standalone offset + metadata commits),
//! - `OffsetFetch` (key `9`, v1 — committed offset + metadata lookup),
//! - `FindCoordinator` (key `10`, v0..=3 including KIP-482 flexible v3),
//! - `JoinGroup` (key `11`, v0 — deterministic member assignment, protocol intersection, leader election, and monotone `TlaConsumerGroup` generation advance),
//! - `Heartbeat` (key `12`, v0 — membership and generation validation),
//! - `LeaveGroup` (key `13`, v0 — graceful member removal and rebalance generation advance),
//! - `SyncGroup` (key `14`, v0 — leader partition-assignment distribution).

// A contracted fn is written once, through `contract_fn!`: under a Trust compiler
// (`cfg(clean_islands)`, build.rs) it carries its `ensures` clause, which no stock rustc can
// parse, and every other compiler gets the plain fn.
#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

// Plain-Rust twins of the functions this crate's Clean islands compile, for a compiler
// that cannot lex the islands.
#[cfg(any(test, not(clean_islands)))]
mod twins;

pub mod compress;
pub mod crc32c;
#[cfg(feature = "durable")]
pub mod durable;
pub mod record_batch;
pub mod sasl;
pub mod server;
pub mod zstd;

pub mod kafka_tls;
pub use compress::{
    compression_codec_in_spec_range, crc32_ieee, gzip_compress, gzip_decompress,
    kafka_compact_len_clamp, kafka_decompress_cap_clamp, lz4_compress, lz4_decompress,
    snappy_compress, snappy_compress_xerial, snappy_decompress, xxhash32, xxhash64, zstd_compress,
    zstd_decompress, DecompressError, GZIP_MAGIC, LZ4_FRAME_MAGIC_LE, MAX_DECOMPRESSED_BATCH_BYTES,
    XERIAL_SNAPPY_MAGIC, ZSTD_MAGIC_LE,
};
pub use crc32c::crc32c;
#[cfg(feature = "durable")]
pub use durable::DurableKafkaStore;
pub use record_batch::{
    decode_record_batch_v2, encode_record_batch_v2, record_batch_magic_v2, BatchDecodeError,
    KafkaHeader, KafkaRecord, RecordBatchV2, COMPRESSION_GZIP, COMPRESSION_LZ4, COMPRESSION_MASK,
    COMPRESSION_NONE, COMPRESSION_SNAPPY, COMPRESSION_ZSTD, RECORD_BATCH_HEADER_LEN,
    RECORD_BATCH_MAGIC_V2,
};
pub use sasl::{
    build_plain_token, encode_sasl_authenticate_request, encode_sasl_handshake_request,
    kafka_sasl_is_authenticated, kafka_sasl_pbkdf2_clamp, kafka_sasl_phase_advance,
    respond_sasl_authenticate, respond_sasl_handshake, SaslAuthOutcome, SaslConfig, SaslMechanism,
    SaslSession, SaslUserRecord, ScramSha256Client, DEFAULT_SCRAM_ITERS, ILLEGAL_SASL_STATE,
    MAX_PBKDF2_ITERS, MAX_SASL_TOKEN_BYTES, PHASE_AUTHENTICATED, PHASE_FAILED, PHASE_HANDSHAKEN,
    PHASE_SCRAM_CHALLENGE, PHASE_UNAUTHENTICATED, SASL_AUTHENTICATE, SASL_AUTHENTICATION_FAILED,
    SASL_HANDSHAKE, UNSUPPORTED_SASL_MECHANISM,
};
#[cfg(feature = "durable")]
pub use server::respond_with_durable;
#[cfg(feature = "aead")]
pub use server::KafkaEncryptedListener;
pub use server::{
    kafka_generation_advance, kafka_generation_matches, kafka_partition_clamp, respond_with_engine,
    respond_with_store, CommittedOffset, JoinGroupResult, KafkaClient, KafkaEngine, KafkaServer,
    KafkaServerHandle, KafkaStore, COORDINATOR_NOT_AVAILABLE, CORRUPT_MESSAGE, ILLEGAL_GENERATION,
    INCONSISTENT_GROUP_PROTOCOL, INVALID_GROUP_ID, INVALID_PRODUCER_EPOCH, INVALID_REQUEST,
    MAX_KAFKA_FRAME_LEN, MAX_TOPIC_PARTITIONS, OFFSET_OUT_OF_RANGE, OUT_OF_ORDER_SEQUENCE_NUMBER,
    REBALANCE_IN_PROGRESS, TIMESTAMP_EARLIEST, TIMESTAMP_LATEST, UNKNOWN_MEMBER_ID,
};

use std::collections::HashSet;

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
mod kafka_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{kafka_clamp_str_len, kafka_negotiate_error_code};
#[cfg(clean_islands)]
pub use kafka_island::{kafka_clamp_str_len, kafka_negotiate_error_code};

contract_fn! {
    /// Verified Kafka API version range check linked via `clean-kernel-defeq` to
    /// `version_within_max_isl`.
    #[must_use]
    pub const fn version_within_max(req_ver: u64, max_ver: u64) -> bool
    clauses [ensures result == (req_ver <= max_ver)]
    {
        req_ver <= max_ver
    }
}

/// Kafka API keys this surface answers.
pub const PRODUCE: i16 = 0;
pub const FETCH: i16 = 1;
pub const LIST_OFFSETS: i16 = 2;
pub const METADATA: i16 = 3;
pub const OFFSET_COMMIT: i16 = 8;
pub const OFFSET_FETCH: i16 = 9;
pub const FIND_COORDINATOR: i16 = 10;
pub const JOIN_GROUP: i16 = 11;
pub const HEARTBEAT: i16 = 12;
pub const LEAVE_GROUP: i16 = 13;
pub const SYNC_GROUP: i16 = 14;
pub const API_VERSIONS: i16 = 18;

/// Kafka error codes this surface emits.
pub const NONE: i16 = 0;
pub const UNKNOWN_TOPIC_OR_PARTITION: i16 = 3;
pub const UNSUPPORTED_VERSION: i16 = 35;

/// What astream advertises in an `ApiVersions` response: `(api_key, min, max)`.
const SUPPORTED: &[(i16, i16, i16)] = &[
    (API_VERSIONS, 0, 3),
    (METADATA, 0, 9),
    (PRODUCE, 3, 3),
    (FETCH, 4, 4),
    (LIST_OFFSETS, 1, 1),
    (OFFSET_COMMIT, 2, 2),
    (OFFSET_FETCH, 1, 1),
    (FIND_COORDINATOR, 0, 3),
    (JOIN_GROUP, 0, 0),
    (HEARTBEAT, 0, 0),
    (LEAVE_GROUP, 0, 0),
    (SYNC_GROUP, 0, 0),
    (SASL_HANDSHAKE, 0, 1),
    (SASL_AUTHENTICATE, 0, 2),
];

/// The `(min, max)` version range astream implements for `api_key`, or `None` for an unknown key.
const fn version_range(api_key: i16) -> Option<(i16, i16)> {
    let mut rest = SUPPORTED;
    while let &[(k, min, max), ref tail @ ..] = rest {
        if k == api_key {
            return Some((min, max));
        }
        rest = tail;
    }
    None
}

/// One broker astream advertises to Kafka clients (this node).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BrokerMeta {
    pub node_id: i32,
    pub host: String,
    pub port: i32,
}

/// Topic descriptor carrying its partition count (`1..=MAX_TOPIC_PARTITIONS`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TopicMeta {
    pub name: String,
    pub partitions: i32,
}

/// The cluster view astream presents over the Kafka protocol: this single broker
/// and the topics it serves.
#[derive(Debug, Clone)]
pub struct ClusterMeta {
    pub broker: BrokerMeta,
    pub topics: Vec<String>,
}

// ---- Kafka wire primitives (every wire integer is big-endian) ----

/// Encode a big-endian `i16` into its 2-byte wire representation.
#[must_use]
pub const fn encode_i16_be(v: i16) -> [u8; 2] {
    let u = v as u16;
    [(u >> 8) as u8, u as u8]
}

/// Decode a big-endian `i16` from its 2-byte wire representation.
#[must_use]
pub const fn decode_i16_be(raw: &[u8; 2]) -> i16 {
    (((raw[0] as u16) << 8) | (raw[1] as u16)) as i16
}

/// Encode a big-endian `i32` into its 4-byte wire representation.
#[must_use]
pub const fn encode_i32_be(v: i32) -> [u8; 4] {
    let u = v as u32;
    [(u >> 24) as u8, (u >> 16) as u8, (u >> 8) as u8, u as u8]
}

/// Decode a big-endian `i32` from its 4-byte wire representation.
#[must_use]
pub const fn decode_i32_be(raw: &[u8; 4]) -> i32 {
    (((raw[0] as u32) << 24) | ((raw[1] as u32) << 16) | ((raw[2] as u32) << 8) | (raw[3] as u32))
        as i32
}

/// Encode the 8-byte fixed prefix of a Kafka request header
/// `(api_key: i16, api_version: i16, correlation_id: i32)`.
#[must_use]
pub const fn encode_req_header_prefix(
    api_key: i16,
    api_version: i16,
    correlation_id: i32,
) -> [u8; 8] {
    let k = api_key as u16;
    let v = api_version as u16;
    let c = correlation_id as u32;
    [
        (k >> 8) as u8,
        k as u8,
        (v >> 8) as u8,
        v as u8,
        (c >> 24) as u8,
        (c >> 16) as u8,
        (c >> 8) as u8,
        c as u8,
    ]
}

/// Decode the 8-byte fixed prefix of a Kafka request header
/// `(api_key: i16, api_version: i16, correlation_id: i32)`.
#[must_use]
pub const fn decode_req_header_prefix(raw: &[u8; 8]) -> (i16, i16, i32) {
    let api_key = (((raw[0] as u16) << 8) | (raw[1] as u16)) as i16;
    let api_version = (((raw[2] as u16) << 8) | (raw[3] as u16)) as i16;
    let correlation_id = (((raw[4] as u32) << 24)
        | ((raw[5] as u32) << 16)
        | ((raw[6] as u32) << 8)
        | (raw[7] as u32)) as i32;
    (api_key, api_version, correlation_id)
}

/// Encode the 8-byte Kafka response frame header `(size: i32, correlation_id: i32)`.
#[must_use]
pub const fn encode_resp_frame_header(size: i32, correlation_id: i32) -> [u8; 8] {
    let s = size as u32;
    let c = correlation_id as u32;
    [
        (s >> 24) as u8,
        (s >> 16) as u8,
        (s >> 8) as u8,
        s as u8,
        (c >> 24) as u8,
        (c >> 16) as u8,
        (c >> 8) as u8,
        c as u8,
    ]
}

/// Decode the 8-byte Kafka response frame header `(size: i32, correlation_id: i32)`.
#[must_use]
pub const fn decode_resp_frame_header(raw: &[u8; 8]) -> (i32, i32) {
    let size = (((raw[0] as u32) << 24)
        | ((raw[1] as u32) << 16)
        | ((raw[2] as u32) << 8)
        | (raw[3] as u32)) as i32;
    let correlation_id = (((raw[4] as u32) << 24)
        | ((raw[5] as u32) << 16)
        | ((raw[6] as u32) << 8)
        | (raw[7] as u32)) as i32;
    (size, correlation_id)
}

/// Encode one 6-byte `ApiVersions` entry `(api_key: i16, min_version: i16, max_version: i16)`.
#[must_use]
pub const fn encode_api_version_entry(api_key: i16, min_version: i16, max_version: i16) -> [u8; 6] {
    let k = api_key as u16;
    let min = min_version as u16;
    let max = max_version as u16;
    [
        (k >> 8) as u8,
        k as u8,
        (min >> 8) as u8,
        min as u8,
        (max >> 8) as u8,
        max as u8,
    ]
}

/// Decode one 6-byte `ApiVersions` entry `(api_key: i16, min_version: i16, max_version: i16)`.
#[must_use]
pub const fn decode_api_version_entry(raw: &[u8; 6]) -> (i16, i16, i16) {
    let api_key = (((raw[0] as u16) << 8) | (raw[1] as u16)) as i16;
    let min_version = (((raw[2] as u16) << 8) | (raw[3] as u16)) as i16;
    let max_version = (((raw[4] as u16) << 8) | (raw[5] as u16)) as i16;
    (api_key, min_version, max_version)
}

/// Encode the 30-byte single-partition Metadata v0 array for a served topic:
/// `(count=1: i32, error_code: i16, partition_id: i32, leader: i32, replicas_len=1: i32, replica0: i32, isr_len=1: i32, isr0: i32)`.
#[must_use]
pub const fn encode_single_partition_array(
    error_code: i16,
    partition_id: i32,
    node: i32,
) -> [u8; 30] {
    let e = error_code as u16;
    let p = partition_id as u32;
    let n = node as u32;
    [
        0,
        0,
        0,
        1,
        (e >> 8) as u8,
        e as u8,
        (p >> 24) as u8,
        (p >> 16) as u8,
        (p >> 8) as u8,
        p as u8,
        (n >> 24) as u8,
        (n >> 16) as u8,
        (n >> 8) as u8,
        n as u8,
        0,
        0,
        0,
        1,
        (n >> 24) as u8,
        (n >> 16) as u8,
        (n >> 8) as u8,
        n as u8,
        0,
        0,
        0,
        1,
        (n >> 24) as u8,
        (n >> 16) as u8,
        (n >> 8) as u8,
        n as u8,
    ]
}

/// Decode the 30-byte single-partition Metadata v0 array into
/// `(count, error_code, partition_id, leader, replicas_len, replica0, isr_len, isr0)`.
#[must_use]
pub const fn decode_single_partition_array(
    raw: &[u8; 30],
) -> (i32, i16, i32, i32, i32, i32, i32, i32) {
    let count = (((raw[0] as u32) << 24)
        | ((raw[1] as u32) << 16)
        | ((raw[2] as u32) << 8)
        | (raw[3] as u32)) as i32;
    let error_code = (((raw[4] as u16) << 8) | (raw[5] as u16)) as i16;
    let partition_id = (((raw[6] as u32) << 24)
        | ((raw[7] as u32) << 16)
        | ((raw[8] as u32) << 8)
        | (raw[9] as u32)) as i32;
    let leader = (((raw[10] as u32) << 24)
        | ((raw[11] as u32) << 16)
        | ((raw[12] as u32) << 8)
        | (raw[13] as u32)) as i32;
    let replicas_len = (((raw[14] as u32) << 24)
        | ((raw[15] as u32) << 16)
        | ((raw[16] as u32) << 8)
        | (raw[17] as u32)) as i32;
    let replica0 = (((raw[18] as u32) << 24)
        | ((raw[19] as u32) << 16)
        | ((raw[20] as u32) << 8)
        | (raw[21] as u32)) as i32;
    let isr_len = (((raw[22] as u32) << 24)
        | ((raw[23] as u32) << 16)
        | ((raw[24] as u32) << 8)
        | (raw[25] as u32)) as i32;
    let isr0 = (((raw[26] as u32) << 24)
        | ((raw[27] as u32) << 16)
        | ((raw[28] as u32) << 8)
        | (raw[29] as u32)) as i32;
    (
        count,
        error_code,
        partition_id,
        leader,
        replicas_len,
        replica0,
        isr_len,
        isr0,
    )
}

pub(crate) fn put_i16(o: &mut Vec<u8>, v: i16) {
    o.extend_from_slice(&encode_i16_be(v));
}
pub(crate) fn put_i32(o: &mut Vec<u8>, v: i32) {
    o.extend_from_slice(&encode_i32_be(v));
}
pub(crate) fn put_str(o: &mut Vec<u8>, s: &str) {
    // A Kafka v0 STRING length is an i16: a name >= 32768 bytes would wrap to a
    // negative length and be decoded as a null string, corrupting the rest of the
    // frame. Clamp to the largest char boundary that fits so length == bytes written.
    // (Advertised names are short; this is fail-safe defense-in-depth.)
    let mut n = kafka_clamp_str_len(s.len() as u64, i16::MAX as u64) as usize;
    while n > 0 && !s.is_char_boundary(n) {
        n -= 1;
    }
    // `get` rather than an index: `n <= s.len()` by construction, so this is always
    // `Some`; the fallback (an empty string, length 0) still keeps length == bytes.
    let bytes = match s.as_bytes().get(..n) {
        Some(b) => b,
        None => &[],
    };
    put_i16(o, bytes.len() as i16);
    o.extend_from_slice(bytes);
}

pub(crate) const fn take_i16(b: &[u8]) -> Option<(i16, &[u8])> {
    let &[b0, b1, ref rest @ ..] = b else {
        return None;
    };
    let val = (((b0 as u16) << 8) | (b1 as u16)) as i16;
    Some((val, rest))
}

pub(crate) const fn take_i32(b: &[u8]) -> Option<(i32, &[u8])> {
    let &[b0, b1, b2, b3, ref rest @ ..] = b else {
        return None;
    };
    let val = (((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32)) as i32;
    Some((val, rest))
}

pub(crate) const fn take_kstring_len(b: &[u8]) -> Option<(Option<usize>, &[u8])> {
    let &[b0, b1, ref rest @ ..] = b else {
        return None;
    };
    let n = (((b0 as u16) << 8) | (b1 as u16)) as i16;
    if n < 0 {
        return Some((None, rest));
    }
    let len = n as usize;
    if rest.len() < len {
        return None;
    }
    Some((Some(len), rest))
}

/// A bounds-checked big-endian cursor over a request body (fails closed).
struct Cur<'a> {
    b: &'a [u8],
}
impl Cur<'_> {
    fn i16(&mut self) -> Option<i16> {
        let (v, rest) = take_i16(self.b)?;
        self.b = rest;
        Some(v)
    }
    fn i32(&mut self) -> Option<i32> {
        let (v, rest) = take_i32(self.b)?;
        self.b = rest;
        Some(v)
    }
    fn kstring(&mut self) -> Option<Option<String>> {
        let (len, after_len) = take_kstring_len(self.b)?;
        let Some(len) = len else {
            self.b = after_len;
            return Some(None); // null string
        };
        let Ok(s) = core::str::from_utf8(after_len.get(..len)?) else {
            return None;
        };
        let owned = s.to_owned();
        self.b = after_len.get(len..)?;
        Some(Some(owned))
    }
}

/// Encode an unsigned 32-bit integer as a KIP-482 LEB128 `UNSIGNED_VARINT` (1..=5 bytes).
pub fn put_uvarint(o: &mut Vec<u8>, mut v: u32) {
    let mut steps = 0usize;
    while v >= 0x80 && steps < 5 {
        o.push(((v as u8) & 0x7f) | 0x80);
        v >>= 7;
        steps = steps.saturating_add(1);
    }
    o.push(v as u8);
}

/// Decode a KIP-482 LEB128 `UNSIGNED_VARINT` (`u32`), failing closed on truncation or
/// 5th-byte overflow.
#[must_use]
pub const fn take_uvarint(mut b: &[u8]) -> Option<(u32, &[u8])> {
    let mut acc = 0u32;
    let mut shift = 0u32;
    let mut idx = 0usize;
    while idx < 5 {
        let &[byte, ref rest @ ..] = b else {
            return None;
        };
        if idx == 4 && (byte & 0xf0) != 0 {
            return None;
        }
        acc |= ((byte & 0x7f) as u32) << (shift & 31);
        if (byte & 0x80) == 0 {
            return Some((acc, rest));
        }
        b = rest;
        shift = shift.saturating_add(7);
        idx = idx.saturating_add(1);
    }
    None
}

/// Emit an empty KIP-482 `TAG_BUFFER` (`0` tagged fields).
#[inline]
pub fn put_empty_tags(o: &mut Vec<u8>) {
    o.push(0);
}

/// Skip a KIP-482 `TAG_BUFFER` (`num_tags: uvarint`, followed by `num_tags` `(tag, size, data)`
/// entries), failing closed on truncation or overflow.
#[must_use]
pub const fn skip_tag_buffer(b: &[u8]) -> Option<&[u8]> {
    let Some((num_tags, mut cur)) = take_uvarint(b) else {
        return None;
    };
    let mut idx = 0u32;
    while idx < num_tags {
        let Some((_tag_id, after_id)) = take_uvarint(cur) else {
            return None;
        };
        let Some((tag_len, after_len)) = take_uvarint(after_id) else {
            return None;
        };
        let ulen = tag_len as usize;
        if after_len.len() < ulen {
            return None;
        }
        let (_, next_cur) = after_len.split_at(ulen);
        cur = next_cur;
        idx = idx.saturating_add(1);
    }
    Some(cur)
}

/// Encode a KIP-482 `COMPACT_STRING` (`uvarint(len + 1)` + UTF-8 bytes), clamped at a valid
/// UTF-8 boundary via Clean-origin [`kafka_compact_len_clamp`].
pub fn put_compact_str(o: &mut Vec<u8>, s: &str) {
    let mut n = kafka_compact_len_clamp(s.len() as u64, i16::MAX as u64) as usize;
    while n > 0 && !s.is_char_boundary(n) {
        n -= 1;
    }
    let bytes = match s.as_bytes().get(..n) {
        Some(b) => b,
        None => &[],
    };
    put_uvarint(o, (bytes.len() as u32).saturating_add(1));
    o.extend_from_slice(bytes);
}

/// Encode a KIP-482 `COMPACT_NULLABLE_STRING` (`0` for `None`, `len + 1` + bytes for `Some`).
pub fn put_compact_nullable_str(o: &mut Vec<u8>, s: Option<&str>) {
    match s {
        Some(v) => put_compact_str(o, v),
        None => o.push(0),
    }
}

/// Decode a KIP-482 `COMPACT_NULLABLE_STRING`, returning `(Option<&str>, remaining)`.
#[must_use]
pub fn take_compact_nullable_str(b: &[u8]) -> Option<(Option<&str>, &[u8])> {
    let (raw_len, rest) = take_uvarint(b)?;
    if raw_len == 0 {
        return Some((None, rest));
    }
    let len = (raw_len - 1) as usize;
    let slice = rest.get(..len)?;
    let Ok(s) = core::str::from_utf8(slice) else {
        return None;
    };
    Some((Some(s), rest.get(len..)?))
}

/// Decode a non-null KIP-482 `COMPACT_STRING`, returning `(&str, remaining)`.
#[must_use]
pub fn take_compact_str(b: &[u8]) -> Option<(&str, &[u8])> {
    let (Some(s), rest) = take_compact_nullable_str(b)? else {
        return None;
    };
    Some((s, rest))
}

/// Whether `(api_key, api_version)` uses KIP-482 Request Header v2 (`client_id` + `TAG_BUFFER`).
#[must_use]
pub const fn is_flexible_request(api_key: i16, api_version: i16) -> bool {
    (api_key == API_VERSIONS && api_version >= 3)
        || (api_key == METADATA && api_version >= 9)
        || (api_key == FIND_COORDINATOR && api_version >= 3)
        || (api_key == SASL_AUTHENTICATE && api_version >= 2)
}

/// Whether `(api_key, api_version)` uses KIP-482 Response Header v1 (`correlation_id` +
/// `TAG_BUFFER`). Per KIP-482 / KIP-511, `ApiVersions` ALWAYS uses Response Header v0!
#[must_use]
pub const fn is_flexible_response(api_key: i16, api_version: i16) -> bool {
    (api_key == METADATA && api_version >= 9)
        || (api_key == FIND_COORDINATOR && api_version >= 3)
        || (api_key == SASL_AUTHENTICATE && api_version >= 2)
}

/// A decoded Kafka request header (v1 or KIP-482 v2 header with header `TAG_BUFFER` consumed).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReqHeader {
    pub api_key: i16,
    pub api_version: i16,
    pub correlation_id: i32,
    pub client_id: Option<String>,
}

/// Parse a Kafka request (WITHOUT the outer 4-byte size prefix — the caller frames
/// that). Consumes the KIP-482 Request Header v2 `TAG_BUFFER` when present so the returned
/// `body_at` offset always points at the start of the request body. Panic-free.
pub fn parse_header(req: &[u8]) -> Option<(ReqHeader, usize)> {
    let mut c = Cur { b: req };
    let api_key = c.i16()?;
    let api_version = c.i16()?;
    let correlation_id = c.i32()?;
    let client_id = c.kstring()?;
    if is_flexible_request(api_key, api_version) {
        if api_key == API_VERSIONS && c.b.is_empty() {
            // Allow bare header-only ApiVersions v3/v4+ bootstrap probes.
        } else {
            c.b = skip_tag_buffer(c.b)?;
        }
    }
    let body_at = req.len().saturating_sub(c.b.len());
    Some((
        ReqHeader {
            api_key,
            api_version,
            correlation_id,
            client_id,
        },
        body_at,
    ))
}

pub(crate) fn frame_response_for(
    api_key: i16,
    api_version: i16,
    correlation_id: i32,
    payload: &[u8],
) -> Option<Vec<u8>> {
    if !payload.is_empty() && is_flexible_response(api_key, api_version) {
        let with_hdr_tag = payload.len().checked_add(1)?;
        let size = frame_size(with_hdr_tag)?;
        let hdr = encode_resp_frame_header(size, correlation_id);
        let mut out = Vec::with_capacity(8usize.saturating_add(with_hdr_tag));
        out.extend_from_slice(&hdr);
        out.push(0); // ResponseHeader v1 empty TAG_BUFFER
        out.extend_from_slice(payload);
        Some(out)
    } else {
        let size = frame_size(payload.len())?;
        let hdr = encode_resp_frame_header(size, correlation_id);
        Some([&hdr[..], payload].concat())
    }
}

fn validate_api_versions_v3_body(body: &[u8]) -> bool {
    if body.is_empty() {
        return true;
    }
    let Some((_client_sw_name, r1)) = take_compact_nullable_str(body) else {
        return false;
    };
    let Some((_client_sw_ver, r2)) = take_compact_nullable_str(r1) else {
        return false;
    };
    skip_tag_buffer(r2).is_some()
}

/// Build a full Kafka response frame (with the 4-byte size prefix) for `req` against
/// `cluster`. Returns `None` if the request header is unparseable, or if the
/// response would not fit the protocol's i32 frame size.
///
/// Version-gated (see the module docs): an `ApiVersions` request above the supported
/// range (`v4+`) gets a v0-shaped body with `error_code = UNSUPPORTED_VERSION` plus the
/// supported-versions array (KIP-511 bootstrap downgrade); `ApiVersions` `v0..=3`
/// negotiates natively (including KIP-482 flexible `v3` inside Response Header v0).
pub fn respond(req: &[u8], cluster: &ClusterMeta) -> Option<Vec<u8>> {
    let cap_hint = cluster.topics.len().min(65_536);
    let mut topics = Vec::with_capacity(cap_hint);
    for t in &cluster.topics {
        topics.push(TopicMeta {
            name: t.clone(),
            partitions: 1,
        });
    }
    respond_multi(req, &cluster.broker, &topics)
}

/// The response frame's size prefix: the correlation id plus the payload, or
/// `None` if that does not fit the protocol's i32 size field.
pub(crate) const fn frame_size(payload_len: usize) -> Option<i32> {
    let Some(n) = payload_len.checked_add(4) else {
        return None;
    };
    if n > i32::MAX as usize {
        None
    } else {
        Some(n as i32)
    }
}

/// ApiVersions response body for `v0..=3` (or v0-shaped downgrade body on `error_code != 0`).
fn api_versions_response_versioned(api_version: i16, error_code: i16) -> Vec<u8> {
    let mut o = Vec::new();
    put_i16(&mut o, error_code);
    if error_code != NONE || api_version <= 0 {
        put_i32(&mut o, SUPPORTED.len() as i32);
        for &(key, min, max) in SUPPORTED {
            o.extend_from_slice(&encode_api_version_entry(key, min, max));
        }
        return o;
    }
    if api_version <= 2 {
        put_i32(&mut o, SUPPORTED.len() as i32);
        for &(key, min, max) in SUPPORTED {
            o.extend_from_slice(&encode_api_version_entry(key, min, max));
        }
        put_i32(&mut o, 0); // throttle_time_ms
        return o;
    }
    // KIP-482 flexible v3 body: COMPACT_ARRAY of (key, min, max, TAG_BUFFER), throttle_time_ms, TAG_BUFFER.
    put_uvarint(&mut o, (SUPPORTED.len() as u32).saturating_add(1));
    for &(key, min, max) in SUPPORTED {
        o.extend_from_slice(&encode_api_version_entry(key, min, max));
        put_empty_tags(&mut o);
    }
    put_i32(&mut o, 0); // throttle_time_ms
    put_empty_tags(&mut o);
    o
}

/// Build a full Kafka response frame (with the 4-byte size prefix) for `req` against
/// `broker` + multi-partition `topics`.
#[must_use]
pub fn respond_multi(req: &[u8], broker: &BrokerMeta, topics: &[TopicMeta]) -> Option<Vec<u8>> {
    let (h, body_at) = parse_header(req)?;
    let body = req.get(body_at..)?;
    let supported = match version_range(h.api_key) {
        Some((min, max)) => {
            h.api_version >= min
                && h.api_version >= 0
                && version_within_max(h.api_version as u64, max as u64)
        }
        None => false,
    };
    let payload = match h.api_key {
        API_VERSIONS if h.api_version >= 0 => {
            let max_v = match version_range(API_VERSIONS) {
                Some((_, v)) => v as u64,
                None => 0,
            };
            let code = kafka_negotiate_error_code(
                h.api_version as u64,
                max_v,
                UNSUPPORTED_VERSION as u64,
                NONE as u64,
            ) as i16;
            if code == NONE && h.api_version == 3 && !validate_api_versions_v3_body(body) {
                return None;
            }
            api_versions_response_versioned(h.api_version, code)
        }
        API_VERSIONS => api_versions_response_versioned(0, UNSUPPORTED_VERSION),
        METADATA if supported => {
            metadata_response_multi_versioned(h.api_version, body, broker, topics)?
        }
        _ => Vec::new(),
    };
    frame_response_for(h.api_key, h.api_version, h.correlation_id, &payload)
}

/// Parse requested topic list across Metadata `v0..=9`, returning `Ok(None)` when all topics
/// are requested and `Ok(Some(names))` when an explicit list was supplied.
fn parse_metadata_requested_topics(api_version: i16, body: &[u8]) -> Option<Option<Vec<String>>> {
    if api_version >= 9 {
        let (raw_count, mut cur) = take_uvarint(body)?;
        if raw_count == 0 {
            // Null compact array => all topics.
            if cur.len() >= 3 {
                let rest = cur.get(3..)?;
                let _ = skip_tag_buffer(rest)?;
            }
            return Some(None);
        }
        let count = raw_count - 1;
        let mut names = Vec::new();
        let mut idx = 0u32;
        while idx < count {
            let (name_opt, after_name) = take_compact_nullable_str(cur)?;
            let next_cur = skip_tag_buffer(after_name)?;
            if let Some(s) = name_opt {
                names.push(s.to_owned());
            }
            cur = next_cur;
            idx = idx.saturating_add(1);
        }
        if cur.len() >= 3 {
            let rest = cur.get(3..)?;
            let _ = skip_tag_buffer(rest)?;
        }
        return Some(Some(names));
    }

    let mut c = Cur { b: body };
    if api_version == 0 {
        match c.i32() {
            Some(n) if n > 0 => {
                let mut v = Vec::new();
                let mut idx = 0i32;
                while idx < n {
                    match c.kstring() {
                        Some(Some(s)) => v.push(s),
                        Some(None) => {}
                        None => break,
                    }
                    idx = idx.saturating_add(1);
                }
                Some(Some(v))
            }
            _ => Some(None),
        }
    } else {
        match c.i32() {
            Some(n) if n < 0 => Some(None),
            Some(0) => Some(Some(Vec::new())),
            Some(n) => {
                let mut v = Vec::new();
                let mut idx = 0i32;
                while idx < n {
                    match c.kstring() {
                        Some(Some(s)) => v.push(s),
                        Some(None) => {}
                        None => break,
                    }
                    idx = idx.saturating_add(1);
                }
                Some(Some(v))
            }
            None => None,
        }
    }
}

/// Metadata `v0..=9` response body supporting multi-partition topics (`TopicMeta`) and
/// KIP-482 flexible `v9` compact framing.
pub(crate) fn metadata_response_multi_versioned(
    api_version: i16,
    body: &[u8],
    broker: &BrokerMeta,
    topics: &[TopicMeta],
) -> Option<Vec<u8>> {
    let requested = parse_metadata_requested_topics(api_version, body)?;
    let resolved: Vec<(&str, Option<i32>)> = if let Some(ref req_list) = requested {
        let mut seen = HashSet::new();
        let mut out_list = Vec::new();
        for t in req_list {
            let name = t.as_str();
            if seen.insert(name) {
                let mut found_parts: Option<i32> = None;
                for tm in topics {
                    if tm.name == name {
                        found_parts = Some(tm.partitions);
                        break;
                    }
                }
                out_list.push((name, found_parts));
            }
        }
        out_list
    } else {
        let cap = topics.len();
        let mut out_list = if cap <= 65_536 {
            Vec::with_capacity(cap)
        } else {
            Vec::new()
        };
        for tm in topics {
            out_list.push((tm.name.as_str(), Some(tm.partitions)));
        }
        out_list
    };

    let node = broker.node_id;
    let mut o = Vec::new();

    if api_version == 0 {
        put_i32(&mut o, 1);
        put_i32(&mut o, broker.node_id);
        put_str(&mut o, &broker.host);
        put_i32(&mut o, broker.port);
        put_i32(&mut o, resolved.len() as i32);
        for &(name, parts_opt) in &resolved {
            match parts_opt {
                Some(parts) => put_topic_partitions_v0(&mut o, name, parts, node),
                None => put_topic_v0(&mut o, name, false, node),
            }
        }
        return Some(o);
    }

    if api_version >= 9 {
        put_i32(&mut o, 0); // throttle_time_ms
        put_uvarint(&mut o, 2); // brokers COMPACT_ARRAY(1)
        put_i32(&mut o, broker.node_id);
        put_compact_str(&mut o, &broker.host);
        put_i32(&mut o, broker.port);
        put_compact_nullable_str(&mut o, None); // rack
        put_empty_tags(&mut o);
        put_compact_nullable_str(&mut o, Some("astream")); // cluster_id
        put_i32(&mut o, node); // controller_id
        put_uvarint(&mut o, (resolved.len() as u32).saturating_add(1));
        for &(name, parts_opt) in &resolved {
            match parts_opt {
                Some(parts) => {
                    let p_count = if parts <= 1 { 1 } else { parts };
                    put_i16(&mut o, NONE);
                    put_compact_str(&mut o, name);
                    o.push(0); // is_internal = false
                    put_uvarint(&mut o, (p_count as u32).saturating_add(1));
                    let mut pid = 0i32;
                    while pid < p_count {
                        put_i16(&mut o, NONE);
                        put_i32(&mut o, pid);
                        put_i32(&mut o, node); // leader_id
                        put_i32(&mut o, 0); // leader_epoch
                        put_uvarint(&mut o, 2); // replica_nodes len=1
                        put_i32(&mut o, node);
                        put_uvarint(&mut o, 2); // isr_nodes len=1
                        put_i32(&mut o, node);
                        put_uvarint(&mut o, 1); // offline_replicas len=0
                        put_empty_tags(&mut o);
                        pid = pid.saturating_add(1);
                    }
                    put_i32(&mut o, i32::MIN); // topic_authorized_operations
                    put_empty_tags(&mut o);
                }
                None => {
                    put_i16(&mut o, UNKNOWN_TOPIC_OR_PARTITION);
                    put_compact_str(&mut o, name);
                    o.push(0); // is_internal = false
                    put_uvarint(&mut o, 1); // partitions len=0
                    put_i32(&mut o, i32::MIN); // topic_authorized_operations
                    put_empty_tags(&mut o);
                }
            }
        }
        put_i32(&mut o, i32::MIN); // cluster_authorized_operations
        put_empty_tags(&mut o);
        return Some(o);
    }

    // Metadata v1..=8 (non-flexible)
    if api_version >= 3 {
        put_i32(&mut o, 0); // throttle_time_ms
    }
    put_i32(&mut o, 1); // brokers len=1
    put_i32(&mut o, broker.node_id);
    put_str(&mut o, &broker.host);
    put_i32(&mut o, broker.port);
    put_i16(&mut o, -1); // rack = null
    if api_version >= 2 {
        put_str(&mut o, "astream"); // cluster_id
    }
    put_i32(&mut o, node); // controller_id
    put_i32(&mut o, resolved.len() as i32);
    for &(name, parts_opt) in &resolved {
        match parts_opt {
            Some(parts) => {
                let p_count = if parts <= 1 { 1 } else { parts };
                put_i16(&mut o, NONE);
                put_str(&mut o, name);
                o.push(0); // is_internal = false
                put_i32(&mut o, p_count);
                let mut pid = 0i32;
                while pid < p_count {
                    put_i16(&mut o, NONE);
                    put_i32(&mut o, pid);
                    put_i32(&mut o, node);
                    if api_version >= 7 {
                        put_i32(&mut o, 0); // leader_epoch
                    }
                    put_i32(&mut o, 1);
                    put_i32(&mut o, node);
                    put_i32(&mut o, 1);
                    put_i32(&mut o, node);
                    if api_version >= 5 {
                        put_i32(&mut o, 0); // offline_replicas len=0
                    }
                    pid = pid.saturating_add(1);
                }
                if api_version >= 8 {
                    put_i32(&mut o, i32::MIN);
                }
            }
            None => {
                put_i16(&mut o, UNKNOWN_TOPIC_OR_PARTITION);
                put_str(&mut o, name);
                o.push(0);
                put_i32(&mut o, 0);
                if api_version >= 8 {
                    put_i32(&mut o, i32::MIN);
                }
            }
        }
    }
    if api_version >= 8 {
        put_i32(&mut o, i32::MIN);
    }
    Some(o)
}

fn put_topic_partitions_v0(o: &mut Vec<u8>, name: &str, partitions: i32, node: i32) {
    let count = if partitions <= 1 { 1 } else { partitions };
    if count == 1 {
        put_topic_v0(o, name, true, node);
        return;
    }
    put_i16(o, NONE);
    put_str(o, name);
    put_i32(o, count);
    let mut pid = 0i32;
    while pid < count {
        put_i16(o, NONE);
        put_i32(o, pid);
        put_i32(o, node); // leader
        put_i32(o, 1); // replicas len
        put_i32(o, node); // replica 0
        put_i32(o, 1); // isr len
        put_i32(o, node); // isr 0
        pid = pid.saturating_add(1);
    }
}

/// Emit one Metadata v0 topic entry. A served topic gets `error=none` and its single
/// partition (led by `node`); an unserved-but-requested topic gets
/// `UNKNOWN_TOPIC_OR_PARTITION` and an empty partition array.
fn put_topic_v0(o: &mut Vec<u8>, name: &str, served: bool, node: i32) {
    if !served {
        put_i16(o, UNKNOWN_TOPIC_OR_PARTITION);
        put_str(o, name);
        put_i32(o, 0); // no partitions
        return;
    }
    put_i16(o, NONE); // topic error = none
    put_str(o, name);
    // one partition (id 0), led by this broker, replicas=[node], isr=[node]
    o.extend_from_slice(&encode_single_partition_array(NONE, 0, node));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cluster() -> ClusterMeta {
        ClusterMeta {
            broker: BrokerMeta {
                node_id: 0,
                host: "127.0.0.1".into(),
                port: 9092,
            },
            topics: vec!["astream".into()],
        }
    }

    /// A real ApiVersions v0 request, byte-for-byte per the Kafka protocol:
    /// api_key=18, api_version=0, correlation_id=7, client_id="kc" (no body).
    fn api_versions_request() -> Vec<u8> {
        let mut r = Vec::new();
        r.extend_from_slice(&18i16.to_be_bytes());
        r.extend_from_slice(&0i16.to_be_bytes());
        r.extend_from_slice(&7i32.to_be_bytes());
        r.extend_from_slice(&2i16.to_be_bytes());
        r.extend_from_slice(b"kc");
        r
    }

    #[test]
    fn answers_apiversions_v0_in_spec_format() {
        let resp = respond(&api_versions_request(), &cluster()).unwrap();
        // size:i32 | correlation_id:i32 | error:i16 | count:i32 | entries...
        let size = i32::from_be_bytes(resp[0..4].try_into().unwrap()) as usize;
        assert_eq!(size, resp.len() - 4, "size prefix counts the rest");
        assert_eq!(
            i32::from_be_bytes(resp[4..8].try_into().unwrap()),
            7,
            "correlation id echoed"
        );
        assert_eq!(
            i16::from_be_bytes(resp[8..10].try_into().unwrap()),
            0,
            "no error"
        );
        let count = i32::from_be_bytes(resp[10..14].try_into().unwrap());
        assert_eq!(count, SUPPORTED.len() as i32);
        // First advertised API is ApiVersions itself, capped at v3 (KIP-482 flexible).
        assert_eq!(
            i16::from_be_bytes(resp[14..16].try_into().unwrap()),
            API_VERSIONS
        );
        assert_eq!(
            i16::from_be_bytes(resp[18..20].try_into().unwrap()),
            3,
            "max_version capped at 3"
        );
    }

    /// A real Metadata v0 request for all topics (topic array count = 0).
    fn metadata_request_all() -> Vec<u8> {
        let mut r = Vec::new();
        r.extend_from_slice(&3i16.to_be_bytes()); // api_key = Metadata
        r.extend_from_slice(&0i16.to_be_bytes()); // version 0
        r.extend_from_slice(&42i32.to_be_bytes()); // correlation id
        r.extend_from_slice(&2i16.to_be_bytes());
        r.extend_from_slice(b"kc"); // client_id
        r.extend_from_slice(&0i32.to_be_bytes()); // topics: 0 = all
        r
    }

    #[test]
    fn answers_metadata_v0_with_broker_and_topic() {
        let resp = respond(&metadata_request_all(), &cluster()).unwrap();
        assert_eq!(
            i32::from_be_bytes(resp[4..8].try_into().unwrap()),
            42,
            "correlation id echoed"
        );
        // Decode the body: brokers[1] then topics[].
        let mut c = Cur { b: &resp[8..] };
        assert_eq!(c.i32().unwrap(), 1, "one broker advertised");
        assert_eq!(c.i32().unwrap(), 0, "node_id 0");
        assert_eq!(c.kstring().unwrap().unwrap(), "127.0.0.1", "broker host");
        assert_eq!(c.i32().unwrap(), 9092, "broker port");
        assert_eq!(c.i32().unwrap(), 1, "one topic");
        assert_eq!(c.i16().unwrap(), 0, "topic error none");
        assert_eq!(c.kstring().unwrap().unwrap(), "astream", "topic name");
        assert_eq!(c.i32().unwrap(), 1, "one partition");
        let _perr = c.i16().unwrap();
        assert_eq!(c.i32().unwrap(), 0, "partition 0");
        assert_eq!(c.i32().unwrap(), 0, "leader = this node");
    }

    #[test]
    fn unparseable_request_is_none_not_a_panic() {
        assert_eq!(respond(&[0, 1], &cluster()), None);
        assert_eq!(respond(&[], &cluster()), None);
    }

    /// An ApiVersions request at a FLEXIBLE version (v4) above astream's supported range (0..=3).
    fn api_versions_request_v4() -> Vec<u8> {
        let mut r = Vec::new();
        r.extend_from_slice(&18i16.to_be_bytes()); // api_key = ApiVersions
        r.extend_from_slice(&4i16.to_be_bytes()); // api_version = 4 (above max 3)
        r.extend_from_slice(&9i32.to_be_bytes()); // correlation id
        r.extend_from_slice(&2i16.to_be_bytes());
        r.extend_from_slice(b"kc");
        r
    }

    #[test]
    fn apiversions_unsupported_version_returns_error_35_with_range() {
        // Per the Kafka bootstrap special case (KIP-511), an ApiVersions request above the
        // supported range (v4 > max v3) gets a v0-framed body: error_code = UNSUPPORTED_VERSION(35)
        // PLUS the supported array, so the client downgrades — never error 0 with v0
        // bytes (which a flexible client misparses).
        let resp = respond(&api_versions_request_v4(), &cluster()).unwrap();
        assert_eq!(
            i32::from_be_bytes(resp[4..8].try_into().unwrap()),
            9,
            "correlation echoed"
        );
        assert_eq!(
            i16::from_be_bytes(resp[8..10].try_into().unwrap()),
            35,
            "UNSUPPORTED_VERSION, not 0"
        );
        let count = i32::from_be_bytes(resp[10..14].try_into().unwrap());
        assert_eq!(count, SUPPORTED.len() as i32, "range still advertised");
        assert_eq!(
            i16::from_be_bytes(resp[14..16].try_into().unwrap()),
            API_VERSIONS
        );
        assert_eq!(
            i16::from_be_bytes(resp[18..20].try_into().unwrap()),
            3,
            "max_version 3"
        );
    }

    /// A Metadata v0 request naming exactly one topic.
    fn metadata_request_for(name: &str) -> Vec<u8> {
        let mut r = Vec::new();
        r.extend_from_slice(&3i16.to_be_bytes());
        r.extend_from_slice(&0i16.to_be_bytes());
        r.extend_from_slice(&7i32.to_be_bytes());
        r.extend_from_slice(&2i16.to_be_bytes());
        r.extend_from_slice(b"kc");
        r.extend_from_slice(&1i32.to_be_bytes()); // one topic requested
        r.extend_from_slice(&(name.len() as i16).to_be_bytes());
        r.extend_from_slice(name.as_bytes());
        r
    }

    #[test]
    fn metadata_unknown_requested_topic_is_error_3_not_dropped() {
        let resp = respond(&metadata_request_for("nope"), &cluster()).unwrap();
        let mut c = Cur { b: &resp[8..] };
        assert_eq!(c.i32().unwrap(), 1, "one broker");
        assert_eq!(c.i32().unwrap(), 0, "node_id");
        assert_eq!(c.kstring().unwrap().unwrap(), "127.0.0.1");
        assert_eq!(c.i32().unwrap(), 9092);
        assert_eq!(
            c.i32().unwrap(),
            1,
            "one topic returned, NOT silently dropped"
        );
        assert_eq!(c.i16().unwrap(), 3, "UNKNOWN_TOPIC_OR_PARTITION");
        assert_eq!(
            c.kstring().unwrap().unwrap(),
            "nope",
            "echoes requested name"
        );
        assert_eq!(c.i32().unwrap(), 0, "no partitions");
    }

    #[test]
    fn metadata_oversized_topic_count_terminates_on_short_body() {
        // Claim a million topics but supply exactly one, then EOF: the loop must stop
        // when the body is exhausted (count is attacker-controlled, never a bound).
        let mut r = Vec::new();
        r.extend_from_slice(&3i16.to_be_bytes());
        r.extend_from_slice(&0i16.to_be_bytes());
        r.extend_from_slice(&5i32.to_be_bytes());
        r.extend_from_slice(&2i16.to_be_bytes());
        r.extend_from_slice(b"kc");
        r.extend_from_slice(&1_000_000i32.to_be_bytes()); // claim 1,000,000 topics...
        r.extend_from_slice(&7i16.to_be_bytes());
        r.extend_from_slice(b"astream"); // ...but supply one, then the body ends
        let resp = respond(&r, &cluster()).unwrap(); // returns (does not spin)
        let mut c = Cur { b: &resp[8..] };
        assert_eq!(c.i32().unwrap(), 1, "one broker");
        let _ = c.i32().unwrap();
        let _ = c.kstring().unwrap();
        let _ = c.i32().unwrap();
        assert_eq!(c.i32().unwrap(), 1, "the one supplied topic, not a million");
        assert_eq!(c.i16().unwrap(), 0, "served topic, error none");
        assert_eq!(c.kstring().unwrap().unwrap(), "astream");
    }

    #[test]
    fn a_request_naming_topics_is_never_widened_to_all_topics() {
        // Two topics claimed; one null entry, then the body ends: nothing readable
        // was named, but the client asked for specific topics, not for all of them.
        let mut r = Vec::new();
        r.extend_from_slice(&3i16.to_be_bytes());
        r.extend_from_slice(&0i16.to_be_bytes());
        r.extend_from_slice(&5i32.to_be_bytes());
        r.extend_from_slice(&2i16.to_be_bytes());
        r.extend_from_slice(b"kc");
        r.extend_from_slice(&2i32.to_be_bytes()); // two topics...
        r.extend_from_slice(&(-1i16).to_be_bytes()); // ...a null one, then EOF
        let resp = respond(&r, &cluster()).unwrap();
        let mut c = Cur { b: &resp[8..] };
        assert_eq!(c.i32().unwrap(), 1, "one broker");
        let _ = c.i32().unwrap();
        let _ = c.kstring().unwrap();
        let _ = c.i32().unwrap();
        assert_eq!(c.i32().unwrap(), 0, "no topics, not every served topic");
        assert!(c.b.is_empty(), "nothing after the empty topic array");
    }

    #[test]
    fn metadata_duplicate_requested_topics_are_answered_once() {
        // A client may name the same topic many times; Kafka answers the SET of
        // requested topics. Echoing every repeat would let a request of tiny
        // repeated names amplify into a response many times its size.
        let mut r = Vec::new();
        r.extend_from_slice(&3i16.to_be_bytes());
        r.extend_from_slice(&0i16.to_be_bytes());
        r.extend_from_slice(&5i32.to_be_bytes());
        r.extend_from_slice(&2i16.to_be_bytes());
        r.extend_from_slice(b"kc");
        let names = ["astream", "nope", "astream", "nope", "astream"];
        r.extend_from_slice(&(names.len() as i32).to_be_bytes());
        for n in names {
            r.extend_from_slice(&(n.len() as i16).to_be_bytes());
            r.extend_from_slice(n.as_bytes());
        }
        let resp = respond(&r, &cluster()).unwrap();
        let mut c = Cur { b: &resp[8..] };
        assert_eq!(c.i32().unwrap(), 1, "one broker");
        let _ = c.i32().unwrap();
        let _ = c.kstring().unwrap();
        let _ = c.i32().unwrap();
        assert_eq!(c.i32().unwrap(), 2, "each distinct topic answered once");
        assert_eq!(c.i16().unwrap(), 0, "served topic first, in request order");
        assert_eq!(c.kstring().unwrap().unwrap(), "astream");
        assert_eq!(c.i32().unwrap(), 1, "one partition");
        // error, id, leader, replicas[1], isr[1]
        let _ = c.i16();
        for _ in 0..6 {
            let _ = c.i32();
        }
        assert_eq!(c.i16().unwrap(), UNKNOWN_TOPIC_OR_PARTITION);
        assert_eq!(c.kstring().unwrap().unwrap(), "nope");
        assert_eq!(c.i32().unwrap(), 0, "no partitions");
        assert!(c.b.is_empty(), "nothing after the two topics");
    }

    #[test]
    fn put_str_clamps_to_a_char_boundary_and_its_length_counts_the_bytes_written() {
        // Short: written whole.
        let mut o = Vec::new();
        put_str(&mut o, "astream");
        assert_eq!(o, b"\x00\x07astream");
        // Too long for an i16 length, and 32767 falls inside a 2-byte char: the
        // clamp backs off to 32766, and the length prefix says exactly that.
        let long = "\u{e9}".repeat(20_000); // 40000 bytes
        let mut o = Vec::new();
        put_str(&mut o, &long);
        let n = i16::from_be_bytes([o[0], o[1]]);
        assert_eq!(n, 32_766);
        assert_eq!(o.len(), 2 + 32_766, "length prefix == bytes written");
        assert!(std::str::from_utf8(&o[2..]).is_ok(), "never splits a char");
    }

    #[test]
    fn respond_frames_size_then_correlation_id_then_payload() {
        // The frame is exactly size:i32 | correlation_id:i32 | payload, for both a
        // full answer and the empty-bodied answer to an unknown API.
        let resp = respond(&api_versions_request(), &cluster()).unwrap();
        let size = i32::from_be_bytes(resp[0..4].try_into().unwrap());
        assert_eq!(size as usize, resp.len() - 4);
        let mut unknown = api_versions_request();
        unknown[0..2].copy_from_slice(&999i16.to_be_bytes());
        let resp = respond(&unknown, &cluster()).unwrap();
        assert_eq!(
            resp,
            [0, 0, 0, 4, 0, 0, 0, 7],
            "size 4, correlation id 7, no body"
        );
    }

    #[test]
    fn a_response_too_large_for_the_i32_size_prefix_is_refused() {
        // The size prefix is an i32; a length that does not fit must not wrap
        // into a negative or short size that desyncs the client's framing.
        let max = i32::MAX as usize;
        assert_eq!(frame_size(0), Some(4));
        assert_eq!(frame_size(max - 4), Some(i32::MAX));
        assert_eq!(frame_size(max - 3), None);
        assert_eq!(frame_size(usize::MAX), None);
    }

    #[test]
    fn clean_origin_kafka_wire_kernels_clamp_and_negotiate_versions() {
        assert_eq!(kafka_clamp_str_len(7, 32_767), 7);
        assert_eq!(kafka_clamp_str_len(40_000, 32_767), 32_767);
        assert!(version_within_max(0, 0));
        assert!(!version_within_max(3, 0));
        assert_eq!(
            kafka_negotiate_error_code(0, 0, UNSUPPORTED_VERSION as u64, NONE as u64),
            0
        );
        assert_eq!(
            kafka_negotiate_error_code(3, 0, UNSUPPORTED_VERSION as u64, NONE as u64),
            UNSUPPORTED_VERSION as u64
        );
        assert_eq!(decode_i16_be(&encode_i16_be(-32_000)), -32_000);
        assert_eq!(decode_i32_be(&encode_i32_be(-1_234_567)), -1_234_567);
        assert_eq!(
            decode_req_header_prefix(&encode_req_header_prefix(18, 3, 42)),
            (18, 3, 42)
        );
        assert_eq!(
            decode_resp_frame_header(&encode_resp_frame_header(128, 7)),
            (128, 7)
        );
        assert_eq!(
            decode_api_version_entry(&encode_api_version_entry(18, 0, 0)),
            (18, 0, 0)
        );
        assert_eq!(
            decode_single_partition_array(&encode_single_partition_array(0, 0, 9)),
            (1, 0, 0, 9, 1, 9, 1, 9)
        );
    }

    #[test]
    fn crc32c_matches_rfc3720_test_vectors_and_unaligned_slices() {
        assert_eq!(crc32c(b""), 0x0000_0000);
        assert_eq!(crc32c(b"123456789"), 0xE306_9283);
        assert_eq!(crc32c(&[0u8; 32]), 0x8A91_36AA);
        assert_eq!(crc32c(&[0xFFu8; 32]), 0x62A8_AB43);
        let mut asc = [0u8; 32];
        let mut dec = [0u8; 32];
        for i in 0..32 {
            asc[i] = i as u8;
            dec[i] = (31 - i) as u8;
        }
        assert_eq!(crc32c(&asc), 0x46DD_794E);
        assert_eq!(crc32c(&dec), 0x113F_DB5C);

        // Incremental + multi-block (137 bytes > 8-byte slicing stride) consistency.
        let mut big = Vec::new();
        for i in 0..137u16 {
            big.push((i.wrapping_mul(37) & 0xff) as u8);
        }
        let whole = crc32c(&big);
        let split = crate::crc32c::crc32c_update(crc32c(&big[..29]), &big[29..]);
        assert_eq!(whole, split);
    }

    #[test]
    fn zigzag_varints_and_record_batch_v2_roundtrip_and_reject_corruption() {
        use crate::record_batch::{put_varint, put_varlong, take_varint, take_varlong};

        for &v in &[0i32, -1, 1, -64, 63, -65, 64, i32::MIN, i32::MAX] {
            let mut b = Vec::new();
            put_varint(&mut b, v);
            let (got, rem) = take_varint(&b).expect("valid varint");
            assert_eq!(got, v);
            assert!(rem.is_empty());
        }
        for &v in &[
            0i64,
            -1,
            1,
            -1_000_000_000_000,
            1_000_000_000_000,
            i64::MIN,
            i64::MAX,
        ] {
            let mut b = Vec::new();
            put_varlong(&mut b, v);
            let (got, rem) = take_varlong(&b).expect("valid varlong");
            assert_eq!(got, v);
            assert!(rem.is_empty());
        }
        // 5-byte overflow varint and 10-byte overflow varlong fail closed.
        assert!(take_varint(&[0x80, 0x80, 0x80, 0x80, 0x10]).is_none());
        assert!(
            take_varlong(&[0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x02]).is_none()
        );

        let batch = RecordBatchV2 {
            base_offset: 42,
            partition_leader_epoch: 3,
            attributes: 0,
            producer_id: 9001,
            producer_epoch: 2,
            base_sequence: 10,
            records: vec![
                KafkaRecord {
                    timestamp_ms: 1_700_000_000_100,
                    key: Some(b"s-1".to_vec()),
                    value: Some(b"hello fabric".to_vec()),
                    headers: vec![KafkaHeader {
                        key: "source".into(),
                        value: Some(b"aterm".to_vec()),
                    }],
                },
                KafkaRecord {
                    timestamp_ms: 1_700_000_000_250,
                    key: None,
                    value: None, // tombstone
                    headers: vec![KafkaHeader {
                        key: "null-hdr".into(),
                        value: None,
                    }],
                },
            ],
        };
        let mut raw = encode_record_batch_v2(&batch).expect("encode batch");
        assert!(record_batch_magic_v2(raw[16]));
        let (decoded, used) = decode_record_batch_v2(&raw).expect("decode batch");
        assert_eq!(used, raw.len());
        assert_eq!(decoded, batch);

        // Flip 1 bit in the payload -> CRC-32C fails closed BEFORE record parsing!
        let last = raw.len() - 1;
        raw[last] ^= 0x01;
        assert!(matches!(
            decode_record_batch_v2(&raw),
            Err(BatchDecodeError::BadCrc { .. })
        ));
    }

    #[test]
    fn kip98_idempotent_store_deduplicates_retries_and_fences_epochs_and_sequences() {
        let mut store = KafkaStore::new(&["astream".to_owned()]);
        let mk_batch = |pid: i64, epoch: i16, seq: i32, payloads: &[&[u8]]| -> Vec<u8> {
            let records = payloads
                .iter()
                .enumerate()
                .map(|(i, p)| KafkaRecord {
                    timestamp_ms: 1_000 + (i as i64) * 10,
                    key: None,
                    value: Some(p.to_vec()),
                    headers: Vec::new(),
                })
                .collect();
            encode_record_batch_v2(&RecordBatchV2 {
                base_offset: 0,
                partition_leader_epoch: 0,
                attributes: 0,
                producer_id: pid,
                producer_epoch: epoch,
                base_sequence: seq,
                records,
            })
            .unwrap()
        };

        // First batch (pid=77, epoch=0, seq=0, 2 records) -> base_offset 0, hw 2.
        let b0 = mk_batch(77, 0, 0, &[b"r0", b"r1"]);
        assert_eq!(store.append_batch("astream", 0, &b0), (NONE, 0));
        assert_eq!(store.high_watermark("astream"), Some(2));

        // Exact retry of b0 -> deduplicated, returns original base_offset 0, hw stays 2!
        assert_eq!(store.append_batch("astream", 0, &b0), (NONE, 0));
        assert_eq!(store.high_watermark("astream"), Some(2));

        // Sequence gap (seq=3 instead of expected 2) -> OUT_OF_ORDER_SEQUENCE_NUMBER.
        let gap = mk_batch(77, 0, 3, &[b"r3"]);
        assert_eq!(
            store.append_batch("astream", 0, &gap),
            (OUT_OF_ORDER_SEQUENCE_NUMBER, -1)
        );

        // Next contiguous batch (seq=2, 1 record) -> base_offset 2, hw 3.
        let b2 = mk_batch(77, 0, 2, &[b"r2"]);
        assert_eq!(store.append_batch("astream", 0, &b2), (NONE, 2));
        assert_eq!(store.high_watermark("astream"), Some(3));

        // Epoch bump to epoch=1 must reset sequence to 0; stale epoch=0 is fenced!
        let b_epoch1_bad_seq = mk_batch(77, 1, 3, &[b"bad"]);
        assert_eq!(
            store.append_batch("astream", 0, &b_epoch1_bad_seq),
            (OUT_OF_ORDER_SEQUENCE_NUMBER, -1)
        );
        let b_epoch1 = mk_batch(77, 1, 0, &[b"e1-r0"]);
        assert_eq!(store.append_batch("astream", 0, &b_epoch1), (NONE, 3));
        let stale_epoch0 = mk_batch(77, 0, 3, &[b"zombie"]);
        assert_eq!(
            store.append_batch("astream", 0, &stale_epoch0),
            (INVALID_PRODUCER_EPOCH, -1)
        );
    }

    #[test]
    fn live_tcp_kafka_server_speaks_apiversions_produce_fetch_and_list_offsets() {
        let meta = ClusterMeta {
            broker: BrokerMeta {
                node_id: 1,
                host: "127.0.0.1".into(),
                port: 0,
            },
            topics: vec!["events".into()],
        };
        let store = KafkaStore::new(&meta.topics);
        let mut srv = KafkaServer::bind("127.0.0.1:0", meta, store).expect("bind KafkaServer");
        let mut client =
            KafkaClient::connect(srv.local_addr(), "aterm-kafka-test").expect("connect client");

        // 1. Over-eager flexible v4 ApiVersions gets error 35 + supported range; flexible v3 and v0 succeed!
        let (err_v4, range_v4) = client.api_versions(4).expect("ApiVersions v4");
        assert_eq!(err_v4, UNSUPPORTED_VERSION);
        assert_eq!(range_v4.len(), SUPPORTED.len());
        let (err_v3, range_v3) = client.api_versions(3).expect("ApiVersions v3");
        assert_eq!(err_v3, NONE);
        assert_eq!(range_v3.len(), SUPPORTED.len());
        assert!(range_v3.contains(&(API_VERSIONS, 0, 3)));
        assert!(range_v3.contains(&(METADATA, 0, 9)));
        assert!(range_v3.contains(&(FIND_COORDINATOR, 0, 3)));
        let (err_v0, range_v0) = client.api_versions(0).expect("ApiVersions v0");
        assert_eq!(err_v0, NONE);
        assert!(range_v0.contains(&(PRODUCE, 3, 3)));
        assert!(range_v0.contains(&(FETCH, 4, 4)));
        assert!(range_v0.contains(&(LIST_OFFSETS, 1, 1)));

        // 2. Produce two RecordBatch v2 batches over TCP.
        let batch1 = RecordBatchV2 {
            base_offset: 0,
            partition_leader_epoch: 0,
            attributes: 0,
            producer_id: 500,
            producer_epoch: 0,
            base_sequence: 0,
            records: vec![
                KafkaRecord {
                    timestamp_ms: 10_000,
                    key: Some(b"k0".to_vec()),
                    value: Some(b"v0".to_vec()),
                    headers: Vec::new(),
                },
                KafkaRecord {
                    timestamp_ms: 10_050,
                    key: Some(b"k1".to_vec()),
                    value: Some(b"v1".to_vec()),
                    headers: Vec::new(),
                },
            ],
        };
        let batch2 = RecordBatchV2 {
            base_offset: 0,
            partition_leader_epoch: 0,
            attributes: 0,
            producer_id: 500,
            producer_epoch: 0,
            base_sequence: 2,
            records: vec![KafkaRecord {
                timestamp_ms: 20_000,
                key: Some(b"k2".to_vec()),
                value: Some(b"v2".to_vec()),
                headers: Vec::new(),
            }],
        };
        assert_eq!(client.produce("events", 0, &batch1).unwrap(), (NONE, 0));
        // Duplicate retry over TCP is deduplicated!
        assert_eq!(client.produce("events", 0, &batch1).unwrap(), (NONE, 0));
        assert_eq!(client.produce("events", 0, &batch2).unwrap(), (NONE, 2));

        // Corrupted batch over TCP is rejected with CORRUPT_MESSAGE (2) without dropping socket.
        let mut corrupt = encode_record_batch_v2(&batch2).unwrap();
        let tail = corrupt.len() - 1;
        corrupt[tail] ^= 0x80;
        assert_eq!(
            client.produce_raw("events", 0, &corrupt).unwrap(),
            (CORRUPT_MESSAGE, -1)
        );

        // 3. ListOffsets v1: earliest -> 0, latest -> 3, timestamp 10_020 -> offset 1 (10_050).
        assert_eq!(
            client
                .list_offsets("events", 0, TIMESTAMP_EARLIEST)
                .unwrap(),
            (NONE, -1, 0)
        );
        assert_eq!(
            client.list_offsets("events", 0, TIMESTAMP_LATEST).unwrap(),
            (NONE, -1, 3)
        );
        assert_eq!(
            client.list_offsets("events", 0, 10_020).unwrap(),
            (NONE, 10_050, 1)
        );

        // 4. Fetch v4 from offset 0 returns both restamped batches (base_offset 0 and 2) + hw=3.
        let (ferr, hw, batches) = client.fetch("events", 0, 0, 64 * 1024).unwrap();
        assert_eq!(ferr, NONE);
        assert_eq!(hw, 3);
        assert_eq!(batches.len(), 2);
        assert_eq!(batches[0].base_offset, 0);
        assert_eq!(batches[0].records.len(), 2);
        assert_eq!(batches[1].base_offset, 2);
        assert_eq!(batches[1].records[0].value.as_deref(), Some(&b"v2"[..]));

        // Out-of-range fetch returns OFFSET_OUT_OF_RANGE (1) and current hw=3.
        let (oor_err, oor_hw, oor_batches) = client.fetch("events", 0, 99, 64 * 1024).unwrap();
        assert_eq!(oor_err, OFFSET_OUT_OF_RANGE);
        assert_eq!(oor_hw, 3);
        assert!(oor_batches.is_empty());

        drop(client);
        srv.shutdown();
    }

    #[test]
    fn multi_partition_and_consumer_group_coordinator_lifecycle_fences_stale_generations() {
        let meta = ClusterMeta {
            broker: BrokerMeta {
                node_id: 7,
                host: "127.0.0.1".into(),
                port: 0,
            },
            topics: vec!["orders".into()],
        };
        let store = KafkaStore::with_partitions(&[("orders".into(), 4)]);
        let mut srv = KafkaServer::bind("127.0.0.1:0", meta, store).expect("bind KafkaServer");
        let addr = srv.local_addr();

        let mut c1 = KafkaClient::connect(addr, "consumer-1").expect("connect c1");
        let mut c2 = KafkaClient::connect(addr, "consumer-2").expect("connect c2");

        // 1. Metadata v0 advertises all 4 partitions (0..4) and dynamically bound port.
        let (bmeta, topics) = c1.metadata(&["orders", "missing"]).expect("metadata");
        assert_eq!(bmeta.node_id, 7);
        assert_eq!(bmeta.port, i32::from(addr.port()));
        assert_eq!(topics.len(), 2);
        assert_eq!(topics[0], (NONE, "orders".to_owned(), vec![0, 1, 2, 3]));
        assert_eq!(
            topics[1],
            (UNKNOWN_TOPIC_OR_PARTITION, "missing".to_owned(), Vec::new())
        );

        // 2. Produce & Fetch independently across partitions 0..4; partition 4 is refused.
        for pid in 0..4i32 {
            let batch = RecordBatchV2 {
                base_offset: 0,
                partition_leader_epoch: 0,
                attributes: 0,
                producer_id: 900 + i64::from(pid),
                producer_epoch: 0,
                base_sequence: 0,
                records: vec![KafkaRecord {
                    timestamp_ms: 50_000 + i64::from(pid) * 100,
                    key: Some(format!("pk-{pid}").into_bytes()),
                    value: Some(format!("pv-{pid}").into_bytes()),
                    headers: Vec::new(),
                }],
            };
            assert_eq!(c1.produce("orders", pid, &batch).unwrap(), (NONE, 0));
        }
        let dummy = RecordBatchV2 {
            base_offset: 0,
            partition_leader_epoch: 0,
            attributes: 0,
            producer_id: -1,
            producer_epoch: -1,
            base_sequence: -1,
            records: vec![KafkaRecord {
                timestamp_ms: 1,
                key: None,
                value: Some(b"x".to_vec()),
                headers: Vec::new(),
            }],
        };
        assert_eq!(
            c1.produce("orders", 4, &dummy).unwrap(),
            (UNKNOWN_TOPIC_OR_PARTITION, -1)
        );

        // 3. FindCoordinator v0 resolves coordinator (and rejects empty group_id).
        assert_eq!(c1.find_coordinator("").unwrap().0, INVALID_GROUP_ID);
        let (fc_err, coord) = c1.find_coordinator("cg-orders").unwrap();
        assert_eq!(fc_err, NONE);
        assert_eq!(coord.port, i32::from(addr.port()));

        // 4. Consumer 1 joins at generation 1 as leader; SyncGroup distributes [0,1,2,3].
        let j1 = c1
            .join_group(
                "cg-orders",
                10_000,
                "",
                "consumer",
                &[("range", b"sub-c1"), ("roundrobin", b"rr-c1")],
            )
            .unwrap();
        assert_eq!(j1.error_code, NONE);
        assert_eq!(j1.generation_id, 1);
        assert_eq!(j1.group_protocol, "range");
        assert_eq!(j1.leader_id, j1.member_id);
        assert_eq!(j1.members.len(), 1);

        let (sg1_err, sg1_assign) = c1
            .sync_group(
                "cg-orders",
                1,
                &j1.member_id,
                &[(&j1.member_id, b"parts:0,1,2,3")],
            )
            .unwrap();
        assert_eq!(sg1_err, NONE);
        assert_eq!(sg1_assign, b"parts:0,1,2,3");
        assert_eq!(c1.heartbeat("cg-orders", 1, &j1.member_id).unwrap(), NONE);

        // Incompatible protocol_type or disjoint protocol name is refused without advancing generation!
        let bad_proto = c2
            .join_group("cg-orders", 10_000, "", "connect", &[("range", b"x")])
            .unwrap();
        assert_eq!(bad_proto.error_code, INCONSISTENT_GROUP_PROTOCOL);
        let disjoint_proto = c2
            .join_group(
                "cg-orders",
                10_000,
                "",
                "consumer",
                &[("sticky-only", b"x")],
            )
            .unwrap();
        assert_eq!(disjoint_proto.error_code, INCONSISTENT_GROUP_PROTOCOL);
        assert_eq!(c1.heartbeat("cg-orders", 1, &j1.member_id).unwrap(), NONE);

        // 5. Consumer 2 joins with common "roundrobin" -> generation advances to 2!
        let j2 = c2
            .join_group(
                "cg-orders",
                10_000,
                "",
                "consumer",
                &[("roundrobin", b"rr-c2")],
            )
            .unwrap();
        assert_eq!(j2.error_code, NONE);
        assert_eq!(j2.generation_id, 2);
        assert_eq!(j2.group_protocol, "roundrobin");
        assert_eq!(j2.leader_id, j1.member_id);
        assert!(
            j2.members.is_empty(),
            "non-leader follower receives empty members list per Kafka JoinGroup spec"
        );

        // Stale generation 1 from c1 is immediately fenced across Heartbeat, SyncGroup, and OffsetCommit!
        assert_eq!(
            c1.heartbeat("cg-orders", 1, &j1.member_id).unwrap(),
            ILLEGAL_GENERATION
        );
        assert_eq!(
            c1.sync_group("cg-orders", 1, &j1.member_id, &[]).unwrap().0,
            ILLEGAL_GENERATION
        );
        assert_eq!(
            c1.offset_commit("cg-orders", 1, &j1.member_id, "orders", 0, 1, None)
                .unwrap(),
            ILLEGAL_GENERATION
        );
        // Standalone (-1, "") commit is also fenced while group has active members!
        assert_eq!(
            c1.offset_commit("cg-orders", -1, "", "orders", 0, 1, None)
                .unwrap(),
            ILLEGAL_GENERATION
        );

        // Leader c1 rejoins with its assigned member_id -> generation advances to 3, leader gets both members!
        let j1_rejoin = c1
            .join_group(
                "cg-orders",
                10_000,
                &j1.member_id,
                "consumer",
                &[("range", b"sub-c1"), ("roundrobin", b"rr-c1")],
            )
            .unwrap();
        assert_eq!(j1_rejoin.error_code, NONE);
        assert_eq!(j1_rejoin.generation_id, 3);
        assert_eq!(j1_rejoin.group_protocol, "roundrobin");
        assert_eq!(j1_rejoin.members.len(), 2);

        // Leader installs split assignments [0,1] and [2,3]; follower fetches [2,3].
        let (s_lead_err, s_lead_bytes) = c1
            .sync_group(
                "cg-orders",
                3,
                &j1.member_id,
                &[(&j1.member_id, b"parts:0,1"), (&j2.member_id, b"parts:2,3")],
            )
            .unwrap();
        assert_eq!(s_lead_err, NONE);
        assert_eq!(s_lead_bytes, b"parts:0,1");

        let (s_fol_err, s_fol_bytes) = c2.sync_group("cg-orders", 3, &j2.member_id, &[]).unwrap();
        assert_eq!(s_fol_err, NONE);
        assert_eq!(s_fol_bytes, b"parts:2,3");

        // Commit offsets on partitions 0 and 2 at generation 3; partition 1 stays uncommitted (-1).
        assert_eq!(
            c1.offset_commit("cg-orders", 3, &j1.member_id, "orders", 0, 1, Some("c1-p0"))
                .unwrap(),
            NONE
        );
        assert_eq!(
            c2.offset_commit("cg-orders", 3, &j2.member_id, "orders", 2, 1, None)
                .unwrap(),
            NONE
        );
        assert_eq!(
            c1.offset_fetch("cg-orders", "orders", 0).unwrap(),
            CommittedOffset {
                error_code: NONE,
                offset: 1,
                metadata: Some("c1-p0".into()),
            }
        );
        assert_eq!(
            c1.offset_fetch("cg-orders", "orders", 1).unwrap(),
            CommittedOffset {
                error_code: NONE,
                offset: -1,
                metadata: None,
            }
        );
        assert_eq!(
            c2.offset_fetch("cg-orders", "orders", 2).unwrap(),
            CommittedOffset {
                error_code: NONE,
                offset: 1,
                metadata: None,
            }
        );

        // 6. Leader c1 leaves -> generation advances to 4 and c2 becomes new leader on rejoin;
        //    c1's old member_id is now UNKNOWN_MEMBER_ID (25).
        assert_eq!(c1.leave_group("cg-orders", &j1.member_id).unwrap(), NONE);
        assert_eq!(
            c1.heartbeat("cg-orders", 4, &j1.member_id).unwrap(),
            UNKNOWN_MEMBER_ID
        );
        assert_eq!(
            c2.heartbeat("cg-orders", 3, &j2.member_id).unwrap(),
            ILLEGAL_GENERATION
        );
        let j2_leader = c2
            .join_group(
                "cg-orders",
                10_000,
                &j2.member_id,
                "consumer",
                &[("roundrobin", b"rr-c2")],
            )
            .unwrap();
        assert_eq!(j2_leader.error_code, NONE);
        assert_eq!(j2_leader.generation_id, 5);
        assert_eq!(j2_leader.leader_id, j2.member_id);
        assert_eq!(j2_leader.members.len(), 1);

        drop(c1);
        drop(c2);
        srv.shutdown();
    }

    #[cfg(feature = "durable")]
    #[test]
    fn durable_kafka_store_recovers_multipartition_logs_idempotence_offsets_and_generations() {
        let tmp_dir = std::env::temp_dir().join(format!(
            "astream-kafka-durable-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0)
        ));
        let _ = std::fs::remove_dir_all(&tmp_dir);

        let topics = vec![("telemetry.v1".to_owned(), 4)];
        let meta = ClusterMeta {
            broker: BrokerMeta {
                node_id: 1,
                host: "127.0.0.1".into(),
                port: 0,
            },
            topics: vec!["telemetry.v1".into()],
        };

        let assigned_member: String;
        {
            let durable =
                DurableKafkaStore::open(&tmp_dir, 4, &topics).expect("open DurableKafkaStore #1");
            assert_eq!(durable.shards(), 4);
            let mut srv =
                KafkaServer::bind_durable("127.0.0.1:0", meta.clone(), durable).expect("bind #1");
            let mut cli =
                KafkaClient::connect(srv.local_addr(), "durable-cli-1").expect("connect #1");

            // Produce idempotent batches across all 4 partitions (mapped onto 4 independent shards).
            for pid in 0..4i32 {
                let b0 = RecordBatchV2 {
                    base_offset: 0,
                    partition_leader_epoch: 0,
                    attributes: 0,
                    producer_id: 7_000 + i64::from(pid),
                    producer_epoch: 2,
                    base_sequence: 0,
                    records: vec![
                        KafkaRecord {
                            timestamp_ms: 100_000 + i64::from(pid),
                            key: Some(format!("k-{pid}-0").into_bytes()),
                            value: Some(format!("val-{pid}-0").into_bytes()),
                            headers: Vec::new(),
                        },
                        KafkaRecord {
                            timestamp_ms: 100_010 + i64::from(pid),
                            key: Some(format!("k-{pid}-1").into_bytes()),
                            value: Some(format!("val-{pid}-1").into_bytes()),
                            headers: Vec::new(),
                        },
                    ],
                };
                assert_eq!(cli.produce("telemetry.v1", pid, &b0).unwrap(), (NONE, 0));
            }

            // Join group (gen 1), SyncGroup, and commit offsets across all 4 partitions.
            let joined = cli
                .join_group(
                    "aterm-fleet.group",
                    15_000,
                    "",
                    "consumer",
                    &[("range", b"meta-v1")],
                )
                .unwrap();
            assert_eq!(joined.error_code, NONE);
            assert_eq!(joined.generation_id, 1);
            assigned_member = joined.member_id.clone();

            let (sg_err, _) = cli
                .sync_group(
                    "aterm-fleet.group",
                    1,
                    &assigned_member,
                    &[(&assigned_member, b"p:0,1,2,3")],
                )
                .unwrap();
            assert_eq!(sg_err, NONE);

            for pid in 0..4i32 {
                assert_eq!(
                    cli.offset_commit(
                        "aterm-fleet.group",
                        1,
                        &assigned_member,
                        "telemetry.v1",
                        pid,
                        2,
                        Some(&format!("chk-p{pid}")),
                    )
                    .unwrap(),
                    NONE
                );
            }

            drop(cli);
            srv.shutdown();
        }

        // Reopen DurableKafkaStore from disk over the same 4-shard directory and verify
        // full recovery of records, KIP-98 producer epochs/sequences, committed offsets, and
        // consumer-group generation monotonicity!
        {
            let durable2 =
                DurableKafkaStore::open(&tmp_dir, 4, &topics).expect("reopen DurableKafkaStore #2");
            let (resident_records, _resident_bytes, retained_records) = durable2.broker_residency();
            assert_eq!(resident_records, 4);
            assert!(retained_records > resident_records);
            for pid in 0..4i32 {
                assert_eq!(
                    durable2.high_watermark_partition("telemetry.v1", pid),
                    Some(2)
                );
            }
            let mut srv2 =
                KafkaServer::bind_durable("127.0.0.1:0", meta, durable2).expect("bind #2");
            let mut cli2 =
                KafkaClient::connect(srv2.local_addr(), "durable-cli-2").expect("connect #2");

            for pid in 0..4i32 {
                let (ferr, hw, batches) = cli2.fetch("telemetry.v1", pid, 0, 64 * 1024).unwrap();
                assert_eq!(ferr, NONE);
                assert_eq!(hw, 2);
                assert_eq!(batches.len(), 1);
                assert_eq!(batches[0].records.len(), 2);
                assert_eq!(
                    batches[0].records[1].value.as_deref(),
                    Some(format!("val-{pid}-1").as_bytes())
                );

                // KIP-98 idempotent retry of the pre-restart batch is deduplicated at offset 0!
                let retry_b0 = RecordBatchV2 {
                    base_offset: 0,
                    partition_leader_epoch: 0,
                    attributes: 0,
                    producer_id: 7_000 + i64::from(pid),
                    producer_epoch: 2,
                    base_sequence: 0,
                    records: vec![
                        KafkaRecord {
                            timestamp_ms: 100_000 + i64::from(pid),
                            key: Some(format!("k-{pid}-0").into_bytes()),
                            value: Some(format!("val-{pid}-0").into_bytes()),
                            headers: Vec::new(),
                        },
                        KafkaRecord {
                            timestamp_ms: 100_010 + i64::from(pid),
                            key: Some(format!("k-{pid}-1").into_bytes()),
                            value: Some(format!("val-{pid}-1").into_bytes()),
                            headers: Vec::new(),
                        },
                    ],
                };
                assert_eq!(
                    cli2.produce("telemetry.v1", pid, &retry_b0).unwrap(),
                    (NONE, 0)
                );

                // Stale producer_epoch (1 < 2) is fenced across the restart!
                let zombie = RecordBatchV2 {
                    base_offset: 0,
                    partition_leader_epoch: 0,
                    attributes: 0,
                    producer_id: 7_000 + i64::from(pid),
                    producer_epoch: 1,
                    base_sequence: 0,
                    records: vec![KafkaRecord {
                        timestamp_ms: 200_000,
                        key: None,
                        value: Some(b"zombie".to_vec()),
                        headers: Vec::new(),
                    }],
                };
                assert_eq!(
                    cli2.produce("telemetry.v1", pid, &zombie).unwrap(),
                    (INVALID_PRODUCER_EPOCH, -1)
                );

                // Next sequence (base_sequence = 2) appends cleanly at offset 2 across restart!
                let next_batch = RecordBatchV2 {
                    base_offset: 0,
                    partition_leader_epoch: 0,
                    attributes: 0,
                    producer_id: 7_000 + i64::from(pid),
                    producer_epoch: 2,
                    base_sequence: 2,
                    records: vec![KafkaRecord {
                        timestamp_ms: 200_000 + i64::from(pid),
                        key: None,
                        value: Some(format!("after-restart-{pid}").into_bytes()),
                        headers: Vec::new(),
                    }],
                };
                assert_eq!(
                    cli2.produce("telemetry.v1", pid, &next_batch).unwrap(),
                    (NONE, 2)
                );

                // Committed consumer-group offset + metadata survived restart!
                assert_eq!(
                    cli2.offset_fetch("aterm-fleet.group", "telemetry.v1", pid)
                        .unwrap(),
                    CommittedOffset {
                        error_code: NONE,
                        offset: 2,
                        metadata: Some(format!("chk-p{pid}")),
                    }
                );
            }

            // Recovered member + generation 1 still validates Heartbeat, SyncGroup, and OffsetCommit;
            // re-joining advances monotonically to generation 2!
            assert_eq!(
                cli2.heartbeat("aterm-fleet.group", 1, &assigned_member)
                    .unwrap(),
                NONE
            );
            let (_, recovered_assign) = cli2
                .sync_group("aterm-fleet.group", 1, &assigned_member, &[])
                .unwrap();
            assert_eq!(recovered_assign, b"p:0,1,2,3");

            let rejoin = cli2
                .join_group(
                    "aterm-fleet.group",
                    15_000,
                    &assigned_member,
                    "consumer",
                    &[("range", b"meta-v2")],
                )
                .unwrap();
            assert_eq!(rejoin.error_code, NONE);
            assert_eq!(rejoin.generation_id, 2);
            assert_eq!(
                cli2.offset_commit(
                    "aterm-fleet.group",
                    2,
                    &assigned_member,
                    "telemetry.v1",
                    0,
                    3,
                    Some("chk-p0-gen2"),
                )
                .unwrap(),
                NONE
            );
            assert_eq!(
                cli2.offset_fetch("aterm-fleet.group", "telemetry.v1", 0)
                    .unwrap(),
                CommittedOffset {
                    error_code: NONE,
                    offset: 3,
                    metadata: Some("chk-p0-gen2".into()),
                }
            );

            drop(cli2);
            srv2.shutdown();
        }

        let _ = std::fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn xxhash32_snappy_xerial_and_lz4_frame_codecs_roundtrip_and_reject_bombs() {
        // Official xxHash32 test vectors (empty, 1-byte, 3-byte, 9-byte, and 32-byte multi-stripe).
        assert_eq!(xxhash32(b"", 0), 0x02CC_5D05);
        assert_eq!(xxhash32(b"", 2_654_435_761), 0x36B7_8AE7);
        assert_eq!(xxhash32(b"a", 0), 0x550D_7456);
        assert_eq!(xxhash32(b"abc", 0), 0x32D1_53FF);
        assert_eq!(xxhash32(b"123456789", 0), 0x937B_AD67);
        assert_eq!(
            xxhash32(b"0123456789abcdef0123456789abcdef", 0),
            0xEB88_8D30
        );
        assert_eq!(
            xxhash32(b"0123456789abcdef0123456789abcdef", 2_654_435_761),
            0xD5CB_F572
        );

        assert!(compression_codec_in_spec_range(0));
        assert!(compression_codec_in_spec_range(2));
        assert!(compression_codec_in_spec_range(3));
        assert!(compression_codec_in_spec_range(4));
        assert!(!compression_codec_in_spec_range(5));

        let mut multi_block = Vec::with_capacity(96 * 1024);
        for i in 0..4_096u32 {
            multi_block.extend_from_slice(b"astream-kafka-aterm-telemetry-frame-");
            multi_block.extend_from_slice(&i.to_le_bytes());
        }
        let samples: &[&[u8]] = &[
            b"",
            b"short",
            b"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
            b"0123456789abcdef0123456789abcdef0123456789abcdef",
            &multi_block,
        ];

        for &sample in samples {
            let raw_snap = snappy_compress(sample);
            let dec_snap = snappy_decompress(&raw_snap, MAX_DECOMPRESSED_BATCH_BYTES).unwrap();
            assert_eq!(dec_snap, sample);

            let xer_snap = snappy_compress_xerial(sample);
            let dec_xer = snappy_decompress(&xer_snap, MAX_DECOMPRESSED_BATCH_BYTES).unwrap();
            assert_eq!(dec_xer, sample);

            let lz4 = lz4_compress(sample);
            let dec_lz4 = lz4_decompress(&lz4, MAX_DECOMPRESSED_BATCH_BYTES).unwrap();
            assert_eq!(dec_lz4, sample);
        }
        // Repetitive 160 KiB input compresses >3x under both Snappy and LZ4.
        assert!(snappy_compress(&multi_block).len() * 3 < multi_block.len());
        assert!(lz4_compress(&multi_block).len() * 3 < multi_block.len());

        // Zip-bomb / cap enforcement fails closed before allocating.
        let big_snap = snappy_compress(&multi_block);
        assert_eq!(
            snappy_decompress(&big_snap, 1024),
            Err(DecompressError::OutputTooLarge)
        );
        let big_lz4 = lz4_compress(&multi_block);
        assert_eq!(
            lz4_decompress(&big_lz4, 1024),
            Err(DecompressError::OutputTooLarge)
        );

        // Tampered LZ4 content xxHash32 checksum fails closed.
        let mut bad_lz4 = lz4_compress(b"hello kafka lz4 frame");
        let last = bad_lz4.len() - 1;
        bad_lz4[last] ^= 0x01;
        assert_eq!(
            lz4_decompress(&bad_lz4, 4096),
            Err(DecompressError::Corrupt)
        );
    }

    #[test]
    fn kip482_flexible_apiversions_metadata_findcoordinator_and_compressed_batches_over_tcp() {
        let meta = ClusterMeta {
            broker: BrokerMeta {
                node_id: 3,
                host: "127.0.0.1".into(),
                port: 0,
            },
            topics: vec!["logs".into()],
        };
        let store = KafkaStore::with_partitions(&[("logs".into(), 2)]);
        let mut srv = KafkaServer::bind("127.0.0.1:0", meta, store).expect("bind KafkaServer");
        let addr = srv.local_addr();
        let mut client = KafkaClient::connect(addr, "kip482-client").expect("connect");

        // 1. KIP-482 flexible ApiVersions v3 with non-empty Request Header v2 tagged fields!
        let mut raw_av3_hdr_tags = Vec::new();
        put_i16(&mut raw_av3_hdr_tags, API_VERSIONS);
        put_i16(&mut raw_av3_hdr_tags, 3);
        put_i32(&mut raw_av3_hdr_tags, 77);
        put_str(&mut raw_av3_hdr_tags, "tagged-cli");
        // Header TAG_BUFFER: 1 unknown tag (id=9, len=3, payload="xyz")
        put_uvarint(&mut raw_av3_hdr_tags, 1);
        put_uvarint(&mut raw_av3_hdr_tags, 9);
        put_uvarint(&mut raw_av3_hdr_tags, 3);
        raw_av3_hdr_tags.extend_from_slice(b"xyz");
        // Body: client_software_name, client_software_version, body TAG_BUFFER with 1 unknown tag
        put_compact_str(&mut raw_av3_hdr_tags, "rdkafka");
        put_compact_str(&mut raw_av3_hdr_tags, "2.4.0");
        put_uvarint(&mut raw_av3_hdr_tags, 1);
        put_uvarint(&mut raw_av3_hdr_tags, 4);
        put_uvarint(&mut raw_av3_hdr_tags, 2);
        raw_av3_hdr_tags.extend_from_slice(b"ok");

        let av3_resp = respond(&raw_av3_hdr_tags, &cluster()).expect("ApiVersions v3 response");
        assert_eq!(decode_i32_be(av3_resp[4..8].try_into().unwrap()), 77);
        assert_eq!(decode_i16_be(av3_resp[8..10].try_into().unwrap()), NONE);

        // 2. Live TCP KIP-482 Metadata v9 (both all-topics `None` and explicit `Some`) + FindCoordinator v3.
        let (bmeta_all, cid_all, topics_all) = client.metadata_v9(None).expect("Metadata v9 all");
        assert_eq!(bmeta_all.node_id, 3);
        assert_eq!(bmeta_all.port, i32::from(addr.port()));
        assert_eq!(cid_all.as_deref(), Some("astream"));
        assert_eq!(topics_all, vec![(NONE, "logs".to_owned(), vec![0, 1])]);

        let (_, _, topics_sub) = client
            .metadata_v9(Some(&["logs", "unknown"]))
            .expect("Metadata v9 subset");
        assert_eq!(topics_sub.len(), 2);
        assert_eq!(topics_sub[0], (NONE, "logs".to_owned(), vec![0, 1]));
        assert_eq!(
            topics_sub[1],
            (UNKNOWN_TOPIC_OR_PARTITION, "unknown".to_owned(), Vec::new())
        );

        let (fc_err, fc_coord) = client
            .find_coordinator_v3("cg-flex")
            .expect("FindCoordinator v3");
        assert_eq!(fc_err, NONE);
        assert_eq!(fc_coord.node_id, 3);
        assert_eq!(fc_coord.port, i32::from(addr.port()));
        assert_eq!(client.find_coordinator_v3("").unwrap().0, INVALID_GROUP_ID);

        // 3. Produce Snappy-compressed (`COMPRESSION_SNAPPY = 2`) and LZ4-compressed (`COMPRESSION_LZ4 = 3`)
        // RecordBatch v2 batches over live TCP and fetch them back intact!
        let snappy_batch = RecordBatchV2 {
            base_offset: 0,
            partition_leader_epoch: 0,
            attributes: COMPRESSION_SNAPPY,
            producer_id: 3001,
            producer_epoch: 0,
            base_sequence: 0,
            records: vec![
                KafkaRecord {
                    timestamp_ms: 90_000,
                    key: Some(b"snappy-k0".to_vec()),
                    value: Some(b"snappy-payload-repeated-snappy-payload-repeated".to_vec()),
                    headers: vec![KafkaHeader {
                        key: "codec".into(),
                        value: Some(b"snappy".to_vec()),
                    }],
                },
                KafkaRecord {
                    timestamp_ms: 90_010,
                    key: None,
                    value: Some(b"snappy-second-record".to_vec()),
                    headers: Vec::new(),
                },
            ],
        };
        let lz4_batch = RecordBatchV2 {
            base_offset: 0,
            partition_leader_epoch: 0,
            attributes: COMPRESSION_LZ4,
            producer_id: 3001,
            producer_epoch: 0,
            base_sequence: 2,
            records: vec![KafkaRecord {
                timestamp_ms: 90_020,
                key: Some(b"lz4-k2".to_vec()),
                value: Some(b"lz4-frame-payload-lz4-frame-payload-lz4-frame-payload".to_vec()),
                headers: vec![KafkaHeader {
                    key: "codec".into(),
                    value: Some(b"lz4".to_vec()),
                }],
            }],
        };

        assert_eq!(client.produce("logs", 0, &snappy_batch).unwrap(), (NONE, 0));
        assert_eq!(client.produce("logs", 0, &lz4_batch).unwrap(), (NONE, 2));

        // Also craft an explicit JVM Xerial-framed Snappy RecordBatch v2 and Produce it raw!
        let uncomp_single = RecordBatchV2 {
            base_offset: 0,
            partition_leader_epoch: 0,
            attributes: COMPRESSION_NONE,
            producer_id: 3001,
            producer_epoch: 0,
            base_sequence: 3,
            records: vec![KafkaRecord {
                timestamp_ms: 90_030,
                key: Some(b"xerial-k3".to_vec()),
                value: Some(b"jvm-kafka-clients-xerial-snappy-chunk".to_vec()),
                headers: Vec::new(),
            }],
        };
        let raw_uncomp = encode_record_batch_v2(&uncomp_single).unwrap();
        let xerial_records = snappy_compress_xerial(&raw_uncomp[RECORD_BATCH_HEADER_LEN..]);
        let mut xerial_crc_region = Vec::new();
        xerial_crc_region.extend_from_slice(&encode_i16_be(COMPRESSION_SNAPPY));
        xerial_crc_region.extend_from_slice(&raw_uncomp[23..RECORD_BATCH_HEADER_LEN]);
        xerial_crc_region.extend_from_slice(&xerial_records);
        let xerial_crc = crc32c(&xerial_crc_region);
        let xerial_batch_len = (49 + xerial_records.len()) as i32;
        let mut xerial_wire = Vec::new();
        xerial_wire.extend_from_slice(&0i64.to_be_bytes());
        xerial_wire.extend_from_slice(&encode_i32_be(xerial_batch_len));
        xerial_wire.extend_from_slice(&0i32.to_be_bytes());
        xerial_wire.push(RECORD_BATCH_MAGIC_V2);
        xerial_wire.extend_from_slice(&encode_i32_be(xerial_crc as i32));
        xerial_wire.extend_from_slice(&xerial_crc_region);
        assert_eq!(
            client.produce_raw("logs", 0, &xerial_wire).unwrap(),
            (NONE, 3)
        );

        let (ferr, hw, fetched) = client.fetch("logs", 0, 0, 128 * 1024).unwrap();
        assert_eq!(ferr, NONE);
        assert_eq!(hw, 4);
        assert_eq!(fetched.len(), 3);
        assert_eq!(fetched[0].base_offset, 0);
        assert_eq!(fetched[0].attributes, COMPRESSION_SNAPPY);
        assert_eq!(fetched[0].records, snappy_batch.records);
        assert_eq!(fetched[1].base_offset, 2);
        assert_eq!(fetched[1].attributes, COMPRESSION_LZ4);
        assert_eq!(fetched[1].records, lz4_batch.records);
        assert_eq!(fetched[2].base_offset, 3);
        assert_eq!(fetched[2].attributes, COMPRESSION_SNAPPY);
        assert_eq!(fetched[2].records, uncomp_single.records);

        // 4. Produce Gzip-compressed (`COMPRESSION_GZIP = 1`) RecordBatch v2 over live TCP and Fetch back!
        let gzip_batch = RecordBatchV2 {
            base_offset: 0,
            partition_leader_epoch: 0,
            attributes: COMPRESSION_GZIP,
            producer_id: 3001,
            producer_epoch: 0,
            base_sequence: 4,
            records: vec![
                KafkaRecord {
                    timestamp_ms: 90_040,
                    key: Some(b"gzip-k4".to_vec()),
                    value: Some(
                        b"rfc1952-gzip-deflate-payload-repeated-rfc1952-gzip-deflate-payload"
                            .to_vec(),
                    ),
                    headers: vec![KafkaHeader {
                        key: "codec".into(),
                        value: Some(b"gzip".to_vec()),
                    }],
                },
                KafkaRecord {
                    timestamp_ms: 90_050,
                    key: None,
                    value: Some(b"gzip-second-record".to_vec()),
                    headers: Vec::new(),
                },
            ],
        };
        assert_eq!(client.produce("logs", 0, &gzip_batch).unwrap(), (NONE, 4));
        let (gferr, ghw, gfetched) = client.fetch("logs", 0, 4, 128 * 1024).unwrap();
        assert_eq!(gferr, NONE);
        assert_eq!(ghw, 6);
        assert_eq!(gfetched.len(), 1);
        assert_eq!(gfetched[0].base_offset, 4);
        assert_eq!(gfetched[0].attributes, COMPRESSION_GZIP);
        assert_eq!(gfetched[0].records, gzip_batch.records);

        // 5. Produce Zstandard-compressed (`COMPRESSION_ZSTD = 4`) RecordBatch v2 over live TCP and Fetch back!
        let zstd_batch = RecordBatchV2 {
            base_offset: 0,
            partition_leader_epoch: 0,
            attributes: COMPRESSION_ZSTD,
            producer_id: 3001,
            producer_epoch: 0,
            base_sequence: 6,
            records: vec![
                KafkaRecord {
                    timestamp_ms: 90_060,
                    key: Some(b"zstd-k6".to_vec()),
                    value: Some(
                        b"rfc8878-zstd-fse-payload-repeated-rfc8878-zstd-fse-payload-repeated"
                            .to_vec(),
                    ),
                    headers: vec![KafkaHeader {
                        key: "codec".into(),
                        value: Some(b"zstd".to_vec()),
                    }],
                },
                KafkaRecord {
                    timestamp_ms: 90_070,
                    key: None,
                    value: Some(b"zstd-second-record".to_vec()),
                    headers: Vec::new(),
                },
            ],
        };
        assert_eq!(client.produce("logs", 0, &zstd_batch).unwrap(), (NONE, 6));
        let (zferr, zhw, zfetched) = client.fetch("logs", 0, 6, 128 * 1024).unwrap();
        assert_eq!(zferr, NONE);
        assert_eq!(zhw, 8);
        assert_eq!(zfetched.len(), 1);
        assert_eq!(zfetched[0].base_offset, 6);
        assert_eq!(zfetched[0].attributes, COMPRESSION_ZSTD);
        assert_eq!(zfetched[0].records, zstd_batch.records);

        drop(client);
        srv.shutdown();
    }

    #[test]
    fn gzip_rfc1952_deflate_stored_fixed_dynamic_multimember_and_fail_closed_checks() {
        // IEEE 802.3 CRC-32 test vectors.
        assert_eq!(crc32_ieee(b""), 0x0000_0000);
        assert_eq!(crc32_ieee(b"123456789"), 0xCBF4_3926);

        let mut repetitive = Vec::with_capacity(96 * 1024);
        for i in 0..3_000u32 {
            repetitive.extend_from_slice(b"astream-kafka-gzip-aterm-bus-frame-");
            repetitive.extend_from_slice(&i.to_le_bytes());
        }
        for sample in [
            &b""[..],
            &b"x"[..],
            &b"abc"[..],
            &b"0123456789abcdef0123456789abcdef0123456789abcdef"[..],
            &repetitive[..],
        ] {
            let gz = gzip_compress(sample);
            assert_eq!(&gz[..2], &GZIP_MAGIC);
            let dec = gzip_decompress(&gz, MAX_DECOMPRESSED_BATCH_BYTES).unwrap();
            assert_eq!(dec, sample);
        }
        assert!(gzip_compress(&repetitive).len() * 3 < repetitive.len());

        // Interop against external zlib level-9 BTYPE=2 (Dynamic Huffman) Gzip stream.
        let zlib_dynamic: [u8; 149] = [
            31, 139, 8, 0, 0, 0, 0, 0, 2, 255, 165, 212, 59, 14, 194, 64, 16, 4, 209, 156, 99, 76,
            108, 16, 189, 252, 247, 54, 22, 76, 96, 89, 236, 26, 123, 76, 98, 113, 119, 124, 2, 8,
            42, 110, 85, 246, 212, 139, 69, 29, 186, 187, 101, 107, 195, 199, 231, 206, 223, 94,
            98, 178, 198, 38, 127, 89, 222, 55, 214, 119, 229, 177, 174, 67, 91, 124, 91, 231, 88,
            151, 218, 91, 142, 113, 246, 207, 102, 249, 25, 139, 196, 137, 196, 7, 18, 31, 73, 124,
            34, 241, 153, 196, 23, 18, 95, 73, 124, 67, 72, 24, 49, 100, 76, 8, 153, 144, 50, 33,
            102, 66, 206, 132, 160, 9, 73, 19, 162, 38, 100, 45, 33, 107, 137, 253, 25, 178, 150,
            254, 88, 251, 2, 211, 10, 193, 232, 198, 5, 0, 0,
        ];
        assert_eq!((zlib_dynamic[10] >> 1) & 3, 2);
        let mut expected_json = Vec::new();
        for i in 0..24 {
            expected_json.extend_from_slice(
                format!("{{\"topic\":\"aterm.events\",\"seq\":{i},\"kind\":\"pane-out\",\"ok\":true}}\n")
                    .as_bytes(),
            );
        }
        assert_eq!(
            gzip_decompress(&zlib_dynamic, MAX_DECOMPRESSED_BATCH_BYTES).unwrap(),
            expected_json
        );

        // Stored BTYPE=00 block with optional FEXTRA + FNAME + FCOMMENT + FHCRC header fields,
        // concatenated with a second Gzip member (multi-member RFC 1952 §2.2).
        let stored_payload = b"stored-deflate-block";
        let mut member1 = vec![
            0x1f,
            0x8b,
            0x08,
            0x02 | 0x04 | 0x08 | 0x10, // FHCRC | FEXTRA | FNAME | FCOMMENT
            1,
            2,
            3,
            4,
            0,
            3,
        ];
        member1.extend_from_slice(&3u16.to_le_bytes()); // XLEN = 3
        member1.extend_from_slice(b"ext");
        member1.extend_from_slice(b"batch.gz\0");
        member1.extend_from_slice(b"kafka-comment\0");
        let hcrc16 = (crc32_ieee(&member1) & 0xffff) as u16;
        member1.extend_from_slice(&hcrc16.to_le_bytes());
        member1.push(0x01); // BFINAL=1, BTYPE=00 (Stored)
        let slen = stored_payload.len() as u16;
        member1.extend_from_slice(&slen.to_le_bytes());
        member1.extend_from_slice(&(!slen).to_le_bytes());
        member1.extend_from_slice(stored_payload);
        member1.extend_from_slice(&crc32_ieee(stored_payload).to_le_bytes());
        member1.extend_from_slice(&(stored_payload.len() as u32).to_le_bytes());

        let member2 = gzip_compress(b"+second-member");
        let mut multi_member = member1.clone();
        multi_member.extend_from_slice(&member2);
        assert_eq!(
            gzip_decompress(&multi_member, 4096).unwrap(),
            b"stored-deflate-block+second-member"
        );

        // Zip-bomb / cap enforcement and fail-closed CRC32, ISIZE, FHCRC, and reserved-FLG checks.
        let big_gz = gzip_compress(&repetitive);
        assert_eq!(
            gzip_decompress(&big_gz, 512),
            Err(DecompressError::OutputTooLarge)
        );
        let mut bad_crc = gzip_compress(b"hello kafka gzip");
        let crc_idx = bad_crc.len() - 8;
        bad_crc[crc_idx] ^= 0x01;
        assert_eq!(
            gzip_decompress(&bad_crc, 4096),
            Err(DecompressError::Corrupt)
        );
        let mut bad_isize = gzip_compress(b"hello kafka gzip");
        let isz_idx = bad_isize.len() - 4;
        bad_isize[isz_idx] ^= 0x01;
        assert_eq!(
            gzip_decompress(&bad_isize, 4096),
            Err(DecompressError::Corrupt)
        );
        let mut bad_flg = gzip_compress(b"hello");
        bad_flg[3] |= 0x20; // reserved bit 5 set
        assert_eq!(
            gzip_decompress(&bad_flg, 4096),
            Err(DecompressError::Corrupt)
        );
    }

    #[test]
    fn zstd_rfc8878_1stream_4stream_treeless_multiblock_and_fail_closed_checks() {
        // Standard XXH64 empty-slice test vector (seed = 0).
        assert_eq!(xxhash64(b"", 0), 0xEF46_DB37_51D8_E999);
        assert_ne!(xxhash64(b"astream-zstd", 0), xxhash64(b"astream-zstd", 1));

        // 1. Roundtrip `zstd_compress` -> `zstd_decompress` across empty, single-byte, RLE-uniform,
        // incompressible raw, repetitive structured, and >128 KiB multi-block payloads.
        let uniform_rle = vec![0xA5u8; 8_192];
        let mut pseudo_random = Vec::with_capacity(1_024);
        let mut lcg = 0x1234_5678_9ABC_DEF0u64;
        for _ in 0..1_024 {
            lcg = lcg
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            pseudo_random.push((lcg >> 56) as u8);
        }
        let mut multi_block = Vec::with_capacity(220 * 1024);
        for i in 0..5_500u32 {
            multi_block.extend_from_slice(b"astream-kafka-zstd-multiblock-aterm-bus-");
            multi_block.extend_from_slice(&i.to_le_bytes());
        }
        for sample in [
            &b""[..],
            &b"z"[..],
            &b"short-raw"[..],
            &uniform_rle[..],
            &pseudo_random[..],
            &multi_block[..],
        ] {
            let enc = zstd_compress(sample);
            assert_eq!(&enc[..4], &ZSTD_MAGIC_LE);
            let dec = zstd_decompress(&enc, MAX_DECOMPRESSED_BATCH_BYTES).unwrap();
            assert_eq!(dec, sample);
        }
        assert!(zstd_compress(&uniform_rle).len() < 32);
        assert!(zstd_compress(&multi_block).len() * 3 < multi_block.len());

        // 2. Interop against external `zstd` v1.5.7 `-19 --check` (1-stream Huffman + FSE sequences).
        let zstd_v157_1stream: [u8; 128] = [
            40, 181, 47, 253, 4, 104, 157, 3, 0, 82, 69, 19, 24, 112, 171, 14, 230, 8, 138, 244,
            253, 103, 86, 105, 250, 127, 206, 178, 44, 27, 113, 152, 7, 160, 17, 7, 7, 75, 109, 82,
            17, 62, 215, 216, 82, 187, 17, 62, 215, 216, 82, 11, 60, 204, 40, 45, 111, 212, 163,
            55, 83, 3, 166, 19, 185, 60, 65, 11, 227, 40, 201, 39, 188, 28, 125, 105, 202, 13, 11,
            135, 194, 61, 47, 63, 20, 72, 237, 59, 1, 24, 168, 16, 248, 236, 255, 29, 208, 59, 215,
            16, 254, 255, 21, 225, 239, 7, 18, 81, 72, 36, 145, 170, 64, 206, 76, 34, 36, 73, 70,
            109, 53, 0, 100, 10, 160, 88, 215, 9,
        ];
        let mut expected_json = Vec::new();
        for i in 0..24 {
            expected_json.extend_from_slice(
                format!("{{\"topic\":\"aterm.events\",\"seq\":{i},\"kind\":\"pane-out\",\"ok\":true}}\n")
                    .as_bytes(),
            );
        }
        assert_eq!(
            zstd_decompress(&zstd_v157_1stream, MAX_DECOMPRESSED_BATCH_BYTES).unwrap(),
            expected_json
        );

        // 3. Interop against external `zstd` v1.5.7 `-9 --check` (4-stream Huffman + FSE weights).
        let zstd_v157_4stream: [u8; 353] = [
            40, 181, 47, 253, 4, 96, 165, 10, 0, 198, 90, 66, 22, 128, 39, 233, 31, 56, 236, 0,
            204, 146, 4, 12, 172, 232, 41, 138, 162, 8, 187, 12, 108, 51, 122, 67, 0, 56, 0, 55, 0,
            78, 202, 188, 217, 78, 89, 252, 23, 187, 177, 10, 185, 212, 114, 79, 93, 210, 198, 86,
            202, 60, 150, 85, 114, 201, 45, 102, 178, 47, 133, 8, 15, 0, 40, 28, 20, 195, 204, 12,
            193, 96, 16, 40, 40, 133, 193, 139, 2, 130, 225, 7, 162, 3, 8, 138, 2, 97, 134, 40, 94,
            12, 16, 102, 102, 8, 15, 8, 100, 138, 117, 213, 149, 52, 29, 99, 162, 83, 66, 227, 252,
            170, 67, 173, 118, 76, 230, 145, 61, 82, 109, 36, 226, 30, 190, 82, 180, 202, 87, 132,
            60, 232, 220, 68, 156, 60, 147, 141, 43, 35, 149, 184, 71, 176, 149, 251, 112, 16, 159,
            195, 49, 171, 105, 12, 67, 52, 72, 93, 156, 196, 179, 181, 69, 217, 68, 244, 101, 199,
            170, 152, 6, 193, 79, 222, 162, 42, 110, 196, 100, 43, 130, 214, 103, 111, 99, 204, 70,
            217, 224, 85, 255, 48, 39, 185, 65, 216, 250, 107, 132, 85, 206, 5, 117, 42, 45, 19,
            219, 116, 51, 0, 133, 131, 98, 32, 77, 196, 51, 130, 53, 204, 201, 209, 117, 22, 93,
            205, 142, 46, 67, 124, 44, 223, 120, 222, 160, 95, 74, 47, 212, 186, 120, 219, 158,
            133, 247, 196, 208, 139, 58, 101, 85, 217, 255, 100, 233, 221, 229, 215, 31, 246, 138,
            255, 79, 186, 3, 179, 2, 116, 168, 17, 100, 37, 191, 255, 103, 224, 55, 3, 17, 136, 5,
            90, 138, 223, 15, 169, 226, 129, 57, 40, 48, 71, 25, 125, 250, 226, 69, 51, 168, 104,
            6, 21, 154, 81, 103, 95, 171, 124, 41, 140, 180, 235, 244, 197, 139, 102, 212, 217,
            151, 85, 190, 20, 70, 237, 58, 125, 241, 66, 51, 234, 236, 107, 149, 47, 165, 173, 104,
            165, 42, 218, 70, 133, 242,
        ];
        let mut expected_4stream = Vec::new();
        for i in 0..40usize {
            expected_4stream.extend_from_slice(
                format!(
                    "id={:04x}-node={:02}-topic=/f/prod/term/s-{:04x}/out\n",
                    (i * 7919) % 9973,
                    (i * 31) % 97,
                    (i * 104_729) % 65_521
                )
                .as_bytes(),
            );
        }
        assert_eq!(
            zstd_decompress(&zstd_v157_4stream, MAX_DECOMPRESSED_BATCH_BYTES).unwrap(),
            expected_4stream
        );

        // 4. Interop against external `zstd` v1.5.7 `-5 --check` multi-block (>128 KiB) frame
        // exercising `Treeless` repeat Huffman (`lit_type = 3`) + `Repeat_Mode` FSE across blocks!
        let zstd_v157_treeless_multiblock: [u8; 614] = [
            40, 181, 47, 253, 4, 88, 164, 14, 0, 54, 35, 83, 23, 144, 167, 32, 15, 136, 21, 109,
            117, 221, 237, 46, 51, 31, 83, 201, 202, 18, 70, 182, 185, 59, 62, 159, 87, 0, 72, 0,
            73, 0, 74, 53, 236, 181, 199, 75, 219, 99, 161, 108, 55, 150, 140, 221, 84, 125, 248,
            8, 9, 213, 68, 38, 132, 133, 116, 30, 243, 189, 172, 161, 56, 33, 40, 114, 185, 180,
            74, 153, 190, 215, 81, 11, 230, 85, 169, 186, 20, 50, 16, 1, 0, 132, 132, 67, 97, 102,
            38, 224, 160, 48, 96, 80, 16, 10, 228, 96, 80, 80, 232, 130, 129, 5, 10, 14, 8, 1, 51,
            134, 66, 14, 4, 1, 51, 51, 6, 34, 16, 167, 95, 249, 14, 181, 190, 87, 108, 213, 53,
            166, 106, 188, 230, 236, 220, 163, 138, 107, 131, 142, 69, 103, 209, 253, 68, 203, 137,
            57, 22, 226, 113, 137, 196, 157, 82, 252, 91, 193, 18, 83, 74, 100, 98, 105, 136, 182,
            16, 67, 212, 115, 12, 162, 109, 26, 9, 193, 71, 164, 60, 106, 229, 148, 66, 237, 116,
            58, 71, 148, 105, 201, 118, 131, 76, 230, 144, 24, 71, 170, 93, 4, 25, 132, 240, 172,
            246, 62, 138, 172, 145, 49, 142, 61, 7, 151, 25, 105, 67, 144, 108, 80, 39, 33, 41,
            148, 151, 76, 240, 103, 189, 71, 138, 24, 252, 95, 221, 195, 153, 218, 130, 122, 84,
            95, 119, 211, 56, 252, 16, 205, 17, 43, 146, 78, 158, 144, 137, 168, 75, 78, 253, 74,
            99, 175, 81, 51, 197, 178, 135, 94, 230, 246, 230, 95, 162, 227, 199, 60, 147, 255, 20,
            90, 238, 53, 104, 238, 158, 245, 43, 137, 85, 181, 26, 66, 216, 182, 99, 169, 191, 43,
            170, 220, 162, 123, 75, 63, 36, 172, 219, 117, 235, 194, 166, 233, 147, 130, 7, 19,
            139, 48, 42, 73, 74, 89, 50, 217, 225, 140, 180, 247, 119, 197, 234, 205, 111, 20, 128,
            178, 168, 33, 36, 149, 241, 253, 63, 3, 224, 53, 54, 14, 18, 208, 21, 48, 41, 142, 8,
            63, 155, 239, 255, 255, 25, 50, 245, 203, 42, 152, 6, 209, 224, 75, 194, 160, 96, 47,
            32, 2, 184, 61, 108, 28, 86, 220, 224, 137, 46, 96, 121, 166, 6, 202, 75, 77, 68, 225,
            64, 32, 131, 238, 141, 237, 55, 173, 183, 249, 24, 2, 24, 77, 70, 220, 224, 160, 245,
            182, 60, 32, 14, 100, 13, 241, 10, 229, 5, 13, 74, 98, 120, 69, 217, 159, 218, 137,
            146, 8, 94, 81, 246, 167, 118, 162, 36, 130, 87, 148, 253, 169, 157, 40, 137, 224, 21,
            101, 127, 106, 39, 74, 34, 120, 69, 217, 159, 218, 113, 171, 200, 223, 85, 21, 4, 0,
            131, 5, 12, 0, 8, 9, 135, 2, 65, 229, 206, 66, 130, 111, 153, 188, 40, 142, 24, 175,
            12, 237, 98, 203, 32, 199, 67, 148, 183, 37, 62, 26, 102, 53, 184, 131, 78, 156, 104,
            76, 139, 78, 6, 147, 116, 112, 96, 150, 137, 201, 130, 33, 32, 209, 198, 63, 19, 125,
            87, 81, 0, 128, 73, 4, 229, 62, 1, 96, 12, 207, 47, 73, 28, 142, 77, 64, 192, 36, 130,
            250, 152, 4, 0, 147, 8, 250, 86, 18, 0, 76, 18, 68, 221, 36, 39, 10, 150, 160, 209, 35,
            0, 192, 132, 32, 40, 28, 125, 4, 193, 8, 82, 111, 198, 17, 30, 78, 68, 18, 198, 20,
            206, 35, 65, 20, 54, 140, 73, 180, 11, 87, 251, 10, 199, 213,
        ];
        let mut unit1 = Vec::new();
        for i in 0..60usize {
            unit1.extend_from_slice(
                format!(
                    "id={:04x}-node={:02}-topic=/f/prod/term/s-{:04x}/out\n",
                    (i * 7919) % 9973,
                    (i * 31) % 97,
                    (i * 104_729) % 65_521
                )
                .as_bytes(),
            );
        }
        let mut expected_treeless = Vec::with_capacity(153 * 1024);
        for _ in 0..55 {
            expected_treeless.extend_from_slice(&unit1);
        }
        for i in 0..12usize {
            expected_treeless.extend_from_slice(
                format!(
                    "id={:04x}-node={:02}-topic=/f/prod/term/s-{:04x}/out\n",
                    (i * 6151) % 9973,
                    (i * 43) % 97,
                    (i * 99_991) % 65_521
                )
                .as_bytes(),
            );
        }
        assert_eq!(
            zstd_decompress(&zstd_v157_treeless_multiblock, MAX_DECOMPRESSED_BATCH_BYTES).unwrap(),
            expected_treeless
        );

        // 5. Concatenated Zstd frames + skippable metadata frame (`0x184D2A50`).
        let mut concat = vec![0x50, 0x2A, 0x4D, 0x18, 4, 0, 0, 0, b'm', b'e', b't', b'a'];
        concat.extend_from_slice(&zstd_compress(b"part-one:"));
        concat.extend_from_slice(&zstd_compress(b"part-two"));
        assert_eq!(
            zstd_decompress(&concat, 4096).unwrap(),
            b"part-one:part-two"
        );

        // 6. Fail-closed checks: skippable-only rejected, zip-bomb budget cap, corrupt checksum,
        // reserved FHD bit, and non-zero Dictionary_ID rejected.
        let skip_only = [0x50, 0x2A, 0x4D, 0x18, 2, 0, 0, 0, 0xAA, 0xBB];
        assert_eq!(
            zstd_decompress(&skip_only, 4096),
            Err(DecompressError::Corrupt)
        );
        let big_enc = zstd_compress(&multi_block);
        assert_eq!(
            zstd_decompress(&big_enc, 1024),
            Err(DecompressError::OutputTooLarge)
        );
        let mut bad_csum = zstd_compress(b"hello zstd kafka");
        let last_idx = bad_csum.len() - 1;
        bad_csum[last_idx] ^= 0x01;
        assert_eq!(
            zstd_decompress(&bad_csum, 4096),
            Err(DecompressError::Corrupt)
        );
        let mut bad_fhd = zstd_compress(b"hello zstd kafka");
        bad_fhd[4] |= 0x08; // Reserved bit 3 set
        assert_eq!(
            zstd_decompress(&bad_fhd, 4096),
            Err(DecompressError::Corrupt)
        );
        // Frame with Dictionary_ID_Flag = 1 and non-zero dict_id = 7 -> fail closed!
        let ext_dict_frame = [0x28, 0xB5, 0x2F, 0xFD, 0x21, 0x07, 0x00, 0x01, 0x00, 0x00];
        assert_eq!(
            zstd_decompress(&ext_dict_frame, 4096),
            Err(DecompressError::Corrupt)
        );
    }

    #[test]
    fn live_tcp_kafka_server_enforces_sasl_plain_and_scram_sha256_before_data_plane() {
        let cluster = ClusterMeta {
            broker: BrokerMeta {
                node_id: 0,
                host: "127.0.0.1".to_owned(),
                port: 0,
            },
            topics: vec!["secure-events".to_owned()],
        };
        let store = KafkaStore::new(&["secure-events".to_owned()]);

        let mut sasl_cfg = SaslConfig::new([0x77; 32]).with_session_lifetime_ms(7_200_000);
        sasl_cfg.add_user("operator", b"s3cr3t-passphrase!", [0x24; 16], 4096);

        let mut srv = KafkaServer::bind_sasl("127.0.0.1:0", cluster, store, sasl_cfg)
            .expect("bind SASL server");
        let addr = srv.local_addr();

        // 1. Unauthenticated connection can call ApiVersions, but Produce/Metadata is refused!
        let mut unauth = KafkaClient::connect(addr, "unauth-cli").expect("connect unauth");
        let (av_err, entries) = unauth.api_versions(3).expect("ApiVersions v3 pre-auth");
        assert_eq!(av_err, NONE);
        assert!(entries.iter().any(|e| e.0 == SASL_HANDSHAKE));
        assert!(entries.iter().any(|e| e.0 == SASL_AUTHENTICATE));
        assert!(
            unauth.metadata_v9(None).is_err(),
            "Metadata before SASL auth must drop connection"
        );

        // 2. Wrong password returns SASL_AUTHENTICATION_FAILED and closes socket!
        let mut bad_cli = KafkaClient::connect(addr, "bad-cli").expect("connect bad");
        let bad_out = bad_cli
            .sasl_authenticate_plain(2, "operator", b"wrong")
            .expect("bad plain resp");
        assert_eq!(bad_out.error_code, SASL_AUTHENTICATION_FAILED);
        assert!(
            bad_cli.api_versions(3).is_err(),
            "socket closed after terminal PHASE_FAILED"
        );

        // 3. SASL PLAIN v2 flexible authenticates and Produce + Fetch succeed!
        let mut plain_cli = KafkaClient::connect(addr, "plain-cli").expect("connect plain");
        let plain_out = plain_cli
            .sasl_authenticate_plain(2, "operator", b"s3cr3t-passphrase!")
            .expect("plain auth");
        assert_eq!(plain_out.error_code, NONE);
        assert_eq!(plain_out.session_lifetime_ms, 7_200_000);
        let batch = RecordBatchV2 {
            base_offset: 0,
            partition_leader_epoch: 0,
            attributes: 0,
            producer_id: -1,
            producer_epoch: -1,
            base_sequence: -1,
            records: vec![KafkaRecord {
                timestamp_ms: 91_000,
                key: Some(b"k1".to_vec()),
                value: Some(b"from-plain".to_vec()),
                headers: Vec::new(),
            }],
        };
        let (p_err, base_off) = plain_cli
            .produce("secure-events", 0, &batch)
            .expect("produce after PLAIN");
        assert_eq!(p_err, NONE);
        assert_eq!(base_off, 0);

        // 4. Mutual SCRAM-SHA-256 (v2 flexible) authenticates, verifies ServerSignature, and fetches!
        let mut scram_cli = KafkaClient::connect(addr, "scram-cli").expect("connect scram");
        scram_cli
            .sasl_authenticate_scram_sha256(
                2,
                "operator",
                b"s3cr3t-passphrase!",
                "clientNonceAbcXYZ987",
            )
            .expect("SCRAM-SHA-256 mutual auth");
        let (f_err, hw, batches) = scram_cli
            .fetch("secure-events", 0, 0, 65_536)
            .expect("fetch after SCRAM-SHA-256");
        assert_eq!(f_err, NONE);
        assert_eq!(hw, 1);
        assert_eq!(batches.len(), 1);
        assert_eq!(
            batches[0].records[0].value.as_deref(),
            Some(&b"from-plain"[..])
        );

        drop(plain_cli);
        drop(scram_cli);
        srv.shutdown();
    }

    #[cfg(all(feature = "identity", feature = "durable"))]
    #[test]
    fn kafka_encrypted_listeners_enforce_sealed_handshake_identity_and_sasl_e2e() {
        use crate::durable::DurableKafkaStore;
        use crate::sasl::SaslConfig;
        use crate::server::KafkaEncryptedListener;
        use std::sync::Arc;

        let cluster = ClusterMeta {
            broker: BrokerMeta {
                node_id: 0,
                host: "127.0.0.1".to_owned(),
                port: 0,
            },
            topics: vec!["tls-events".to_owned()],
        };

        // 1. Pre-shared-key `Sealed` listener rejects plaintext & wrong-PSK clients, serves right PSK.
        let psk = [0x42u8; 32];
        let mut sealed_srv = KafkaServer::bind_encrypted(
            "127.0.0.1:0",
            cluster.clone(),
            KafkaStore::new(&["tls-events".to_owned()]),
            KafkaEncryptedListener::Sealed { key: psk },
        )
        .expect("bind Sealed listener");
        let sealed_addr = sealed_srv.local_addr();

        if let Ok(mut plain_cli) = KafkaClient::connect(sealed_addr, "plain-probe") {
            assert!(
                plain_cli.api_versions(3).is_err(),
                "plaintext client must fail against Sealed listener"
            );
        }
        if let Ok(mut wrong_key_cli) =
            KafkaClient::connect_sealed(sealed_addr, "wrong-psk", [0x99u8; 32])
        {
            assert!(
                wrong_key_cli.api_versions(3).is_err(),
                "wrong PSK must fail AEAD tag authentication"
            );
        }

        let mut sealed_cli =
            KafkaClient::connect_sealed(sealed_addr, "sealed-ok", psk).expect("connect_sealed");
        let (av_err, _) = sealed_cli.api_versions(3).expect("sealed ApiVersions");
        assert_eq!(av_err, NONE);
        sealed_srv.shutdown();

        // 2. Forward-secret X25519 + PSK `Handshake` listener rejects wrong PSK, serves right PSK.
        let hs_psk = [0x77u8; 32];
        let mut hs_srv = KafkaServer::bind_encrypted(
            "127.0.0.1:0",
            cluster.clone(),
            KafkaStore::new(&["tls-events".to_owned()]),
            KafkaEncryptedListener::Handshake { psk: hs_psk },
        )
        .expect("bind Handshake listener");
        let hs_addr = hs_srv.local_addr();
        if let Ok(mut wrong_hs) = KafkaClient::connect_handshake(hs_addr, "wrong-hs", [0x88u8; 32])
        {
            assert!(
                wrong_hs.api_versions(3).is_err(),
                "wrong forward-secret PSK must fail HKDF-derived AEAD tag"
            );
        }
        let mut hs_cli =
            KafkaClient::connect_handshake(hs_addr, "hs-ok", hs_psk).expect("connect_handshake");
        let (hs_av_err, _) = hs_cli.api_versions(3).expect("handshake ApiVersions");
        assert_eq!(hs_av_err, NONE);
        hs_srv.shutdown();

        // 3. Mutual Ed25519 `Identity` signed-DH + durable ShardedBroker + SCRAM-SHA-256 SASL!
        let host_id = Arc::new(astream_aead::IdentityKeypair::from_seed([0x11u8; 32]));
        let host_pub = host_id.public();
        let allowed_client_id = astream_aead::IdentityKeypair::from_seed([0x22u8; 32]);
        let rogue_client_id = astream_aead::IdentityKeypair::from_seed([0x33u8; 32]);
        let wrong_host_pub = astream_aead::IdentityKeypair::from_seed([0x44u8; 32]).public();

        let dir = std::env::temp_dir().join(format!(
            "astream-kafka-tls-{}-{}",
            std::process::id(),
            991122u64
        ));
        let _ = std::fs::remove_dir_all(&dir);
        let durable_store = DurableKafkaStore::open(&dir, 2, &[("tls-events".to_owned(), 2)])
            .expect("open DurableKafkaStore");

        let mut sasl_cfg = SaslConfig::new([0x55; 32]);
        sasl_cfg.add_user("alice", b"mutual-tls-scram!", [0x66; 16], 4096);

        let mut id_srv = KafkaServer::bind_durable_encrypted_sasl(
            "127.0.0.1:0",
            cluster,
            durable_store,
            KafkaEncryptedListener::Identity {
                host: Arc::clone(&host_id),
                authorized_clients: vec![allowed_client_id.public()],
            },
            sasl_cfg,
        )
        .expect("bind durable Identity+SASL server");
        let id_addr = id_srv.local_addr();

        // Client pinning wrong server host key fails mutual handshake immediately!
        assert!(
            KafkaClient::connect_identity(
                id_addr,
                "wrong-pin",
                &allowed_client_id,
                &wrong_host_pub
            )
            .is_err(),
            "pinned host key mismatch must fail closed"
        );

        // Unauthorized client Ed25519 key is rejected by the server allow-list!
        if let Ok(mut rogue_cli) =
            KafkaClient::connect_identity(id_addr, "rogue-id", &rogue_client_id, &host_pub)
        {
            assert!(
                rogue_cli.api_versions(3).is_err(),
                "unauthorized client Ed25519 key must be closed by server"
            );
        }

        // Authorized Ed25519 client still cannot call data-plane Produce before SASL completes!
        let mut pre_sasl =
            KafkaClient::connect_identity(id_addr, "pre-sasl", &allowed_client_id, &host_pub)
                .expect("connect_identity");
        assert!(
            pre_sasl.metadata_v9(None).is_err(),
            "ListenerSecurityPolicy(require_encrypted=true, require_sasl=true) must block pre-SASL data APIs"
        );
        drop(pre_sasl);

        // Authorized Ed25519 + mutual SCRAM-SHA-256 produces and fetches durably!
        let mut authed =
            KafkaClient::connect_identity(id_addr, "authed-id", &allowed_client_id, &host_pub)
                .expect("connect_identity authed");
        authed
            .sasl_authenticate_scram_sha256(2, "alice", b"mutual-tls-scram!", "tlsNonce012345")
            .expect("SCRAM over mutual Ed25519");

        let batch = RecordBatchV2 {
            base_offset: 0,
            partition_leader_epoch: 0,
            attributes: 0,
            producer_id: 77,
            producer_epoch: 0,
            base_sequence: 0,
            records: vec![KafkaRecord {
                timestamp_ms: 123_456,
                key: Some(b"k-tls".to_vec()),
                value: Some(b"sealed-durable-payload".to_vec()),
                headers: Vec::new(),
            }],
        };
        let (p_err, base_off) = authed
            .produce("tls-events", 1, &batch)
            .expect("produce over Identity+SCRAM");
        assert_eq!(p_err, NONE);
        assert_eq!(base_off, 0);

        let (f_err, hw, batches) = authed
            .fetch("tls-events", 1, 0, 65_536)
            .expect("fetch over Identity+SCRAM");
        assert_eq!(f_err, NONE);
        assert_eq!(hw, 1);
        assert_eq!(
            batches[0].records[0].value.as_deref(),
            Some(&b"sealed-durable-payload"[..])
        );

        drop(authed);
        id_srv.shutdown();
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[cfg(all(feature = "durable", feature = "identity"))]
    #[test]
    fn kafka_certified_ssh_agent_and_roaming_udp_listeners_e2e() {
        use crate::durable::DurableKafkaStore;
        use crate::sasl::SaslConfig;
        use crate::server::KafkaEncryptedListener;

        let cluster = ClusterMeta {
            broker: BrokerMeta {
                node_id: 0,
                host: "127.0.0.1".to_owned(),
                port: 0,
            },
            topics: vec!["cert-roam-events".to_owned()],
        };

        let pid = std::process::id();
        let now_ms = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_millis() as u64;
        let t0 = now_ms.saturating_sub(5_000);
        let t1 = t0.saturating_add(600_000);

        // 1. Mutual CA-certified SIGMA + overlapping HostCertRotator + external SSH_AUTH_SOCK!
        #[cfg(unix)]
        let sock_dir =
            std::path::PathBuf::from(format!("/tmp/kfk_ag_{}_{}", pid, now_ms % 1_000_000));
        #[cfg(unix)]
        std::fs::create_dir_all(&sock_dir).unwrap();
        #[cfg(unix)]
        let sock_path = sock_dir.join("a.s");

        let ca_kp = astream_aead::IdentityKeypair::from_seed([0xA1u8; 32]);
        let rogue_ca_kp = astream_aead::IdentityKeypair::from_seed([0xA2u8; 32]);
        let host_k1 = astream_aead::IdentityKeypair::from_seed([0xB1u8; 32]);
        let host_k2 = astream_aead::IdentityKeypair::from_seed([0xB2u8; 32]);
        let client_kp = astream_aead::IdentityKeypair::from_seed([0xC1u8; 32]);
        let ca_pub = ca_kp.public();
        let host_pub_1 = host_k1.public();
        let host_pub_2 = host_k2.public();
        let client_pub = client_kp.public();

        #[cfg(unix)]
        let agent = astream_aead::SshAgentServer::bind(
            &sock_path,
            vec![
                (ca_kp, "kafka-ca".to_owned()),
                (host_k1, "kafka-host-1".to_owned()),
                (client_kp, "kafka-client".to_owned()),
            ],
        )
        .unwrap();

        #[cfg(unix)]
        let ca = astream_aead::CertificateAuthority::new(
            astream_aead::SshAgentSigner::connect_for_key(&sock_path, ca_pub).unwrap(),
            "ssh-ca://kafka-fleet",
        )
        .unwrap();
        #[cfg(not(unix))]
        let ca = astream_aead::CertificateAuthority::new(ca_kp, "ssh-ca://kafka-fleet").unwrap();

        let rogue_ca =
            astream_aead::CertificateAuthority::new(rogue_ca_kp, "ssh-ca://kafka-fleet").unwrap();

        let host_cert_1 = ca
            .issue(
                astream_aead::CertRole::Host,
                host_pub_1,
                "n-kafka-0",
                1,
                t0,
                t1,
            )
            .unwrap();
        let host_cert_2 = ca
            .issue(
                astream_aead::CertRole::Host,
                host_pub_2,
                "n-kafka-0",
                2,
                t0,
                t1,
            )
            .unwrap();
        let client_cert = ca
            .issue(
                astream_aead::CertRole::Client,
                client_pub,
                "a-kafka-producer",
                10,
                t0,
                t1,
            )
            .unwrap();
        let rogue_client_kp = astream_aead::IdentityKeypair::from_seed([0xD1u8; 32]);
        let rogue_cert = rogue_ca
            .issue(
                astream_aead::CertRole::Client,
                rogue_client_kp.public(),
                "a-rogue",
                99,
                t0,
                t1,
            )
            .unwrap();

        #[cfg(unix)]
        let host_signer_1 = astream_aead::IdentitySigner::from(
            astream_aead::SshAgentSigner::connect_for_key(&sock_path, host_pub_1).unwrap(),
        );
        #[cfg(not(unix))]
        let host_signer_1 = astream_aead::IdentitySigner::from(host_k1);

        #[cfg(unix)]
        let client_signer = astream_aead::IdentitySigner::from(
            astream_aead::SshAgentSigner::connect_for_key(&sock_path, client_pub).unwrap(),
        );
        #[cfg(not(unix))]
        let client_signer = astream_aead::IdentitySigner::from(client_kp);

        let host_rotator = astream_aead::HostCertRotator::new(host_signer_1, host_cert_1).unwrap();
        let trust_store = astream_aead::CertTrustStore::new(vec![ca_pub], 3_600_000).unwrap();
        let shared_trust = astream_aead::SharedCertTrust::new(trust_store.clone());

        let cert_dir = std::env::temp_dir().join(format!("astream-kafka-cert-{pid}"));
        let _ = std::fs::remove_dir_all(&cert_dir);
        let durable_cert =
            DurableKafkaStore::open(&cert_dir, 2, &[("cert-roam-events".to_owned(), 2)]).unwrap();

        let mut sasl_cfg = SaslConfig::new([0x31; 32]);
        sasl_cfg.add_user("svc", b"cert-roam-secret", [0x42; 16], 4096);

        let mut cert_srv = KafkaServer::bind_durable_encrypted_sasl(
            "127.0.0.1:0",
            cluster.clone(),
            durable_cert,
            KafkaEncryptedListener::Certified {
                host_rotator: host_rotator.clone(),
                client_trust: shared_trust,
            },
            sasl_cfg.clone(),
        )
        .unwrap();
        let cert_addr = cert_srv.local_addr();

        // Rogue-CA client certificate is refused!
        let rogue_signer = astream_aead::IdentitySigner::from(rogue_client_kp);
        if let Ok(mut bad_cli) = KafkaClient::connect_certified(
            cert_addr,
            "rogue-cert",
            &rogue_signer,
            &rogue_cert,
            &trust_store,
            Some("n-kafka-0"),
        ) {
            assert!(bad_cli.api_versions(3).is_err());
        }

        // Valid SSH-agent client connects against generation-1 host cert, then host rotates to
        // generation-2 live without restarting KafkaServer!
        let (mut cli1, vhost1) = KafkaClient::connect_certified_verified(
            cert_addr,
            "cert-cli-1",
            &client_signer,
            &client_cert,
            &trust_store,
            Some("n-kafka-0"),
        )
        .unwrap();
        assert_eq!(vhost1.serial, 1);
        cli1.sasl_authenticate_scram_sha256(2, "svc", b"cert-roam-secret", "certNonce0001")
            .unwrap();

        assert_eq!(
            host_rotator
                .rotate(host_k2, host_cert_2, now_ms.saturating_add(60_000), now_ms)
                .unwrap(),
            2
        );
        let (mut cli2, vhost2) = KafkaClient::connect_certified_verified(
            cert_addr,
            "cert-cli-2",
            &client_signer,
            &client_cert,
            &trust_store,
            Some("n-kafka-0"),
        )
        .unwrap();
        assert_eq!(vhost2.serial, 2);
        cli2.sasl_authenticate_scram_sha256(2, "svc", b"cert-roam-secret", "certNonce0002")
            .unwrap();

        let batch0 = RecordBatchV2 {
            base_offset: 0,
            partition_leader_epoch: 0,
            attributes: 0,
            producer_id: 91,
            producer_epoch: 0,
            base_sequence: 0,
            records: vec![KafkaRecord {
                timestamp_ms: 1_000,
                key: Some(b"k0".to_vec()),
                value: Some(b"certified-ssh-agent-batch".to_vec()),
                headers: Vec::new(),
            }],
        };
        assert_eq!(
            cli2.produce("cert-roam-events", 0, &batch0).unwrap(),
            (NONE, 0)
        );
        drop(cli1);
        drop(cli2);
        cert_srv.shutdown();
        #[cfg(unix)]
        {
            agent.shutdown();
            let _ = std::fs::remove_dir_all(&sock_dir);
        }
        let _ = std::fs::remove_dir_all(&cert_dir);

        // 2. Zero-gap AEAD-over-UDP Roaming listener + SASL SCRAM-SHA-256 across live socket migrations!
        let roam_dir = std::env::temp_dir().join(format!("astream-kafka-roam-{pid}"));
        let _ = std::fs::remove_dir_all(&roam_dir);
        let durable_roam =
            DurableKafkaStore::open(&roam_dir, 2, &[("cert-roam-events".to_owned(), 2)]).unwrap();
        let roam_psk = [0x6Bu8; 32];
        let mut roam_srv = KafkaServer::bind_durable_roaming_sasl(
            "127.0.0.1:0",
            cluster,
            durable_roam,
            roam_psk,
            sasl_cfg,
        )
        .unwrap();
        let roam_addr = roam_srv.local_addr();

        let (mut roam_cli, roam_handle) =
            KafkaClient::connect_roaming(roam_addr, "roam-kafka-cli", roam_psk).unwrap();
        let orig_local = roam_handle.local_addr().unwrap();
        roam_cli
            .sasl_authenticate_scram_sha256(2, "svc", b"cert-roam-secret", "roamNonce0001")
            .unwrap();

        assert_eq!(
            roam_cli.produce("cert-roam-events", 1, &batch0).unwrap(),
            (NONE, 0)
        );

        // Migrate client across TWO fresh ephemeral UDP sockets without re-authenticating SASL!
        let mig1 = roam_handle.migrate().unwrap();
        assert_ne!(mig1, orig_local);
        let batch1 = RecordBatchV2 {
            base_offset: 0,
            partition_leader_epoch: 0,
            attributes: 0,
            producer_id: 91,
            producer_epoch: 0,
            base_sequence: 1,
            records: vec![KafkaRecord {
                timestamp_ms: 2_000,
                key: Some(b"k1".to_vec()),
                value: Some(b"post-migration-batch".to_vec()),
                headers: Vec::new(),
            }],
        };
        assert_eq!(
            roam_cli.produce("cert-roam-events", 1, &batch1).unwrap(),
            (NONE, 1)
        );

        let mig2 = roam_handle.migrate().unwrap();
        assert_ne!(mig2, mig1);
        let (f_err, hw, batches) = roam_cli.fetch("cert-roam-events", 1, 0, 65_536).unwrap();
        assert_eq!(f_err, NONE);
        assert_eq!(hw, 2);
        assert_eq!(batches.len(), 2);
        assert_eq!(
            batches[0].records[0].value.as_deref(),
            Some(&b"certified-ssh-agent-batch"[..])
        );
        assert_eq!(
            batches[1].records[0].value.as_deref(),
            Some(&b"post-migration-batch"[..])
        );

        drop(roam_cli);
        roam_srv.shutdown();
        let _ = std::fs::remove_dir_all(&roam_dir);
    }
}
