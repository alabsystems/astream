//! Helper process for the `survives_real_sigkill_while_appending` test.
//!
//! Opens the log at `argv[1]` and appends fsync'd records in a loop, printing
//! `acked <seq>` on stdout (flushed) after each `FileLog::append` returns — i.e.
//! after that record's fsync. The parent test reads those acks and SIGKILLs this
//! process while it is still in the loop, then proves every record it acked
//! before the signal is recovered from the file it left behind. The kill lands
//! at an arbitrary point of the append loop, so the on-disk tail is whatever the
//! signal interrupted — not authored here.
//!
//! Bounded at `MAX_RECORDS` so a parent that fails to kill it cannot fill the
//! disk; past that it blocks forever (still killable). Not run by `cargo test`
//! directly; only spawned by the test via `CARGO_BIN_EXE_crash_child`.

#![forbid(unsafe_code)]

// A contracted fn is written once, through `contract_fn!`: under a Trust compiler
// (`cfg(clean_islands)`, build.rs) it carries its `ensures` clause, which no stock rustc can
// parse, and every other compiler gets the plain fn.
#[macro_use]
#[path = "../../../astream-wire/contract_fn.rs"]
mod contract_fn;

// Plain-Rust twins of the functions this binary's Clean island compiles, for a compiler
// that cannot lex the island.
#[cfg(any(test, not(clean_islands)))]
#[path = "islands/crash_child_twins.rs"]
mod twins;

use astream_engine::{Envelope, FileLog, Offset};
use astream_term::Record;
use std::io::Write;
use std::time::Duration;

const MAX_RECORDS: u64 = 20_000;
/// Each record carries a few KiB so an append is a real multi-page write.
const BODY_LEN: usize = 4096;

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "islands/crash_child_island.rs"]
mod crash_child_island;
#[cfg(clean_islands)]
use crash_child_island::crash_child_advance_seq;
#[cfg(not(clean_islands))]
use twins::crash_child_advance_seq;

contract_fn! {
    /// Verified loop guard checking whether `seq` is strictly below `MAX_RECORDS`.
    pub const fn crash_child_can_append(seq: u64) -> bool
    clauses [ensures result == (seq < 20000)]
    {
        seq < MAX_RECORDS
    }
}

/// Four-byte magic prefix (`"ACRC"`) for a 20-byte `crash_child` ack wire header.
pub const CRASH_CHILD_ACK_WIRE_MAGIC: [u8; 4] = *b"ACRC";

/// Wire format version for `crash_child` ack wire headers.
pub const CRASH_CHILD_ACK_WIRE_VERSION: u8 = 1;

/// Encode a 20-byte `crash_child` ack wire header:
/// `[0..4] = b"ACRC"`, `[4] = version (1)`, `[5] = fill_byte (b'x')`,
/// `[6..8] = body_len (BE)`, `[8..16] = seq (BE)`, `[16..20] = max_records (20_000 BE)`.
#[must_use]
pub const fn crash_child_encode_ack_wire(seq: u64, body_len: u16) -> Option<[u8; 20]> {
    let max_rec = MAX_RECORDS as u32;
    let out = [
        CRASH_CHILD_ACK_WIRE_MAGIC[0],
        CRASH_CHILD_ACK_WIRE_MAGIC[1],
        CRASH_CHILD_ACK_WIRE_MAGIC[2],
        CRASH_CHILD_ACK_WIRE_MAGIC[3],
        CRASH_CHILD_ACK_WIRE_VERSION,
        b'x',
        ((body_len >> 8) & 0xFF) as u8,
        (body_len & 0xFF) as u8,
        ((seq >> 56) & 0xFF) as u8,
        ((seq >> 48) & 0xFF) as u8,
        ((seq >> 40) & 0xFF) as u8,
        ((seq >> 32) & 0xFF) as u8,
        ((seq >> 24) & 0xFF) as u8,
        ((seq >> 16) & 0xFF) as u8,
        ((seq >> 8) & 0xFF) as u8,
        (seq & 0xFF) as u8,
        ((max_rec >> 24) & 0xFF) as u8,
        ((max_rec >> 16) & 0xFF) as u8,
        ((max_rec >> 8) & 0xFF) as u8,
        (max_rec & 0xFF) as u8,
    ];
    if !crash_child_can_append(seq) || body_len == 0 {
        return None;
    }
    Some(out)
}

/// Decode a 20-byte `crash_child` ack wire header into `(seq, body_len)`.
#[must_use]
pub const fn crash_child_decode_ack_wire(buf: &[u8]) -> Option<(u64, u16)> {
    let [b'A', b'C', b'R', b'C', CRASH_CHILD_ACK_WIRE_VERSION, b'x', b0, b1, s0, s1, s2, s3, s4, s5, s6, s7, 0x00, 0x00, 0x4E, 0x20, ..] =
        *buf
    else {
        return None;
    };
    let body_len = ((b0 as u16) << 8) | (b1 as u16);
    let seq = ((s0 as u64) << 56)
        | ((s1 as u64) << 48)
        | ((s2 as u64) << 40)
        | ((s3 as u64) << 32)
        | ((s4 as u64) << 24)
        | ((s5 as u64) << 16)
        | ((s6 as u64) << 8)
        | (s7 as u64);
    if !crash_child_can_append(seq) || body_len == 0 {
        return None;
    }
    Some((seq, body_len))
}

/// Four-byte magic prefix (`"ACRR"`) for a 20-byte `crash_child` recovery report wire header.
pub const CRASH_CHILD_RECOVERY_WIRE_MAGIC: [u8; 4] = *b"ACRR";

/// Wire format version for `crash_child` recovery report wire headers.
pub const CRASH_CHILD_RECOVERY_WIRE_VERSION: u8 = 1;

/// Encode a 20-byte `crash_child` recovery report wire header:
/// `[0..4] = b"ACRR"`, `[4] = version (1)`, `[5] = clean_eof (0/1)`, `[6..8] = 0`,
/// `[8..16] = recovered_records (BE)` (`<= MAX_RECORDS`),
/// `[16..20] = truncated_tail_bytes (BE)` (`0` when `clean_eof` is true).
#[must_use]
pub const fn crash_child_encode_recovery_wire(
    recovered_records: u64,
    truncated_tail_bytes: u32,
    clean_eof: bool,
) -> Option<[u8; 20]> {
    let eof_tag = clean_eof as u8;
    let out = [
        CRASH_CHILD_RECOVERY_WIRE_MAGIC[0],
        CRASH_CHILD_RECOVERY_WIRE_MAGIC[1],
        CRASH_CHILD_RECOVERY_WIRE_MAGIC[2],
        CRASH_CHILD_RECOVERY_WIRE_MAGIC[3],
        CRASH_CHILD_RECOVERY_WIRE_VERSION,
        eof_tag,
        0,
        0,
        ((recovered_records >> 56) & 0xFF) as u8,
        ((recovered_records >> 48) & 0xFF) as u8,
        ((recovered_records >> 40) & 0xFF) as u8,
        ((recovered_records >> 32) & 0xFF) as u8,
        ((recovered_records >> 24) & 0xFF) as u8,
        ((recovered_records >> 16) & 0xFF) as u8,
        ((recovered_records >> 8) & 0xFF) as u8,
        (recovered_records & 0xFF) as u8,
        ((truncated_tail_bytes >> 24) & 0xFF) as u8,
        ((truncated_tail_bytes >> 16) & 0xFF) as u8,
        ((truncated_tail_bytes >> 8) & 0xFF) as u8,
        (truncated_tail_bytes & 0xFF) as u8,
    ];
    if recovered_records > MAX_RECORDS || (clean_eof && truncated_tail_bytes != 0) {
        return None;
    }
    Some(out)
}

/// Decode a 20-byte `crash_child` recovery report wire header into
/// `(recovered_records, truncated_tail_bytes, clean_eof)`.
#[must_use]
pub const fn crash_child_decode_recovery_wire(buf: &[u8]) -> Option<(u64, u32, bool)> {
    let [b'A', b'C', b'R', b'R', CRASH_CHILD_RECOVERY_WIRE_VERSION, eof_tag, 0, 0, r0, r1, r2, r3, r4, r5, r6, r7, t0, t1, t2, t3, ..] =
        *buf
    else {
        return None;
    };
    let recovered_records = ((r0 as u64) << 56)
        | ((r1 as u64) << 48)
        | ((r2 as u64) << 40)
        | ((r3 as u64) << 32)
        | ((r4 as u64) << 24)
        | ((r5 as u64) << 16)
        | ((r6 as u64) << 8)
        | (r7 as u64);
    let truncated_tail_bytes =
        ((t0 as u32) << 24) | ((t1 as u32) << 16) | ((t2 as u32) << 8) | (t3 as u32);
    let clean_eof = match eof_tag {
        0 => false,
        1 => true,
        _ => return None,
    };
    if recovered_records > MAX_RECORDS || (clean_eof && truncated_tail_bytes != 0) {
        return None;
    }
    Some((recovered_records, truncated_tail_bytes, clean_eof))
}

/// Four-byte magic prefix (`"ACRP"`) for a 20-byte `crash_child` progress wire header.
pub const CRASH_CHILD_PROGRESS_WIRE_MAGIC: [u8; 4] = *b"ACRP";

/// Wire format version for `crash_child` progress wire headers.
pub const CRASH_CHILD_PROGRESS_WIRE_VERSION: u8 = 1;

/// Encode a 20-byte `crash_child` progress wire header:
/// `[0..4] = b"ACRP"`, `[4] = version (1)`, `[5] = parked (0/1)`, `[6..8] = 0`,
/// `[8..16] = initial_seq (BE)` (`<= current_seq`),
/// `[16..20] = current_seq (BE)` (`<= MAX_RECORDS`).
#[must_use]
pub const fn crash_child_encode_progress_wire(
    initial_seq: u64,
    current_seq: u32,
    parked: bool,
) -> Option<[u8; 20]> {
    let parked_tag = parked as u8;
    let out = [
        CRASH_CHILD_PROGRESS_WIRE_MAGIC[0],
        CRASH_CHILD_PROGRESS_WIRE_MAGIC[1],
        CRASH_CHILD_PROGRESS_WIRE_MAGIC[2],
        CRASH_CHILD_PROGRESS_WIRE_MAGIC[3],
        CRASH_CHILD_PROGRESS_WIRE_VERSION,
        parked_tag,
        0,
        0,
        ((initial_seq >> 56) & 0xFF) as u8,
        ((initial_seq >> 48) & 0xFF) as u8,
        ((initial_seq >> 40) & 0xFF) as u8,
        ((initial_seq >> 32) & 0xFF) as u8,
        ((initial_seq >> 24) & 0xFF) as u8,
        ((initial_seq >> 16) & 0xFF) as u8,
        ((initial_seq >> 8) & 0xFF) as u8,
        (initial_seq & 0xFF) as u8,
        ((current_seq >> 24) & 0xFF) as u8,
        ((current_seq >> 16) & 0xFF) as u8,
        ((current_seq >> 8) & 0xFF) as u8,
        (current_seq & 0xFF) as u8,
    ];
    if (current_seq as u64) > MAX_RECORDS
        || initial_seq > (current_seq as u64)
        || (parked && (current_seq as u64) < MAX_RECORDS)
    {
        return None;
    }
    Some(out)
}

/// Decode a 20-byte `crash_child` progress wire header into `(initial_seq, current_seq, parked)`.
#[must_use]
pub const fn crash_child_decode_progress_wire(buf: &[u8]) -> Option<(u64, u32, bool)> {
    let [b'A', b'C', b'R', b'P', CRASH_CHILD_PROGRESS_WIRE_VERSION, parked_tag, 0, 0, i0, i1, i2, i3, i4, i5, i6, i7, c0, c1, c2, c3, ..] =
        *buf
    else {
        return None;
    };
    let initial_seq = ((i0 as u64) << 56)
        | ((i1 as u64) << 48)
        | ((i2 as u64) << 40)
        | ((i3 as u64) << 32)
        | ((i4 as u64) << 24)
        | ((i5 as u64) << 16)
        | ((i6 as u64) << 8)
        | (i7 as u64);
    let current_seq = ((c0 as u32) << 24) | ((c1 as u32) << 16) | ((c2 as u32) << 8) | (c3 as u32);
    let parked = match parked_tag {
        0 => false,
        1 => true,
        _ => return None,
    };
    if (current_seq as u64) > MAX_RECORDS
        || initial_seq > (current_seq as u64)
        || (parked && (current_seq as u64) < MAX_RECORDS)
    {
        return None;
    }
    Some((initial_seq, current_seq, parked))
}

/// Four-byte magic prefix (`"ACCF"`) for a 20-byte `crash_child` config wire header.
pub const CRASH_CHILD_CONFIG_WIRE_MAGIC: [u8; 4] = *b"ACCF";

/// Wire format version for `crash_child` config wire headers.
pub const CRASH_CHILD_CONFIG_WIRE_VERSION: u8 = 1;

/// Encode a 20-byte `crash_child` config wire header:
/// `[0..4] = b"ACCF"`, `[4] = version (1)`, `[5] = fill_byte`,
/// `[6..8] = body_len (BE)`, `[8..12] = park_secs (BE)`,
/// `[12..20] = max_records (BE)` (`1..=MAX_RECORDS`).
#[must_use]
pub const fn crash_child_encode_config_wire(
    fill_byte: u8,
    body_len: u16,
    park_secs: u32,
    max_records: u64,
) -> Option<[u8; 20]> {
    let out = [
        CRASH_CHILD_CONFIG_WIRE_MAGIC[0],
        CRASH_CHILD_CONFIG_WIRE_MAGIC[1],
        CRASH_CHILD_CONFIG_WIRE_MAGIC[2],
        CRASH_CHILD_CONFIG_WIRE_MAGIC[3],
        CRASH_CHILD_CONFIG_WIRE_VERSION,
        fill_byte,
        ((body_len >> 8) & 0xFF) as u8,
        (body_len & 0xFF) as u8,
        ((park_secs >> 24) & 0xFF) as u8,
        ((park_secs >> 16) & 0xFF) as u8,
        ((park_secs >> 8) & 0xFF) as u8,
        (park_secs & 0xFF) as u8,
        ((max_records >> 56) & 0xFF) as u8,
        ((max_records >> 48) & 0xFF) as u8,
        ((max_records >> 40) & 0xFF) as u8,
        ((max_records >> 32) & 0xFF) as u8,
        ((max_records >> 24) & 0xFF) as u8,
        ((max_records >> 16) & 0xFF) as u8,
        ((max_records >> 8) & 0xFF) as u8,
        (max_records & 0xFF) as u8,
    ];
    if fill_byte == 0
        || body_len == 0
        || park_secs == 0
        || max_records == 0
        || max_records > MAX_RECORDS
    {
        return None;
    }
    Some(out)
}

/// Decode a 20-byte `crash_child` config wire header into
/// `(fill_byte, body_len, park_secs, max_records)`.
#[must_use]
pub const fn crash_child_decode_config_wire(buf: &[u8]) -> Option<(u8, u16, u32, u64)> {
    let [b'A', b'C', b'C', b'F', CRASH_CHILD_CONFIG_WIRE_VERSION, fill_byte, b0, b1, p0, p1, p2, p3, m0, m1, m2, m3, m4, m5, m6, m7, ..] =
        *buf
    else {
        return None;
    };
    let body_len = ((b0 as u16) << 8) | (b1 as u16);
    let park_secs = ((p0 as u32) << 24) | ((p1 as u32) << 16) | ((p2 as u32) << 8) | (p3 as u32);
    let max_records = ((m0 as u64) << 56)
        | ((m1 as u64) << 48)
        | ((m2 as u64) << 40)
        | ((m3 as u64) << 32)
        | ((m4 as u64) << 24)
        | ((m5 as u64) << 16)
        | ((m6 as u64) << 8)
        | (m7 as u64);
    if fill_byte == 0
        || body_len == 0
        || park_secs == 0
        || max_records == 0
        || max_records > MAX_RECORDS
    {
        return None;
    }
    Some((fill_byte, body_len, park_secs, max_records))
}

/// Four-byte magic prefix (`"ACTL"`) for a 20-byte `crash_child` tail inspection wire header.
pub const CRASH_CHILD_TAIL_WIRE_MAGIC: [u8; 4] = *b"ACTL";

/// Wire format version for `crash_child` tail inspection wire headers.
pub const CRASH_CHILD_TAIL_WIRE_VERSION: u8 = 1;

/// Encode a 20-byte `crash_child` tail inspection wire header:
/// `[0..4] = b"ACTL"`, `[4] = version (1)`, `[5] = torn_tail (0/1)`, `[6..8] = 0`,
/// `[8..12] = acked_count (BE)` (`<= MAX_RECORDS`), `[12..20] = file_bytes (BE)`.
#[must_use]
pub const fn crash_child_encode_tail_wire(
    torn_tail: bool,
    acked_count: u32,
    file_bytes: u64,
) -> Option<[u8; 20]> {
    let torn_tag = torn_tail as u8;
    let out = [
        CRASH_CHILD_TAIL_WIRE_MAGIC[0],
        CRASH_CHILD_TAIL_WIRE_MAGIC[1],
        CRASH_CHILD_TAIL_WIRE_MAGIC[2],
        CRASH_CHILD_TAIL_WIRE_MAGIC[3],
        CRASH_CHILD_TAIL_WIRE_VERSION,
        torn_tag,
        0,
        0,
        ((acked_count >> 24) & 0xFF) as u8,
        ((acked_count >> 16) & 0xFF) as u8,
        ((acked_count >> 8) & 0xFF) as u8,
        (acked_count & 0xFF) as u8,
        ((file_bytes >> 56) & 0xFF) as u8,
        ((file_bytes >> 48) & 0xFF) as u8,
        ((file_bytes >> 40) & 0xFF) as u8,
        ((file_bytes >> 32) & 0xFF) as u8,
        ((file_bytes >> 24) & 0xFF) as u8,
        ((file_bytes >> 16) & 0xFF) as u8,
        ((file_bytes >> 8) & 0xFF) as u8,
        (file_bytes & 0xFF) as u8,
    ];
    if (acked_count as u64) > MAX_RECORDS || (acked_count > 0 && file_bytes == 0) {
        return None;
    }
    Some(out)
}

/// Decode a 20-byte `crash_child` tail inspection wire header into
/// `(torn_tail, acked_count, file_bytes)`.
#[must_use]
pub const fn crash_child_decode_tail_wire(buf: &[u8]) -> Option<(bool, u32, u64)> {
    let [b'A', b'C', b'T', b'L', CRASH_CHILD_TAIL_WIRE_VERSION, torn_tag, 0, 0, a0, a1, a2, a3, f0, f1, f2, f3, f4, f5, f6, f7, ..] =
        *buf
    else {
        return None;
    };
    let acked_count = ((a0 as u32) << 24) | ((a1 as u32) << 16) | ((a2 as u32) << 8) | (a3 as u32);
    let file_bytes = ((f0 as u64) << 56)
        | ((f1 as u64) << 48)
        | ((f2 as u64) << 40)
        | ((f3 as u64) << 32)
        | ((f4 as u64) << 24)
        | ((f5 as u64) << 16)
        | ((f6 as u64) << 8)
        | (f7 as u64);
    let torn_tail = match torn_tag {
        0 => false,
        1 => true,
        _ => return None,
    };
    if (acked_count as u64) > MAX_RECORDS || (acked_count > 0 && file_bytes == 0) {
        return None;
    }
    Some((torn_tail, acked_count, file_bytes))
}

/// Four-byte magic prefix (`"ACRS"`) for a 20-byte `crash_child` WAL-seal wire header.
pub const CRASH_CHILD_SEAL_WIRE_MAGIC: [u8; 4] = *b"ACRS";

/// Wire format version for `crash_child` WAL-seal wire headers.
pub const CRASH_CHILD_SEAL_WIRE_VERSION: u8 = 1;

/// Encode a 20-byte `crash_child` WAL-seal wire header:
/// `[0..4] = b"ACRS"`, `[4] = version (1)`, `[5] = clean_seal (0/1)`, `[6..8] = 0`,
/// `[8..12] = sealed_count (BE)` (`<= MAX_RECORDS`), `[12..20] = chain_tag (BE)`.
#[must_use]
pub const fn crash_child_encode_seal_wire(
    clean_seal: bool,
    sealed_count: u32,
    chain_tag: u64,
) -> Option<[u8; 20]> {
    let seal_flag = clean_seal as u8;
    let out = [
        CRASH_CHILD_SEAL_WIRE_MAGIC[0],
        CRASH_CHILD_SEAL_WIRE_MAGIC[1],
        CRASH_CHILD_SEAL_WIRE_MAGIC[2],
        CRASH_CHILD_SEAL_WIRE_MAGIC[3],
        CRASH_CHILD_SEAL_WIRE_VERSION,
        seal_flag,
        0,
        0,
        ((sealed_count >> 24) & 0xFF) as u8,
        ((sealed_count >> 16) & 0xFF) as u8,
        ((sealed_count >> 8) & 0xFF) as u8,
        (sealed_count & 0xFF) as u8,
        ((chain_tag >> 56) & 0xFF) as u8,
        ((chain_tag >> 48) & 0xFF) as u8,
        ((chain_tag >> 40) & 0xFF) as u8,
        ((chain_tag >> 32) & 0xFF) as u8,
        ((chain_tag >> 24) & 0xFF) as u8,
        ((chain_tag >> 16) & 0xFF) as u8,
        ((chain_tag >> 8) & 0xFF) as u8,
        (chain_tag & 0xFF) as u8,
    ];
    if (sealed_count as u64) > MAX_RECORDS || (clean_seal && chain_tag == 0) {
        return None;
    }
    Some(out)
}

/// Decode a 20-byte `crash_child` WAL-seal wire header into
/// `(clean_seal, sealed_count, chain_tag)`.
#[must_use]
pub const fn crash_child_decode_seal_wire(buf: &[u8]) -> Option<(bool, u32, u64)> {
    let [b'A', b'C', b'R', b'S', CRASH_CHILD_SEAL_WIRE_VERSION, seal_flag, 0, 0, s0, s1, s2, s3, c0, c1, c2, c3, c4, c5, c6, c7, ..] =
        *buf
    else {
        return None;
    };
    let sealed_count = ((s0 as u32) << 24) | ((s1 as u32) << 16) | ((s2 as u32) << 8) | (s3 as u32);
    let chain_tag = ((c0 as u64) << 56)
        | ((c1 as u64) << 48)
        | ((c2 as u64) << 40)
        | ((c3 as u64) << 32)
        | ((c4 as u64) << 24)
        | ((c5 as u64) << 16)
        | ((c6 as u64) << 8)
        | (c7 as u64);
    let clean_seal = match seal_flag {
        0 => false,
        1 => true,
        _ => return None,
    };
    if (sealed_count as u64) > MAX_RECORDS || (clean_seal && chain_tag == 0) {
        return None;
    }
    Some((clean_seal, sealed_count, chain_tag))
}

/// Four-byte magic prefix (`"ACRF"`) for a 20-byte `crash_child` fsync checkpoint wire header.
pub const CRASH_CHILD_FSYNC_WIRE_MAGIC: [u8; 4] = *b"ACRF";

/// Wire format version for `crash_child` fsync checkpoint wire headers.
pub const CRASH_CHILD_FSYNC_WIRE_VERSION: u8 = 1;

/// Encode a 20-byte `crash_child` fsync checkpoint wire header:
/// `[0..4] = b"ACRF"`, `[4] = version (1)`, `[5] = barrier_mode` (`1..=2`), `[6..8] = 0`,
/// `[8..12] = durable_seq (BE)` (`<= MAX_RECORDS`), `[12..20] = synced_bytes (BE)`.
#[must_use]
pub const fn crash_child_encode_fsync_wire(
    barrier_mode: u8,
    durable_seq: u32,
    synced_bytes: u64,
) -> Option<[u8; 20]> {
    let out = [
        CRASH_CHILD_FSYNC_WIRE_MAGIC[0],
        CRASH_CHILD_FSYNC_WIRE_MAGIC[1],
        CRASH_CHILD_FSYNC_WIRE_MAGIC[2],
        CRASH_CHILD_FSYNC_WIRE_MAGIC[3],
        CRASH_CHILD_FSYNC_WIRE_VERSION,
        barrier_mode,
        0,
        0,
        ((durable_seq >> 24) & 0xFF) as u8,
        ((durable_seq >> 16) & 0xFF) as u8,
        ((durable_seq >> 8) & 0xFF) as u8,
        (durable_seq & 0xFF) as u8,
        ((synced_bytes >> 56) & 0xFF) as u8,
        ((synced_bytes >> 48) & 0xFF) as u8,
        ((synced_bytes >> 40) & 0xFF) as u8,
        ((synced_bytes >> 32) & 0xFF) as u8,
        ((synced_bytes >> 24) & 0xFF) as u8,
        ((synced_bytes >> 16) & 0xFF) as u8,
        ((synced_bytes >> 8) & 0xFF) as u8,
        (synced_bytes & 0xFF) as u8,
    ];
    if barrier_mode == 0
        || barrier_mode > 2
        || (durable_seq as u64) > MAX_RECORDS
        || synced_bytes == 0
    {
        return None;
    }
    Some(out)
}

/// Decode a 20-byte `crash_child` fsync checkpoint wire header into
/// `(barrier_mode, durable_seq, synced_bytes)`.
#[must_use]
pub const fn crash_child_decode_fsync_wire(buf: &[u8]) -> Option<(u8, u32, u64)> {
    let [b'A', b'C', b'R', b'F', CRASH_CHILD_FSYNC_WIRE_VERSION, barrier_mode, 0, 0, d0, d1, d2, d3, b0, b1, b2, b3, b4, b5, b6, b7, ..] =
        *buf
    else {
        return None;
    };
    let durable_seq = ((d0 as u32) << 24) | ((d1 as u32) << 16) | ((d2 as u32) << 8) | (d3 as u32);
    let synced_bytes = ((b0 as u64) << 56)
        | ((b1 as u64) << 48)
        | ((b2 as u64) << 40)
        | ((b3 as u64) << 32)
        | ((b4 as u64) << 24)
        | ((b5 as u64) << 16)
        | ((b6 as u64) << 8)
        | (b7 as u64);
    if barrier_mode == 0
        || barrier_mode > 2
        || (durable_seq as u64) > MAX_RECORDS
        || synced_bytes == 0
    {
        return None;
    }
    Some((barrier_mode, durable_seq, synced_bytes))
}

fn main() -> std::process::ExitCode {
    let mut args = std::env::args_os().skip(1);
    let Some(raw_path) = args.next() else {
        return std::process::ExitCode::from(1);
    };
    let Ok(path) = raw_path.into_string() else {
        return std::process::ExitCode::from(1);
    };

    let Ok((mut log, report)) = FileLog::open(std::path::Path::new(path.as_str())) else {
        return std::process::ExitCode::from(1);
    };
    let mut seq = report.records;
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    while crash_child_can_append(seq) {
        let mut body = format!("line {seq} ").into_bytes();
        body.resize(BODY_LEN, b'x');
        let env = Envelope {
            seq: Offset(seq),
            ts_logical: seq,
            caused_by: None,
            record: Record::Out(body),
        };
        let Ok(encoded) = env.encode() else {
            return std::process::ExitCode::from(1);
        };
        if log.append(&encoded).is_err()
            || writeln!(out, "acked {seq}").is_err()
            || out.flush().is_err()
        {
            return std::process::ExitCode::from(1);
        }
        // Acked == durably on disk. Flushed so the parent sees it immediately.
        seq = crash_child_advance_seq(seq, seq.saturating_add(1));
    }
    std::thread::sleep(Duration::from_secs(3600));
    std::process::ExitCode::SUCCESS
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn seal_and_fsync_wire_headers_round_trip() {
        let s = crash_child_encode_seal_wire(true, 42, 0xCAFE_BEEF_1234_5678).unwrap();
        assert_eq!(
            crash_child_decode_seal_wire(&s),
            Some((true, 42, 0xCAFE_BEEF_1234_5678))
        );
        assert!(crash_child_encode_seal_wire(true, 42, 0).is_none());

        let f = crash_child_encode_fsync_wire(1, 42, 172_032).unwrap();
        assert_eq!(crash_child_decode_fsync_wire(&f), Some((1, 42, 172_032)));
        assert!(crash_child_encode_fsync_wire(0, 42, 172_032).is_none());
    }
}
