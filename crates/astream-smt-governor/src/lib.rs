// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Per-crate `I * D` Clean/SMT shard complexity estimator, Z3 `wall-backstop == 0` watchdog, `verify-ready.sh` monotone 80% floor ratchet, upstream `OD-1` allowlist fence, `astream-wire` `unknown == 0` invariant gate, and `VERIFY_JOBS` slot pool. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod floor_ratchet_calc;
pub mod od1_allowlist_fence;
pub mod parallel_shard_slots;
pub mod rlimit_watchdog;
pub mod vc_complexity_score;
pub mod wire_zero_unknown_gate;

/// Four-byte magic prefix (`"ASMT"`) for a 16-byte `astream-smt-governor` wire budget header.
pub const SMT_GOVERNOR_WIRE_MAGIC: [u8; 4] = *b"ASMT";

/// Wire format version for `astream-smt-governor` budget headers.
pub const SMT_GOVERNOR_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `astream-smt-governor` wire budget header:
/// `[0..4] = b"ASMT"`, `[4] = version (1)`, `[5] = verdict_tag` (`0..=3`), `[6..8] = 0`,
/// `[8..12] = proved_count (BE)`, `[12..16] = floor_count (BE)`.
#[must_use]
pub const fn encode_smt_governor_wire(
    verdict_tag: u8,
    proved_count: u32,
    floor_count: u32,
) -> Option<[u8; 16]> {
    if verdict_tag > 3 || (verdict_tag == 0 && proved_count < floor_count) {
        return None;
    }
    Some([
        SMT_GOVERNOR_WIRE_MAGIC[0],
        SMT_GOVERNOR_WIRE_MAGIC[1],
        SMT_GOVERNOR_WIRE_MAGIC[2],
        SMT_GOVERNOR_WIRE_MAGIC[3],
        SMT_GOVERNOR_WIRE_VERSION,
        verdict_tag,
        0,
        0,
        ((proved_count >> 24) & 0xFF) as u8,
        ((proved_count >> 16) & 0xFF) as u8,
        ((proved_count >> 8) & 0xFF) as u8,
        (proved_count & 0xFF) as u8,
        ((floor_count >> 24) & 0xFF) as u8,
        ((floor_count >> 16) & 0xFF) as u8,
        ((floor_count >> 8) & 0xFF) as u8,
        (floor_count & 0xFF) as u8,
    ])
}

/// Decode a 16-byte `astream-smt-governor` wire budget header into
/// `(verdict_tag, proved_count, floor_count)`.
#[must_use]
pub const fn decode_smt_governor_wire(buf: &[u8]) -> Option<(u8, u32, u32)> {
    let [b'A', b'S', b'M', b'T', SMT_GOVERNOR_WIRE_VERSION, verdict_tag, 0, 0, p0, p1, p2, p3, f0, f1, f2, f3, ..] =
        *buf
    else {
        return None;
    };
    let proved_count = ((p0 as u32) << 24) | ((p1 as u32) << 16) | ((p2 as u32) << 8) | (p3 as u32);
    let floor_count = ((f0 as u32) << 24) | ((f1 as u32) << 16) | ((f2 as u32) << 8) | (f3 as u32);
    if verdict_tag > 3 || (verdict_tag == 0 && proved_count < floor_count) {
        return None;
    }
    Some((verdict_tag, proved_count, floor_count))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn smt_governor_wire_roundtrips_and_enforces_floor_on_pass() {
        let Some(frame) = encode_smt_governor_wire(0, 600, 480) else {
            panic!("valid governor frame should encode");
        };
        assert_eq!(decode_smt_governor_wire(&frame), Some((0, 600, 480)));
        assert_eq!(encode_smt_governor_wire(0, 9, 10), None);
        assert_eq!(encode_smt_governor_wire(4, 20, 10), None);
        let mut bad = frame;
        bad[0] = b'X';
        assert_eq!(decode_smt_governor_wire(&bad), None);
    }
}
