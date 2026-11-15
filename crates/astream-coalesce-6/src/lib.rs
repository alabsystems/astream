// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Macaroon discharge, Last radix cursors, SIGMA identity binding, damage coalescing, and restart fences (shard 6 of 6, batches 59..60). forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod abrew_compat_guard;
pub mod autopilot_land_gate;
pub mod binary_self_clobber_guard;
pub mod sys_stall_inspector;
pub mod trust_lane_selector;
pub mod worker_task_awaiter;

/// Four-byte magic prefix (`"AC06"`) for a 16-byte `astream-coalesce-6` shard wire snapshot header.
pub const COALESCE_6_WIRE_MAGIC: [u8; 4] = *b"AC06";

/// Wire format version for `astream-coalesce-6` shard snapshot headers.
pub const COALESCE_6_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `astream-coalesce-6` shard wire snapshot header:
/// `[0..4] = b"AC06"`, `[4] = version (1)`, `[5] = kind_tag` (`0..=7`), `[6..8] = 0`,
/// `[8..12] = epoch_seq (BE)`, `[12..16] = item_count (BE)`.
#[must_use]
pub const fn encode_coalesce_6_wire(
    kind_tag: u8,
    epoch_seq: u32,
    item_count: u32,
) -> Option<[u8; 16]> {
    if kind_tag > 7 || epoch_seq == 0 {
        return None;
    }
    Some([
        COALESCE_6_WIRE_MAGIC[0],
        COALESCE_6_WIRE_MAGIC[1],
        COALESCE_6_WIRE_MAGIC[2],
        COALESCE_6_WIRE_MAGIC[3],
        COALESCE_6_WIRE_VERSION,
        kind_tag,
        0,
        0,
        ((epoch_seq >> 24) & 0xFF) as u8,
        ((epoch_seq >> 16) & 0xFF) as u8,
        ((epoch_seq >> 8) & 0xFF) as u8,
        (epoch_seq & 0xFF) as u8,
        ((item_count >> 24) & 0xFF) as u8,
        ((item_count >> 16) & 0xFF) as u8,
        ((item_count >> 8) & 0xFF) as u8,
        (item_count & 0xFF) as u8,
    ])
}

/// Decode a 16-byte `astream-coalesce-6` shard wire snapshot header into `(kind_tag, epoch_seq, item_count)`.
#[must_use]
pub const fn decode_coalesce_6_wire(buf: &[u8]) -> Option<(u8, u32, u32)> {
    let [b'A', b'C', b'0', b'6', COALESCE_6_WIRE_VERSION, kind_tag, 0, 0, a0, a1, a2, a3, b0, b1, b2, b3, ..] =
        *buf
    else {
        return None;
    };
    let epoch_seq = ((a0 as u32) << 24) | ((a1 as u32) << 16) | ((a2 as u32) << 8) | (a3 as u32);
    let item_count = ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32);
    if kind_tag > 7 || epoch_seq == 0 {
        return None;
    }
    Some((kind_tag, epoch_seq, item_count))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn coalesce_6_wire_roundtrips_and_rejects_malformed() {
        let Some(frame) = encode_coalesce_6_wire(2, 1_024, 19) else {
            panic!("valid astream-coalesce-6 wire header should encode");
        };
        assert_eq!(decode_coalesce_6_wire(&frame), Some((2, 1_024, 19)));
        assert_eq!(encode_coalesce_6_wire(2, 0, 19), None);
        assert_eq!(encode_coalesce_6_wire(8, 1_024, 19), None);
        let mut bad = frame;
        bad[4] = 9;
        assert_eq!(decode_coalesce_6_wire(&bad), None);
    }
}
