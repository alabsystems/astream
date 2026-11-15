// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Deterministic agent turn budgets, shadow audit ledgers, and perception classifiers (shard 6 of 6, batches 119..120). forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod agent_self_restart_validator;
pub mod agy_quota_pool_rotator;
pub mod bind_will_compaction_unblocker;
pub mod mouse_sgr_pixel_coord_fence;
pub mod tail_coalesced_wakeup_valve;
pub mod wan_keepalive_liveness_probe;

/// Four-byte magic prefix (`"AG06"`) for a 16-byte `astream-cognition-6` shard wire snapshot header.
pub const COGNITION_6_WIRE_MAGIC: [u8; 4] = *b"AG06";

/// Wire format version for `astream-cognition-6` shard snapshot headers.
pub const COGNITION_6_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `astream-cognition-6` shard wire snapshot header:
/// `[0..4] = b"AG06"`, `[4] = version (1)`, `[5] = kind_tag` (`0..=7`), `[6..8] = 0`,
/// `[8..12] = epoch_seq (BE)`, `[12..16] = item_count (BE)`.
#[must_use]
pub const fn encode_cognition_6_wire(
    kind_tag: u8,
    epoch_seq: u32,
    item_count: u32,
) -> Option<[u8; 16]> {
    if kind_tag > 7 || epoch_seq == 0 {
        return None;
    }
    Some([
        COGNITION_6_WIRE_MAGIC[0],
        COGNITION_6_WIRE_MAGIC[1],
        COGNITION_6_WIRE_MAGIC[2],
        COGNITION_6_WIRE_MAGIC[3],
        COGNITION_6_WIRE_VERSION,
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

/// Decode a 16-byte `astream-cognition-6` shard wire snapshot header into `(kind_tag, epoch_seq, item_count)`.
#[must_use]
pub const fn decode_cognition_6_wire(buf: &[u8]) -> Option<(u8, u32, u32)> {
    let [b'A', b'G', b'0', b'6', COGNITION_6_WIRE_VERSION, kind_tag, 0, 0, a0, a1, a2, a3, b0, b1, b2, b3, ..] =
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
    fn cognition_6_wire_roundtrips_and_rejects_malformed() {
        let Some(frame) = encode_cognition_6_wire(2, 1_024, 19) else {
            panic!("valid astream-cognition-6 wire header should encode");
        };
        assert_eq!(decode_cognition_6_wire(&frame), Some((2, 1_024, 19)));
        assert_eq!(encode_cognition_6_wire(2, 0, 19), None);
        assert_eq!(encode_cognition_6_wire(8, 1_024, 19), None);
        let mut bad = frame;
        bad[4] = 9;
        assert_eq!(decode_cognition_6_wire(&bad), None);
    }
}
