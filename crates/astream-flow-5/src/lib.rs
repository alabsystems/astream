// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Adaptive flow control, backpressure horizons, session multiplexing, and replay determinism (shard 5 of 6, batches 69..70). forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod batch_seal_continuity_scanner;
pub mod cross_face_ack_seq_guard;
pub mod durable_kafka_shard_mapper;
pub mod program_predictor_lru;
pub mod unclean_boot_generation_mover;
pub mod wire_stats_fleet_isolator;

/// Four-byte magic prefix (`"AF05"`) for a 16-byte `astream-flow-5` shard wire snapshot header.
pub const FLOW_5_WIRE_MAGIC: [u8; 4] = *b"AF05";

/// Wire format version for `astream-flow-5` shard snapshot headers.
pub const FLOW_5_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `astream-flow-5` shard wire snapshot header:
/// `[0..4] = b"AF05"`, `[4] = version (1)`, `[5] = kind_tag` (`0..=7`), `[6..8] = 0`,
/// `[8..12] = epoch_seq (BE)`, `[12..16] = item_count (BE)`.
#[must_use]
pub const fn encode_flow_5_wire(kind_tag: u8, epoch_seq: u32, item_count: u32) -> Option<[u8; 16]> {
    if kind_tag > 7 || epoch_seq == 0 {
        return None;
    }
    Some([
        FLOW_5_WIRE_MAGIC[0],
        FLOW_5_WIRE_MAGIC[1],
        FLOW_5_WIRE_MAGIC[2],
        FLOW_5_WIRE_MAGIC[3],
        FLOW_5_WIRE_VERSION,
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

/// Decode a 16-byte `astream-flow-5` shard wire snapshot header into `(kind_tag, epoch_seq, item_count)`.
#[must_use]
pub const fn decode_flow_5_wire(buf: &[u8]) -> Option<(u8, u32, u32)> {
    let [b'A', b'F', b'0', b'5', FLOW_5_WIRE_VERSION, kind_tag, 0, 0, a0, a1, a2, a3, b0, b1, b2, b3, ..] =
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
    fn flow_5_wire_roundtrips_and_rejects_malformed() {
        let Some(frame) = encode_flow_5_wire(2, 1_024, 19) else {
            panic!("valid astream-flow-5 wire header should encode");
        };
        assert_eq!(decode_flow_5_wire(&frame), Some((2, 1_024, 19)));
        assert_eq!(encode_flow_5_wire(2, 0, 19), None);
        assert_eq!(encode_flow_5_wire(8, 1_024, 19), None);
        let mut bad = frame;
        bad[4] = 9;
        assert_eq!(decode_flow_5_wire(&bad), None);
    }
}
