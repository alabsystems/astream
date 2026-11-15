// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Segment chains, Merkle accumulators, nonce challenges, selftest pins, and transport guards (shard 4 of 6, batches 43..44). forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod agy_quota_rotator;
pub mod batch_seal_verifier;
pub mod consumer_rebalance_gen;
pub mod inbox_envelope_guard;
pub mod osc133_shell_prompt;
pub mod privacy_consent_classifier;

/// Four-byte magic prefix (`"AI04"`) for a 16-byte `astream-integrity-4` shard wire snapshot header.
pub const INTEGRITY_4_WIRE_MAGIC: [u8; 4] = *b"AI04";

/// Wire format version for `astream-integrity-4` shard snapshot headers.
pub const INTEGRITY_4_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `astream-integrity-4` shard wire snapshot header:
/// `[0..4] = b"AI04"`, `[4] = version (1)`, `[5] = kind_tag` (`0..=7`), `[6..8] = 0`,
/// `[8..12] = epoch_seq (BE)`, `[12..16] = item_count (BE)`.
#[must_use]
pub const fn encode_integrity_4_wire(
    kind_tag: u8,
    epoch_seq: u32,
    item_count: u32,
) -> Option<[u8; 16]> {
    if kind_tag > 7 || epoch_seq == 0 {
        return None;
    }
    Some([
        INTEGRITY_4_WIRE_MAGIC[0],
        INTEGRITY_4_WIRE_MAGIC[1],
        INTEGRITY_4_WIRE_MAGIC[2],
        INTEGRITY_4_WIRE_MAGIC[3],
        INTEGRITY_4_WIRE_VERSION,
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

/// Decode a 16-byte `astream-integrity-4` shard wire snapshot header into `(kind_tag, epoch_seq, item_count)`.
#[must_use]
pub const fn decode_integrity_4_wire(buf: &[u8]) -> Option<(u8, u32, u32)> {
    let [b'A', b'I', b'0', b'4', INTEGRITY_4_WIRE_VERSION, kind_tag, 0, 0, a0, a1, a2, a3, b0, b1, b2, b3, ..] =
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
    fn integrity_4_wire_roundtrips_and_rejects_malformed() {
        let Some(frame) = encode_integrity_4_wire(2, 1_024, 19) else {
            panic!("valid astream-integrity-4 wire header should encode");
        };
        assert_eq!(decode_integrity_4_wire(&frame), Some((2, 1_024, 19)));
        assert_eq!(encode_integrity_4_wire(2, 0, 19), None);
        assert_eq!(encode_integrity_4_wire(8, 1_024, 19), None);
        let mut bad = frame;
        bad[4] = 9;
        assert_eq!(decode_integrity_4_wire(&bad), None);
    }
}
