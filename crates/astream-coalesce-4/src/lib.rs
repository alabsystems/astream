// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Macaroon discharge, Last radix cursors, SIGMA identity binding, damage coalescing, and restart fences (shard 4 of 6, batches 55..56). forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod agy_pool_rotator;
pub mod disk_headroom_waiter;
pub mod env_var_stripper;
pub mod escalation_table_planner;
pub mod keepalive_probe_budget;
pub mod needs_you_banner_arbiter;

/// Four-byte magic prefix (`"AC04"`) for a 48-byte `astream-coalesce-4` shard wire seal header.
pub const COALESCE_4_WIRE_MAGIC: [u8; 4] = *b"AC04";

/// Wire format version for `astream-coalesce-4` shard seal headers.
pub const COALESCE_4_WIRE_VERSION: u8 = 1;

/// Encode a 48-byte `astream-coalesce-4` shard wire seal header:
/// `[0..4] = b"AC04"`, `[4] = version (1)`, `[5] = kind_tag` (`0..=7`), `[6..8] = 0`,
/// followed by five big-endian `u64` words (`epoch_seq`, `base_offset`, `head_offset`,
/// `window_mask`, `digest_fold`).
#[must_use]
pub const fn encode_coalesce_4_wire(
    kind_tag: u8,
    epoch_seq: u64,
    base_offset: u64,
    head_offset: u64,
    window_mask: u64,
    digest_fold: u64,
) -> Option<[u8; 48]> {
    if kind_tag > 7 || epoch_seq == 0 || head_offset < base_offset {
        return None;
    }
    Some([
        COALESCE_4_WIRE_MAGIC[0],
        COALESCE_4_WIRE_MAGIC[1],
        COALESCE_4_WIRE_MAGIC[2],
        COALESCE_4_WIRE_MAGIC[3],
        COALESCE_4_WIRE_VERSION,
        kind_tag,
        0,
        0,
        ((epoch_seq >> 56) & 0xFF) as u8,
        ((epoch_seq >> 48) & 0xFF) as u8,
        ((epoch_seq >> 40) & 0xFF) as u8,
        ((epoch_seq >> 32) & 0xFF) as u8,
        ((epoch_seq >> 24) & 0xFF) as u8,
        ((epoch_seq >> 16) & 0xFF) as u8,
        ((epoch_seq >> 8) & 0xFF) as u8,
        (epoch_seq & 0xFF) as u8,
        ((base_offset >> 56) & 0xFF) as u8,
        ((base_offset >> 48) & 0xFF) as u8,
        ((base_offset >> 40) & 0xFF) as u8,
        ((base_offset >> 32) & 0xFF) as u8,
        ((base_offset >> 24) & 0xFF) as u8,
        ((base_offset >> 16) & 0xFF) as u8,
        ((base_offset >> 8) & 0xFF) as u8,
        (base_offset & 0xFF) as u8,
        ((head_offset >> 56) & 0xFF) as u8,
        ((head_offset >> 48) & 0xFF) as u8,
        ((head_offset >> 40) & 0xFF) as u8,
        ((head_offset >> 32) & 0xFF) as u8,
        ((head_offset >> 24) & 0xFF) as u8,
        ((head_offset >> 16) & 0xFF) as u8,
        ((head_offset >> 8) & 0xFF) as u8,
        (head_offset & 0xFF) as u8,
        ((window_mask >> 56) & 0xFF) as u8,
        ((window_mask >> 48) & 0xFF) as u8,
        ((window_mask >> 40) & 0xFF) as u8,
        ((window_mask >> 32) & 0xFF) as u8,
        ((window_mask >> 24) & 0xFF) as u8,
        ((window_mask >> 16) & 0xFF) as u8,
        ((window_mask >> 8) & 0xFF) as u8,
        (window_mask & 0xFF) as u8,
        ((digest_fold >> 56) & 0xFF) as u8,
        ((digest_fold >> 48) & 0xFF) as u8,
        ((digest_fold >> 40) & 0xFF) as u8,
        ((digest_fold >> 32) & 0xFF) as u8,
        ((digest_fold >> 24) & 0xFF) as u8,
        ((digest_fold >> 16) & 0xFF) as u8,
        ((digest_fold >> 8) & 0xFF) as u8,
        (digest_fold & 0xFF) as u8,
    ])
}

/// Decode a 48-byte `astream-coalesce-4` shard wire seal header into
/// `(kind_tag, epoch_seq, base_offset, head_offset, window_mask, digest_fold)`.
#[must_use]
pub const fn decode_coalesce_4_wire(buf: &[u8]) -> Option<(u8, u64, u64, u64, u64, u64)> {
    let [b'A', b'C', b'0', b'4', COALESCE_4_WIRE_VERSION, kind_tag, 0, 0, a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3, b4, b5, b6, b7, c0, c1, c2, c3, c4, c5, c6, c7, d0, d1, d2, d3, d4, d5, d6, d7, e0, e1, e2, e3, e4, e5, e6, e7, ..] =
        *buf
    else {
        return None;
    };
    let epoch_seq = ((a0 as u64) << 56)
        | ((a1 as u64) << 48)
        | ((a2 as u64) << 40)
        | ((a3 as u64) << 32)
        | ((a4 as u64) << 24)
        | ((a5 as u64) << 16)
        | ((a6 as u64) << 8)
        | (a7 as u64);
    let base_offset = ((b0 as u64) << 56)
        | ((b1 as u64) << 48)
        | ((b2 as u64) << 40)
        | ((b3 as u64) << 32)
        | ((b4 as u64) << 24)
        | ((b5 as u64) << 16)
        | ((b6 as u64) << 8)
        | (b7 as u64);
    let head_offset = ((c0 as u64) << 56)
        | ((c1 as u64) << 48)
        | ((c2 as u64) << 40)
        | ((c3 as u64) << 32)
        | ((c4 as u64) << 24)
        | ((c5 as u64) << 16)
        | ((c6 as u64) << 8)
        | (c7 as u64);
    let window_mask = ((d0 as u64) << 56)
        | ((d1 as u64) << 48)
        | ((d2 as u64) << 40)
        | ((d3 as u64) << 32)
        | ((d4 as u64) << 24)
        | ((d5 as u64) << 16)
        | ((d6 as u64) << 8)
        | (d7 as u64);
    let digest_fold = ((e0 as u64) << 56)
        | ((e1 as u64) << 48)
        | ((e2 as u64) << 40)
        | ((e3 as u64) << 32)
        | ((e4 as u64) << 24)
        | ((e5 as u64) << 16)
        | ((e6 as u64) << 8)
        | (e7 as u64);
    if kind_tag > 7 || epoch_seq == 0 || head_offset < base_offset {
        return None;
    }
    Some((
        kind_tag,
        epoch_seq,
        base_offset,
        head_offset,
        window_mask,
        digest_fold,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn coalesce_4_wire_roundtrips_and_rejects_malformed() {
        let Some(frame) = encode_coalesce_4_wire(
            4,
            2_048,
            1_000,
            1_500,
            0xFFFF_0000_FFFF_0001,
            0x0102_0304_0506_0708,
        ) else {
            panic!("valid astream-coalesce-4 wire seal header should encode");
        };
        assert_eq!(
            decode_coalesce_4_wire(&frame),
            Some((
                4,
                2_048,
                1_000,
                1_500,
                0xFFFF_0000_FFFF_0001,
                0x0102_0304_0506_0708,
            ))
        );
        assert_eq!(encode_coalesce_4_wire(4, 0, 1_000, 1_500, 1, 1), None);
        assert_eq!(encode_coalesce_4_wire(4, 2_048, 1_600, 1_500, 1, 1), None);
        assert_eq!(encode_coalesce_4_wire(8, 2_048, 1_000, 1_500, 1, 1), None);
        let mut bad = frame;
        bad[4] = 9;
        assert_eq!(decode_coalesce_4_wire(&bad), None);
    }
}
