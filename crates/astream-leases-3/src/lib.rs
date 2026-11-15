// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Boot-scoped incarnation leases, WAN RTT window autoscaling, and quorum fence protocols (shard 3 of 6, batches 77..78). forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod bracketed_paste_sanitizer;
pub mod incarnation_lease_fence;
pub mod kitty_enhancement_ring;
pub mod land_turn_auditor;
pub mod mark_durable_trailer;
pub mod prebind_watermark_guard;

/// Four-byte magic prefix (`"AL03"`) for a 32-byte `astream-leases-3` shard wire checkpoint header.
pub const LEASES_3_WIRE_MAGIC: [u8; 4] = *b"AL03";

/// Wire format version for `astream-leases-3` shard checkpoint headers.
pub const LEASES_3_WIRE_VERSION: u8 = 1;

/// Encode a 32-byte `astream-leases-3` shard wire checkpoint header:
/// `[0..4] = b"AL03"`, `[4] = version (1)`, `[5] = kind_tag` (`0..=7`), `[6..8] = 0`,
/// `[8..16] = epoch_seq (BE)`, `[16..24] = committed_offset (BE)`, `[24..32] = digest_fold (BE)`.
#[must_use]
pub const fn encode_leases_3_wire(
    kind_tag: u8,
    epoch_seq: u64,
    committed_offset: u64,
    digest_fold: u64,
) -> Option<[u8; 32]> {
    if kind_tag > 7 || epoch_seq == 0 {
        return None;
    }
    Some([
        LEASES_3_WIRE_MAGIC[0],
        LEASES_3_WIRE_MAGIC[1],
        LEASES_3_WIRE_MAGIC[2],
        LEASES_3_WIRE_MAGIC[3],
        LEASES_3_WIRE_VERSION,
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
        ((committed_offset >> 56) & 0xFF) as u8,
        ((committed_offset >> 48) & 0xFF) as u8,
        ((committed_offset >> 40) & 0xFF) as u8,
        ((committed_offset >> 32) & 0xFF) as u8,
        ((committed_offset >> 24) & 0xFF) as u8,
        ((committed_offset >> 16) & 0xFF) as u8,
        ((committed_offset >> 8) & 0xFF) as u8,
        (committed_offset & 0xFF) as u8,
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

/// Decode a 32-byte `astream-leases-3` shard wire checkpoint header into
/// `(kind_tag, epoch_seq, committed_offset, digest_fold)`.
#[must_use]
pub const fn decode_leases_3_wire(buf: &[u8]) -> Option<(u8, u64, u64, u64)> {
    let [b'A', b'L', b'0', b'3', LEASES_3_WIRE_VERSION, kind_tag, 0, 0, a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3, b4, b5, b6, b7, c0, c1, c2, c3, c4, c5, c6, c7, ..] =
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
    let committed_offset = ((b0 as u64) << 56)
        | ((b1 as u64) << 48)
        | ((b2 as u64) << 40)
        | ((b3 as u64) << 32)
        | ((b4 as u64) << 24)
        | ((b5 as u64) << 16)
        | ((b6 as u64) << 8)
        | (b7 as u64);
    let digest_fold = ((c0 as u64) << 56)
        | ((c1 as u64) << 48)
        | ((c2 as u64) << 40)
        | ((c3 as u64) << 32)
        | ((c4 as u64) << 24)
        | ((c5 as u64) << 16)
        | ((c6 as u64) << 8)
        | (c7 as u64);
    if kind_tag > 7 || epoch_seq == 0 {
        return None;
    }
    Some((kind_tag, epoch_seq, committed_offset, digest_fold))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn leases_3_wire_roundtrips_and_rejects_malformed() {
        let Some(frame) = encode_leases_3_wire(3, 4_096, 65_536, 0x0102_0304_0506_0708) else {
            panic!("valid astream-leases-3 wire header should encode");
        };
        assert_eq!(
            decode_leases_3_wire(&frame),
            Some((3, 4_096, 65_536, 0x0102_0304_0506_0708))
        );
        assert_eq!(encode_leases_3_wire(3, 0, 65_536, 1), None);
        assert_eq!(encode_leases_3_wire(8, 4_096, 65_536, 1), None);
        let mut bad = frame;
        bad[4] = 9;
        assert_eq!(decode_leases_3_wire(&bad), None);
    }
}
