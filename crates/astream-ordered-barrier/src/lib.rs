// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Apple `F_BARRIERFSYNC` `Durability::Ordered` boot-volume `fstat` resolver, Darwin refusal `Strict` fallback latch, escalated `visible_head` hold, failed-flush `Lossy` poison, `100ms` horizon coalescer, and same-batch `/a/bind` matcher. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod barrier_refusal_fallback;
pub mod boot_volume_fstat;
pub mod escalation_hold_head;
pub mod failed_flush_poison;
pub mod horizon_coalesce_timer;
pub mod pre_bind_batch_match;

/// Four-byte magic prefix (`"AOBR"`) for a 16-byte `astream-ordered-barrier` wire snapshot header.
pub const ORDERED_BARRIER_WIRE_MAGIC: [u8; 4] = *b"AOBR";

/// Wire format version for `astream-ordered-barrier` snapshot headers.
pub const ORDERED_BARRIER_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `astream-ordered-barrier` wire snapshot header:
/// `[0..4] = b"AOBR"`, `[4] = version (1)`, `[5] = barrier_tag` (`0..=3`), `[6..8] = 0`,
/// `[8..12] = horizon_seq (BE)`, `[12..16] = held_batches (BE)`.
#[must_use]
pub const fn encode_ordered_barrier_wire(
    barrier_tag: u8,
    horizon_seq: u32,
    held_batches: u32,
) -> Option<[u8; 16]> {
    if barrier_tag > 3 || horizon_seq == 0 {
        return None;
    }
    Some([
        ORDERED_BARRIER_WIRE_MAGIC[0],
        ORDERED_BARRIER_WIRE_MAGIC[1],
        ORDERED_BARRIER_WIRE_MAGIC[2],
        ORDERED_BARRIER_WIRE_MAGIC[3],
        ORDERED_BARRIER_WIRE_VERSION,
        barrier_tag,
        0,
        0,
        ((horizon_seq >> 24) & 0xFF) as u8,
        ((horizon_seq >> 16) & 0xFF) as u8,
        ((horizon_seq >> 8) & 0xFF) as u8,
        (horizon_seq & 0xFF) as u8,
        ((held_batches >> 24) & 0xFF) as u8,
        ((held_batches >> 16) & 0xFF) as u8,
        ((held_batches >> 8) & 0xFF) as u8,
        (held_batches & 0xFF) as u8,
    ])
}

/// Decode a 16-byte `astream-ordered-barrier` wire snapshot header into `(barrier_tag, horizon_seq, held_batches)`.
#[must_use]
pub const fn decode_ordered_barrier_wire(buf: &[u8]) -> Option<(u8, u32, u32)> {
    let [b'A', b'O', b'B', b'R', ORDERED_BARRIER_WIRE_VERSION, barrier_tag, 0, 0, a0, a1, a2, a3, b0, b1, b2, b3, ..] =
        *buf
    else {
        return None;
    };
    let horizon_seq = ((a0 as u32) << 24) | ((a1 as u32) << 16) | ((a2 as u32) << 8) | (a3 as u32);
    let held_batches = ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32);
    if barrier_tag > 3 || horizon_seq == 0 {
        return None;
    }
    Some((barrier_tag, horizon_seq, held_batches))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ordered_barrier_wire_roundtrips_and_rejects_malformed() {
        let Some(frame) = encode_ordered_barrier_wire(1, 900, 4) else {
            panic!("valid astream-ordered-barrier wire header should encode");
        };
        assert_eq!(decode_ordered_barrier_wire(&frame), Some((1, 900, 4)));
        assert_eq!(encode_ordered_barrier_wire(1, 0, 4), None);
        assert_eq!(encode_ordered_barrier_wire(4, 900, 4), None);
        let mut bad = frame;
        bad[4] = 9;
        assert_eq!(decode_ordered_barrier_wire(&bad), None);
    }
}
