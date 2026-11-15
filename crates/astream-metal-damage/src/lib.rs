// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! macOS Metal terminal dirty-row damage bitset, 120Hz ProMotion adaptive frame pacer, 3-slot `MTLBuffer` in-flight ring, keystroke-reset cursor blink FSM, crisp procedural U+2500..U+259F box-drawing router, and luminance contrast floor. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod box_drawing_procedural;
pub mod contrast_apca_floor;
pub mod cursor_blink_epoch;
pub mod dirty_row_bitset;
pub mod promotion_120hz_pacer;
pub mod triple_buffer_ring;

/// Four-byte magic prefix (`"AMTL"`) for a 16-byte `astream-metal-damage` wire snapshot header.
pub const METAL_DAMAGE_WIRE_MAGIC: [u8; 4] = *b"AMTL";

/// Wire format version for `astream-metal-damage` snapshot headers.
pub const METAL_DAMAGE_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `astream-metal-damage` wire snapshot header:
/// `[0..4] = b"AMTL"`, `[4] = version (1)`, `[5] = pace_tag` (`0..=3`), `[6..8] = 0`,
/// `[8..12] = dirty_rows (BE)`, `[12..16] = frame_seq (BE)`.
#[must_use]
pub const fn encode_metal_damage_wire(
    pace_tag: u8,
    dirty_rows: u32,
    frame_seq: u32,
) -> Option<[u8; 16]> {
    if pace_tag > 3 || dirty_rows == 0 {
        return None;
    }
    Some([
        METAL_DAMAGE_WIRE_MAGIC[0],
        METAL_DAMAGE_WIRE_MAGIC[1],
        METAL_DAMAGE_WIRE_MAGIC[2],
        METAL_DAMAGE_WIRE_MAGIC[3],
        METAL_DAMAGE_WIRE_VERSION,
        pace_tag,
        0,
        0,
        ((dirty_rows >> 24) & 0xFF) as u8,
        ((dirty_rows >> 16) & 0xFF) as u8,
        ((dirty_rows >> 8) & 0xFF) as u8,
        (dirty_rows & 0xFF) as u8,
        ((frame_seq >> 24) & 0xFF) as u8,
        ((frame_seq >> 16) & 0xFF) as u8,
        ((frame_seq >> 8) & 0xFF) as u8,
        (frame_seq & 0xFF) as u8,
    ])
}

/// Decode a 16-byte `astream-metal-damage` wire snapshot header into `(pace_tag, dirty_rows, frame_seq)`.
#[must_use]
pub const fn decode_metal_damage_wire(buf: &[u8]) -> Option<(u8, u32, u32)> {
    let [b'A', b'M', b'T', b'L', METAL_DAMAGE_WIRE_VERSION, pace_tag, 0, 0, a0, a1, a2, a3, b0, b1, b2, b3, ..] =
        *buf
    else {
        return None;
    };
    let dirty_rows = ((a0 as u32) << 24) | ((a1 as u32) << 16) | ((a2 as u32) << 8) | (a3 as u32);
    let frame_seq = ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32);
    if pace_tag > 3 || dirty_rows == 0 {
        return None;
    }
    Some((pace_tag, dirty_rows, frame_seq))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn metal_damage_wire_roundtrips_and_rejects_malformed() {
        let Some(frame) = encode_metal_damage_wire(1, 48, 1200) else {
            panic!("valid astream-metal-damage wire header should encode");
        };
        assert_eq!(decode_metal_damage_wire(&frame), Some((1, 48, 1200)));
        assert_eq!(encode_metal_damage_wire(1, 0, 1200), None);
        assert_eq!(encode_metal_damage_wire(4, 48, 1200), None);
        let mut bad = frame;
        bad[4] = 9;
        assert_eq!(decode_metal_damage_wire(&bad), None);
    }
}
