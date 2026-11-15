// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Kitty `CSI u` lossless modifier decoder, multi-key leader-chord timeout FSM, macOS IME `markedText` composition fence, remote-stall key-repeat governor, SGR `?1006` mouse coordinate clamp, and `?1004` focus debouncer. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod chord_timeout_fsm;
pub mod csi_u_modifier_mask;
pub mod focus_event_debouncer;
pub mod ime_preedit_fence;
pub mod mouse_sgr_1006_clamp;
pub mod repeat_rate_governor;

/// Four-byte magic prefix (`"AKBD"`) for a 16-byte `astream-keybind-chord` wire snapshot header.
pub const KEYBIND_CHORD_WIRE_MAGIC: [u8; 4] = *b"AKBD";

/// Wire format version for `astream-keybind-chord` snapshot headers.
pub const KEYBIND_CHORD_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `astream-keybind-chord` wire snapshot header:
/// `[0..4] = b"AKBD"`, `[4] = version (1)`, `[5] = mod_tag` (`0..=3`), `[6..8] = 0`,
/// `[8..12] = chord_ms (BE)`, `[12..16] = keycode (BE)`.
#[must_use]
pub const fn encode_keybind_chord_wire(
    mod_tag: u8,
    chord_ms: u32,
    keycode: u32,
) -> Option<[u8; 16]> {
    if mod_tag > 3 || chord_ms == 0 {
        return None;
    }
    Some([
        KEYBIND_CHORD_WIRE_MAGIC[0],
        KEYBIND_CHORD_WIRE_MAGIC[1],
        KEYBIND_CHORD_WIRE_MAGIC[2],
        KEYBIND_CHORD_WIRE_MAGIC[3],
        KEYBIND_CHORD_WIRE_VERSION,
        mod_tag,
        0,
        0,
        ((chord_ms >> 24) & 0xFF) as u8,
        ((chord_ms >> 16) & 0xFF) as u8,
        ((chord_ms >> 8) & 0xFF) as u8,
        (chord_ms & 0xFF) as u8,
        ((keycode >> 24) & 0xFF) as u8,
        ((keycode >> 16) & 0xFF) as u8,
        ((keycode >> 8) & 0xFF) as u8,
        (keycode & 0xFF) as u8,
    ])
}

/// Decode a 16-byte `astream-keybind-chord` wire snapshot header into `(mod_tag, chord_ms, keycode)`.
#[must_use]
pub const fn decode_keybind_chord_wire(buf: &[u8]) -> Option<(u8, u32, u32)> {
    let [b'A', b'K', b'B', b'D', KEYBIND_CHORD_WIRE_VERSION, mod_tag, 0, 0, a0, a1, a2, a3, b0, b1, b2, b3, ..] =
        *buf
    else {
        return None;
    };
    let chord_ms = ((a0 as u32) << 24) | ((a1 as u32) << 16) | ((a2 as u32) << 8) | (a3 as u32);
    let keycode = ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32);
    if mod_tag > 3 || chord_ms == 0 {
        return None;
    }
    Some((mod_tag, chord_ms, keycode))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keybind_chord_wire_roundtrips_and_rejects_malformed() {
        let Some(frame) = encode_keybind_chord_wire(1, 250, 97) else {
            panic!("valid astream-keybind-chord wire header should encode");
        };
        assert_eq!(decode_keybind_chord_wire(&frame), Some((1, 250, 97)));
        assert_eq!(encode_keybind_chord_wire(1, 0, 97), None);
        assert_eq!(encode_keybind_chord_wire(4, 250, 97), None);
        let mut bad = frame;
        bad[4] = 9;
        assert_eq!(decode_keybind_chord_wire(&bad), None);
    }
}
