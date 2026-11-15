// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm` 5-target cross-cell (`stock-check.sh` / `aterm-verify`) matrix tracker, `ring` `links` override pin, `-D warnings` zero-finding gate, `^trust:` exclusion check, Windows Unix-target scoping, and `0/1/2` exit triad. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod exit_verdict_triad;
pub mod five_cell_matrix;
pub mod ring_links_pin;
pub mod stock_not_trust_guard;
pub mod win_unix_target_skip;
pub mod zero_cell_warnings;

/// Four-byte magic prefix (`"AXCL"`) for a 16-byte `astream-cross-cells` wire snapshot header.
pub const CROSS_CELLS_WIRE_MAGIC: [u8; 4] = *b"AXCL";

/// Wire format version for `astream-cross-cells` snapshot headers.
pub const CROSS_CELLS_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `astream-cross-cells` wire snapshot header:
/// `[0..4] = b"AXCL"`, `[4] = version (1)`, `[5] = verdict_tag` (`0..=2`), `[6..8] = 0`,
/// `[8..12] = cells_checked (BE)`, `[12..16] = warnings_denied (BE)`.
#[must_use]
pub const fn encode_cross_cells_wire(
    verdict_tag: u8,
    cells_checked: u32,
    warnings_denied: u32,
) -> Option<[u8; 16]> {
    if verdict_tag > 2 || cells_checked == 0 {
        return None;
    }
    Some([
        CROSS_CELLS_WIRE_MAGIC[0],
        CROSS_CELLS_WIRE_MAGIC[1],
        CROSS_CELLS_WIRE_MAGIC[2],
        CROSS_CELLS_WIRE_MAGIC[3],
        CROSS_CELLS_WIRE_VERSION,
        verdict_tag,
        0,
        0,
        ((cells_checked >> 24) & 0xFF) as u8,
        ((cells_checked >> 16) & 0xFF) as u8,
        ((cells_checked >> 8) & 0xFF) as u8,
        (cells_checked & 0xFF) as u8,
        ((warnings_denied >> 24) & 0xFF) as u8,
        ((warnings_denied >> 16) & 0xFF) as u8,
        ((warnings_denied >> 8) & 0xFF) as u8,
        (warnings_denied & 0xFF) as u8,
    ])
}

/// Decode a 16-byte `astream-cross-cells` wire snapshot header into `(verdict_tag, cells_checked, warnings_denied)`.
#[must_use]
pub const fn decode_cross_cells_wire(buf: &[u8]) -> Option<(u8, u32, u32)> {
    let [b'A', b'X', b'C', b'L', CROSS_CELLS_WIRE_VERSION, verdict_tag, 0, 0, a0, a1, a2, a3, b0, b1, b2, b3, ..] =
        *buf
    else {
        return None;
    };
    let cells_checked =
        ((a0 as u32) << 24) | ((a1 as u32) << 16) | ((a2 as u32) << 8) | (a3 as u32);
    let warnings_denied =
        ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32);
    if verdict_tag > 2 || cells_checked == 0 {
        return None;
    }
    Some((verdict_tag, cells_checked, warnings_denied))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cross_cells_wire_roundtrips_and_rejects_malformed() {
        let Some(frame) = encode_cross_cells_wire(1, 12, 12) else {
            panic!("valid astream-cross-cells wire header should encode");
        };
        assert_eq!(decode_cross_cells_wire(&frame), Some((1, 12, 12)));
        assert_eq!(encode_cross_cells_wire(1, 0, 12), None);
        assert_eq!(encode_cross_cells_wire(3, 12, 12), None);
        let mut bad = frame;
        bad[4] = 9;
        assert_eq!(decode_cross_cells_wire(&bad), None);
    }
}
