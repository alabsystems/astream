// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Broker-native consistent `Cut` frontier across `ShardedBroker` bus records (`DESIGN-aterm-fabric.md` §10), pairwise causal dependency verifier, `bt_ms` skew envelope, held-gap cut guard, incarnation lease pin, and replay cursor. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod bt_skew_envelope;
pub mod bus_cut_frontier;
pub mod causal_dep_matrix;
pub mod held_gap_cut_guard;
pub mod incarnation_lease_cut;
pub mod replay_slice_cursor;

/// Four-byte magic prefix (`"ALNK"`) for a 16-byte `astream-link-cut` frontier wire header.
pub const LINK_CUT_WIRE_MAGIC: [u8; 4] = *b"ALNK";

/// Wire format version for `astream-link-cut` frontier headers.
pub const LINK_CUT_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `astream-link-cut` frontier wire header:
/// `[0..4] = b"ALNK"`, `[4] = version (1)`, `[5] = cut_mode_tag` (`0..=2`), `[6..8] = 0`,
/// `[8..12] = incarnation (BE)`, `[12..16] = frontier_seq (BE)`.
#[must_use]
pub const fn encode_link_cut_wire(
    cut_mode_tag: u8,
    incarnation: u32,
    frontier_seq: u32,
) -> Option<[u8; 16]> {
    if cut_mode_tag > 2 || incarnation == 0 {
        return None;
    }
    Some([
        LINK_CUT_WIRE_MAGIC[0],
        LINK_CUT_WIRE_MAGIC[1],
        LINK_CUT_WIRE_MAGIC[2],
        LINK_CUT_WIRE_MAGIC[3],
        LINK_CUT_WIRE_VERSION,
        cut_mode_tag,
        0,
        0,
        ((incarnation >> 24) & 0xFF) as u8,
        ((incarnation >> 16) & 0xFF) as u8,
        ((incarnation >> 8) & 0xFF) as u8,
        (incarnation & 0xFF) as u8,
        ((frontier_seq >> 24) & 0xFF) as u8,
        ((frontier_seq >> 16) & 0xFF) as u8,
        ((frontier_seq >> 8) & 0xFF) as u8,
        (frontier_seq & 0xFF) as u8,
    ])
}

/// Decode a 16-byte `astream-link-cut` frontier wire header into
/// `(cut_mode_tag, incarnation, frontier_seq)`.
#[must_use]
pub const fn decode_link_cut_wire(buf: &[u8]) -> Option<(u8, u32, u32)> {
    let [b'A', b'L', b'N', b'K', LINK_CUT_WIRE_VERSION, cut_mode_tag, 0, 0, i0, i1, i2, i3, f0, f1, f2, f3, ..] =
        *buf
    else {
        return None;
    };
    let incarnation = ((i0 as u32) << 24) | ((i1 as u32) << 16) | ((i2 as u32) << 8) | (i3 as u32);
    let frontier_seq = ((f0 as u32) << 24) | ((f1 as u32) << 16) | ((f2 as u32) << 8) | (f3 as u32);
    if cut_mode_tag > 2 || incarnation == 0 {
        return None;
    }
    Some((cut_mode_tag, incarnation, frontier_seq))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn link_cut_wire_roundtrips_and_rejects_zero_incarnation() {
        let Some(frame) = encode_link_cut_wire(1, 7, 1_024) else {
            panic!("valid link-cut frame should encode");
        };
        assert_eq!(decode_link_cut_wire(&frame), Some((1, 7, 1_024)));
        assert_eq!(encode_link_cut_wire(1, 0, 1_024), None);
        assert_eq!(encode_link_cut_wire(3, 7, 1_024), None);
        let mut bad = frame;
        bad[7] = 1;
        assert_eq!(decode_link_cut_wire(&bad), None);
    }
}
