// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `atpkg-abrew` native compatibility guards refusing `--real`/`--no-reroute`/`ABREW_REAL`, confining unpack paths to the `atpkg` prefix, sealing bottle SHA-256 digests, routing supported casks, scoping `bundle`, and latching disabled stubs. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod bottle_sha256_seal;
pub mod brewfile_bundle_mode;
pub mod cask_kind_router;
pub mod disabled_stub_latch;
pub mod prefix_confinement_gate;
pub mod real_brew_bypass_refusal;

/// Four-byte magic prefix (`"ABRW"`) for a 16-byte `astream-abrew-bottle` wire snapshot header.
pub const ABREW_BOTTLE_WIRE_MAGIC: [u8; 4] = *b"ABRW";

/// Wire format version for `astream-abrew-bottle` snapshot headers.
pub const ABREW_BOTTLE_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `astream-abrew-bottle` wire snapshot header:
/// `[0..4] = b"ABRW"`, `[4] = version (1)`, `[5] = cask_tag` (`0..=3`), `[6..8] = 0`,
/// `[8..12] = bottle_kb (BE)`, `[12..16] = installed_count (BE)`.
#[must_use]
pub const fn encode_abrew_bottle_wire(
    cask_tag: u8,
    bottle_kb: u32,
    installed_count: u32,
) -> Option<[u8; 16]> {
    if cask_tag > 3 || bottle_kb == 0 {
        return None;
    }
    Some([
        ABREW_BOTTLE_WIRE_MAGIC[0],
        ABREW_BOTTLE_WIRE_MAGIC[1],
        ABREW_BOTTLE_WIRE_MAGIC[2],
        ABREW_BOTTLE_WIRE_MAGIC[3],
        ABREW_BOTTLE_WIRE_VERSION,
        cask_tag,
        0,
        0,
        ((bottle_kb >> 24) & 0xFF) as u8,
        ((bottle_kb >> 16) & 0xFF) as u8,
        ((bottle_kb >> 8) & 0xFF) as u8,
        (bottle_kb & 0xFF) as u8,
        ((installed_count >> 24) & 0xFF) as u8,
        ((installed_count >> 16) & 0xFF) as u8,
        ((installed_count >> 8) & 0xFF) as u8,
        (installed_count & 0xFF) as u8,
    ])
}

/// Decode a 16-byte `astream-abrew-bottle` wire snapshot header into `(cask_tag, bottle_kb, installed_count)`.
#[must_use]
pub const fn decode_abrew_bottle_wire(buf: &[u8]) -> Option<(u8, u32, u32)> {
    let [b'A', b'B', b'R', b'W', ABREW_BOTTLE_WIRE_VERSION, cask_tag, 0, 0, a0, a1, a2, a3, b0, b1, b2, b3, ..] =
        *buf
    else {
        return None;
    };
    let bottle_kb = ((a0 as u32) << 24) | ((a1 as u32) << 16) | ((a2 as u32) << 8) | (a3 as u32);
    let installed_count =
        ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32);
    if cask_tag > 3 || bottle_kb == 0 {
        return None;
    }
    Some((cask_tag, bottle_kb, installed_count))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn abrew_bottle_wire_roundtrips_and_rejects_malformed() {
        let Some(frame) = encode_abrew_bottle_wire(1, 4096, 18) else {
            panic!("valid astream-abrew-bottle wire header should encode");
        };
        assert_eq!(decode_abrew_bottle_wire(&frame), Some((1, 4096, 18)));
        assert_eq!(encode_abrew_bottle_wire(1, 0, 18), None);
        assert_eq!(encode_abrew_bottle_wire(4, 4096, 18), None);
        let mut bad = frame;
        bad[4] = 9;
        assert_eq!(decode_abrew_bottle_wire(&bad), None);
    }
}
