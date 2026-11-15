// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `targo` explicit verification-lane enforcer (`--unverified` vs `trust`), stale `trust` toolchain symlink detector (`aterm pkg repair`), per-target availability router, `rustup` PATH pin verifier, disk cache reclaimer, and index pin monotonicity. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod build_cache_reclaimer;
pub mod index_pin_monotonicity;
pub mod path_toolchain_pin;
pub mod stale_trust_link_probe;
pub mod target_availability_gate;
pub mod targo_lane_enforcer;

/// Four-byte magic prefix (`"APKG"`) for a 16-byte `astream-atpkg-toolchain` lane pin wire header.
pub const ATPKG_TOOLCHAIN_WIRE_MAGIC: [u8; 4] = *b"APKG";

/// Wire format version for `astream-atpkg-toolchain` lane pin headers.
pub const ATPKG_TOOLCHAIN_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `astream-atpkg-toolchain` lane pin wire header:
/// `[0..4] = b"APKG"`, `[4] = version (1)`, `[5] = lane_tag` (`0 = trust`, `1 = unverified`, `2 = stock`),
/// `[6..8] = 0`, `[8..12] = store_rev (BE)`, `[12..16] = reclaimed_mb (BE)`.
#[must_use]
pub const fn encode_atpkg_toolchain_wire(
    lane_tag: u8,
    store_rev: u32,
    reclaimed_mb: u32,
) -> Option<[u8; 16]> {
    if lane_tag > 2 || (lane_tag == 0 && store_rev == 0) {
        return None;
    }
    Some([
        ATPKG_TOOLCHAIN_WIRE_MAGIC[0],
        ATPKG_TOOLCHAIN_WIRE_MAGIC[1],
        ATPKG_TOOLCHAIN_WIRE_MAGIC[2],
        ATPKG_TOOLCHAIN_WIRE_MAGIC[3],
        ATPKG_TOOLCHAIN_WIRE_VERSION,
        lane_tag,
        0,
        0,
        ((store_rev >> 24) & 0xFF) as u8,
        ((store_rev >> 16) & 0xFF) as u8,
        ((store_rev >> 8) & 0xFF) as u8,
        (store_rev & 0xFF) as u8,
        ((reclaimed_mb >> 24) & 0xFF) as u8,
        ((reclaimed_mb >> 16) & 0xFF) as u8,
        ((reclaimed_mb >> 8) & 0xFF) as u8,
        (reclaimed_mb & 0xFF) as u8,
    ])
}

/// Decode a 16-byte `astream-atpkg-toolchain` lane pin wire header into
/// `(lane_tag, store_rev, reclaimed_mb)`.
#[must_use]
pub const fn decode_atpkg_toolchain_wire(buf: &[u8]) -> Option<(u8, u32, u32)> {
    let [b'A', b'P', b'K', b'G', ATPKG_TOOLCHAIN_WIRE_VERSION, lane_tag, 0, 0, s0, s1, s2, s3, r0, r1, r2, r3, ..] =
        *buf
    else {
        return None;
    };
    let store_rev = ((s0 as u32) << 24) | ((s1 as u32) << 16) | ((s2 as u32) << 8) | (s3 as u32);
    let reclaimed_mb = ((r0 as u32) << 24) | ((r1 as u32) << 16) | ((r2 as u32) << 8) | (r3 as u32);
    if lane_tag > 2 || (lane_tag == 0 && store_rev == 0) {
        return None;
    }
    Some((lane_tag, store_rev, reclaimed_mb))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn atpkg_toolchain_wire_roundtrips_and_requires_nonzero_trust_rev() {
        let Some(frame) = encode_atpkg_toolchain_wire(0, 15_698, 512) else {
            panic!("valid toolchain frame should encode");
        };
        assert_eq!(decode_atpkg_toolchain_wire(&frame), Some((0, 15_698, 512)));
        assert_eq!(encode_atpkg_toolchain_wire(0, 0, 0), None);
        assert_eq!(encode_atpkg_toolchain_wire(3, 15_698, 0), None);
        let mut bad = frame;
        bad[4] = 9;
        assert_eq!(decode_atpkg_toolchain_wire(&bad), None);
    }
}
