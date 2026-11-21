// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! External identity authority: SSH-agent certificate validity chain, OIDC JWT `nbf`/`exp` claims window, overlapping host-key rollover, peer allowlist epoch reload, certificate revocation serial check, and principal key rotation ledger. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod allowlist_epoch_reload;
pub mod cert_revocation_serial;
pub mod host_key_rollover;
pub mod oidc_claims_window;
pub mod principal_key_rotation;
pub mod ssh_cert_validity;

/// Four-byte magic prefix (`"AEXT"`) for a 16-byte `astream-ext-authority` wire snapshot header.
pub const EXT_AUTHORITY_WIRE_MAGIC: [u8; 4] = *b"AEXT";

/// Wire format version for `astream-ext-authority` snapshot headers.
pub const EXT_AUTHORITY_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `astream-ext-authority` wire snapshot header:
/// `[0..4] = b"AEXT"`, `[4] = version (1)`, `[5] = auth_tag` (`0..=3`), `[6..8] = 0`,
/// `[8..12] = allowlist_epoch (BE)`, `[12..16] = serial_floor (BE)`.
#[must_use]
pub const fn encode_ext_authority_wire(
    auth_tag: u8,
    allowlist_epoch: u32,
    serial_floor: u32,
) -> Option<[u8; 16]> {
    if auth_tag > 3 || allowlist_epoch == 0 {
        return None;
    }
    Some([
        EXT_AUTHORITY_WIRE_MAGIC[0],
        EXT_AUTHORITY_WIRE_MAGIC[1],
        EXT_AUTHORITY_WIRE_MAGIC[2],
        EXT_AUTHORITY_WIRE_MAGIC[3],
        EXT_AUTHORITY_WIRE_VERSION,
        auth_tag,
        0,
        0,
        ((allowlist_epoch >> 24) & 0xFF) as u8,
        ((allowlist_epoch >> 16) & 0xFF) as u8,
        ((allowlist_epoch >> 8) & 0xFF) as u8,
        (allowlist_epoch & 0xFF) as u8,
        ((serial_floor >> 24) & 0xFF) as u8,
        ((serial_floor >> 16) & 0xFF) as u8,
        ((serial_floor >> 8) & 0xFF) as u8,
        (serial_floor & 0xFF) as u8,
    ])
}

/// Decode a 16-byte `astream-ext-authority` wire snapshot header into `(auth_tag, allowlist_epoch, serial_floor)`.
#[must_use]
pub const fn decode_ext_authority_wire(buf: &[u8]) -> Option<(u8, u32, u32)> {
    let [b'A', b'E', b'X', b'T', EXT_AUTHORITY_WIRE_VERSION, auth_tag, 0, 0, a0, a1, a2, a3, b0, b1, b2, b3, ..] =
        *buf
    else {
        return None;
    };
    let allowlist_epoch =
        ((a0 as u32) << 24) | ((a1 as u32) << 16) | ((a2 as u32) << 8) | (a3 as u32);
    let serial_floor = ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32);
    if auth_tag > 3 || allowlist_epoch == 0 {
        return None;
    }
    Some((auth_tag, allowlist_epoch, serial_floor))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ext_authority_wire_roundtrips_and_rejects_malformed() {
        let Some(frame) = encode_ext_authority_wire(1, 9, 1042) else {
            panic!("valid astream-ext-authority wire header should encode");
        };
        assert_eq!(decode_ext_authority_wire(&frame), Some((1, 9, 1042)));
        assert_eq!(encode_ext_authority_wire(1, 0, 1042), None);
        assert_eq!(encode_ext_authority_wire(4, 9, 1042), None);
        let mut bad = frame;
        bad[4] = 9;
        assert_eq!(decode_ext_authority_wire(&bad), None);
    }
}
