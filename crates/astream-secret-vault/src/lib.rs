// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Ephemeral secret-lease scrub tracker, `astream-cap` `exp=` attenuation verifier, `REQUIREMENTS R6` `n-<hash>` identity-to-principal pin, monotone revocation filter, per-tab SSH-agent sign budget, and bearer-token log redactor. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod cap_attenuation_chain;
pub mod principal_key_pin;
pub mod redacted_debug_formatter;
pub mod revocation_epoch_list;
pub mod ssh_agent_forwarding_gate;
pub mod zeroize_lease_buffer;

/// Four-byte magic prefix (`"ASVT"`) for a 16-byte `astream-secret-vault` wire snapshot header.
pub const SECRET_VAULT_WIRE_MAGIC: [u8; 4] = *b"ASVT";

/// Wire format version for `astream-secret-vault` snapshot headers.
pub const SECRET_VAULT_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `astream-secret-vault` wire snapshot header:
/// `[0..4] = b"ASVT"`, `[4] = version (1)`, `[5] = scope_tag` (`0..=3`), `[6..8] = 0`,
/// `[8..12] = epoch (BE)`, `[12..16] = attenuation_depth (BE)`.
#[must_use]
pub const fn encode_secret_vault_wire(
    scope_tag: u8,
    epoch: u32,
    attenuation_depth: u32,
) -> Option<[u8; 16]> {
    if scope_tag > 3 || epoch == 0 {
        return None;
    }
    Some([
        SECRET_VAULT_WIRE_MAGIC[0],
        SECRET_VAULT_WIRE_MAGIC[1],
        SECRET_VAULT_WIRE_MAGIC[2],
        SECRET_VAULT_WIRE_MAGIC[3],
        SECRET_VAULT_WIRE_VERSION,
        scope_tag,
        0,
        0,
        ((epoch >> 24) & 0xFF) as u8,
        ((epoch >> 16) & 0xFF) as u8,
        ((epoch >> 8) & 0xFF) as u8,
        (epoch & 0xFF) as u8,
        ((attenuation_depth >> 24) & 0xFF) as u8,
        ((attenuation_depth >> 16) & 0xFF) as u8,
        ((attenuation_depth >> 8) & 0xFF) as u8,
        (attenuation_depth & 0xFF) as u8,
    ])
}

/// Decode a 16-byte `astream-secret-vault` wire snapshot header into `(scope_tag, epoch, attenuation_depth)`.
#[must_use]
pub const fn decode_secret_vault_wire(buf: &[u8]) -> Option<(u8, u32, u32)> {
    let [b'A', b'S', b'V', b'T', SECRET_VAULT_WIRE_VERSION, scope_tag, 0, 0, a0, a1, a2, a3, b0, b1, b2, b3, ..] =
        *buf
    else {
        return None;
    };
    let epoch = ((a0 as u32) << 24) | ((a1 as u32) << 16) | ((a2 as u32) << 8) | (a3 as u32);
    let attenuation_depth =
        ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32);
    if scope_tag > 3 || epoch == 0 {
        return None;
    }
    Some((scope_tag, epoch, attenuation_depth))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn secret_vault_wire_roundtrips_and_rejects_malformed() {
        let Some(frame) = encode_secret_vault_wire(1, 12, 3) else {
            panic!("valid astream-secret-vault wire header should encode");
        };
        assert_eq!(decode_secret_vault_wire(&frame), Some((1, 12, 3)));
        assert_eq!(encode_secret_vault_wire(1, 0, 3), None);
        assert_eq!(encode_secret_vault_wire(4, 12, 3), None);
        let mut bad = frame;
        bad[4] = 9;
        assert_eq!(decode_secret_vault_wire(&bad), None);
    }
}
