// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! 0-RTT `SpeculativeTerminal` cooked-shell line predictor, `ProgramPredictor` deterministic rule learner, POSIX `ECHOCTL` caret expander, `>= 0.80` watermark-squash hit-rate gate, tentative underline span, and divergence rollback. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod caret_ctrl_expander;
pub mod cooked_line_predictor;
pub mod divergence_epoch_rollback;
pub mod program_rule_learner;
pub mod underline_tentative_span;
pub mod watermark_squash_gate;

/// Four-byte magic prefix (`"AECH"`) for a 16-byte `astream-speculative-echo` wire snapshot header.
pub const SPECULATIVE_ECHO_WIRE_MAGIC: [u8; 4] = *b"AECH";

/// Wire format version for `astream-speculative-echo` snapshot headers.
pub const SPECULATIVE_ECHO_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `astream-speculative-echo` wire snapshot header:
/// `[0..4] = b"AECH"`, `[4] = version (1)`, `[5] = mode_tag` (`0..=3`), `[6..8] = 0`,
/// `[8..12] = predicted_epoch (BE)`, `[12..16] = tentative_cols (BE)`.
#[must_use]
pub const fn encode_speculative_echo_wire(
    mode_tag: u8,
    predicted_epoch: u32,
    tentative_cols: u32,
) -> Option<[u8; 16]> {
    if mode_tag > 3 || predicted_epoch == 0 {
        return None;
    }
    Some([
        SPECULATIVE_ECHO_WIRE_MAGIC[0],
        SPECULATIVE_ECHO_WIRE_MAGIC[1],
        SPECULATIVE_ECHO_WIRE_MAGIC[2],
        SPECULATIVE_ECHO_WIRE_MAGIC[3],
        SPECULATIVE_ECHO_WIRE_VERSION,
        mode_tag,
        0,
        0,
        ((predicted_epoch >> 24) & 0xFF) as u8,
        ((predicted_epoch >> 16) & 0xFF) as u8,
        ((predicted_epoch >> 8) & 0xFF) as u8,
        (predicted_epoch & 0xFF) as u8,
        ((tentative_cols >> 24) & 0xFF) as u8,
        ((tentative_cols >> 16) & 0xFF) as u8,
        ((tentative_cols >> 8) & 0xFF) as u8,
        (tentative_cols & 0xFF) as u8,
    ])
}

/// Decode a 16-byte `astream-speculative-echo` wire snapshot header into `(mode_tag, predicted_epoch, tentative_cols)`.
#[must_use]
pub const fn decode_speculative_echo_wire(buf: &[u8]) -> Option<(u8, u32, u32)> {
    let [b'A', b'E', b'C', b'H', SPECULATIVE_ECHO_WIRE_VERSION, mode_tag, 0, 0, a0, a1, a2, a3, b0, b1, b2, b3, ..] =
        *buf
    else {
        return None;
    };
    let predicted_epoch =
        ((a0 as u32) << 24) | ((a1 as u32) << 16) | ((a2 as u32) << 8) | (a3 as u32);
    let tentative_cols =
        ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32);
    if mode_tag > 3 || predicted_epoch == 0 {
        return None;
    }
    Some((mode_tag, predicted_epoch, tentative_cols))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn speculative_echo_wire_roundtrips_and_rejects_malformed() {
        let Some(frame) = encode_speculative_echo_wire(1, 77, 16) else {
            panic!("valid astream-speculative-echo wire header should encode");
        };
        assert_eq!(decode_speculative_echo_wire(&frame), Some((1, 77, 16)));
        assert_eq!(encode_speculative_echo_wire(1, 0, 16), None);
        assert_eq!(encode_speculative_echo_wire(4, 77, 16), None);
        let mut bad = frame;
        bad[4] = 9;
        assert_eq!(decode_speculative_echo_wire(&bad), None);
    }
}
