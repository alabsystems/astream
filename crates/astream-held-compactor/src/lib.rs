// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Crash-safe `<log>.held` `SLACK_DIV = 4` byte-cut planner, `2x` churn rewrite trigger, `Response::Gap` (`0x87`) range/count ledger, restart-durable first-seen stamps, person-vs-node mail hold policy, and `<log>.compact` intent FSM. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod churn_rewrite_trigger;
pub mod compact_intent_fsm;
pub mod first_seen_age_stamp;
pub mod gap_notice_ledger;
pub mod person_vs_node_mail;
pub mod slack_div_quarter_cut;

/// Four-byte magic prefix (`"AHCP"`) for a 16-byte `astream-held-compactor` wire snapshot header.
pub const HELD_COMPACTOR_WIRE_MAGIC: [u8; 4] = *b"AHCP";

/// Wire format version for `astream-held-compactor` snapshot headers.
pub const HELD_COMPACTOR_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `astream-held-compactor` wire snapshot header:
/// `[0..4] = b"AHCP"`, `[4] = version (1)`, `[5] = class_tag` (`0..=3`), `[6..8] = 0`,
/// `[8..12] = reclaimed_kb (BE)`, `[12..16] = cut_seq (BE)`.
#[must_use]
pub const fn encode_held_compactor_wire(
    class_tag: u8,
    reclaimed_kb: u32,
    cut_seq: u32,
) -> Option<[u8; 16]> {
    if class_tag > 3 || reclaimed_kb == 0 {
        return None;
    }
    Some([
        HELD_COMPACTOR_WIRE_MAGIC[0],
        HELD_COMPACTOR_WIRE_MAGIC[1],
        HELD_COMPACTOR_WIRE_MAGIC[2],
        HELD_COMPACTOR_WIRE_MAGIC[3],
        HELD_COMPACTOR_WIRE_VERSION,
        class_tag,
        0,
        0,
        ((reclaimed_kb >> 24) & 0xFF) as u8,
        ((reclaimed_kb >> 16) & 0xFF) as u8,
        ((reclaimed_kb >> 8) & 0xFF) as u8,
        (reclaimed_kb & 0xFF) as u8,
        ((cut_seq >> 24) & 0xFF) as u8,
        ((cut_seq >> 16) & 0xFF) as u8,
        ((cut_seq >> 8) & 0xFF) as u8,
        (cut_seq & 0xFF) as u8,
    ])
}

/// Decode a 16-byte `astream-held-compactor` wire snapshot header into `(class_tag, reclaimed_kb, cut_seq)`.
#[must_use]
pub const fn decode_held_compactor_wire(buf: &[u8]) -> Option<(u8, u32, u32)> {
    let [b'A', b'H', b'C', b'P', HELD_COMPACTOR_WIRE_VERSION, class_tag, 0, 0, a0, a1, a2, a3, b0, b1, b2, b3, ..] =
        *buf
    else {
        return None;
    };
    let reclaimed_kb = ((a0 as u32) << 24) | ((a1 as u32) << 16) | ((a2 as u32) << 8) | (a3 as u32);
    let cut_seq = ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32);
    if class_tag > 3 || reclaimed_kb == 0 {
        return None;
    }
    Some((class_tag, reclaimed_kb, cut_seq))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn held_compactor_wire_roundtrips_and_rejects_malformed() {
        let Some(frame) = encode_held_compactor_wire(1, 8192, 64) else {
            panic!("valid astream-held-compactor wire header should encode");
        };
        assert_eq!(decode_held_compactor_wire(&frame), Some((1, 8192, 64)));
        assert_eq!(encode_held_compactor_wire(1, 0, 64), None);
        assert_eq!(encode_held_compactor_wire(4, 8192, 64), None);
        let mut bad = frame;
        bad[4] = 9;
        assert_eq!(decode_held_compactor_wire(&bad), None);
    }
}
