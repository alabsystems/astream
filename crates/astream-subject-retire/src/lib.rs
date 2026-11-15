// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Distinct-subject budget & `Request::Retire` protocol (`docs/ROADMAP.md` §2): `max_subjects_per_producer` quota meter, `last_owner` carried-charge authorization, live/durable will target retirement blocker, `COMMIT_TAG_RETIRE` (`u64::MAX`) marker validator, `PendingRetire` visible-head overlay, and uncarried-cut retirement refusal. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod active_will_retire_guard;
pub mod commit_tag_retire_mark;
pub mod last_owner_charge_auth;
pub mod pending_retire_overlay;
pub mod producer_subject_quota;
pub mod uncarried_cut_refusal;

/// Four-byte magic prefix (`"ASRT"`) for a 16-byte `astream-subject-retire` wire snapshot header.
pub const SUBJECT_RETIRE_WIRE_MAGIC: [u8; 4] = *b"ASRT";

/// Wire format version for `astream-subject-retire` snapshot headers.
pub const SUBJECT_RETIRE_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `astream-subject-retire` wire snapshot header:
/// `[0..4] = b"ASRT"`, `[4] = version (1)`, `[5] = retire_tag` (`0..=3`), `[6..8] = 0`,
/// `[8..12] = log_base (BE)`, `[12..16] = active_wills (BE)`.
#[must_use]
pub const fn encode_subject_retire_wire(
    retire_tag: u8,
    log_base: u32,
    active_wills: u32,
) -> Option<[u8; 16]> {
    if retire_tag > 3 || log_base == 0 {
        return None;
    }
    Some([
        SUBJECT_RETIRE_WIRE_MAGIC[0],
        SUBJECT_RETIRE_WIRE_MAGIC[1],
        SUBJECT_RETIRE_WIRE_MAGIC[2],
        SUBJECT_RETIRE_WIRE_MAGIC[3],
        SUBJECT_RETIRE_WIRE_VERSION,
        retire_tag,
        0,
        0,
        ((log_base >> 24) & 0xFF) as u8,
        ((log_base >> 16) & 0xFF) as u8,
        ((log_base >> 8) & 0xFF) as u8,
        (log_base & 0xFF) as u8,
        ((active_wills >> 24) & 0xFF) as u8,
        ((active_wills >> 16) & 0xFF) as u8,
        ((active_wills >> 8) & 0xFF) as u8,
        (active_wills & 0xFF) as u8,
    ])
}

/// Decode a 16-byte `astream-subject-retire` wire snapshot header into `(retire_tag, log_base, active_wills)`.
#[must_use]
pub const fn decode_subject_retire_wire(buf: &[u8]) -> Option<(u8, u32, u32)> {
    let [b'A', b'S', b'R', b'T', SUBJECT_RETIRE_WIRE_VERSION, retire_tag, 0, 0, a0, a1, a2, a3, b0, b1, b2, b3, ..] =
        *buf
    else {
        return None;
    };
    let log_base = ((a0 as u32) << 24) | ((a1 as u32) << 16) | ((a2 as u32) << 8) | (a3 as u32);
    let active_wills = ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32);
    if retire_tag > 3 || log_base == 0 {
        return None;
    }
    Some((retire_tag, log_base, active_wills))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn subject_retire_wire_roundtrips_and_rejects_malformed() {
        let Some(frame) = encode_subject_retire_wire(1, 2048, 2) else {
            panic!("valid astream-subject-retire wire header should encode");
        };
        assert_eq!(decode_subject_retire_wire(&frame), Some((1, 2048, 2)));
        assert_eq!(encode_subject_retire_wire(1, 0, 2), None);
        assert_eq!(encode_subject_retire_wire(4, 2048, 2), None);
        let mut bad = frame;
        bad[4] = 9;
        assert_eq!(decode_subject_retire_wire(&bad), None);
    }
}
