// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm harness agy` multi-pool (`Gemini`/`Claude`/`Gpt`) 5-hour & weekly quota ledgers, `pick` pool rotator, pre-fanout worker admission gate, window reset clock, capability-tier floor, and burn-rate forecast. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod burn_rate_forecast;
pub mod cooldown_reset_clock;
pub mod fanout_admission_gate;
pub mod model_pick_rotator;
pub mod pool_window_ledger;
pub mod tier_fallback_policy;

/// Four-byte magic prefix (`"AAGY"`) for a 16-byte `astream-agy-quota` pool window wire header.
pub const AGY_QUOTA_WIRE_MAGIC: [u8; 4] = *b"AAGY";

/// Wire format version for `astream-agy-quota` pool window headers.
pub const AGY_QUOTA_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `astream-agy-quota` pool window wire header:
/// `[0..4] = b"AAGY"`, `[4] = version (1)`, `[5] = pool_tag` (`0..=2`), `[6..8] = 0`,
/// `[8..12] = five_hour_bps (BE)`, `[12..16] = weekly_bps (BE)`.
#[must_use]
pub const fn encode_agy_quota_wire(
    pool_tag: u8,
    five_hour_bps: u32,
    weekly_bps: u32,
) -> Option<[u8; 16]> {
    if pool_tag > 2 || five_hour_bps > 10_000 || weekly_bps > 10_000 {
        return None;
    }
    Some([
        AGY_QUOTA_WIRE_MAGIC[0],
        AGY_QUOTA_WIRE_MAGIC[1],
        AGY_QUOTA_WIRE_MAGIC[2],
        AGY_QUOTA_WIRE_MAGIC[3],
        AGY_QUOTA_WIRE_VERSION,
        pool_tag,
        0,
        0,
        ((five_hour_bps >> 24) & 0xFF) as u8,
        ((five_hour_bps >> 16) & 0xFF) as u8,
        ((five_hour_bps >> 8) & 0xFF) as u8,
        (five_hour_bps & 0xFF) as u8,
        ((weekly_bps >> 24) & 0xFF) as u8,
        ((weekly_bps >> 16) & 0xFF) as u8,
        ((weekly_bps >> 8) & 0xFF) as u8,
        (weekly_bps & 0xFF) as u8,
    ])
}

/// Decode a 16-byte `astream-agy-quota` pool window wire header into
/// `(pool_tag, five_hour_bps, weekly_bps)`.
#[must_use]
pub const fn decode_agy_quota_wire(buf: &[u8]) -> Option<(u8, u32, u32)> {
    let [b'A', b'A', b'G', b'Y', AGY_QUOTA_WIRE_VERSION, pool_tag, 0, 0, h0, h1, h2, h3, w0, w1, w2, w3, ..] =
        *buf
    else {
        return None;
    };
    let five_hour_bps =
        ((h0 as u32) << 24) | ((h1 as u32) << 16) | ((h2 as u32) << 8) | (h3 as u32);
    let weekly_bps = ((w0 as u32) << 24) | ((w1 as u32) << 16) | ((w2 as u32) << 8) | (w3 as u32);
    if pool_tag > 2 || five_hour_bps > 10_000 || weekly_bps > 10_000 {
        return None;
    }
    Some((pool_tag, five_hour_bps, weekly_bps))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn agy_quota_wire_roundtrips_and_rejects_out_of_range_bps() {
        let Some(frame) = encode_agy_quota_wire(1, 7_500, 9_200) else {
            panic!("valid quota frame should encode");
        };
        assert_eq!(decode_agy_quota_wire(&frame), Some((1, 7_500, 9_200)));
        assert_eq!(encode_agy_quota_wire(3, 5_000, 5_000), None);
        assert_eq!(encode_agy_quota_wire(0, 10_001, 5_000), None);
        let mut bad = frame;
        bad[6] = 1;
        assert_eq!(decode_agy_quota_wire(&bad), None);
    }
}
