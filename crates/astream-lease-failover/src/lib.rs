// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Autonomous lease-heartbeat replica failover daemon: leader lease TTL expiry clock, quorum witness ballot counter, epoch-fenced automatic replica promotion, zombie-leader stale-epoch write fence, divergent-tail truncation point, and follower catch-up lag admission gate. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod divergent_tail_trunc;
pub mod epoch_auto_promote;
pub mod follower_lag_admission;
pub mod leader_lease_ttl;
pub mod quorum_witness_ballot;
pub mod zombie_leader_fence;

/// Four-byte magic prefix (`"ALFO"`) for a 16-byte `astream-lease-failover` wire snapshot header.
pub const LEASE_FAILOVER_WIRE_MAGIC: [u8; 4] = *b"ALFO";

/// Wire format version for `astream-lease-failover` snapshot headers.
pub const LEASE_FAILOVER_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `astream-lease-failover` wire snapshot header:
/// `[0..4] = b"ALFO"`, `[4] = version (1)`, `[5] = role_tag` (`0..=3`), `[6..8] = 0`,
/// `[8..12] = ballot_epoch (BE)`, `[12..16] = ttl_ms (BE)`.
#[must_use]
pub const fn encode_lease_failover_wire(
    role_tag: u8,
    ballot_epoch: u32,
    ttl_ms: u32,
) -> Option<[u8; 16]> {
    if role_tag > 3 || ballot_epoch == 0 {
        return None;
    }
    Some([
        LEASE_FAILOVER_WIRE_MAGIC[0],
        LEASE_FAILOVER_WIRE_MAGIC[1],
        LEASE_FAILOVER_WIRE_MAGIC[2],
        LEASE_FAILOVER_WIRE_MAGIC[3],
        LEASE_FAILOVER_WIRE_VERSION,
        role_tag,
        0,
        0,
        ((ballot_epoch >> 24) & 0xFF) as u8,
        ((ballot_epoch >> 16) & 0xFF) as u8,
        ((ballot_epoch >> 8) & 0xFF) as u8,
        (ballot_epoch & 0xFF) as u8,
        ((ttl_ms >> 24) & 0xFF) as u8,
        ((ttl_ms >> 16) & 0xFF) as u8,
        ((ttl_ms >> 8) & 0xFF) as u8,
        (ttl_ms & 0xFF) as u8,
    ])
}

/// Decode a 16-byte `astream-lease-failover` wire snapshot header into `(role_tag, ballot_epoch, ttl_ms)`.
#[must_use]
pub const fn decode_lease_failover_wire(buf: &[u8]) -> Option<(u8, u32, u32)> {
    let [b'A', b'L', b'F', b'O', LEASE_FAILOVER_WIRE_VERSION, role_tag, 0, 0, a0, a1, a2, a3, b0, b1, b2, b3, ..] =
        *buf
    else {
        return None;
    };
    let ballot_epoch = ((a0 as u32) << 24) | ((a1 as u32) << 16) | ((a2 as u32) << 8) | (a3 as u32);
    let ttl_ms = ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32);
    if role_tag > 3 || ballot_epoch == 0 {
        return None;
    }
    Some((role_tag, ballot_epoch, ttl_ms))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lease_failover_wire_roundtrips_and_rejects_malformed() {
        let Some(frame) = encode_lease_failover_wire(1, 19, 5000) else {
            panic!("valid astream-lease-failover wire header should encode");
        };
        assert_eq!(decode_lease_failover_wire(&frame), Some((1, 19, 5000)));
        assert_eq!(encode_lease_failover_wire(1, 0, 5000), None);
        assert_eq!(encode_lease_failover_wire(4, 19, 5000), None);
        let mut bad = frame;
        bad[4] = 9;
        assert_eq!(decode_lease_failover_wire(&bad), None);
    }
}
