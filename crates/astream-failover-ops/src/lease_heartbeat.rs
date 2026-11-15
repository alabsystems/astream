// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! CRC-framed `ALHB\x01` leader lease heartbeat wire codec and deterministic follower
//! failover detector (`ROADMAP.md` line 106, `DESIGN-aterm-fabric.md` §15 line 4075,
//! `Astream.Failover.TlaLeaseHeartbeat`).
//!
//! Wraps leader lease heartbeats inside [`astream_wire::Frame`] (`CRC-32/IEEE`) carrying
//! `(epoch, leader_id, bt_ms, lease_ttl_ms, visible_head, durable_head)` and tracks follower
//! lease liveness without trusting unsynchronized wall clocks across nodes:
//! - Advances `expiry_bt_ms` monotonically via Clean-origin `lease_hb_expiry_advance`.
//! - Clamps consecutive missed-tick probes via `lease_hb_miss_clamp` (`<= MAX_MISSED_HEARTBEATS`).
//! - Triggers autonomous candidate election iff both `lease_hb_expired(local_mono_ms, expiry_mono_ms)`
//!   and `missed_ticks >= election_miss_threshold` hold, preventing spurious single-packet failovers.

use astream_wire::frame::{decode_frame_slice, encode_frame_header};

#[cfg(clean_islands)]
#[path = "lease_heartbeat_island.rs"]
mod lease_heartbeat_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lease_hb_miss_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lease_hb_expiry_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use lease_heartbeat_island::{lease_hb_expiry_advance, lease_hb_miss_clamp};

/// Wire magic for `ALHB` v1 leader lease heartbeat payloads.
pub const LEASE_HB_MAGIC: [u8; 4] = *b"ALHB";
/// Wire format version `1`.
pub const LEASE_HB_VERSION: u8 = 1;
/// Maximum consecutive missed heartbeat ticks tracked (`lease_hb_miss_clamp`).
pub const MAX_MISSED_HEARTBEATS: u64 = 16;

contract_fn! {
    /// Verified expiry predicate (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `lease_hb_expired_isl`.
    #[must_use]
    pub const fn lease_hb_expired(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Decoded `ALHB\x01` leader lease heartbeat payload.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LeaderHeartbeat {
    pub epoch: u64,
    pub leader_id: u64,
    pub leader_bt_ms: u64,
    pub lease_ttl_ms: u64,
    pub visible_head: u64,
    pub durable_head: u64,
}

fn read_hb_u64(p: &[u8], off: usize) -> Result<u64, &'static str> {
    let end = match off.checked_add(8) {
        Some(e) => e,
        None => return Err("heartbeat offset overflow"),
    };
    let s = match p.get(off..end) {
        Some(sl) => sl,
        None => return Err("truncated heartbeat field"),
    };
    let mut b = [0u8; 8];
    b.copy_from_slice(s);
    Ok(u64::from_le_bytes(b))
}

#[inline(never)]
fn frame_hb_header(p: &[u8; 56]) -> Result<[u8; 12], astream_wire::FrameError> {
    encode_frame_header(p)
}

impl LeaderHeartbeat {
    /// Encodes the heartbeat inside a CRC-32/IEEE [`astream_wire::Frame`].
    pub fn encode_framed(&self) -> Result<Vec<u8>, &'static str> {
        if self.lease_ttl_ms == 0 || self.durable_head > self.visible_head {
            return Err("invalid heartbeat lease_ttl_ms or durable_head");
        }
        let mut p = [0u8; 56];
        if let Some(s) = p.get_mut(0..4) {
            s.copy_from_slice(&LEASE_HB_MAGIC);
        }
        if let Some(slot) = p.get_mut(4) {
            *slot = LEASE_HB_VERSION;
        }
        if let Some(s) = p.get_mut(8..16) {
            s.copy_from_slice(&self.epoch.to_le_bytes());
        }
        if let Some(s) = p.get_mut(16..24) {
            s.copy_from_slice(&self.leader_id.to_le_bytes());
        }
        if let Some(s) = p.get_mut(24..32) {
            s.copy_from_slice(&self.leader_bt_ms.to_le_bytes());
        }
        if let Some(s) = p.get_mut(32..40) {
            s.copy_from_slice(&self.lease_ttl_ms.to_le_bytes());
        }
        if let Some(s) = p.get_mut(40..48) {
            s.copy_from_slice(&self.visible_head.to_le_bytes());
        }
        if let Some(s) = p.get_mut(48..56) {
            s.copy_from_slice(&self.durable_head.to_le_bytes());
        }
        let hdr = match frame_hb_header(&p) {
            Ok(h) => h,
            Err(_) => return Err("frame encode failed"),
        };
        let mut out = Vec::new();
        out.extend_from_slice(&hdr);
        out.extend_from_slice(&p);
        Ok(out)
    }

    /// Decodes and CRC-verifies a framed `ALHB\x01` heartbeat.
    pub fn decode_framed(bytes: &[u8]) -> Result<Self, &'static str> {
        let (p, consumed) = match decode_frame_slice(bytes) {
            Ok(Some(pair)) => pair,
            Ok(None) => return Err("truncated heartbeat frame"),
            Err(_) => return Err("corrupt or truncated heartbeat frame"),
        };
        if consumed != bytes.len() || p.len() != 56 {
            return Err("unexpected heartbeat frame size");
        }
        if p.get(0..4) != Some(LEASE_HB_MAGIC.as_slice()) || p.get(4) != Some(&LEASE_HB_VERSION) {
            return Err("bad ALHB magic or version");
        }
        if p.get(5..8) != Some(&[0, 0, 0]) {
            return Err("non-zero ALHB reserved bytes");
        }
        let epoch = read_hb_u64(p, 8)?;
        let leader_id = read_hb_u64(p, 16)?;
        let leader_bt_ms = read_hb_u64(p, 24)?;
        let lease_ttl_ms = read_hb_u64(p, 32)?;
        let visible_head = read_hb_u64(p, 40)?;
        let durable_head = read_hb_u64(p, 48)?;
        if lease_ttl_ms == 0 || durable_head > visible_head {
            return Err("invalid heartbeat lease_ttl_ms or durable_head");
        }
        Ok(Self {
            epoch,
            leader_id,
            leader_bt_ms,
            lease_ttl_ms,
            visible_head,
            durable_head,
        })
    }
}

/// Follower lease monitor state machine.
#[derive(Debug, Clone)]
pub struct HeartbeatLeaseTracker {
    highest_epoch: u64,
    leader_id: Option<u64>,
    expiry_mono_ms: u64,
    missed_ticks: u64,
    election_miss_threshold: u64,
}

impl HeartbeatLeaseTracker {
    /// Creates a follower lease tracker requiring `election_miss_threshold` missed probes past `expiry_mono_ms`.
    #[must_use]
    pub const fn new(election_miss_threshold: u64) -> Self {
        let clamped = lease_hb_miss_clamp(election_miss_threshold, MAX_MISSED_HEARTBEATS);
        Self {
            highest_epoch: 0,
            leader_id: None,
            expiry_mono_ms: 0,
            missed_ticks: 0,
            election_miss_threshold: if clamped == 0 { 1 } else { clamped },
        }
    }

    #[must_use]
    pub const fn highest_epoch(&self) -> u64 {
        self.highest_epoch
    }

    #[must_use]
    pub const fn expiry_mono_ms(&self) -> u64 {
        self.expiry_mono_ms
    }

    #[must_use]
    pub const fn missed_ticks(&self) -> u64 {
        self.missed_ticks
    }

    /// Processes an incoming leader heartbeat at follower monotonic clock `now_mono_ms`.
    /// Fences stale epochs (`hb.epoch < highest_epoch`) fail-closed!
    pub fn observe_heartbeat(
        &mut self,
        hb: &LeaderHeartbeat,
        now_mono_ms: u64,
    ) -> Result<u64, &'static str> {
        if hb.lease_ttl_ms == 0 || hb.durable_head > hb.visible_head {
            return Err("invalid heartbeat lease_ttl_ms or durable_head");
        }
        if hb.epoch < self.highest_epoch {
            return Err("stale leader epoch fenced");
        }
        let new_epoch = hb.epoch > self.highest_epoch;
        if !new_epoch {
            if let Some(cur) = self.leader_id {
                if cur != hb.leader_id {
                    return Err("conflicting leader_id in same epoch");
                }
            }
        }
        self.highest_epoch = hb.epoch;
        self.leader_id = Some(hb.leader_id);
        self.missed_ticks = 0;
        let cand_expiry = now_mono_ms.saturating_add(hb.lease_ttl_ms);
        if new_epoch {
            self.expiry_mono_ms = cand_expiry;
        } else {
            self.expiry_mono_ms = lease_hb_expiry_advance(self.expiry_mono_ms, cand_expiry);
        }
        Ok(self.expiry_mono_ms)
    }

    /// Evaluates a periodic daemon tick at `now_mono_ms`; returns `true` iff the follower
    /// should trigger autonomous candidate election (`ROADMAP.md` line 106).
    pub fn poll_election_due(&mut self, now_mono_ms: u64) -> bool {
        if !lease_hb_expired(now_mono_ms, self.expiry_mono_ms) {
            self.missed_ticks = 0;
            return false;
        }
        let next_miss = self.missed_ticks.saturating_add(1);
        self.missed_ticks = lease_hb_miss_clamp(next_miss, MAX_MISSED_HEARTBEATS);
        lease_hb_expired(self.missed_ticks, self.election_miss_threshold)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn framed_heartbeat_roundtrips_fences_stale_leaders_and_triggers_failover_after_threshold() {
        let hb = LeaderHeartbeat {
            epoch: 3,
            leader_id: 101,
            leader_bt_ms: 50_000,
            lease_ttl_ms: 500,
            visible_head: 120,
            durable_head: 118,
        };
        let mut bytes = hb.encode_framed().unwrap();
        assert_eq!(LeaderHeartbeat::decode_framed(&bytes).unwrap(), hb);
        bytes[20] ^= 0xFF; // corrupt CRC payload
        assert!(LeaderHeartbeat::decode_framed(&bytes).is_err());

        let mut tracker = HeartbeatLeaseTracker::new(3);
        assert_eq!(tracker.observe_heartbeat(&hb, 1_000).unwrap(), 1_500);
        // Stale epoch 2 zombie leader is fenced!
        let stale = LeaderHeartbeat {
            epoch: 2,
            leader_id: 99,
            ..hb
        };
        assert!(tracker.observe_heartbeat(&stale, 1_100).is_err());

        // Before expiry (1_499 < 1_500), election is not due.
        assert!(!tracker.poll_election_due(1_499));
        // At 1_500..1_700: 1st and 2nd missed ticks dampen transient jitter; 3rd triggers failover!
        assert!(!tracker.poll_election_due(1_500));
        assert!(!tracker.poll_election_due(1_600));
        assert!(tracker.poll_election_due(1_700));
        assert_eq!(tracker.missed_ticks(), 3);
    }
}
