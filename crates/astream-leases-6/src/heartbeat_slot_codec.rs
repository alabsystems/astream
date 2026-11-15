// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Fixed 24-byte `"ASHB"` fabric node heartbeat wire codec (`Astream.Wire.TlaHeartbeatSlotCodec`).
//!
//! Stack-allocated, zero-heap, zero-indexing wire frame carrying `(epoch, head_offset,
//! active_sessions, load_permille)` for `aterm-link` / `astream-broker` node liveness beacons
//! with `0` `runtime_checked` and `0` `unknown` obligations in `astream-wire`.

#[cfg(clean_islands)]
#[path = "heartbeat_slot_codec_island.rs"]
mod heartbeat_slot_codec_island;
#[cfg(clean_islands)]
pub use heartbeat_slot_codec_island::{hb_epoch_advance, hb_load_clamp};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn hb_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn hb_load_clamp(cand_load: u64, max_load: u64) -> u64 {
    if cand_load < max_load {
        cand_load
    } else {
        max_load
    }
}

contract_fn! {
    /// Verified check that `load_permille <= 1000`, linked via `clean-kernel-defeq`
    /// to `hb_load_within_scale_isl`.
    #[must_use]
    pub const fn hb_load_within_scale(load_permille: u64) -> bool
    clauses [ensures result == (load_permille <= 1000)]
    {
        load_permille <= 1000
    }
}

/// 4-byte wire magic for v1 fabric heartbeat frames (`"ASHB"`).
pub const V1_HEARTBEAT_MAGIC: [u8; 4] = *b"ASHB";

/// Exact encoded byte size of `V1HeartbeatFrame` (`4 + 8 + 8 + 2 + 2 = 24`).
pub const V1_HEARTBEAT_BYTES: usize = 24;

/// Maximum normalized load in per-mille (`1000` = 100.0% core capacity).
pub const MAX_LOAD_PERMILLE: u16 = 1_000;

/// Decode error for `V1HeartbeatFrame`.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum HeartbeatWireError {
    InvalidLength { got: usize },
    BadMagic,
    LoadOutOfScale { got: u16 },
}

/// Stack-only 24-byte fabric node heartbeat frame.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct V1HeartbeatFrame {
    pub epoch: u64,
    pub head_offset: u64,
    pub active_sessions: u16,
    pub load_permille: u16,
}

impl V1HeartbeatFrame {
    /// Construct a normalized heartbeat frame with `load_permille` clamped to `0..=1000`.
    #[must_use]
    pub const fn normalized(
        epoch: u64,
        head_offset: u64,
        active_sessions: u16,
        load_permille: u16,
    ) -> Self {
        let clamped_load = hb_load_clamp(load_permille as u64, MAX_LOAD_PERMILLE as u64) as u16;
        Self {
            epoch,
            head_offset,
            active_sessions,
            load_permille: clamped_load,
        }
    }

    /// Advance from a prior heartbeat, fencing stale epochs (`cand_epoch < self.epoch`).
    #[must_use]
    pub const fn advance_from(
        self,
        cand_epoch: u64,
        cand_head: u64,
        active_sessions: u16,
        cand_load_permille: u16,
    ) -> Self {
        if cand_epoch < self.epoch {
            return self;
        }
        let ep = hb_epoch_advance(self.epoch, cand_epoch);
        let ld = hb_load_clamp(cand_load_permille as u64, MAX_LOAD_PERMILLE as u64) as u16;
        Self {
            epoch: ep,
            head_offset: cand_head,
            active_sessions,
            load_permille: ld,
        }
    }

    /// Encode into a fixed 24-byte array.
    #[must_use]
    pub const fn encode(self) -> [u8; V1_HEARTBEAT_BYTES] {
        let ld = hb_load_clamp(self.load_permille as u64, MAX_LOAD_PERMILLE as u64) as u16;
        let [m0, m1, m2, m3] = V1_HEARTBEAT_MAGIC;
        let [e0, e1, e2, e3, e4, e5, e6, e7] = self.epoch.to_be_bytes();
        let [h0, h1, h2, h3, h4, h5, h6, h7] = self.head_offset.to_be_bytes();
        let [s0, s1] = self.active_sessions.to_be_bytes();
        let [l0, l1] = ld.to_be_bytes();
        [
            m0, m1, m2, m3, e0, e1, e2, e3, e4, e5, e6, e7, h0, h1, h2, h3, h4, h5, h6, h7, s0, s1,
            l0, l1,
        ]
    }

    /// Decode a 24-byte `"ASHB"` frame, rejecting out-of-scale `load_permille > 1000`.
    pub const fn decode(bytes: &[u8]) -> Result<Self, HeartbeatWireError> {
        let &[m0, m1, m2, m3, e0, e1, e2, e3, e4, e5, e6, e7, h0, h1, h2, h3, h4, h5, h6, h7, s0, s1, l0, l1] =
            bytes
        else {
            return Err(HeartbeatWireError::InvalidLength { got: bytes.len() });
        };
        if m0 != b'A' || m1 != b'S' || m2 != b'H' || m3 != b'B' {
            return Err(HeartbeatWireError::BadMagic);
        }
        let load = u16::from_be_bytes([l0, l1]);
        if !hb_load_within_scale(load as u64) {
            return Err(HeartbeatWireError::LoadOutOfScale { got: load });
        }
        Ok(Self {
            epoch: u64::from_be_bytes([e0, e1, e2, e3, e4, e5, e6, e7]),
            head_offset: u64::from_be_bytes([h0, h1, h2, h3, h4, h5, h6, h7]),
            active_sessions: u16::from_be_bytes([s0, s1]),
            load_permille: load,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encodes_decodes_and_rejects_over_1000_permille() {
        let hb = V1HeartbeatFrame::normalized(7, 4_096, 12, 1_500);
        assert_eq!(hb.load_permille, 1_000);
        let raw = hb.encode();
        assert_eq!(V1HeartbeatFrame::decode(&raw), Ok(hb));

        let mut bad = raw;
        bad[22] = 0x04;
        bad[23] = 0x00; // 1024 > 1000
        assert_eq!(
            V1HeartbeatFrame::decode(&bad),
            Err(HeartbeatWireError::LoadOutOfScale { got: 1024 })
        );
    }
}
