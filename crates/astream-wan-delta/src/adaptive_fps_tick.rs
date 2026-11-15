// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! RTT + unacked-bytes adaptive WAN frame-rate governor (`16 ms` 60 Hz .. `250 ms` 4 Hz)
//! preventing terminal bufferbloat over cellular/satellite links (`Astream.WanDelta.TlaAdaptiveFpsTick`).

#[cfg(clean_islands)]
#[path = "adaptive_fps_tick_island.rs"]
mod adaptive_fps_tick_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn fps_interval_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn fps_tick_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use adaptive_fps_tick_island::{fps_interval_clamp, fps_tick_advance};

/// Minimum frame interval (`16` ms = ~60 Hz).
pub const MIN_FRAME_INTERVAL_MS: u64 = 16;
/// Maximum frame interval (`250` ms = 4 Hz guaranteed responsiveness floor).
pub const MAX_FRAME_INTERVAL_MS: u64 = 250;

contract_fn! {
    /// Verified frame-due predicate (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `fps_tick_due_isl`.
    #[must_use]
    pub const fn fps_tick_due(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Congestion-aware WAN render tick governor.
#[derive(Debug, Clone)]
pub struct AdaptiveFpsGovernor {
    interval_ms: u64,
    last_sent_ms: u64,
}

impl Default for AdaptiveFpsGovernor {
    fn default() -> Self {
        Self::new()
    }
}

impl AdaptiveFpsGovernor {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            interval_ms: MIN_FRAME_INTERVAL_MS,
            last_sent_ms: 0,
        }
    }

    pub fn update_network_telemetry(&mut self, srtt_ms: u64, inflight_frames: u64) -> u64 {
        let half = srtt_ms >> 1;
        let base = if half < MIN_FRAME_INTERVAL_MS {
            MIN_FRAME_INTERVAL_MS
        } else {
            half
        };
        let penalty = inflight_frames.saturating_mul(25);
        self.interval_ms = fps_interval_clamp(base.saturating_add(penalty), MAX_FRAME_INTERVAL_MS);
        self.interval_ms
    }

    pub fn poll_send_due(&mut self, now_ms: u64) -> bool {
        let due_at = self.last_sent_ms.saturating_add(self.interval_ms);
        if fps_tick_due(now_ms, due_at) {
            self.last_sent_ms = fps_tick_advance(self.last_sent_ms, now_ms);
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn governor_runs_60hz_on_lan_and_throttles_to_4hz_under_satellite_congestion() {
        let mut g = AdaptiveFpsGovernor::new();
        assert_eq!(g.update_network_telemetry(4, 0), 16);
        assert_eq!(g.update_network_telemetry(600, 5), 250);
        assert!(!g.poll_send_due(100));
        assert!(g.poll_send_due(250));
    }
}
