// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bandwidth-Delay Product (`BDP`) WAN pacing window and in-flight byte ledger
//! (`Astream.Mesh.TlaWanPacing`).
//!
//! Sizes cross-region replication pipelines dynamically from measured `(bw_bytes_per_sec, rtt_ms)`
//! clamped to `[MIN_WAN_WINDOW_BYTES ..= MAX_WAN_INFLIGHT_BYTES]` via Clean-origin
//! `pacing_window_clamp`, tracks cumulative acknowledged bytes monotonically via
//! `pacing_sent_advance`, and gates sends via `pacing_can_send`.

#[cfg(clean_islands)]
#[path = "wan_pacing_island.rs"]
mod wan_pacing_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pacing_window_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pacing_sent_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use wan_pacing_island::{pacing_sent_advance, pacing_window_clamp};

/// Minimum WAN send window (`64 KiB`) so startup probes never stall.
pub const MIN_WAN_WINDOW_BYTES: u64 = 65_536;
/// Hard ceiling on unacknowledged cross-region bytes per stream (`16 MiB`).
pub const MAX_WAN_INFLIGHT_BYTES: u64 = 16_777_216;

contract_fn! {
    /// Verified window admission predicate (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `pacing_can_send_isl`.
    #[must_use]
    pub const fn pacing_can_send(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Dynamic BDP-paced WAN stream controller.
#[derive(Debug, Clone)]
pub struct WanPacingScheduler {
    window_bytes: u64,
    sent_cumulative: u64,
    acked_cumulative: u64,
}

impl Default for WanPacingScheduler {
    fn default() -> Self {
        Self::new()
    }
}

impl WanPacingScheduler {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            window_bytes: MIN_WAN_WINDOW_BYTES,
            sent_cumulative: 0,
            acked_cumulative: 0,
        }
    }

    #[must_use]
    pub const fn window_bytes(&self) -> u64 {
        self.window_bytes
    }

    #[must_use]
    pub const fn inflight_bytes(&self) -> u64 {
        self.sent_cumulative.saturating_sub(self.acked_cumulative)
    }

    /// Recomputes `window_bytes = clamp(bw_bytes_per_sec * rtt_ms / 1000, MIN..=MAX)`.
    pub fn update_bdp(&mut self, bw_bytes_per_sec: u64, rtt_ms: u64) -> u64 {
        let raw_bdp = (bw_bytes_per_sec / 1000).saturating_mul(rtt_ms);
        let floored = if raw_bdp < MIN_WAN_WINDOW_BYTES {
            MIN_WAN_WINDOW_BYTES
        } else {
            raw_bdp
        };
        self.window_bytes = pacing_window_clamp(floored, MAX_WAN_INFLIGHT_BYTES);
        self.window_bytes
    }

    /// Attempts to reserve `frame_bytes` in the active BDP window.
    pub fn try_acquire(&mut self, frame_bytes: u64) -> bool {
        let next_inflight = self.inflight_bytes().saturating_add(frame_bytes);
        if !pacing_can_send(self.window_bytes, next_inflight) {
            return false;
        }
        let cand_sent = self.sent_cumulative.saturating_add(frame_bytes);
        self.sent_cumulative = pacing_sent_advance(self.sent_cumulative, cand_sent);
        true
    }

    /// Advances cumulative acknowledged byte watermark monotonically (`<= sent_cumulative`).
    pub fn on_ack_cumulative(&mut self, acked_total: u64) -> u64 {
        let bounded = pacing_window_clamp(acked_total, self.sent_cumulative);
        self.acked_cumulative = pacing_sent_advance(self.acked_cumulative, bounded);
        self.inflight_bytes()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bdp_window_autoscales_with_rtt_and_enforces_inflight_ceiling() {
        let mut pacer = WanPacingScheduler::new();
        // 100 MB/s over 80 ms WAN -> 8 MB BDP window!
        let win = pacer.update_bdp(100_000_000, 80);
        assert_eq!(win, 8_000_000);

        assert!(pacer.try_acquire(5_000_000));
        assert!(!pacer.try_acquire(4_000_000)); // 9 MB > 8 MB window!
        assert_eq!(pacer.on_ack_cumulative(3_000_000), 2_000_000);
        assert!(pacer.try_acquire(4_000_000)); // 6 MB <= 8 MB window!
    }
}
