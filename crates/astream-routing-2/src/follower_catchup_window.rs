// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bounded out-of-lock follower catch-up window (`Astream.Broker.TlaFollowerCatchupWindow`).
//!
//! Prevents lagging `Replicated`-tier followers from stalling hot producer batches
//! under `Mutex<BrokerLog>`: followers that fall more than `max_insync_lag` behind
//! leader `hw` stream bounded catch-up pages (`<= max_page_bytes`) outside the
//! publish lock and rejoin the synchronous quorum once caught up.

#[cfg(clean_islands)]
#[path = "follower_catchup_window_island.rs"]
mod follower_catchup_window_island;
#[cfg(clean_islands)]
pub use follower_catchup_window_island::{catchup_page_clamp, follower_ack_advance};

/// Default maximum bytes shipped in a single follower catch-up page (`256 KiB`).
pub const DEFAULT_MAX_CATCHUP_PAGE_BYTES: u64 = 262_144;

/// Default maximum record lag within which a follower remains in the synchronous ISR.
pub const DEFAULT_MAX_INSYNC_LAG_RECORDS: u64 = 64;

#[cfg(not(clean_islands))]
/// Monotonically advance a follower's durably acknowledged offset.
#[must_use]
pub const fn follower_ack_advance(cur_ack: u64, cand_ack: u64) -> u64 {
    if cur_ack < cand_ack {
        cand_ack
    } else {
        cur_ack
    }
}

#[cfg(not(clean_islands))]
/// Clamp a single catch-up page byte budget to `max_page_bytes`.
#[must_use]
pub const fn catchup_page_clamp(cand_bytes: u64, max_page_bytes: u64) -> u64 {
    if cand_bytes < max_page_bytes {
        cand_bytes
    } else {
        max_page_bytes
    }
}

contract_fn! {
    /// True iff `lag_records` is within `max_insync_lag`.
    #[must_use]
    pub const fn follower_within_insync(lag_records: u64, max_insync_lag: u64) -> bool
    clauses [ensures result == (lag_records <= max_insync_lag)]
    {
        lag_records <= max_insync_lag
    }
}

/// Membership state of a `Replicated`-tier follower relative to leader `hw`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FollowerSyncMode {
    CatchingUp,
    InSync,
}

/// Stateful catch-up window controller for one `Replicated` follower.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FollowerCatchupWindow {
    acked_offset: u64,
    last_page_bytes: u64,
    max_page_bytes: u64,
    max_insync_lag: u64,
    mode: FollowerSyncMode,
}

impl Default for FollowerCatchupWindow {
    fn default() -> Self {
        Self::new(
            DEFAULT_MAX_CATCHUP_PAGE_BYTES,
            DEFAULT_MAX_INSYNC_LAG_RECORDS,
        )
    }
}

impl FollowerCatchupWindow {
    #[must_use]
    pub const fn new(max_page_bytes: u64, max_insync_lag: u64) -> Self {
        let pcap = if max_page_bytes == 0 {
            DEFAULT_MAX_CATCHUP_PAGE_BYTES
        } else {
            max_page_bytes
        };
        Self {
            acked_offset: 0,
            last_page_bytes: 0,
            max_page_bytes: pcap,
            max_insync_lag,
            mode: FollowerSyncMode::InSync,
        }
    }

    #[must_use]
    pub const fn acked_offset(&self) -> u64 {
        self.acked_offset
    }

    #[must_use]
    pub const fn last_page_bytes(&self) -> u64 {
        self.last_page_bytes
    }

    #[must_use]
    pub const fn mode(&self) -> FollowerSyncMode {
        self.mode
    }

    /// Compute the bounded byte budget for the next catch-up page and update `mode` vs `leader_hw`.
    pub fn plan_page(&mut self, leader_hw: u64, requested_bytes: u64) -> (FollowerSyncMode, u64) {
        let lag = leader_hw.saturating_sub(self.acked_offset);
        self.mode = if follower_within_insync(lag, self.max_insync_lag) {
            FollowerSyncMode::InSync
        } else {
            FollowerSyncMode::CatchingUp
        };
        let budget = catchup_page_clamp(requested_bytes, self.max_page_bytes);
        self.last_page_bytes = budget;
        (self.mode, budget)
    }

    /// Record a durable follower ack up to `cand_ack` and refresh `InSync` status vs `leader_hw`.
    pub fn record_ack(&mut self, cand_ack: u64, leader_hw: u64) -> FollowerSyncMode {
        self.acked_offset = follower_ack_advance(self.acked_offset, cand_ack);
        let lag = leader_hw.saturating_sub(self.acked_offset);
        self.mode = if follower_within_insync(lag, self.max_insync_lag) {
            FollowerSyncMode::InSync
        } else {
            FollowerSyncMode::CatchingUp
        };
        self.mode
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn transitions_catching_up_to_in_sync_with_clamped_pages() {
        let mut win = FollowerCatchupWindow::new(65_536, 16);
        // Leader jumps to hw = 500 -> follower lags by 500 > 16 -> CatchingUp, page clamped to 64 KiB
        let (mode, budget) = win.plan_page(500, 1_000_000);
        assert_eq!(mode, FollowerSyncMode::CatchingUp);
        assert_eq!(budget, 65_536);

        // Follower catches up to 490 (lag = 10 <= 16) -> rejoins ISR!
        assert_eq!(win.record_ack(490, 500), FollowerSyncMode::InSync);
        assert_eq!(win.acked_offset(), 490);
    }
}
