// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Follower catch-up lag admission gate (`Broker::rejoin_followers`,
//! `Astream.LeaseFail.TlaFollowerLagAdmission`) keeping rejoining followers in non-blocking
//! catch-up streaming until lag drops within synchronous quorum tolerance.

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "follower_lag_admission_island.rs"]
mod follower_lag_admission_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lhf_lag_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lhf_match_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use follower_lag_admission_island::{lhf_lag_clamp, lhf_match_advance};

/// Maximum synchronous-quorum admission lag (`65_536` bytes = 1 replicate batch).
pub const MAX_SYNC_ADMISSION_LAG_BYTES: u64 = 65_536;

contract_fn! {
    /// Verified caught-up follower threshold (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `lhf_caught_up_isl`.
    #[must_use]
    pub const fn lhf_caught_up(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct FollowerLagGate {
    follower_matched_bytes: u64,
    max_sync_lag: u64,
}

impl FollowerLagGate {
    #[must_use]
    pub const fn new(max_sync_lag: u64) -> Self {
        Self {
            follower_matched_bytes: 0,
            max_sync_lag: lhf_lag_clamp(max_sync_lag, MAX_SYNC_ADMISSION_LAG_BYTES),
        }
    }

    pub fn update_progress(&mut self, matched_bytes: u64, leader_head_bytes: u64) -> bool {
        if matched_bytes > leader_head_bytes {
            return false;
        }
        self.follower_matched_bytes = lhf_match_advance(self.follower_matched_bytes, matched_bytes);
        if self.follower_matched_bytes > leader_head_bytes {
            return false;
        }
        let lag = leader_head_bytes.saturating_sub(self.follower_matched_bytes);
        lhf_caught_up(self.max_sync_lag, lag)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn admits_follower_to_sync_quorum_only_when_lag_within_one_batch() {
        let mut g = FollowerLagGate::new(65_536);
        assert!(!g.update_progress(100_000, 200_000));
        assert!(g.update_progress(160_000, 200_000));
    }
}
