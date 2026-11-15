// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Non-blocking follower catch-up demotion and ISR (in-sync replica) re-admission fence
//! (`Astream.Broker.TlaReplicaCatchupFence`).
//!
//! Prevents a stalled or high-RTT follower (`REPLICA_IO_TIMEOUT`) from stalling the synchronous
//! `Replicated` writer lock path:
//! - Demotes a follower from `InSync` to `CatchingUp` immediately on timeout or lag overflow,
//! - Monotonically advances `follower_ack` via Clean-origin [`replica_ack_advance_b121`],
//! - Re-admits a `CatchingUp` follower to `InSync` only when `follower_ack >= leader_head` and
//!   `stable_batches >= min_stable_batches`, clamping active ISR membership via
//!   [`replica_insync_clamp_b121`].

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
#[path = "replica_catchup_fence_island.rs"]
mod replica_catchup_fence_island;
#[cfg(clean_islands)]
pub use replica_catchup_fence_island::{replica_ack_advance_b121, replica_insync_clamp_b121};

#[cfg(not(clean_islands))]
/// Clamp in-sync replica count to `total_replicas`.
#[must_use]
pub const fn replica_insync_clamp_b121(cand_in_sync: u64, total_replicas: u64) -> u64 {
    if cand_in_sync < total_replicas {
        cand_in_sync
    } else {
        total_replicas
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance durable follower acknowledgement watermark.
#[must_use]
pub const fn replica_ack_advance_b121(cur_ack: u64, cand_ack: u64) -> u64 {
    if cur_ack < cand_ack {
        cand_ack
    } else {
        cur_ack
    }
}

contract_fn! {
    /// True iff `follower_ack` still lags strictly behind `leader_head`.
    #[must_use]
    pub const fn replica_lag_present_b121(follower_ack: u64, leader_head: u64) -> bool
    clauses [ensures result == (follower_ack < leader_head)]
    {
        follower_ack < leader_head
    }
}

pub const MAX_TRACKED_FOLLOWERS: usize = 8;

/// Membership phase of a single follower relative to synchronous quorum shipping.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FollowerSyncPhase {
    InSync,
    CatchingUp,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct FollowerSlot {
    active: bool,
    phase: FollowerSyncPhase,
    durable_ack: u64,
    stable_batches: u64,
}

impl FollowerSlot {
    const EMPTY: Self = Self {
        active: false,
        phase: FollowerSyncPhase::CatchingUp,
        durable_ack: 0,
        stable_batches: 0,
    };
}

/// Bounded ISR & async catch-up fence for `Replicated` broker followers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReplicaCatchupFence {
    slots: [FollowerSlot; MAX_TRACKED_FOLLOWERS],
    total_replicas: u64,
    in_sync_count: u64,
    max_lag_records: u64,
    min_stable_batches: u64,
}

impl ReplicaCatchupFence {
    /// Construct an ISR fence with `follower_count` initially `InSync` followers (`+1` leader).
    #[must_use]
    pub fn new(follower_count: usize, max_lag_records: u64, min_stable_batches: u64) -> Self {
        let capped = if follower_count <= MAX_TRACKED_FOLLOWERS {
            follower_count
        } else {
            MAX_TRACKED_FOLLOWERS
        };
        let mut slots = [FollowerSlot::EMPTY; MAX_TRACKED_FOLLOWERS];
        if let Some(mut rest) = slots.get_mut(..capped) {
            while let [slot, tail @ ..] = rest {
                slot.active = true;
                slot.phase = FollowerSyncPhase::InSync;
                rest = tail;
            }
        }
        let total_replicas = (capped as u64).saturating_add(1);
        let in_sync = replica_insync_clamp_b121(total_replicas, total_replicas);
        Self {
            slots,
            total_replicas,
            in_sync_count: in_sync,
            max_lag_records,
            min_stable_batches: if min_stable_batches == 0 {
                1
            } else {
                min_stable_batches
            },
        }
    }

    fn recompute_in_sync(&mut self) {
        let mut count = 1u64; // leader itself
        let mut rest = self.slots.as_slice();
        while let &[slot, ref tail @ ..] = rest {
            if slot.active && slot.phase == FollowerSyncPhase::InSync {
                count = count.saturating_add(1);
            }
            rest = tail;
        }
        self.in_sync_count = replica_insync_clamp_b121(count, self.total_replicas);
    }

    /// Number of replicas (`leader + InSync followers`) currently in synchronous quorum.
    #[must_use]
    pub const fn in_sync_count(&self) -> u64 {
        self.in_sync_count
    }

    /// Whether `quorum_needed` can be satisfied by current `InSync` replicas.
    #[must_use]
    pub const fn has_sync_quorum(&self, quorum_needed: u64) -> bool {
        self.in_sync_count >= quorum_needed
    }

    /// Demote `follower_idx` out of synchronous shipping on I/O timeout or disconnect.
    pub fn record_timeout(&mut self, follower_idx: usize) -> bool {
        let Some(slot) = self.slots.get_mut(follower_idx) else {
            return false;
        };
        if !slot.active {
            return false;
        }
        slot.phase = FollowerSyncPhase::CatchingUp;
        slot.stable_batches = 0;
        self.recompute_in_sync();
        true
    }

    /// Record a durable follower ack at `cand_ack` against `leader_head`, demoting if lag exceeds
    /// `max_lag_records` or promoting back to `InSync` once caught up and stable.
    #[allow(clippy::question_mark)]
    pub fn record_ack(
        &mut self,
        follower_idx: usize,
        cand_ack: u64,
        leader_head: u64,
    ) -> Option<FollowerSyncPhase> {
        let max_lag = self.max_lag_records;
        let min_stable = self.min_stable_batches;
        let phase_out = {
            let Some(slot) = self.slots.get_mut(follower_idx) else {
                return None;
            };
            if !slot.active {
                return None;
            }
            slot.durable_ack = replica_ack_advance_b121(slot.durable_ack, cand_ack);
            let lag = leader_head.saturating_sub(slot.durable_ack);
            if lag > max_lag {
                slot.phase = FollowerSyncPhase::CatchingUp;
                slot.stable_batches = 0;
            } else {
                slot.stable_batches = slot.stable_batches.saturating_add(1);
                if slot.phase == FollowerSyncPhase::CatchingUp
                    && !replica_lag_present_b121(slot.durable_ack, leader_head)
                    && slot.stable_batches >= min_stable
                {
                    slot.phase = FollowerSyncPhase::InSync;
                }
            }
            slot.phase
        };
        self.recompute_in_sync();
        Some(phase_out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stalled_follower_demotes_and_readmits_only_when_caught_up_and_stable() {
        let mut fence = ReplicaCatchupFence::new(2, 16, 2);
        assert_eq!(fence.in_sync_count(), 3);
        assert!(fence.has_sync_quorum(2));

        // Follower 1 times out -> demoted immediately; 2-of-3 quorum still holds via leader + f0!
        assert!(fence.record_timeout(1));
        assert_eq!(fence.in_sync_count(), 2);
        assert!(fence.has_sync_quorum(2));

        // Partial catch-up batch 1 (ack=90 < leader_head=100, lag=10 <= 16): still CatchingUp.
        assert_eq!(
            fence.record_ack(1, 90, 100),
            Some(FollowerSyncPhase::CatchingUp)
        );
        // Caught up at 100 on batch 2 (stable_batches=2 >= 2): promoted back to InSync!
        assert_eq!(
            fence.record_ack(1, 100, 100),
            Some(FollowerSyncPhase::InSync)
        );
        assert_eq!(fence.in_sync_count(), 3);

        // Regression ack (50 < 100) is ignored monotonically; excessive lag demotes.
        assert_eq!(
            fence.record_ack(1, 50, 120),
            Some(FollowerSyncPhase::CatchingUp)
        );
        assert_eq!(fence.in_sync_count(), 2);
    }
}
