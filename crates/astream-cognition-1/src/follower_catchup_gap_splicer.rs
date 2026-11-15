// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Replicated follower lag catch-up vs compacted-base reseed planner
//! (`Astream.Broker.TlaFollowerCatchupGapSplicer`).
//!
//! Coordinates non-blocking follower catch-up in `astream-broker`: determines whether a lagging
//! follower (`follower_hw`) can stream bounded `max_chunk_records` catch-up slices from
//! `[leader_base, leader_hw)` or requires a base-snapshot reseed because `follower_hw < leader_base`.

#[cfg(clean_islands)]
#[path = "follower_catchup_gap_splicer_island.rs"]
mod follower_catchup_gap_splicer_island;
#[cfg(clean_islands)]
pub use follower_catchup_gap_splicer_island::{catchup_chunk_clamp_b109, follower_hw_advance_b109};

#[cfg(not(clean_islands))]
/// Clamp per-slice follower catch-up record count to `max_chunk`.
#[must_use]
pub const fn catchup_chunk_clamp_b109(cand_records: u64, max_chunk: u64) -> u64 {
    if cand_records < max_chunk {
        cand_records
    } else {
        max_chunk
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the follower's confirmed high-watermark offset.
#[must_use]
pub const fn follower_hw_advance_b109(cur_hw: u64, cand_hw: u64) -> u64 {
    if cur_hw < cand_hw {
        cand_hw
    } else {
        cur_hw
    }
}

contract_fn! {
    /// True iff `follower_hw` is still retained in the leader's `[leader_base, leader_hw]` window.
    #[must_use]
    pub const fn follower_in_retained_log_b109(
        follower_hw: u64,
        leader_base: u64,
        leader_hw: u64,
    ) -> bool
    clauses [ensures result == (leader_base <= follower_hw && follower_hw <= leader_hw)]
    {
        leader_base <= follower_hw && follower_hw <= leader_hw
    }
}

/// Catch-up plan for a `Replicated` follower.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FollowerCatchupPlan {
    CaughtUp { follower_hw: u64 },
    StreamChunk { start_offset: u64, count: u64 },
    ReseedFromCompactedBase { leader_base: u64 },
    FollowerAheadDivergence { follower_hw: u64, leader_hw: u64 },
}

/// Stateful catch-up planner for one `Replicated` follower link.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FollowerCatchupGapSplicer {
    follower_hw: u64,
    max_chunk_records: u64,
}

impl FollowerCatchupGapSplicer {
    #[must_use]
    pub const fn new(initial_follower_hw: u64, max_chunk_records: u64) -> Self {
        let cap = if max_chunk_records == 0 {
            128
        } else {
            max_chunk_records
        };
        Self {
            follower_hw: initial_follower_hw,
            max_chunk_records: cap,
        }
    }

    #[must_use]
    pub const fn follower_hw(&self) -> u64 {
        self.follower_hw
    }

    /// Compute the next non-blocking catch-up step given `(leader_base, leader_hw)`.
    #[must_use]
    pub fn plan_next(&self, leader_base: u64, leader_hw: u64) -> FollowerCatchupPlan {
        if self.follower_hw > leader_hw {
            return FollowerCatchupPlan::FollowerAheadDivergence {
                follower_hw: self.follower_hw,
                leader_hw,
            };
        }
        if !follower_in_retained_log_b109(self.follower_hw, leader_base, leader_hw) {
            return FollowerCatchupPlan::ReseedFromCompactedBase { leader_base };
        }
        let lag = leader_hw.saturating_sub(self.follower_hw);
        if lag == 0 {
            FollowerCatchupPlan::CaughtUp {
                follower_hw: self.follower_hw,
            }
        } else {
            FollowerCatchupPlan::StreamChunk {
                start_offset: self.follower_hw,
                count: catchup_chunk_clamp_b109(lag, self.max_chunk_records),
            }
        }
    }

    /// Record follower acknowledgment advancing `follower_hw`.
    pub fn confirm_ack(&mut self, acked_hw: u64) -> u64 {
        self.follower_hw = follower_hw_advance_b109(self.follower_hw, acked_hw);
        self.follower_hw
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn streams_bounded_chunks_or_reseeds_when_behind_compacted_base() {
        let mut s = FollowerCatchupGapSplicer::new(20, 50);
        assert_eq!(
            s.plan_next(40, 200),
            FollowerCatchupPlan::ReseedFromCompactedBase { leader_base: 40 }
        );
        assert_eq!(s.confirm_ack(40), 40);
        assert_eq!(
            s.plan_next(40, 200),
            FollowerCatchupPlan::StreamChunk {
                start_offset: 40,
                count: 50,
            }
        );
    }
}
