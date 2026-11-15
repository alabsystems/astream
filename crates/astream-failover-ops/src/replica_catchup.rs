// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bounded divergent-tail truncation and `[common..leader_head)` follower catch-up planner
//! (`broker.replicated-tier`, `Astream.Failover.TlaReplicaCatchup`).

#[cfg(clean_islands)]
#[path = "replica_catchup_island.rs"]
mod replica_catchup_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn catchup_batch_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn catchup_cursor_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use replica_catchup_island::{catchup_batch_clamp, catchup_cursor_advance};

/// Maximum records shipped in one follower catch-up page.
pub const MAX_CATCHUP_BATCH_RECORDS: u64 = 4096;

contract_fn! {
    /// Verified completion check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `catchup_complete_isl`.
    #[must_use]
    pub const fn catchup_complete(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Next action for bringing a follower replica into prefix alignment with the leader.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CatchupStep {
    TruncateDivergentTail { target_head: u64 },
    ShipRange { from: u64, count: u64 },
    CaughtUp { head: u64 },
}

/// Stateful follower catch-up planner.
#[derive(Debug, Clone)]
pub struct ReplicaCatchupPlanner {
    page_limit: u64,
    cursor: u64,
    needs_truncate_to: Option<u64>,
}

impl ReplicaCatchupPlanner {
    #[must_use]
    pub const fn new(follower_head: u64, common_prefix_head: u64, page_limit: u64) -> Self {
        let lim = catchup_batch_clamp(page_limit, MAX_CATCHUP_BATCH_RECORDS);
        let eff_lim = if lim == 0 { 1 } else { lim };
        if follower_head > common_prefix_head {
            Self {
                page_limit: eff_lim,
                cursor: common_prefix_head,
                needs_truncate_to: Some(common_prefix_head),
            }
        } else {
            Self {
                page_limit: eff_lim,
                cursor: follower_head,
                needs_truncate_to: None,
            }
        }
    }

    #[must_use]
    pub const fn cursor(&self) -> u64 {
        self.cursor
    }

    pub fn confirm_truncated(&mut self) {
        self.needs_truncate_to = None;
    }

    pub fn next_step(&self, leader_head: u64) -> CatchupStep {
        if let Some(target_head) = self.needs_truncate_to {
            return CatchupStep::TruncateDivergentTail { target_head };
        }
        if catchup_complete(self.cursor, leader_head) {
            return CatchupStep::CaughtUp { head: self.cursor };
        }
        let rem = leader_head.saturating_sub(self.cursor);
        let count = catchup_batch_clamp(rem, self.page_limit);
        CatchupStep::ShipRange {
            from: self.cursor,
            count,
        }
    }

    pub fn confirm_shipped(&mut self, next_offset: u64) -> u64 {
        if self.needs_truncate_to.is_some() {
            return self.cursor;
        }
        self.cursor = catchup_cursor_advance(self.cursor, next_offset);
        self.cursor
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn planner_truncates_divergent_tail_first_then_pages_monotonically_to_leader_head() {
        let mut p = ReplicaCatchupPlanner::new(120, 100, 15);
        assert_eq!(
            p.next_step(135),
            CatchupStep::TruncateDivergentTail { target_head: 100 }
        );
        p.confirm_truncated();
        assert_eq!(
            p.next_step(135),
            CatchupStep::ShipRange {
                from: 100,
                count: 15
            }
        );
        p.confirm_shipped(115);
        assert_eq!(
            p.next_step(135),
            CatchupStep::ShipRange {
                from: 115,
                count: 15
            }
        );
        p.confirm_shipped(130);
        assert_eq!(
            p.next_step(135),
            CatchupStep::ShipRange {
                from: 130,
                count: 5
            }
        );
        p.confirm_shipped(135);
        assert_eq!(p.next_step(135), CatchupStep::CaughtUp { head: 135 });
    }
}
