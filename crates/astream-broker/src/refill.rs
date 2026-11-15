// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Multi-lane coalesced refill planner & cost-bounded handoff meter
//! (`aterm-link` `SPECS.md` critic item B09 `inbox-delivery-accounting`;
//! `Astream.Broker.TlaSharedRefill`).
//!
//! When an endpoint reattaches with `N` session lanes at heterogeneous persisted
//! watermarks `w_1, ..., w_N`, scanning the broker log `N` separate times costs
//! `O(N * log_tail)` index visits. Conversely, scanning the shared parent subtree
//! (`/f/<fleet>/in/<node>/>`) forever when `N` is small and departed sessions hold
//! thousands of unread rows carries unbounded unowed bytes over the wire.
//!
//! [`SharedRefillPlan`] and [`SharedRefillMeter`] implement `aterm-link` B09's
//! 3-phase bounded-competitive refill discipline:
//! 1. **Per-lane below `inbox_oldest`**: any lane with `from < inbox_oldest` reads
//!    its own held lane up to `until = inbox_oldest` first, then joins the shared
//!    read at `max(from, inbox_oldest)` ([`refill_join_cursor_max`]) so no held
//!    record below `inbox_oldest` is ever skipped (`Mutant::RefillJoinBelowTheOldest`).
//! 2. **Shared coalesced scan**: active lanes read together from `shared_from >= inbox_oldest`,
//!    charging `carried * REFILL_ROW_COST` against `(reading - 1) * scanned` saved visits.
//! 3. **Cost-bounded handoff**: as soon as cumulative `owing` exceeds `split_slack`
//!    (`DEFAULT_REFILL_SPLIT_SLACK = FETCH_SCAN_MAX`), the meter returns
//!    [`RefillStep::HandOn`] at the page boundary so remaining lanes finish on their
//!    own filters — bounding total wasted carry to at most `split_slack / REFILL_ROW_COST`
//!    plus a single page.

#[cfg(clean_islands)]
#[path = "refill_island.rs"]
mod refill_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{refill_debt_clamp, refill_join_cursor_max};
#[cfg(clean_islands)]
pub use refill_island::{refill_debt_clamp, refill_join_cursor_max};

/// Scan-equivalent cost of carrying one unowed record over a shared `Fetch` page
/// (`aterm-link` `REFILL_ROW_COST`).
pub const REFILL_ROW_COST: u64 = 192;

/// Default scan-equivalent slack before a shared refill hands remaining lanes back to
/// individual per-lane `Fetch`es: one page's scan, the broker's
/// [`FETCH_SCAN_MAX`](crate::broker::FETCH_SCAN_MAX), or `FETCH_SCAN_MAX / REFILL_ROW_COST`
/// rows carried for no lane. It is defined from that bound, so the slack moves with the page.
pub const DEFAULT_REFILL_SPLIT_SLACK: u64 = crate::broker::FETCH_SCAN_MAX as u64;

/// Maximum number of lanes planned in a single [`SharedRefillPlan`].
pub const MAX_REFILL_LANES: usize = 1024;

contract_fn! {
    /// Kernel-certified invariant that a joined cursor never sits below `inbox_oldest`.
    #[must_use]
    pub const fn refill_cursor_at_least_oldest(cursor: u64, inbox_oldest: u64) -> bool
    clauses [ensures result == (inbox_oldest <= cursor)]
    {
        inbox_oldest <= cursor
    }
}

/// Per-lane schedule produced by [`SharedRefillPlan::build`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LaneSchedule {
    /// Caller-supplied lane identifier (e.g. session id `s-<id>`).
    pub lane_id: String,
    /// Original persisted resume offset for this lane.
    pub original_from: u64,
    /// `Some(inbox_oldest)` when `original_from < inbox_oldest`, requiring a per-lane
    /// `Fetch` over `[original_from .. inbox_oldest)` before joining the shared scan.
    pub catch_up_until: Option<u64>,
    /// Offset at which this lane joins the shared scan (`>= inbox_oldest`).
    pub join_shared_at: u64,
}

/// Coalesced multi-lane refill plan computed from `inbox_oldest` and per-lane cursors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SharedRefillPlan {
    /// Retention floor of the shared parent subtree (`inbox_oldest`).
    pub inbox_oldest: u64,
    /// Starting cursor of the shared scan (`>= inbox_oldest`), or `None` if fewer than
    /// 2 lanes participate (single-lane reads never benefit from a wider shared filter).
    pub shared_from: Option<u64>,
    /// Per-lane schedules in input order.
    pub lanes: Vec<LaneSchedule>,
}

impl SharedRefillPlan {
    /// Compute the 3-phase refill schedule for `lanes` (`(lane_id, from_offset)` pairs)
    /// against `inbox_oldest`.
    pub fn build(inbox_oldest: u64, lanes: &[(&str, u64)]) -> Result<Self, String> {
        if lanes.len() > MAX_REFILL_LANES {
            return Err(format!(
                "refill plan has {} lanes, exceeding max {MAX_REFILL_LANES}",
                lanes.len()
            ));
        }
        let cap = lanes.len().min(MAX_REFILL_LANES);
        let mut schedules = Vec::with_capacity(cap);
        let mut min_join: Option<u64> = None;
        let mut i = 0usize;
        while i < lanes.len() {
            let (id, from) = lanes[i];
            let join_at = refill_join_cursor_max(from, inbox_oldest);
            let _ = refill_cursor_at_least_oldest(join_at, inbox_oldest);
            let catch_up_until = if from < inbox_oldest {
                Some(inbox_oldest)
            } else {
                None
            };
            min_join = Some(match min_join {
                Some(cur) if cur <= join_at => cur,
                _ => join_at,
            });
            schedules.push(LaneSchedule {
                lane_id: id.to_string(),
                original_from: from,
                catch_up_until,
                join_shared_at: join_at,
            });
            i += 1;
        }
        let shared_from = if schedules.len() >= 2 { min_join } else { None };
        Ok(Self {
            inbox_oldest,
            shared_from,
            lanes: schedules,
        })
    }
}

/// Decision after accounting one page of a shared coalesced `Fetch`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RefillStep {
    /// Shared refill reached `head`; all non-stopped lanes are caught up.
    Complete { head: u64 },
    /// Continue reading the shared filter from `next_cursor`.
    Continue { next_cursor: u64, active_debt: u64 },
    /// Shared read exceeded `split_slack` (or stalled); each remaining lane must
    /// read its own narrower filter starting from `handoff_offset`.
    HandOn { handoff_offset: u64 },
}

/// Online cost-vs-savings meter for a shared multi-lane refill (`Astream.Broker.TlaSharedRefill`).
#[derive(Debug, Clone)]
pub struct SharedRefillMeter {
    inbox_oldest: u64,
    cursor: u64,
    owing: i64,
    row_cost: u64,
    split_slack: u64,
    scan_max: u64,
    total_carried: u64,
    handed_on: bool,
}

impl SharedRefillMeter {
    /// Construct a meter starting at `max(initial_from, inbox_oldest)` with
    /// [`REFILL_ROW_COST`] and [`DEFAULT_REFILL_SPLIT_SLACK`].
    #[must_use]
    pub const fn new(inbox_oldest: u64, initial_from: u64, scan_max: u64) -> Self {
        Self::with_params(
            inbox_oldest,
            initial_from,
            REFILL_ROW_COST,
            DEFAULT_REFILL_SPLIT_SLACK,
            scan_max,
        )
    }

    /// Construct a meter with explicit `row_cost`, `split_slack`, and `scan_max`.
    #[must_use]
    pub const fn with_params(
        inbox_oldest: u64,
        initial_from: u64,
        row_cost: u64,
        split_slack: u64,
        scan_max: u64,
    ) -> Self {
        let start = refill_join_cursor_max(initial_from, inbox_oldest);
        Self {
            inbox_oldest,
            cursor: start,
            owing: 0,
            row_cost,
            split_slack,
            scan_max,
            total_carried: 0,
            handed_on: false,
        }
    }

    /// Current shared cursor (`>= inbox_oldest`).
    #[must_use]
    pub const fn cursor(&self) -> u64 {
        self.cursor
    }

    /// Floor `inbox_oldest` this meter was anchored to.
    #[must_use]
    pub const fn inbox_oldest(&self) -> u64 {
        self.inbox_oldest
    }

    /// Total unowed records carried across all observed pages so far.
    #[must_use]
    pub const fn total_carried(&self) -> u64 {
        self.total_carried
    }

    /// Clamped non-negative scan debt (`0..=split_slack`), certified by [`refill_debt_clamp`].
    #[must_use]
    pub const fn active_debt(&self) -> u64 {
        let pos = if self.owing <= 0 {
            0u64
        } else {
            self.owing as u64
        };
        refill_debt_clamp(pos, self.split_slack)
    }

    /// Whether this meter has transitioned to [`RefillStep::HandOn`].
    #[must_use]
    pub const fn is_handed_on(&self) -> bool {
        self.handed_on
    }

    /// Account a completed `Fetch` page `(next, head)` that carried `carried_unowed`
    /// records for no active lane while `reading_lanes` active lanes had `join <= next`.
    pub fn observe_page(
        &mut self,
        next: u64,
        head: u64,
        carried_unowed: u64,
        reading_lanes: usize,
    ) -> RefillStep {
        self.total_carried = self.total_carried.saturating_add(carried_unowed);
        if next >= head {
            self.cursor = refill_join_cursor_max(next, self.inbox_oldest);
            return RefillStep::Complete { head };
        }
        if next <= self.cursor {
            self.handed_on = true;
            return RefillStep::HandOn {
                handoff_offset: self.cursor,
            };
        }
        let scanned = (next - self.cursor).min(self.scan_max);
        let cost = carried_unowed.saturating_mul(self.row_cost);
        let saved = (reading_lanes as u64)
            .saturating_sub(1)
            .saturating_mul(scanned);
        let cost_i64 = if cost > (i64::MAX as u64) {
            i64::MAX
        } else {
            cost as i64
        };
        let saved_i64 = if saved > (i64::MAX as u64) {
            i64::MAX
        } else {
            saved as i64
        };
        self.owing = self
            .owing
            .saturating_add(cost_i64)
            .saturating_sub(saved_i64);
        self.cursor = next;
        let slack_i64 = if self.split_slack > (i64::MAX as u64) {
            i64::MAX
        } else {
            self.split_slack as i64
        };
        if self.owing > slack_i64 {
            self.handed_on = true;
            RefillStep::HandOn {
                handoff_offset: self.cursor,
            }
        } else {
            RefillStep::Continue {
                next_cursor: self.cursor,
                active_debt: self.active_debt(),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plan_separates_below_oldest_lanes_and_joins_at_inbox_oldest() {
        let plan =
            SharedRefillPlan::build(500, &[("s-a", 120), ("s-b", 500), ("s-c", 640)]).unwrap();
        assert_eq!(plan.shared_from, Some(500));
        assert_eq!(plan.lanes[0].catch_up_until, Some(500));
        assert_eq!(plan.lanes[0].join_shared_at, 500);
        assert_eq!(plan.lanes[1].catch_up_until, None);
        assert_eq!(plan.lanes[1].join_shared_at, 500);
        assert_eq!(plan.lanes[2].catch_up_until, None);
        assert_eq!(plan.lanes[2].join_shared_at, 640);

        // Single lane never triggers a wider shared filter.
        let solo = SharedRefillPlan::build(500, &[("s-only", 100)]).unwrap();
        assert_eq!(solo.shared_from, None);
        assert_eq!(solo.lanes[0].join_shared_at, 500);
    }

    #[test]
    fn meter_hands_on_within_b09_slack_bound_and_runs_to_head_when_saving_scans() {
        // Dense unowed traffic (256 unowed rows/page, only 1 reading lane -> 0 saved scans):
        // 256 * 192 = 49,152 <= 65,536 on page 1, then 98,304 > 65,536 on page 2 -> HandOn!
        let mut m = SharedRefillMeter::new(100, 50, 65_536);
        assert_eq!(m.cursor(), 100);
        let s1 = m.observe_page(356, 10_000, 256, 1);
        assert_eq!(
            s1,
            RefillStep::Continue {
                next_cursor: 356,
                active_debt: 256 * REFILL_ROW_COST,
            }
        );
        let s2 = m.observe_page(612, 10_000, 256, 1);
        assert_eq!(
            s2,
            RefillStep::HandOn {
                handoff_offset: 612
            }
        );
        assert!(m.is_handed_on());
        let bound = DEFAULT_REFILL_SPLIT_SLACK / REFILL_ROW_COST + 256;
        assert!(m.total_carried() <= bound);

        // Sparse `ev`-heavy log where 3 sessions scan 10,000 non-inbox records with 0 carried:
        // saved = 2 * 10,000 = 20,000 -> debt stays 0 and finishes at head!
        let mut m2 = SharedRefillMeter::new(0, 0, 65_536);
        assert_eq!(
            m2.observe_page(5_000, 10_000, 0, 3),
            RefillStep::Continue {
                next_cursor: 5_000,
                active_debt: 0,
            }
        );
        assert_eq!(
            m2.observe_page(10_000, 10_000, 0, 3),
            RefillStep::Complete { head: 10_000 }
        );
    }
}
