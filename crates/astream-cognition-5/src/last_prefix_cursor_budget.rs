// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Lock-friendly `Last` bounded prefix-scan cursor
//! (`Astream.Broker.TlaLastPrefixCursorBudget`).
//!
//! Prevents wide wildcard `Last` queries (`LAST_SCAN_MAX` audit) from monopolizing
//! `Mutex<BrokerLog>`: bounds per-lock-slice `BTreeMap` step count to `slice_budget`, yields with
//! a monotonically advancing `cursor_rank` bookmark when exhausted, and caps total matched rows.

#[cfg(clean_islands)]
#[path = "last_prefix_cursor_budget_island.rs"]
mod last_prefix_cursor_budget_island;
#[cfg(clean_islands)]
pub use last_prefix_cursor_budget_island::{
    last_cursor_rank_advance_b118, last_slice_steps_clamp_b118,
};

#[cfg(not(clean_islands))]
/// Clamp per-lock-slice visited subject count to `slice_budget`.
#[must_use]
pub const fn last_slice_steps_clamp_b118(cand_steps: u64, slice_budget: u64) -> u64 {
    if cand_steps < slice_budget {
        cand_steps
    } else {
        slice_budget
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `cursor_rank` across yielded `Last` scan slices.
#[must_use]
pub const fn last_cursor_rank_advance_b118(cur_rank: u64, cand_rank: u64) -> u64 {
    if cur_rank < cand_rank {
        cand_rank
    } else {
        cur_rank
    }
}

contract_fn! {
    /// True iff another subject entry may be visited in the current lock slice.
    #[must_use]
    pub const fn last_slice_has_budget_b118(steps_in_slice: u64, slice_budget: u64) -> bool
    clauses [ensures result == (steps_in_slice < slice_budget)]
    {
        steps_in_slice < slice_budget
    }
}

/// Step outcome during a chunked `Last` prefix scan.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LastScanStepVerdict {
    ContinueInSlice {
        steps_in_slice: u64,
        cursor_rank: u64,
    },
    YieldReleaseLock {
        resume_cursor_rank: u64,
    },
    StopScanCapReached {
        total_scanned: u64,
    },
}

/// Bounded `Last` scan budget controller.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LastPrefixCursorBudget {
    slice_budget: u64,
    max_total_scan: u64,
    steps_in_slice: u64,
    total_scanned: u64,
    cursor_rank: u64,
}

impl LastPrefixCursorBudget {
    #[must_use]
    pub const fn new(slice_budget: u64, max_total_scan: u64) -> Self {
        let sb = if slice_budget == 0 { 256 } else { slice_budget };
        let tot = if max_total_scan < sb {
            sb
        } else {
            max_total_scan
        };
        Self {
            slice_budget: sb,
            max_total_scan: tot,
            steps_in_slice: 0,
            total_scanned: 0,
            cursor_rank: 0,
        }
    }

    #[must_use]
    pub const fn cursor_rank(&self) -> u64 {
        self.cursor_rank
    }

    /// Begin a new lock acquisition slice after yielding.
    pub fn begin_lock_slice(&mut self) {
        self.steps_in_slice = 0;
    }

    /// Visit one `BTreeMap` entry with lexicographic `entry_rank`.
    pub fn visit_entry(&mut self, entry_rank: u64) -> LastScanStepVerdict {
        if self.total_scanned >= self.max_total_scan {
            return LastScanStepVerdict::StopScanCapReached {
                total_scanned: self.total_scanned,
            };
        }
        if !last_slice_has_budget_b118(self.steps_in_slice, self.slice_budget) {
            return LastScanStepVerdict::YieldReleaseLock {
                resume_cursor_rank: self.cursor_rank,
            };
        }
        let cand_steps = self.steps_in_slice.saturating_add(1);
        self.steps_in_slice = last_slice_steps_clamp_b118(cand_steps, self.slice_budget);
        self.total_scanned = self.total_scanned.saturating_add(1);
        self.cursor_rank = last_cursor_rank_advance_b118(self.cursor_rank, entry_rank);
        LastScanStepVerdict::ContinueInSlice {
            steps_in_slice: self.steps_in_slice,
            cursor_rank: self.cursor_rank,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn yields_lock_at_slice_budget_and_resumes_monotonically() {
        let mut b = LastPrefixCursorBudget::new(2, 5);
        assert!(matches!(
            b.visit_entry(10),
            LastScanStepVerdict::ContinueInSlice {
                cursor_rank: 10,
                ..
            }
        ));
        assert!(matches!(
            b.visit_entry(20),
            LastScanStepVerdict::ContinueInSlice {
                cursor_rank: 20,
                ..
            }
        ));
        assert_eq!(
            b.visit_entry(30),
            LastScanStepVerdict::YieldReleaseLock {
                resume_cursor_rank: 20
            }
        );
        b.begin_lock_slice();
        assert!(matches!(
            b.visit_entry(30),
            LastScanStepVerdict::ContinueInSlice {
                cursor_rank: 30,
                ..
            }
        ));
    }
}
