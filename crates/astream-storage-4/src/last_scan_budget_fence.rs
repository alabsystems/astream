// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bounded `Last` (`last_matching`) `BTreeMap` scan slice & continuation cursor fence
//! (`Astream.Broker.TlaLastScanBudgetFence`).
//!
//! Prevents wildcard `Last` queries over large retained subject maps from holding
//! `Mutex<BrokerLog>` across unbounded `BTreeMap` scans: enforces `scanned <= max_scan`
//! (`LAST_SCAN_MAX`) per critical section and advances `scan_epoch` across paginated
//! continuation slices.

#[cfg(clean_islands)]
#[path = "last_scan_budget_fence_island.rs"]
mod last_scan_budget_fence_island;
#[cfg(clean_islands)]
pub use last_scan_budget_fence_island::{last_scan_count_clamp, last_scan_epoch_advance};

#[cfg(not(clean_islands))]
/// Clamp per-slice scanned subject count to `max_scan`.
#[must_use]
pub const fn last_scan_count_clamp(cand_scanned: u64, max_scan: u64) -> u64 {
    if cand_scanned < max_scan {
        cand_scanned
    } else {
        max_scan
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `Last` scan slice epoch.
#[must_use]
pub const fn last_scan_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff the current `Last` scan slice still has budget below `max_scan`.
    #[must_use]
    pub const fn last_scan_has_budget(scanned: u64, max_scan: u64) -> bool
    clauses [ensures result == (scanned < max_scan)]
    {
        scanned < max_scan
    }
}

/// Outcome of a bounded `Last` scan slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LastScanOutcome {
    Completed {
        scan_epoch: u64,
        scanned_in_slice: u64,
        matched: u64,
    },
    YieldedAtCap {
        scan_epoch: u64,
        scanned_in_slice: u64,
        matched: u64,
    },
}

/// Stateful budget fence for paginated `Last` wildcard subject scans.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LastScanBudgetFence {
    max_scan_per_slice: u64,
    scanned_in_slice: u64,
    matched_in_slice: u64,
    scan_epoch: u64,
}

impl LastScanBudgetFence {
    #[must_use]
    pub const fn new(max_scan_per_slice: u64) -> Self {
        let cap = if max_scan_per_slice == 0 {
            1024
        } else {
            max_scan_per_slice
        };
        Self {
            max_scan_per_slice: cap,
            scanned_in_slice: 0,
            matched_in_slice: 0,
            scan_epoch: 0,
        }
    }

    #[must_use]
    pub const fn scan_epoch(&self) -> u64 {
        self.scan_epoch
    }

    #[must_use]
    pub const fn scanned_in_slice(&self) -> u64 {
        self.scanned_in_slice
    }

    /// Begin a fresh bounded `Last` scan slice under `BrokerLog`.
    pub fn begin_slice(&mut self) {
        let cand_ep = self.scan_epoch.saturating_add(1);
        self.scan_epoch = last_scan_epoch_advance(self.scan_epoch, cand_ep);
        self.scanned_in_slice = 0;
        self.matched_in_slice = 0;
    }

    /// Charge one visited subject key (`matched_filter` if it matched the query filter).
    /// Returns `false` once the slice hits `max_scan_per_slice` and must yield the lock.
    pub fn step_entry(&mut self, matched_filter: bool) -> bool {
        if !last_scan_has_budget(self.scanned_in_slice, self.max_scan_per_slice) {
            return false;
        }
        let next = self.scanned_in_slice.saturating_add(1);
        self.scanned_in_slice = last_scan_count_clamp(next, self.max_scan_per_slice);
        if matched_filter {
            self.matched_in_slice = self.matched_in_slice.saturating_add(1);
        }
        last_scan_has_budget(self.scanned_in_slice, self.max_scan_per_slice)
    }

    /// Finalize the current slice (`exhausted == true` iff iterator reached `BTreeMap` end).
    #[must_use]
    pub const fn finish_slice(&self, exhausted: bool) -> LastScanOutcome {
        if exhausted {
            LastScanOutcome::Completed {
                scan_epoch: self.scan_epoch,
                scanned_in_slice: self.scanned_in_slice,
                matched: self.matched_in_slice,
            }
        } else {
            LastScanOutcome::YieldedAtCap {
                scan_epoch: self.scan_epoch,
                scanned_in_slice: self.scanned_in_slice,
                matched: self.matched_in_slice,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn yields_cleanly_at_last_scan_max_and_tracks_matches() {
        let mut fence = LastScanBudgetFence::new(3);
        fence.begin_slice();
        assert!(fence.step_entry(true));
        assert!(fence.step_entry(false));
        // 3rd entry reaches cap (returns false so caller yields lock):
        assert!(!fence.step_entry(true));
        assert!(!fence.step_entry(true));
        assert_eq!(
            fence.finish_slice(false),
            LastScanOutcome::YieldedAtCap {
                scan_epoch: 1,
                scanned_in_slice: 3,
                matched: 2,
            }
        );
    }
}
