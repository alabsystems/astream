// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Subscriber fan-out micro-batch coalescer (`Astream.Broker.TlaTailBatchCoalescer`).
//!
//! Complements `tail_wake` to mitigate 64-subscriber `Mutex<BrokerLog>` contention
//! (`DESIGN-aterm-fabric.md` §13): computes bounded `[start_offset, end_offset)`
//! drain slices (`<= max_batch_records`) per subscriber wakeup so one lock acquisition
//! amortizes across an entire producer burst before socket `flush()`.

#[cfg(clean_islands)]
#[path = "tail_batch_coalescer_island.rs"]
mod tail_batch_coalescer_island;
#[cfg(clean_islands)]
pub use tail_batch_coalescer_island::{tail_batch_records_clamp, tail_flushed_advance};

/// Default maximum records drained per subscriber lock turn.
pub const DEFAULT_MAX_TAIL_BATCH_RECORDS: u64 = 128;

#[cfg(not(clean_islands))]
/// Monotonically advance the subscriber's flushed high-water mark.
#[must_use]
pub const fn tail_flushed_advance(cur_flushed: u64, cand_flushed: u64) -> u64 {
    if cur_flushed < cand_flushed {
        cand_flushed
    } else {
        cur_flushed
    }
}

#[cfg(not(clean_islands))]
/// Clamp per-wakeup drained record count to `max_batch_recs`.
#[must_use]
pub const fn tail_batch_records_clamp(cand_recs: u64, max_batch_recs: u64) -> u64 {
    if cand_recs < max_batch_recs {
        cand_recs
    } else {
        max_batch_recs
    }
}

contract_fn! {
    /// True iff `flushed_hw < published_hw` (unread records remain).
    #[must_use]
    pub const fn tail_has_backlog(flushed_hw: u64, published_hw: u64) -> bool
    clauses [ensures result == (flushed_hw < published_hw)]
    {
        flushed_hw < published_hw
    }
}

/// Planned `[start_offset, end_offset)` drain slice for a single subscriber wakeup.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TailDrainSlice {
    pub start_offset: u64,
    pub end_offset: u64,
    pub count: u64,
    pub more_backlog_remains: bool,
}

/// Per-subscriber fan-out micro-batch planner.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TailBatchCoalescer {
    flushed_hw: u64,
    last_batch_records: u64,
    max_batch_recs: u64,
}

impl Default for TailBatchCoalescer {
    fn default() -> Self {
        Self::new(0, DEFAULT_MAX_TAIL_BATCH_RECORDS)
    }
}

impl TailBatchCoalescer {
    #[must_use]
    pub const fn new(initial_offset: u64, max_batch_recs: u64) -> Self {
        let cap = if max_batch_recs == 0 {
            DEFAULT_MAX_TAIL_BATCH_RECORDS
        } else {
            max_batch_recs
        };
        Self {
            flushed_hw: initial_offset,
            last_batch_records: 0,
            max_batch_recs: cap,
        }
    }

    #[must_use]
    pub const fn flushed_hw(&self) -> u64 {
        self.flushed_hw
    }

    #[must_use]
    pub const fn last_batch_records(&self) -> u64 {
        self.last_batch_records
    }

    /// Compute the next bounded drain slice against `published_hw` (`None` if caught up).
    pub fn plan_drain(&mut self, published_hw: u64) -> Option<TailDrainSlice> {
        if !tail_has_backlog(self.flushed_hw, published_hw) {
            self.last_batch_records = 0;
            return None;
        }
        let avail = published_hw.saturating_sub(self.flushed_hw);
        let take = tail_batch_records_clamp(avail, self.max_batch_recs);
        let start = self.flushed_hw;
        let end = start.saturating_add(take);
        self.flushed_hw = tail_flushed_advance(self.flushed_hw, end);
        self.last_batch_records = take;
        Some(TailDrainSlice {
            start_offset: start,
            end_offset: self.flushed_hw,
            count: take,
            more_backlog_remains: tail_has_backlog(self.flushed_hw, published_hw),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn drains_burst_in_bounded_slices_until_caught_up() {
        let mut coal = TailBatchCoalescer::new(10, 64);
        assert_eq!(coal.plan_drain(10), None);

        // Producer publishes burst up to hw = 100 (90 records)
        let s1 = coal.plan_drain(100).unwrap();
        assert_eq!(
            s1,
            TailDrainSlice {
                start_offset: 10,
                end_offset: 74,
                count: 64,
                more_backlog_remains: true,
            }
        );
        let s2 = coal.plan_drain(100).unwrap();
        assert_eq!(
            s2,
            TailDrainSlice {
                start_offset: 74,
                end_offset: 100,
                count: 26,
                more_backlog_remains: false,
            }
        );
        assert_eq!(coal.plan_drain(100), None);
    }
}
