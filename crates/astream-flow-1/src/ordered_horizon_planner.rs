// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm-link` Ordered-tier horizon & pipeline-window flush planner
//! (`Astream.Broker.TlaOrderedHorizonPlanner`).
//!
//! Coordinates per-batch ordering barriers (`F_BARRIERFSYNC`) and periodic horizon full
//! flushes (`F_FULLFSYNC` at `ORDERED_HORIZON = 100ms` over `PIPELINE_WINDOW = 64`):
//! - Guarantees `durable_head <= ordered_head` and `window_used <= max_window` at every step.
//! - Issues at most one full flush per `horizon_ms` window, satisfying both
//!   `broker.bench.ordered-floor` and `broker.bench.ordered-full-flush-ceiling`.

#[cfg(clean_islands)]
#[path = "ordered_horizon_planner_island.rs"]
mod ordered_horizon_planner_island;
#[cfg(clean_islands)]
pub use ordered_horizon_planner_island::{ordered_durable_clamp, ordered_window_clamp};

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn ordered_durable_clamp(durable: u64, ordered: u64) -> u64 {
    if durable < ordered {
        durable
    } else {
        ordered
    }
}

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn ordered_window_clamp(in_flight: u64, max_window: u64) -> u64 {
    if in_flight < max_window {
        in_flight
    } else {
        max_window
    }
}

contract_fn! {
    /// Verified check that the full-flush horizon has elapsed (`horizon_ms <= elapsed_ms`),
    /// linked via `clean-kernel-defeq` to `ordered_horizon_elapsed_isl`.
    #[must_use]
    pub const fn ordered_horizon_elapsed(
        elapsed_ms: u64,
        horizon_ms: u64,
    ) -> bool
    clauses [ensures result == (horizon_ms <= elapsed_ms)]
    {
        horizon_ms <= elapsed_ms
    }
}

/// Sync primitive required for a committed Ordered-tier batch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OrderedFlushStep {
    /// Issue an ordering barrier (`F_BARRIERFSYNC`) only; horizon has not yet elapsed.
    BarrierOnly {
        /// Milliseconds remaining until the next `F_FULLFSYNC` horizon fires.
        remaining_horizon_ms: u64,
    },
    /// Horizon elapsed since the oldest un-flushed ordered ack: issue `F_FULLFSYNC` and
    /// advance `durable_head` to `ordered_head`.
    HorizonFullSync,
}

/// Stateful Ordered-tier horizon & pipeline-window planner.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OrderedHorizonPlanner {
    horizon_ms: u64,
    max_window: u64,
    durable_head: u64,
    ordered_head: u64,
    window_used: u64,
    first_unflushed_ms: Option<u64>,
    full_flush_count: u64,
    barrier_count: u64,
}

impl OrderedHorizonPlanner {
    /// Default `aterm-link` Ordered-tier horizon (`100` ms).
    pub const ATERM_ORDERED_HORIZON_MS: u64 = 100;
    /// Default `aterm-link` pipelined publish window (`64` in-flight frames).
    pub const ATERM_PIPELINE_WINDOW: u64 = 64;

    /// Create a planner with `horizon_ms` (`0` means flush in full every batch) and
    /// `max_window` (`>= 1`).
    #[must_use]
    pub const fn new(horizon_ms: u64, max_window: u64) -> Self {
        let win = if max_window < 1 { 1 } else { max_window };
        Self {
            horizon_ms,
            max_window: win,
            durable_head: 0,
            ordered_head: 0,
            window_used: 0,
            first_unflushed_ms: None,
            full_flush_count: 0,
            barrier_count: 0,
        }
    }

    /// Durable head covered by a completed `F_FULLFSYNC` (`<= ordered_head`).
    #[must_use]
    pub const fn durable_head(&self) -> u64 {
        self.durable_head
    }

    /// Barrier-ordered head (`>= durable_head`).
    #[must_use]
    pub const fn ordered_head(&self) -> u64 {
        self.ordered_head
    }

    /// Clamped batch size of the most recent pipelined step (`<= max_window`).
    #[must_use]
    pub const fn window_used(&self) -> u64 {
        self.window_used
    }

    /// Cumulative `F_FULLFSYNC` count planned.
    #[must_use]
    pub const fn full_flush_count(&self) -> u64 {
        self.full_flush_count
    }

    /// Cumulative `F_BARRIERFSYNC` count planned.
    #[must_use]
    pub const fn barrier_count(&self) -> u64 {
        self.barrier_count
    }

    /// Plan the sync step for a batch of `raw_batch_records` committed at monotonic `now_ms`.
    pub fn record_batch(&mut self, raw_batch_records: u64, now_ms: u64) -> OrderedFlushStep {
        let clamped_win = ordered_window_clamp(raw_batch_records, self.max_window);
        let next_ordered = self.ordered_head.saturating_add(clamped_win);
        let anchor_ms = match self.first_unflushed_ms {
            Some(t) => t,
            None if clamped_win > 0 => {
                self.first_unflushed_ms = Some(now_ms);
                now_ms
            }
            None => now_ms,
        };
        let elapsed = now_ms.saturating_sub(anchor_ms);
        self.ordered_head = next_ordered;
        self.window_used = clamped_win;

        if self.durable_head < self.ordered_head
            && ordered_horizon_elapsed(elapsed, self.horizon_ms)
        {
            self.durable_head = ordered_durable_clamp(self.ordered_head, self.ordered_head);
            self.first_unflushed_ms = None;
            self.full_flush_count = self.full_flush_count.saturating_add(1);
            OrderedFlushStep::HorizonFullSync
        } else {
            self.durable_head = ordered_durable_clamp(self.durable_head, self.ordered_head);
            self.barrier_count = self.barrier_count.saturating_add(1);
            OrderedFlushStep::BarrierOnly {
                remaining_horizon_ms: self.horizon_ms.saturating_sub(elapsed),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn issues_barriers_within_100ms_horizon_and_at_most_ten_full_flushes_per_second() {
        let mut p = OrderedHorizonPlanner::new(
            OrderedHorizonPlanner::ATERM_ORDERED_HORIZON_MS,
            OrderedHorizonPlanner::ATERM_PIPELINE_WINDOW,
        );

        // Simulate 1,000 ms of pipelined 64-record batches arriving every 10 ms (100 batches = 6,400 ops).
        let mut step_ms = 0u64;
        while step_ms < 1_000 {
            let _ = p.record_batch(64, step_ms);
            assert!(p.durable_head() <= p.ordered_head());
            assert!(p.window_used() <= OrderedHorizonPlanner::ATERM_PIPELINE_WINDOW);
            step_ms += 10;
        }
        assert_eq!(p.ordered_head(), 6_400);
        // Full flushes begin >= 100 ms after first un-flushed ack -> <= 10 full flushes in 1s!
        assert!(p.full_flush_count() >= 8 && p.full_flush_count() <= 10);
        assert!(p.barrier_count() >= 90);
    }
}
