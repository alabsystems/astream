// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `Durability::Ordered { horizon }` idle-timer single-flush & covered-`flush_durable` skip
//! guard (`evidence/manifest.toml` `broker.ordered-tier`;
//! `Astream.Broker.TlaOrderedHorizonIdleTimerFlushGuard`).
//!
//! Enforces the `Ordered` horizon full-flush accounting laws:
//! - While `durable_head < log_head` and `now_ms < horizon_due_ms`, ordinary barrier commits
//!   issue ZERO early full flushes (`a_long_horizon_flushes_nothing_early`),
//! - When `now_ms >= horizon_due_ms` (either after a batch or on the writer's timed wake, or
//!   immediately when `horizon_ms == 0`), ONE full flush covers `log_head` and triggers a
//!   durable `Mark` for idle-mark subscribers (`aterm`'s notifier paging signal),
//! - Any subsequent `flush_durable` call when `durable_head >= target_head` is skipped and
//!   counted (`skipped_covered_flushes`) without touching the device!

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
#[path = "ordered_horizon_idle_timer_flush_guard_island.rs"]
mod ordered_horizon_idle_timer_flush_guard_island;
#[cfg(clean_islands)]
pub use ordered_horizon_idle_timer_flush_guard_island::{
    full_flush_count_advance_b155, horizon_ms_clamp_b155,
};

/// Maximum configured `Ordered` horizon (`3_600_000 ms` = 1 hour).
pub const MAX_ORDERED_HORIZON_MS: u64 = 3_600_000;

#[cfg(not(clean_islands))]
/// Clamp configured `Ordered` horizon to `MAX_ORDERED_HORIZON_MS`.
#[must_use]
pub const fn horizon_ms_clamp_b155(cand_horizon_ms: u64, max_horizon_ms: u64) -> u64 {
    if cand_horizon_ms < max_horizon_ms {
        cand_horizon_ms
    } else {
        max_horizon_ms
    }
}

#[cfg(not(clean_islands))]
/// Advance total issued full-flush counter monotonically.
#[must_use]
pub const fn full_flush_count_advance_b155(cur_flushes: u64, cand_flushes: u64) -> u64 {
    if cur_flushes < cand_flushes {
        cand_flushes
    } else {
        cur_flushes
    }
}

contract_fn! {
    /// True iff `durable_head < log_head` and `now_ms >= horizon_due_ms`.
    #[must_use]
    pub const fn ordered_horizon_due_now_b155(
        durable_head: u64,
        log_head: u64,
        now_ms: u64,
        horizon_due_ms: u64,
    ) -> bool
    clauses [ensures result == (durable_head < log_head && now_ms >= horizon_due_ms)]
    {
        durable_head < log_head && now_ms >= horizon_due_ms
    }
}

/// Writer decision for `Ordered` horizon timer and explicit `flush_durable` requests.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OrderedHorizonDecision {
    ArmedTimerWaitUntil {
        due_ms: u64,
    },
    NoUnflushedRecordsIdle,
    IssuedSingleFullFlushAndNotifyMarks {
        durable_head: u64,
        full_flushes: u64,
    },
    SkippedAlreadyCoveredFlush {
        durable_head: u64,
        skipped_flushes: u64,
    },
}

/// Tracks `Ordered` horizon timer arming, single-flush execution, and covered-flush skipping.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OrderedHorizonTimerGuard {
    horizon_ms: u64,
    log_head: u64,
    durable_head: u64,
    horizon_due_ms: Option<u64>,
    full_flushes: u64,
    skipped_flushes: u64,
}

impl OrderedHorizonTimerGuard {
    #[must_use]
    pub const fn new(horizon_ms: u64) -> Self {
        Self {
            horizon_ms: horizon_ms_clamp_b155(horizon_ms, MAX_ORDERED_HORIZON_MS),
            log_head: 0,
            durable_head: 0,
            horizon_due_ms: None,
            full_flushes: 0,
            skipped_flushes: 0,
        }
    }

    /// Record an ordinary barrier-committed batch reaching `new_head` at `now_ms`.
    pub fn on_ordinary_barrier_commit(
        &mut self,
        new_head: u64,
        now_ms: u64,
    ) -> OrderedHorizonDecision {
        if new_head > self.log_head {
            self.log_head = new_head;
        }
        if self.durable_head >= self.log_head {
            return OrderedHorizonDecision::NoUnflushedRecordsIdle;
        }
        let due = match self.horizon_due_ms {
            Some(d) => d,
            None => {
                let d = now_ms.saturating_add(self.horizon_ms);
                self.horizon_due_ms = Some(d);
                d
            }
        };
        if ordered_horizon_due_now_b155(self.durable_head, self.log_head, now_ms, due) {
            self.execute_full_flush()
        } else {
            OrderedHorizonDecision::ArmedTimerWaitUntil { due_ms: due }
        }
    }

    /// Poll timed wake at `now_ms`.
    pub fn on_timer_wake(&mut self, now_ms: u64) -> OrderedHorizonDecision {
        let Some(due) = self.horizon_due_ms else {
            return OrderedHorizonDecision::NoUnflushedRecordsIdle;
        };
        if ordered_horizon_due_now_b155(self.durable_head, self.log_head, now_ms, due) {
            self.execute_full_flush()
        } else {
            OrderedHorizonDecision::ArmedTimerWaitUntil { due_ms: due }
        }
    }

    /// Explicit `flush_durable(target_head)`: skips device flush if already covered!
    pub fn on_explicit_flush_durable(&mut self, target_head: u64) -> OrderedHorizonDecision {
        if self.durable_head >= target_head {
            self.skipped_flushes = self.skipped_flushes.saturating_add(1);
            OrderedHorizonDecision::SkippedAlreadyCoveredFlush {
                durable_head: self.durable_head,
                skipped_flushes: self.skipped_flushes,
            }
        } else {
            self.execute_full_flush()
        }
    }

    fn execute_full_flush(&mut self) -> OrderedHorizonDecision {
        self.durable_head = self.log_head;
        self.horizon_due_ms = None;
        let next = self.full_flushes.saturating_add(1);
        self.full_flushes = full_flush_count_advance_b155(self.full_flushes, next);
        OrderedHorizonDecision::IssuedSingleFullFlushAndNotifyMarks {
            durable_head: self.durable_head,
            full_flushes: self.full_flushes,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flushes_nothing_early_flushes_once_at_horizon_and_skips_covered_flush_durable() {
        let mut g = OrderedHorizonTimerGuard::new(250);
        assert_eq!(
            g.on_ordinary_barrier_commit(2, 1_000),
            OrderedHorizonDecision::ArmedTimerWaitUntil { due_ms: 1_250 }
        );
        // Second publish at 1_100 ms (< 1_250 ms) flushes nothing early!
        assert_eq!(
            g.on_ordinary_barrier_commit(4, 1_100),
            OrderedHorizonDecision::ArmedTimerWaitUntil { due_ms: 1_250 }
        );
        // Timer wake at 1_250 ms issues ONE full flush covering 4 and notifies durable marks!
        assert_eq!(
            g.on_timer_wake(1_250),
            OrderedHorizonDecision::IssuedSingleFullFlushAndNotifyMarks {
                durable_head: 4,
                full_flushes: 1,
            }
        );
        // Subsequent `flush_durable(4)` is already covered -> skipped & counted!
        assert_eq!(
            g.on_explicit_flush_durable(4),
            OrderedHorizonDecision::SkippedAlreadyCoveredFlush {
                durable_head: 4,
                skipped_flushes: 1,
            }
        );
    }
}
