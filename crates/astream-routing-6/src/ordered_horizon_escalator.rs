// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `Durability::Ordered` full-flush horizon & `Escalation` hold scheduler
//! (`Astream.Broker.TlaOrderedHorizonEscalator`).
//!
//! Coordinates `F_BARRIERFSYNC` batches with periodic/escalated `F_FULLFSYNC`:
//! tracks the timestamp of the first barrier-only batch since the last full flush,
//! demands an immediate full flush when an escalated record arrives or when
//! `ORDERED_HORIZON` elapses, and monotonically advances `durable_head`.

#[cfg(clean_islands)]
#[path = "ordered_horizon_escalator_island.rs"]
mod ordered_horizon_escalator_island;
#[cfg(clean_islands)]
pub use ordered_horizon_escalator_island::{ordered_durable_advance, ordered_held_clamp};

/// Default maximum escalated records held awaiting full flush.
pub const DEFAULT_MAX_ESCALATED_HELD: u64 = 1_024;

#[cfg(not(clean_islands))]
/// Monotonically advance the broker's `F_FULLFSYNC`-backed durable head offset.
#[must_use]
pub const fn ordered_durable_advance(cur_durable: u64, cand_durable: u64) -> u64 {
    if cur_durable < cand_durable {
        cand_durable
    } else {
        cur_durable
    }
}

#[cfg(not(clean_islands))]
/// Clamp escalated held-record count to `max_held`.
#[must_use]
pub const fn ordered_held_clamp(cand_held: u64, max_held: u64) -> u64 {
    if cand_held < max_held {
        cand_held
    } else {
        max_held
    }
}

contract_fn! {
    /// True iff `age_ms >= horizon_ms` (a full flush is due for barrier-acked records).
    #[must_use]
    pub const fn ordered_horizon_due(horizon_ms: u64, age_ms: u64) -> bool
    clauses [ensures result == (horizon_ms <= age_ms)]
    {
        horizon_ms <= age_ms
    }
}

/// Flush action required after staging a batch under `Durability::Ordered`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OrderedFlushPlan {
    BarrierOnly,
    BarrierThenFullFlush { target_head: u64 },
}

/// Stateful `Durability::Ordered` flush & escalation scheduler.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OrderedHorizonEscalator {
    durable_head: u64,
    barrier_head: u64,
    oldest_unflushed_ms: Option<u64>,
    held_escalated: u64,
    horizon_ms: Option<u64>,
    max_held: u64,
}

impl OrderedHorizonEscalator {
    #[must_use]
    pub const fn new(horizon_ms: Option<u64>, max_held: u64) -> Self {
        let cap = if max_held == 0 {
            DEFAULT_MAX_ESCALATED_HELD
        } else {
            max_held
        };
        Self {
            durable_head: 0,
            barrier_head: 0,
            oldest_unflushed_ms: None,
            held_escalated: 0,
            horizon_ms,
            max_held: cap,
        }
    }

    #[must_use]
    pub const fn durable_head(&self) -> u64 {
        self.durable_head
    }

    #[must_use]
    pub const fn held_escalated(&self) -> u64 {
        self.held_escalated
    }

    /// Record a newly barrier-synced batch advancing `barrier_head` at `now_ms`.
    pub fn on_barrier_batch(
        &mut self,
        new_barrier_head: u64,
        escalated_in_batch: u64,
        now_ms: u64,
    ) -> OrderedFlushPlan {
        if new_barrier_head > self.barrier_head {
            self.barrier_head = new_barrier_head;
            if self.oldest_unflushed_ms.is_none() && self.barrier_head > self.durable_head {
                self.oldest_unflushed_ms = Some(now_ms);
            }
        }
        if escalated_in_batch > 0 {
            let cand_h = self.held_escalated.saturating_add(escalated_in_batch);
            self.held_escalated = ordered_held_clamp(cand_h, self.max_held);
            return OrderedFlushPlan::BarrierThenFullFlush {
                target_head: self.barrier_head,
            };
        }
        if let (Some(h_ms), Some(oldest_ms)) = (self.horizon_ms, self.oldest_unflushed_ms) {
            let age = now_ms.saturating_sub(oldest_ms);
            if ordered_horizon_due(h_ms, age) {
                return OrderedFlushPlan::BarrierThenFullFlush {
                    target_head: self.barrier_head,
                };
            }
        }
        OrderedFlushPlan::BarrierOnly
    }

    /// Complete a full flush covering `flushed_up_to`, releasing held escalated records if caught up.
    pub fn on_full_flush_complete(&mut self, flushed_up_to: u64) -> u64 {
        self.durable_head = ordered_durable_advance(self.durable_head, flushed_up_to);
        if self.durable_head >= self.barrier_head {
            self.oldest_unflushed_ms = None;
            self.held_escalated = 0;
        }
        self.durable_head
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn escalates_immediately_on_held_record_or_when_horizon_elapses() {
        let mut sched = OrderedHorizonEscalator::new(Some(250), 64);

        // Ordinary batch at t=1000 -> barrier only
        assert_eq!(
            sched.on_barrier_batch(10, 0, 1_000),
            OrderedFlushPlan::BarrierOnly
        );
        // At t=1250 (250ms >= horizon) -> full flush due!
        assert_eq!(
            sched.on_barrier_batch(15, 0, 1_250),
            OrderedFlushPlan::BarrierThenFullFlush { target_head: 15 }
        );
        assert_eq!(sched.on_full_flush_complete(15), 15);

        // Escalated record at t=1260 triggers immediate full flush even 10ms later!
        assert_eq!(
            sched.on_barrier_batch(16, 1, 1_260),
            OrderedFlushPlan::BarrierThenFullFlush { target_head: 16 }
        );
        assert_eq!(sched.held_escalated(), 1);
        assert_eq!(sched.on_full_flush_complete(16), 16);
        assert_eq!(sched.held_escalated(), 0);
    }
}
