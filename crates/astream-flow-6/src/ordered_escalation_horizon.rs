// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `Durability::Ordered` escalation held-head and full-flush poisoning tracker
//! (`Astream.Broker.TlaOrderedEscalationHorizon`, Island #276).
//!
//! Models the `broker.ordered-tier` state machine (`tests/fixtures/aterm-broker.escalate`):
//! - Ordinary batches ride `F_BARRIERFSYNC`, advancing `visible_head` and `staged_head`
//!   immediately while arming a `horizon_ms` full-flush deadline if `durable_head < visible_head`.
//! - Escalated batches (`Escalate::Subject`, `PrincipalPrefix`, or `Group`) advance
//!   `staged_head` while holding `visible_head` below the escalated record until a full
//!   `F_FULLFSYNC` succeeds.
//! - A failed full flush latches `poisoned` and `served_strict` forever for the open:
//!   `durable_head` and `visible_head` never advance onto the held batch, and any later
//!   flush or write is refused fail-closed.

#![allow(clippy::result_unit_err)]

#[cfg(clean_islands)]
#[path = "ordered_escalation_horizon_island.rs"]
mod ordered_escalation_horizon_island;
#[cfg(clean_islands)]
pub use ordered_escalation_horizon_island::{ordered_head_advance, ordered_horizon_clamp};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn ordered_head_advance(cur: u64, next_off: u64) -> u64 {
    if cur < next_off {
        next_off
    } else {
        cur
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn ordered_horizon_clamp(horizon_ms: u64, max_ms: u64) -> u64 {
    if horizon_ms < max_ms {
        horizon_ms
    } else {
        max_ms
    }
}

/// Default `aterm` Ordered horizon (`100` ms, matching `tests/fixtures/aterm-broker.escalate`).
pub const ATERM_ORDERED_HORIZON_MS: u64 = 100;

/// Maximum configurable Ordered horizon (`1` hour = `3_600_000` ms).
pub const MAX_ORDERED_HORIZON_MS: u64 = 3_600_000;

contract_fn! {
    /// Verified invariant check `durable <= visible`, linked via `clean-kernel-defeq` to
    /// `ordered_heads_ordered_isl`.
    #[must_use]
    pub const fn ordered_heads_ordered(durable: u64, visible: u64) -> bool
    clauses [ensures result == (durable <= visible)]
    {
        durable <= visible
    }
}

contract_fn! {
    /// Verified check that a failed full flush has poisoned the open (`poisoned_flag != 0`),
    /// linked via `clean-kernel-defeq` to `ordered_is_poisoned_isl`.
    #[must_use]
    pub const fn ordered_is_poisoned(poisoned_flag: u64) -> bool
    clauses [ensures result == (0 < poisoned_flag)]
    {
        0 < poisoned_flag
    }
}

/// Outcome of staging a batch on an `OrderedEscalationTracker`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OrderedStageVerdict {
    /// Ordinary batch acks immediately after `F_BARRIERFSYNC`; horizon timer armed at `due_at_ms`.
    AckOnBarrier {
        visible_head: u64,
        horizon_due_ms: Option<u64>,
    },
    /// Escalated batch holds `visible_head` and owes an immediate full flush before acking.
    HoldForFullFlush {
        held_visible_head: u64,
        staged_head: u64,
    },
    /// Open is poisoned by a prior failed full flush; refuse fail-closed.
    RefusedPoisoned,
}

/// Deterministic `Ordered` durability head & horizon tracker.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OrderedEscalationTracker {
    durable_head: u64,
    visible_head: u64,
    staged_head: u64,
    horizon_ms: u64,
    horizon_due_ms: Option<u64>,
    poisoned_flag: u64,
    served_strict: bool,
    full_flushes: u64,
    skipped_flushes: u64,
}

impl OrderedEscalationTracker {
    /// Create a tracker at `base_offset` with `horizon_ms` clamped to `MAX_ORDERED_HORIZON_MS`.
    #[must_use]
    pub const fn new(base_offset: u64, horizon_ms: u64) -> Self {
        let h = ordered_horizon_clamp(horizon_ms, MAX_ORDERED_HORIZON_MS);
        Self {
            durable_head: base_offset,
            visible_head: base_offset,
            staged_head: base_offset,
            horizon_ms: h,
            horizon_due_ms: None,
            poisoned_flag: 0,
            served_strict: false,
            full_flushes: 0,
            skipped_flushes: 0,
        }
    }

    #[must_use]
    pub const fn durable_head(&self) -> u64 {
        self.durable_head
    }

    #[must_use]
    pub const fn visible_head(&self) -> u64 {
        self.visible_head
    }

    #[must_use]
    pub const fn staged_head(&self) -> u64 {
        self.staged_head
    }

    #[must_use]
    pub const fn horizon_ms(&self) -> u64 {
        self.horizon_ms
    }

    #[must_use]
    pub const fn horizon_due_ms(&self) -> Option<u64> {
        self.horizon_due_ms
    }

    #[must_use]
    pub const fn is_poisoned(&self) -> bool {
        ordered_is_poisoned(self.poisoned_flag)
    }

    #[must_use]
    pub const fn served_strict(&self) -> bool {
        self.served_strict
    }

    #[must_use]
    pub const fn full_flushes(&self) -> u64 {
        self.full_flushes
    }

    #[must_use]
    pub const fn skipped_flushes(&self) -> u64 {
        self.skipped_flushes
    }

    /// Stage a batch ending at `batch_end` (`now_ms` monotonic millisecond clock).
    pub fn stage_batch(
        &mut self,
        batch_end: u64,
        escalated: bool,
        now_ms: u64,
    ) -> OrderedStageVerdict {
        if self.is_poisoned() {
            return OrderedStageVerdict::RefusedPoisoned;
        }
        let next_staged = ordered_head_advance(self.staged_head, batch_end);
        self.staged_head = next_staged;
        if escalated || self.served_strict || self.horizon_ms == 0 {
            OrderedStageVerdict::HoldForFullFlush {
                held_visible_head: self.visible_head,
                staged_head: self.staged_head,
            }
        } else {
            self.visible_head = ordered_head_advance(self.visible_head, next_staged);
            if self.durable_head < self.visible_head && self.horizon_due_ms.is_none() {
                self.horizon_due_ms = Some(now_ms.saturating_add(self.horizon_ms));
            }
            OrderedStageVerdict::AckOnBarrier {
                visible_head: self.visible_head,
                horizon_due_ms: self.horizon_due_ms,
            }
        }
    }

    /// Whether the Ordered horizon timer has fallen due at `now_ms`.
    #[must_use]
    pub const fn is_horizon_due(&self, now_ms: u64) -> bool {
        if self.is_poisoned() {
            return false;
        }
        match self.horizon_due_ms {
            Some(due) => now_ms >= due && self.durable_head < self.staged_head,
            None => false,
        }
    }

    /// Complete a full flush (`ok = true` on `F_FULLFSYNC` success, `false` on media failure).
    pub fn finish_full_flush(&mut self, ok: bool) -> Result<u64, ()> {
        if self.is_poisoned() {
            return Err(());
        }
        if !ok {
            self.poisoned_flag = 1;
            self.served_strict = true;
            self.horizon_due_ms = None;
            return Err(());
        }
        if self.durable_head >= self.staged_head {
            self.skipped_flushes = self.skipped_flushes.saturating_add(1);
            self.horizon_due_ms = None;
            return Ok(self.durable_head);
        }
        self.durable_head = ordered_head_advance(self.durable_head, self.staged_head);
        self.visible_head = ordered_head_advance(self.visible_head, self.staged_head);
        self.horizon_due_ms = None;
        self.full_flushes = self.full_flushes.saturating_add(1);
        Ok(self.durable_head)
    }

    /// Latch to `Strict` when Darwin refuses `F_BARRIERFSYNC` (`ENOTSUP` / `ENODEV`).
    pub fn latch_barrier_refused(&mut self) {
        self.served_strict = true;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn escalated_batch_holds_visible_head_and_failed_flush_poisons_forever() {
        let mut t = OrderedEscalationTracker::new(0, ATERM_ORDERED_HORIZON_MS);
        // Ordinary batch 0..3 rides barrier: visible=3, durable=0, due=1000+100.
        assert_eq!(
            t.stage_batch(3, false, 1_000),
            OrderedStageVerdict::AckOnBarrier {
                visible_head: 3,
                horizon_due_ms: Some(1_100),
            }
        );
        assert!(ordered_heads_ordered(t.durable_head(), t.visible_head()));
        assert!(!t.is_horizon_due(1_099));
        assert!(t.is_horizon_due(1_100));

        // Escalated batch 3..5 holds visible_head at 3!
        assert_eq!(
            t.stage_batch(5, true, 1_050),
            OrderedStageVerdict::HoldForFullFlush {
                held_visible_head: 3,
                staged_head: 5,
            }
        );
        assert_eq!(t.visible_head(), 3);
        assert_eq!(t.durable_head(), 0);

        // Full flush succeeds -> both durable and visible reach 5!
        assert_eq!(t.finish_full_flush(true), Ok(5));
        assert_eq!(t.durable_head(), 5);
        assert_eq!(t.visible_head(), 5);
        assert_eq!(t.full_flushes(), 1);
        // Redundant flush is skipped and counted.
        assert_eq!(t.finish_full_flush(true), Ok(5));
        assert_eq!(t.skipped_flushes(), 1);

        // Next escalated batch 5..7 suffers a failed full flush -> poisons!
        let _ = t.stage_batch(7, true, 2_000);
        assert_eq!(t.finish_full_flush(false), Err(()));
        assert!(t.is_poisoned());
        assert!(t.served_strict());
        assert_eq!(t.visible_head(), 5);
        assert_eq!(t.durable_head(), 5);
        // Subsequent success report or stage is refused; held batch 5..7 stays unseen!
        assert_eq!(t.finish_full_flush(true), Err(()));
        assert_eq!(
            t.stage_batch(8, false, 2_010),
            OrderedStageVerdict::RefusedPoisoned
        );
        assert_eq!(t.visible_head(), 5);
    }
}
