// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Per-Subscriber Edge-Triggered Wakeup & Batch Coalescer
//! (`Astream.Broker.TlaSubscriberWakeCoalesce`).
//!
//! Broadcasting `Condvar::notify_all()` on every single group-committed append wakes all 64+
//! subscriber threads even when a subscriber has *not yet drained* the records from its previous
//! wakeup (`acked_cursor < notified_hw`), turning high-fan-out tail loops into lock-contention
//! stampedes (`DESIGN-aterm-fabric.md` §13).
//!
//! [`SubscriberWakeGate`] enforces edge-triggered + watermark-batched wakeups:
//! - If [`sub_already_has_unconsumed_wake`]`(acked_cursor, notified_hw)` holds, a signal is
//!   already pending in user space so redundant kernel `futex`/`ulock` wakeups are elided!
//! - Otherwise, wakes immediately once unread backlog reaches `batch_target` (clamped via
//!   Clean-origin [`sub_wake_backlog_clamp`]), when `urgent` is set, or when the quiet hold window
//!   expires, advancing `notified_hw` monotonically via Clean-origin [`sub_wake_hw_advance`].

#[cfg(clean_islands)]
#[path = "subscriber_wakeup_coalesce_island.rs"]
mod subscriber_wakeup_coalesce_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sub_wake_backlog_clamp(cand_backlog: u64, batch_target: u64) -> u64 {
    if cand_backlog < batch_target {
        cand_backlog
    } else {
        batch_target
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sub_wake_hw_advance(cur_hw: u64, cand_hw: u64) -> u64 {
    if cur_hw < cand_hw {
        cand_hw
    } else {
        cur_hw
    }
}
#[cfg(clean_islands)]
pub use subscriber_wakeup_coalesce_island::{sub_wake_backlog_clamp, sub_wake_hw_advance};

/// Default unread record threshold that triggers an immediate subscriber wakeup.
pub const DEFAULT_SUB_WAKE_BATCH_TARGET: u64 = 16;

contract_fn! {
    /// Kernel-certified check that a subscriber already holds an unconsumed wakeup
    /// (`acked_cursor < notified_hw`), linked via `clean-kernel-defeq` to
    /// `sub_already_has_unconsumed_wake_isl`.
    #[must_use]
    pub const fn sub_already_has_unconsumed_wake(acked_cursor: u64, notified_hw: u64) -> bool
    clauses [ensures result == (acked_cursor < notified_hw)]
    {
        acked_cursor < notified_hw
    }
}

/// Decision returned when evaluating whether to wake a tailing subscriber thread.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubscriberWakeDecision {
    /// Log has no unread records beyond `acked_cursor`.
    IdleUpToDate,
    /// Subscriber was already notified up to `notified_hw > acked_cursor` and has not yet drained;
    /// skip redundant kernel wakeup.
    SuppressAlreadyNotified { notified_hw: u64 },
    /// Unread records (`< batch_target`) are held briefly to coalesce micro-batches.
    CoalescingMicroBatch { clamped_backlog: u64 },
    /// Signal the subscriber's `Condvar`/park token now, covering up to `new_notified_hw`.
    WakeNow { new_notified_hw: u64 },
}

/// Stateful per-subscriber wakeup gate backed by `Astream.Broker.TlaSubscriberWakeCoalesce`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SubscriberWakeGate {
    acked_cursor: u64,
    notified_hw: u64,
    clamped_backlog: u64,
    batch_target: u64,
    hold_ticks: u64,
    max_hold_ticks: u64,
}

impl SubscriberWakeGate {
    /// Construct a wakeup gate starting at `initial_cursor`, with `batch_target` (`>= 1`) and
    /// `max_hold_ticks` (`0` wakes on every first unread record while still suppressing redundant
    /// unconsumed wakeups).
    #[must_use]
    pub const fn new(initial_cursor: u64, batch_target: u64, max_hold_ticks: u64) -> Self {
        let cap = if batch_target == 0 { 1 } else { batch_target };
        Self {
            acked_cursor: initial_cursor,
            notified_hw: initial_cursor,
            clamped_backlog: 0,
            batch_target: cap,
            hold_ticks: 0,
            max_hold_ticks,
        }
    }

    /// Construct a gate with [`DEFAULT_SUB_WAKE_BATCH_TARGET`] and `1` tick max hold.
    #[must_use]
    pub const fn with_defaults(initial_cursor: u64) -> Self {
        Self::new(initial_cursor, DEFAULT_SUB_WAKE_BATCH_TARGET, 1)
    }

    /// Highest log offset drained by the subscriber before re-parking.
    #[must_use]
    pub const fn acked_cursor(&self) -> u64 {
        self.acked_cursor
    }

    /// Monotone high-water offset already covered by an issued wakeup.
    #[must_use]
    pub const fn notified_hw(&self) -> u64 {
        self.notified_hw
    }

    /// Record that the subscriber drained up to `new_cursor` and is about to re-check/park.
    pub fn mark_drained_to(&mut self, new_cursor: u64) {
        if new_cursor > self.acked_cursor {
            self.acked_cursor = new_cursor;
        }
        if self.acked_cursor > self.notified_hw {
            self.notified_hw = sub_wake_hw_advance(self.notified_hw, self.acked_cursor);
        }
        self.clamped_backlog = 0;
        self.hold_ticks = 0;
    }

    /// Evaluate a new broker `log_hw` append and decide whether to issue a kernel wakeup.
    pub fn on_append(&mut self, log_hw: u64, urgent: bool) -> SubscriberWakeDecision {
        if log_hw <= self.acked_cursor {
            self.clamped_backlog = 0;
            return SubscriberWakeDecision::IdleUpToDate;
        }
        if sub_already_has_unconsumed_wake(self.acked_cursor, self.notified_hw) {
            // Extend logical target without issuing a second kernel condvar signal!
            self.notified_hw = sub_wake_hw_advance(self.notified_hw, log_hw);
            return SubscriberWakeDecision::SuppressAlreadyNotified {
                notified_hw: self.notified_hw,
            };
        }

        let unread = log_hw.saturating_sub(self.acked_cursor);
        let clamped = sub_wake_backlog_clamp(unread, self.batch_target);
        self.clamped_backlog = clamped;

        if urgent || self.max_hold_ticks == 0 || unread >= self.batch_target {
            let next_hw = sub_wake_hw_advance(self.notified_hw, log_hw);
            self.notified_hw = next_hw;
            self.clamped_backlog = 0;
            self.hold_ticks = 0;
            SubscriberWakeDecision::WakeNow {
                new_notified_hw: next_hw,
            }
        } else {
            SubscriberWakeDecision::CoalescingMicroBatch {
                clamped_backlog: clamped,
            }
        }
    }

    /// Advance the quiet hold timer and wake any subscriber holding a coalesced micro-batch.
    pub fn on_tick(&mut self, log_hw: u64) -> Option<u64> {
        if log_hw <= self.acked_cursor
            || sub_already_has_unconsumed_wake(self.acked_cursor, self.notified_hw)
        {
            return None;
        }
        self.hold_ticks = self.hold_ticks.saturating_add(1);
        if self.hold_ticks >= self.max_hold_ticks {
            let next_hw = sub_wake_hw_advance(self.notified_hw, log_hw);
            self.notified_hw = next_hw;
            self.clamped_backlog = 0;
            self.hold_ticks = 0;
            Some(next_hw)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn suppresses_thundering_herd_re_wakes_and_flushes_micro_batch_on_target_or_tick() {
        let mut g = SubscriberWakeGate::new(100, 4, 2);
        assert_eq!(
            g.on_append(100, false),
            SubscriberWakeDecision::IdleUpToDate
        );

        // Micro-batch of 2 records coalesces briefly.
        assert_eq!(
            g.on_append(102, false),
            SubscriberWakeDecision::CoalescingMicroBatch { clamped_backlog: 2 }
        );
        // Reaching 4 unread records wakes immediately!
        assert_eq!(
            g.on_append(104, false),
            SubscriberWakeDecision::WakeNow {
                new_notified_hw: 104
            }
        );

        // Further appends before subscriber drains are suppressed (zero redundant futex wakes!).
        assert_eq!(
            g.on_append(110, false),
            SubscriberWakeDecision::SuppressAlreadyNotified { notified_hw: 110 }
        );

        // Subscriber drains up to 110, then 1 record arrives and flushes after 2 quiet ticks.
        g.mark_drained_to(110);
        assert_eq!(
            g.on_append(111, false),
            SubscriberWakeDecision::CoalescingMicroBatch { clamped_backlog: 1 }
        );
        assert_eq!(g.on_tick(111), None);
        assert_eq!(g.on_tick(111), Some(111));
    }
}
