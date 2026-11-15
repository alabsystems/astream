// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Credit-Gated Subscriber Tail Coalescer & Wake Scheduler (`Astream.Broker.TlaTailCreditScheduler`).
//!
//! Addresses two high-load fanout & WAN subscriber failure modes in `astream-broker`:
//! 1. **64+ Subscriber Wake Amplification**: Waking a subscriber whose outbound socket already holds
//!    `max_credit` unacknowledged batches only burns mutex & condvar cycles.
//! 2. **High-RTT WAN Catch-Up Coalescing**: While a slow WAN subscriber is saturated at
//!    `inflight == max_credit`, hundreds of log appends advance `log_hw`. Instead of queuing
//!    hundreds of per-append wakeups, [`TailCreditScheduler`] monotonically records `pending_hw`
//!    (`prev_hw <= pending_hw`) and emits a single coalesced catch-up range `[cursor..dispatch_end)`
//!    the instant `ack_batches` frees credit (`inflight < max_credit && cursor < pending_hw`).

#[cfg(clean_islands)]
#[path = "tail_credit_island.rs"]
mod tail_credit_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tail_inflight_clamp(inflight: u64, max_credit: u64) -> u64 {
    if inflight < max_credit {
        inflight
    } else {
        max_credit
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tail_pending_hw_advance(prev_hw: u64, cand_hw: u64) -> u64 {
    if prev_hw < cand_hw {
        cand_hw
    } else {
        prev_hw
    }
}
#[cfg(clean_islands)]
pub use tail_credit_island::{tail_inflight_clamp, tail_pending_hw_advance};

/// Default maximum in-flight unacknowledged batches per subscriber (`16`).
pub const DEFAULT_SUBSCRIBER_MAX_CREDIT: u64 = 16;

/// Hard ceiling on subscriber batch credit (`4_096`).
pub const HARD_MAX_SUBSCRIBER_CREDIT: u64 = 4_096;

/// Default maximum log records packed into one coalesced catch-up dispatch (`256`).
pub const DEFAULT_MAX_RECORDS_PER_DISPATCH: u64 = 256;

contract_fn! {
    /// Verified check whether a subscriber has both available credit (`inflight < max_credit`)
    /// and unread log records (`cursor < hw`), linked via `clean-kernel-defeq` to
    /// `tail_can_dispatch_isl`.
    #[must_use]
    pub const fn tail_can_dispatch(
        inflight: u64,
        max_credit: u64,
        cursor: u64,
        hw: u64,
    ) -> bool
    clauses [ensures result == ((inflight < max_credit) && (cursor < hw))]
    {
        (inflight < max_credit) && (cursor < hw)
    }
}

/// Dispatch slice `[start_offset..end_offset)` granted to a subscriber's tail writer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TailDispatchGrant {
    pub start_offset: u64,
    pub end_offset: u64,
    pub inflight_after: u64,
}

/// Per-subscriber credit-gated wake & offset-range coalescer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TailCreditScheduler {
    cursor: u64,
    pending_hw: u64,
    inflight: u64,
    max_credit: u64,
    max_records_per_dispatch: u64,
    suppressed_wakes: u64,
}

impl TailCreditScheduler {
    /// Create a scheduler starting at `initial_cursor` with `max_credit` (`1..=HARD_MAX_SUBSCRIBER_CREDIT`).
    #[must_use]
    pub const fn new(initial_cursor: u64, max_credit: u64, max_records_per_dispatch: u64) -> Self {
        let credit = if max_credit == 0 {
            1
        } else if max_credit > HARD_MAX_SUBSCRIBER_CREDIT {
            HARD_MAX_SUBSCRIBER_CREDIT
        } else {
            max_credit
        };
        let chunk = if max_records_per_dispatch == 0 {
            1
        } else {
            max_records_per_dispatch
        };
        Self {
            cursor: initial_cursor,
            pending_hw: initial_cursor,
            inflight: 0,
            max_credit: credit,
            max_records_per_dispatch: chunk,
            suppressed_wakes: 0,
        }
    }

    /// Next unread log offset for this subscriber.
    #[must_use]
    pub const fn cursor(&self) -> u64 {
        self.cursor
    }

    /// Highest log high-water mark observed (`>= cursor`).
    #[must_use]
    pub const fn pending_hw(&self) -> u64 {
        self.pending_hw
    }

    /// Currently unacknowledged dispatched batches (`<= max_credit`).
    #[must_use]
    pub const fn inflight(&self) -> u64 {
        self.inflight
    }

    /// Number of redundant producer notifications coalesced while `inflight == max_credit`.
    #[must_use]
    pub const fn suppressed_wakes(&self) -> u64 {
        self.suppressed_wakes
    }

    /// Notify scheduler that the broker log reached `observed_hw`.
    ///
    /// Returns `true` ONLY when the subscriber thread should actually be woken (`inflight < max_credit`
    /// and `cursor < pending_hw`); otherwise coalesces the wakeup into `pending_hw`!
    pub fn on_log_append(&mut self, observed_hw: u64) -> bool {
        self.pending_hw = tail_pending_hw_advance(self.pending_hw, observed_hw);
        if tail_can_dispatch(self.inflight, self.max_credit, self.cursor, self.pending_hw) {
            true
        } else {
            if self.cursor < self.pending_hw {
                self.suppressed_wakes = self.suppressed_wakes.saturating_add(1);
            }
            false
        }
    }

    /// Claim the next coalesced `[start_offset..end_offset)` batch if credit and unread records exist.
    pub fn poll_dispatch(&mut self) -> Option<TailDispatchGrant> {
        if !tail_can_dispatch(self.inflight, self.max_credit, self.cursor, self.pending_hw) {
            return None;
        }
        let avail = self.pending_hw.saturating_sub(self.cursor);
        let step = if avail < self.max_records_per_dispatch {
            avail
        } else {
            self.max_records_per_dispatch
        };
        let start = self.cursor;
        let end = start.saturating_add(step);
        self.cursor = end;
        self.inflight = tail_inflight_clamp(self.inflight.saturating_add(1), self.max_credit);
        Some(TailDispatchGrant {
            start_offset: start,
            end_offset: end,
            inflight_after: self.inflight,
        })
    }

    /// Acknowledge `acked_batches` completed writes/ACKs and report whether another coalesced
    /// batch is immediately ready to dispatch!
    pub fn ack_batches(&mut self, acked_batches: u64) -> bool {
        let reduced = self.inflight.saturating_sub(acked_batches);
        self.inflight = tail_inflight_clamp(reduced, self.max_credit);
        tail_can_dispatch(self.inflight, self.max_credit, self.cursor, self.pending_hw)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clean_twins_match_invariants() {
        assert_eq!(tail_inflight_clamp(3, 16), 3);
        assert_eq!(tail_inflight_clamp(99, 16), 16);
        assert_eq!(tail_pending_hw_advance(50, 75), 75);
        assert_eq!(tail_pending_hw_advance(75, 40), 75);
        assert!(tail_can_dispatch(0, 2, 10, 11));
        assert!(!tail_can_dispatch(2, 2, 10, 11));
        assert!(!tail_can_dispatch(0, 2, 10, 10));
    }

    #[test]
    fn suppresses_wake_storms_when_saturated_and_catches_up_in_one_coalesced_grant() {
        let mut sched = TailCreditScheduler::new(0, 2, 100);
        assert!(sched.on_log_append(5));
        assert_eq!(
            sched.poll_dispatch(),
            Some(TailDispatchGrant {
                start_offset: 0,
                end_offset: 5,
                inflight_after: 1,
            })
        );
        assert!(sched.on_log_append(12));
        assert_eq!(
            sched.poll_dispatch(),
            Some(TailDispatchGrant {
                start_offset: 5,
                end_offset: 12,
                inflight_after: 2,
            })
        );

        // Credit exhausted (`2 == 2`): 50 log appends all coalesce without waking the subscriber!
        for hw in 13..=62 {
            assert!(!sched.on_log_append(hw));
        }
        assert_eq!(sched.suppressed_wakes(), 50);
        assert_eq!(sched.poll_dispatch(), None);

        // One ACK frees 1 credit and immediately schedules a single coalesced `[12..62)` batch!
        assert!(sched.ack_batches(1));
        assert_eq!(
            sched.poll_dispatch(),
            Some(TailDispatchGrant {
                start_offset: 12,
                end_offset: 62,
                inflight_after: 2,
            })
        );
    }
}
