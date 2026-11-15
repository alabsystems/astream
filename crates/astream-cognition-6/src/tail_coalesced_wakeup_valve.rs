// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Generation-fenced subscriber wakeup coalescing valve for 64+ fan-out `tail_loop`
//! (`Astream.Broker.TlaTailCoalescedWakeup`).
//!
//! Addresses the 64-subscriber `Condvar::notify_all()` contention cliff documented in
//! `DESIGN-aterm-fabric.md` §13: suppresses redundant `notify_all()` calls when either no
//! parked waiters exist or an unconsumed wake epoch already covers pending subscribers up to a
//! bounded batch horizon (`MAX_COALESCED_BATCH = 64`), while guaranteeing immediate flush when
//! a waiter parks behind `published_hw` or an explicit flush boundary arrives.

#[cfg(clean_islands)]
#[path = "tail_coalesced_wakeup_valve_island.rs"]
mod tail_coalesced_wakeup_valve_island;
#[cfg(clean_islands)]
pub use tail_coalesced_wakeup_valve_island::{
    tail_batch_horizon_clamp_b119, tail_notified_hw_advance_b119,
};

#[cfg(not(clean_islands))]
/// Clamp the coalesced wakeup batch horizon to `max_batch`.
#[must_use]
pub const fn tail_batch_horizon_clamp_b119(cand_batch: u64, max_batch: u64) -> u64 {
    if cand_batch < max_batch {
        cand_batch
    } else {
        max_batch
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `notified_hw`.
#[must_use]
pub const fn tail_notified_hw_advance_b119(cur_notified: u64, cand_notified: u64) -> u64 {
    if cur_notified < cand_notified {
        cand_notified
    } else {
        cur_notified
    }
}

contract_fn! {
    /// True iff `published_hw` has advanced strictly past `notified_hw`.
    #[must_use]
    pub const fn tail_has_unnotified_delta_b119(notified_hw: u64, published_hw: u64) -> bool
    clauses [ensures result == (notified_hw < published_hw)]
    {
        notified_hw < published_hw
    }
}

pub const MAX_COALESCED_BATCH: u64 = 64;

/// Decision returned on producer append or idle flush.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TailWakeDecision {
    /// Emit `Condvar::notify_all()` outside the log lock for `notified_hw`.
    NotifyAll {
        notified_hw: u64,
        pending_delta: u64,
    },
    /// Suppress wakeup: either no parked waiters or batch horizon not yet reached.
    CoalescedSkip { unnotified_delta: u64 },
}

/// Coalesced `tail_loop` wakeup valve.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TailCoalescedWakeupValve {
    batch_horizon: u64,
    published_hw: u64,
    notified_hw: u64,
    parked_waiters: u64,
    emitted_wakes: u64,
    coalesced_skips: u64,
}

impl Default for TailCoalescedWakeupValve {
    fn default() -> Self {
        Self::new(8)
    }
}

impl TailCoalescedWakeupValve {
    #[must_use]
    pub const fn new(raw_batch_horizon: u64) -> Self {
        let clamped = tail_batch_horizon_clamp_b119(raw_batch_horizon, MAX_COALESCED_BATCH);
        let horizon = if clamped == 0 { 1 } else { clamped };
        Self {
            batch_horizon: horizon,
            published_hw: 0,
            notified_hw: 0,
            parked_waiters: 0,
            emitted_wakes: 0,
            coalesced_skips: 0,
        }
    }

    #[must_use]
    pub const fn batch_horizon(&self) -> u64 {
        self.batch_horizon
    }

    #[must_use]
    pub const fn notified_hw(&self) -> u64 {
        self.notified_hw
    }

    #[must_use]
    pub const fn emitted_wakes(&self) -> u64 {
        self.emitted_wakes
    }

    #[must_use]
    pub const fn coalesced_skips(&self) -> u64 {
        self.coalesced_skips
    }

    pub fn set_parked_waiters(&mut self, waiters: u64) {
        self.parked_waiters = waiters;
    }

    /// Record a new producer `hw` and decide whether to wake parked `tail_loop` threads now.
    pub fn on_append(&mut self, new_hw: u64, force_flush: bool) -> TailWakeDecision {
        self.published_hw = tail_notified_hw_advance_b119(self.published_hw, new_hw);
        if !tail_has_unnotified_delta_b119(self.notified_hw, self.published_hw) {
            return TailWakeDecision::CoalescedSkip {
                unnotified_delta: 0,
            };
        }
        let delta = self.published_hw.saturating_sub(self.notified_hw);
        if self.parked_waiters == 0 {
            self.coalesced_skips = self.coalesced_skips.saturating_add(1);
            return TailWakeDecision::CoalescedSkip {
                unnotified_delta: delta,
            };
        }
        if force_flush || delta >= self.batch_horizon {
            self.notified_hw = tail_notified_hw_advance_b119(self.notified_hw, self.published_hw);
            self.emitted_wakes = self.emitted_wakes.saturating_add(1);
            TailWakeDecision::NotifyAll {
                notified_hw: self.notified_hw,
                pending_delta: delta,
            }
        } else {
            self.coalesced_skips = self.coalesced_skips.saturating_add(1);
            TailWakeDecision::CoalescedSkip {
                unnotified_delta: delta,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn coalesces_bursts_up_to_horizon_and_flushes_immediately_on_force() {
        let mut v = TailCoalescedWakeupValve::new(4);
        v.set_parked_waiters(64);
        assert_eq!(
            v.on_append(1, false),
            TailWakeDecision::CoalescedSkip {
                unnotified_delta: 1
            }
        );
        assert_eq!(
            v.on_append(3, false),
            TailWakeDecision::CoalescedSkip {
                unnotified_delta: 3
            }
        );
        assert_eq!(
            v.on_append(4, false),
            TailWakeDecision::NotifyAll {
                notified_hw: 4,
                pending_delta: 4
            }
        );
        assert_eq!(
            v.on_append(5, true),
            TailWakeDecision::NotifyAll {
                notified_hw: 5,
                pending_delta: 1
            }
        );
        assert_eq!(v.emitted_wakes(), 2);
        assert_eq!(v.coalesced_skips(), 2);
    }
}
