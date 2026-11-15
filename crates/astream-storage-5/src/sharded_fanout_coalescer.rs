// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Micro-batched shard append -> subscriber wakeup coalescer
//! (`Astream.Broker.TlaShardedFanoutCoalescer`).
//!
//! Mitigates the `Condvar::notify_all()` thundering-herd under 64+ subscribers (`DESIGN-aterm-fabric.md` §13)
//! by coalescing append notifications up to `max_batch_records` or `max_linger_us`, while proving
//! bounded pending-record accumulation and monotonic `wake_epoch` progression.

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
#[path = "sharded_fanout_coalescer_island.rs"]
mod sharded_fanout_coalescer_island;
#[cfg(clean_islands)]
pub use sharded_fanout_coalescer_island::{fanout_batch_clamp, fanout_wake_epoch_advance};

#[cfg(not(clean_islands))]
/// Clamp coalesced un-notified record count to `max_batch`.
#[must_use]
pub const fn fanout_batch_clamp(cand_pending: u64, max_batch: u64) -> u64 {
    if cand_pending < max_batch {
        cand_pending
    } else {
        max_batch
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the shard wakeup epoch.
#[must_use]
pub const fn fanout_wake_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `pending` has reached `max_batch` and must immediately trigger a subscriber wake.
    #[must_use]
    pub const fn fanout_batch_full(pending: u64, max_batch: u64) -> bool
    clauses [ensures result == (pending >= max_batch)]
    {
        pending >= max_batch
    }
}

/// Decision after recording a broker append or timer tick.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FanoutCoalesceAction {
    CoalescePending {
        pending_records: u64,
    },
    EmitWake {
        wake_epoch: u64,
        flushed_records: u64,
        latest_hw: u64,
    },
}

/// Stateful wakeup coalescer for a broker log shard.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ShardedFanoutCoalescer {
    max_batch_records: u64,
    max_linger_us: u64,
    pending_records: u64,
    first_pending_us: u64,
    latest_hw: u64,
    wake_epoch: u64,
}

impl ShardedFanoutCoalescer {
    #[must_use]
    pub const fn new(max_batch_records: u64, max_linger_us: u64) -> Self {
        let cap = if max_batch_records == 0 {
            16
        } else {
            max_batch_records
        };
        let linger = if max_linger_us == 0 {
            250
        } else {
            max_linger_us
        };
        Self {
            max_batch_records: cap,
            max_linger_us: linger,
            pending_records: 0,
            first_pending_us: 0,
            latest_hw: 0,
            wake_epoch: 0,
        }
    }

    #[must_use]
    pub const fn pending_records(&self) -> u64 {
        self.pending_records
    }

    #[must_use]
    pub const fn wake_epoch(&self) -> u64 {
        self.wake_epoch
    }

    /// Record `count` newly appended records advancing `hw_offset` at `now_us`.
    pub fn on_append(&mut self, count: u64, hw_offset: u64, now_us: u64) -> FanoutCoalesceAction {
        if self.pending_records == 0 {
            self.first_pending_us = now_us;
        }
        if hw_offset > self.latest_hw {
            self.latest_hw = hw_offset;
        }
        let add = if count > 1 { count } else { 1 };
        let next = self.pending_records.saturating_add(add);
        self.pending_records = fanout_batch_clamp(next, self.max_batch_records);

        let linger_expired = now_us.saturating_sub(self.first_pending_us) >= self.max_linger_us;
        if fanout_batch_full(self.pending_records, self.max_batch_records) || linger_expired {
            self.flush_now()
        } else {
            FanoutCoalesceAction::CoalescePending {
                pending_records: self.pending_records,
            }
        }
    }

    /// Periodic timer check to flush sub-batch tails once `max_linger_us` elapses.
    pub fn on_tick(&mut self, now_us: u64) -> FanoutCoalesceAction {
        if self.pending_records > 0
            && now_us.saturating_sub(self.first_pending_us) >= self.max_linger_us
        {
            self.flush_now()
        } else {
            FanoutCoalesceAction::CoalescePending {
                pending_records: self.pending_records,
            }
        }
    }

    fn flush_now(&mut self) -> FanoutCoalesceAction {
        let flushed = self.pending_records;
        self.pending_records = 0;
        let next_ep = self.wake_epoch.saturating_add(1);
        self.wake_epoch = fanout_wake_epoch_advance(self.wake_epoch, next_ep);
        FanoutCoalesceAction::EmitWake {
            wake_epoch: self.wake_epoch,
            flushed_records: flushed,
            latest_hw: self.latest_hw,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn coalesces_until_batch_full_or_linger_deadline() {
        let mut c = ShardedFanoutCoalescer::new(4, 200);
        assert_eq!(
            c.on_append(2, 10, 1_000),
            FanoutCoalesceAction::CoalescePending { pending_records: 2 }
        );
        assert_eq!(
            c.on_append(2, 12, 1_050),
            FanoutCoalesceAction::EmitWake {
                wake_epoch: 1,
                flushed_records: 4,
                latest_hw: 12,
            }
        );
        assert_eq!(
            c.on_append(1, 13, 2_000),
            FanoutCoalesceAction::CoalescePending { pending_records: 1 }
        );
        assert_eq!(
            c.on_tick(2_250),
            FanoutCoalesceAction::EmitWake {
                wake_epoch: 2,
                flushed_records: 1,
                latest_hw: 13,
            }
        );
    }
}
