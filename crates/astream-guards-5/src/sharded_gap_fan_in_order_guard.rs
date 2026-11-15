// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Sharded subscription fan-in `ShardedEvent::Gap` pre-delivery ordering guard
//! (`evidence/manifest.toml` `broker.retention-rules` /
//! `a_shards_gap_notice_reaches_the_fan_in_before_its_records`;
//! `Astream.Pump.TlaShardedGapFanInOrderGuard`).
//!
//! Enforces per-shard `Gap` -> `Delivery` ordering across sharded fan-in forwarders:
//! - Forwarders MUST read `recv_event` (never deliveries alone!) so `ShardedEvent::Gap` is
//!   never swallowed,
//! - On each shard (`shard_id < shard_count`), any pending `Gap { from, to }` MUST reach the
//!   fan-in channel BEFORE any record `offset >= to` on that shard!

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
#[path = "sharded_gap_fan_in_order_guard_island.rs"]
mod sharded_gap_fan_in_order_guard_island;
#[cfg(clean_islands)]
pub use sharded_gap_fan_in_order_guard_island::{
    shard_cursor_advance_b154, shard_index_clamp_b154,
};

/// Upper bound on shards per `ShardedSubscription` (`1_024`).
pub const MAX_FAN_IN_SHARDS: u64 = 1_024;

#[cfg(not(clean_islands))]
/// Clamp shard index to `shard_cap`.
#[must_use]
pub const fn shard_index_clamp_b154(cand_shard: u64, shard_cap: u64) -> u64 {
    if cand_shard < shard_cap {
        cand_shard
    } else {
        shard_cap
    }
}

#[cfg(not(clean_islands))]
/// Advance shard fan-in cursor monotonically across forwarded gaps and deliveries.
#[must_use]
pub const fn shard_cursor_advance_b154(cur_cursor: u64, cand_cursor: u64) -> u64 {
    if cur_cursor < cand_cursor {
        cand_cursor
    } else {
        cur_cursor
    }
}

contract_fn! {
    /// True iff no pending gap exists on the shard (`!has_pending_gap`) before forwarding a record.
    #[must_use]
    pub const fn shard_record_delivery_ordered_b154(
        shard_id: u64,
        shard_count: u64,
        has_pending_gap: bool,
        record_offset: u64,
        shard_cursor: u64,
    ) -> bool
    clauses [ensures result == (shard_id < shard_count && !has_pending_gap && record_offset >= shard_cursor)]
    {
        shard_id < shard_count && !has_pending_gap && record_offset >= shard_cursor
    }
}

/// Fan-in forwarding decision for a single shard stream.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShardedFanInDecision {
    QueuedPendingGap { shard_id: u64, from: u64, to: u64 },
    ForwardedGapBeforeRecords { shard_id: u64, new_cursor: u64 },
    ForwardedOrderedRecord { shard_id: u64, next_cursor: u64 },
    RefusedRecordAheadOfPendingGap { shard_id: u64, pending_to: u64 },
    RefusedOutOfBoundsorRegression,
}

/// Per-shard `Gap`-before-`Record` ordering guard for sharded fan-in forwarders.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ShardedGapFanInGuard {
    shard_id: u64,
    shard_count: u64,
    shard_cursor: u64,
    pending_gap: Option<(u64, u64)>,
}

impl ShardedGapFanInGuard {
    #[must_use]
    pub const fn new(shard_id: u64, shard_count: u64) -> Self {
        let cap = shard_index_clamp_b154(shard_count, MAX_FAN_IN_SHARDS);
        Self {
            shard_id: shard_index_clamp_b154(shard_id, cap),
            shard_count: cap,
            shard_cursor: 0,
            pending_gap: None,
        }
    }

    /// Observe `Event::Gap { from, to }` from the shard reader.
    pub fn on_shard_gap_received(&mut self, from: u64, to: u64) -> ShardedFanInDecision {
        if to < from {
            return ShardedFanInDecision::RefusedOutOfBoundsorRegression;
        }
        self.pending_gap = Some((from, to));
        ShardedFanInDecision::QueuedPendingGap {
            shard_id: self.shard_id,
            from,
            to,
        }
    }

    /// Flush the queued `ShardedEvent::Gap` into the fan-in channel BEFORE forwarding records!
    pub fn flush_pending_gap_to_fan_in(&mut self) -> ShardedFanInDecision {
        let Some((_from, to)) = core::mem::take(&mut self.pending_gap) else {
            return ShardedFanInDecision::RefusedOutOfBoundsorRegression;
        };
        self.shard_cursor = shard_cursor_advance_b154(self.shard_cursor, to);
        ShardedFanInDecision::ForwardedGapBeforeRecords {
            shard_id: self.shard_id,
            new_cursor: self.shard_cursor,
        }
    }

    /// Forward a record at `record_offset` into the fan-in channel.
    pub fn forward_shard_record(&mut self, record_offset: u64) -> ShardedFanInDecision {
        if let Some((_from, to)) = self.pending_gap {
            return ShardedFanInDecision::RefusedRecordAheadOfPendingGap {
                shard_id: self.shard_id,
                pending_to: to,
            };
        }
        if !shard_record_delivery_ordered_b154(
            self.shard_id,
            self.shard_count,
            false,
            record_offset,
            self.shard_cursor,
        ) {
            return ShardedFanInDecision::RefusedOutOfBoundsorRegression;
        }
        let next = record_offset.saturating_add(1);
        self.shard_cursor = shard_cursor_advance_b154(self.shard_cursor, next);
        ShardedFanInDecision::ForwardedOrderedRecord {
            shard_id: self.shard_id,
            next_cursor: self.shard_cursor,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_shard_gap_delivery_before_any_subsequent_shard_record() {
        let mut g = ShardedGapFanInGuard::new(2, 8);
        assert_eq!(
            g.on_shard_gap_received(0, 5),
            ShardedFanInDecision::QueuedPendingGap {
                shard_id: 2,
                from: 0,
                to: 5,
            }
        );
        // Attempting to forward record 5 before flushing Gap(0..5) is refused!
        assert_eq!(
            g.forward_shard_record(5),
            ShardedFanInDecision::RefusedRecordAheadOfPendingGap {
                shard_id: 2,
                pending_to: 5,
            }
        );
        assert_eq!(
            g.flush_pending_gap_to_fan_in(),
            ShardedFanInDecision::ForwardedGapBeforeRecords {
                shard_id: 2,
                new_cursor: 5,
            }
        );
        assert_eq!(
            g.forward_shard_record(5),
            ShardedFanInDecision::ForwardedOrderedRecord {
                shard_id: 2,
                next_cursor: 6,
            }
        );
    }
}
