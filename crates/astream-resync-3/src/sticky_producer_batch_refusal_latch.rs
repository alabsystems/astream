// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Sticky send-order per-producer batch-refusal latch (`docs/DESIGN-aterm-fabric.md` §14 open
//! question 7 lines 3979–3998, `Bridge::settle_sender`, aterm `4917b1f339`;
//! `Astream.Broker.TlaStickyProducerBatchRefusalLatch`).
//!
//! Resolves the pipelined out-of-order post hazard after a rolled-back batch:
//! - When a batch rolls back (`ERR_REFUSED`) containing a write at `failed_seq` from a producer,
//!   recording `latched_gap_seq = min(existing_gap, failed_seq)` makes the refusal sticky in send
//!   order: every pipelined write with `producer_seq > latched_gap_seq` reaching a later batch is
//!   refused (`RefusedStickyBatchGap`) instead of landing ahead of `failed_seq`!
//! - Once the producer retries `producer_seq == latched_gap_seq` (and it commits) or explicitly
//!   acknowledges the gap on reconnect, the latch lifts cleanly so multi-post pipelining stays
//!   strictly ordered!

#[cfg(clean_islands)]
#[path = "sticky_producer_batch_refusal_latch_island.rs"]
mod sticky_producer_batch_refusal_latch_island;
#[cfg(clean_islands)]
pub use sticky_producer_batch_refusal_latch_island::{
    committed_seq_advance_b137, pipeline_inflight_clamp_b137,
};

/// Maximum pipelined writes per connection (`MAX_PIPELINE_WINDOW = 64` in aterm).
pub const MAX_PIPELINE_WRITES: u64 = 64;

#[cfg(not(clean_islands))]
/// Clamp in-flight pipelined write count to `window_cap`.
#[must_use]
pub const fn pipeline_inflight_clamp_b137(cand_inflight: u64, window_cap: u64) -> u64 {
    if cand_inflight < window_cap {
        cand_inflight
    } else {
        window_cap
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance highest send-order committed sequence.
#[must_use]
pub const fn committed_seq_advance_b137(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}

contract_fn! {
    /// True iff `!has_sticky_gap || producer_seq <= gap_seq`.
    #[must_use]
    pub const fn write_ordered_under_gap_latch_b137(
        has_sticky_gap: bool,
        producer_seq: u64,
        gap_seq: u64,
    ) -> bool
    clauses [ensures result == (!has_sticky_gap || producer_seq <= gap_seq)]
    {
        !has_sticky_gap || producer_seq <= gap_seq
    }
}

/// Admission verdict for a producer write under sticky send-order batch-refusal latching.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum OrderedWriteVerdict {
    /// Staged into current batch (`producer_seq` preserves send order).
    StagedInOrder,
    /// Refused: earlier pipelined write `gap_seq` failed in a rolled-back batch and has not landed yet!
    RefusedStickyBatchGap { gap_seq: u64 },
    /// Refused: pipeline window (`MAX_PIPELINE_WRITES`) saturated.
    RefusedWindowFull,
}

/// Per-producer send-order batch-refusal latch state machine.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct StickyBatchRefusalLatch {
    window_cap: u64,
    inflight_writes: u64,
    committed_seq: u64,
    sticky_gap_seq: Option<u64>,
}

impl StickyBatchRefusalLatch {
    #[must_use]
    pub const fn new(window_cap: u64) -> Self {
        let cap = if window_cap == 0 {
            MAX_PIPELINE_WRITES
        } else {
            window_cap
        };
        Self {
            window_cap: cap,
            inflight_writes: 0,
            committed_seq: 0,
            sticky_gap_seq: None,
        }
    }

    #[must_use]
    pub const fn inflight_writes(&self) -> u64 {
        pipeline_inflight_clamp_b137(self.inflight_writes, self.window_cap)
    }

    #[must_use]
    pub const fn committed_seq(&self) -> u64 {
        self.committed_seq
    }

    #[must_use]
    pub const fn sticky_gap_seq(&self) -> Option<u64> {
        self.sticky_gap_seq
    }

    /// Evaluate staging a pipelined write at `producer_seq`.
    pub fn stage_write(&mut self, producer_seq: u64) -> OrderedWriteVerdict {
        if self.inflight_writes >= self.window_cap {
            return OrderedWriteVerdict::RefusedWindowFull;
        }
        let (has_gap, g_seq) = match self.sticky_gap_seq {
            Some(g) => (true, g),
            None => (false, 0),
        };
        if !write_ordered_under_gap_latch_b137(has_gap, producer_seq, g_seq) {
            return OrderedWriteVerdict::RefusedStickyBatchGap { gap_seq: g_seq };
        }
        self.inflight_writes =
            pipeline_inflight_clamp_b137(self.inflight_writes.saturating_add(1), self.window_cap);
        OrderedWriteVerdict::StagedInOrder
    }

    /// Record a rolled-back Strict batch whose lowest failed sequence for this producer was `failed_seq`.
    pub fn on_batch_rolled_back(&mut self, failed_seq: u64, batch_count: u64) {
        self.inflight_writes = self.inflight_writes.saturating_sub(batch_count);
        self.sticky_gap_seq = Some(match self.sticky_gap_seq {
            Some(cur) if cur < failed_seq => cur,
            _ => failed_seq,
        });
    }

    /// Record a committed batch whose highest sequence for this producer was `landed_seq`.
    pub fn on_batch_committed(&mut self, landed_seq: u64, batch_count: u64) {
        self.inflight_writes = self.inflight_writes.saturating_sub(batch_count);
        self.committed_seq = committed_seq_advance_b137(self.committed_seq, landed_seq);
        if let Some(gap) = self.sticky_gap_seq {
            if landed_seq >= gap {
                self.sticky_gap_seq = None;
            }
        }
    }

    /// Explicit gap acknowledgement (or fresh connection attach) clears the sticky latch.
    pub fn acknowledge_gap(&mut self) {
        self.sticky_gap_seq = None;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rolled_back_batch_blocks_trailing_pipelined_post_until_gap_retried() {
        let mut l = StickyBatchRefusalLatch::new(64);
        // Producer pipelines seq 10 (reaches batch 1), then seq 11 (reaches batch 2 after batch 1 rolls back):
        assert_eq!(l.stage_write(10), OrderedWriteVerdict::StagedInOrder);
        // Batch 1 fails flush and rolls back seq 10:
        l.on_batch_rolled_back(10, 1);
        assert_eq!(l.sticky_gap_seq(), Some(10));
        // Seq 11 arriving for batch 2 is REFUSED rather than landing out of order ahead of seq 10!
        assert_eq!(
            l.stage_write(11),
            OrderedWriteVerdict::RefusedStickyBatchGap { gap_seq: 10 }
        );
        // Producer retries seq 10 -> allowed, commits, clears latch, then seq 11 lands in order!
        assert_eq!(l.stage_write(10), OrderedWriteVerdict::StagedInOrder);
        l.on_batch_committed(10, 1);
        assert_eq!(l.sticky_gap_seq(), None);
        assert_eq!(l.stage_write(11), OrderedWriteVerdict::StagedInOrder);
        l.on_batch_committed(11, 1);
        assert_eq!(l.committed_seq(), 11);
    }
}
