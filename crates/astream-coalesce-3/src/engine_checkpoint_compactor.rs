// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Snapshot-Anchored Envelope Log Garbage-Collection Planner.
//!
//! Long-lived `aterm` sessions accumulate millions of PTY envelopes in `astream-engine`.
//! Truncating the prefix of an envelope log is only sound up to a committed terminal
//! checkpoint offset that ALSO precedes every active reader/fork cursor (`min_pinned_cursor`),
//! and the GC watermark must advance monotonically so truncated prefix segments are never
//! re-requested.
//!
//! Backed by Clean TLA+ Island `Astream.Engine.TlaCheckpointGcPlanner`
//! (`engine_checkpoint_compactor_island.rs`), proving `safeGcOffset <= minPinnedCursor` and
//! `prevGcOffset <= safeGcOffset`.

#[cfg(clean_islands)]
#[path = "engine_checkpoint_compactor_island.rs"]
mod island;
#[cfg(clean_islands)]
pub use island::{gc_offset_advance, gc_offset_clamp};

#[cfg(not(clean_islands))]
#[inline]
pub const fn gc_offset_clamp(checkpoint_off: u64, min_pinned_cursor: u64) -> u64 {
    if checkpoint_off < min_pinned_cursor {
        checkpoint_off
    } else {
        min_pinned_cursor
    }
}

#[cfg(not(clean_islands))]
#[inline]
pub const fn gc_offset_advance(cur_gc: u64, proposed_gc: u64) -> u64 {
    if cur_gc < proposed_gc {
        proposed_gc
    } else {
        cur_gc
    }
}

contract_fn! {
    /// Kernel-certified check that `checkpoint_off` does not overrun `min_pinned_cursor`.
    #[must_use]
    #[inline]
    pub const fn gc_checkpoint_eligible(checkpoint_off: u64, min_pinned_cursor: u64) -> bool
    clauses [ensures result == (checkpoint_off <= min_pinned_cursor)]
    {
        checkpoint_off <= min_pinned_cursor
    }
}

/// Maximum concurrent pinned reader/fork cursors tracked inline without heap allocation.
pub const MAX_PINNED_READERS: usize = 32;

/// Descriptor of a durable terminal checkpoint anchor in the envelope log.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CheckpointAnchor {
    pub log_offset: u64,
    pub state_digest_lo: u64,
}

/// Active reader or counterfactual fork lease pinning envelopes from `cursor_offset` onward.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ReaderPin {
    reader_id: u64,
    cursor_offset: u64,
    active: bool,
}

impl ReaderPin {
    const EMPTY: Self = Self {
        reader_id: 0,
        cursor_offset: 0,
        active: false,
    };
}

/// Outcome of a GC planning step.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GcCompactionPlan {
    /// Previous GC watermark prior to this step.
    pub prev_gc_offset: u64,
    /// Newly certified monotone GC watermark (`prev_gc_offset <= safe_gc_offset <= min_pinned_cursor`).
    pub safe_gc_offset: u64,
    /// Effective minimum cursor across active readers and `head_offset`.
    pub min_pinned_cursor: u64,
    /// Bytes newly eligible for prefix truncation (`safe_gc_offset - prev_gc_offset`).
    pub reclaimable_span: u64,
}

/// Monotone checkpoint-anchored GC planner for `astream-engine` envelope logs.
#[derive(Debug, Clone)]
pub struct CheckpointGcPlanner {
    prev_gc_offset: u64,
    safe_gc_offset: u64,
    latest_checkpoint: Option<CheckpointAnchor>,
    pins: [ReaderPin; MAX_PINNED_READERS],
}

impl Default for CheckpointGcPlanner {
    fn default() -> Self {
        Self::new()
    }
}

impl CheckpointGcPlanner {
    #[inline]
    pub const fn new() -> Self {
        Self {
            prev_gc_offset: 0,
            safe_gc_offset: 0,
            latest_checkpoint: None,
            pins: [ReaderPin::EMPTY; MAX_PINNED_READERS],
        }
    }

    #[inline]
    pub const fn safe_gc_offset(&self) -> u64 {
        self.safe_gc_offset
    }

    #[inline]
    pub const fn prev_gc_offset(&self) -> u64 {
        self.prev_gc_offset
    }

    #[inline]
    pub const fn latest_checkpoint(&self) -> Option<CheckpointAnchor> {
        self.latest_checkpoint
    }

    /// Commits a durable checkpoint anchor if it advances past any previous checkpoint.
    pub fn record_checkpoint(&mut self, anchor: CheckpointAnchor) -> bool {
        if let Some(prev) = self.latest_checkpoint {
            if anchor.log_offset <= prev.log_offset {
                return false;
            }
        }
        self.latest_checkpoint = Some(anchor);
        true
    }

    /// Registers or advances a pinned reader cursor (`cursor_offset` cannot regress below
    /// `self.safe_gc_offset`). Returns `false` if all 32 reader slots are full.
    pub fn upsert_reader_pin(&mut self, reader_id: u64, cursor_offset: u64) -> bool {
        let clamped_cursor = gc_offset_advance(self.safe_gc_offset, cursor_offset);
        let mut free_slot: Option<usize> = None;
        let mut i = 0usize;
        let mut cur = self.pins.as_mut_slice();
        while let [pin, rest @ ..] = cur {
            if pin.active && pin.reader_id == reader_id {
                pin.cursor_offset = gc_offset_advance(pin.cursor_offset, clamped_cursor);
                return true;
            }
            if !pin.active && free_slot.is_none() {
                free_slot = Some(i);
            }
            i = i.saturating_add(1);
            cur = rest;
        }
        if let Some(slot_idx) = free_slot {
            if let Some(slot) = self.pins.get_mut(slot_idx) {
                *slot = ReaderPin {
                    reader_id,
                    cursor_offset: clamped_cursor,
                    active: true,
                };
                return true;
            }
        }
        false
    }

    /// Releases an active reader pin when a subscriber detaches or a fork completes.
    pub fn release_reader_pin(&mut self, reader_id: u64) -> bool {
        let mut cur = self.pins.as_mut_slice();
        while let [pin, rest @ ..] = cur {
            if pin.active && pin.reader_id == reader_id {
                *pin = ReaderPin::EMPTY;
                return true;
            }
            cur = rest;
        }
        false
    }

    /// Computes the minimum pinned cursor across all active readers and `head_offset`,
    /// guaranteed `>= self.safe_gc_offset`.
    pub fn effective_min_pinned(&self, head_offset: u64) -> u64 {
        let mut min_cur = gc_offset_advance(self.safe_gc_offset, head_offset);
        let mut cur: &[ReaderPin] = &self.pins;
        while let &[pin, ref rest @ ..] = cur {
            if pin.active {
                min_cur = gc_offset_clamp(pin.cursor_offset, min_cur);
            }
            cur = rest;
        }
        gc_offset_advance(self.safe_gc_offset, min_cur)
    }

    /// Evaluates `AdvanceGc` (`Astream.Engine.TlaCheckpointGcPlanner`), advancing
    /// `safe_gc_offset` monotonically up to `min(latest_checkpoint, min_pinned_cursor)`.
    pub fn plan_compaction(&mut self, head_offset: u64) -> GcCompactionPlan {
        let raised_pinned = self.effective_min_pinned(head_offset);
        let cand_checkpoint = match self.latest_checkpoint {
            Some(cp) => cp.log_offset,
            None => 0,
        };
        let clamped_cand = gc_offset_clamp(cand_checkpoint, raised_pinned);
        let next_gc = gc_offset_advance(self.safe_gc_offset, clamped_cand);
        let certified_gc = gc_offset_clamp(next_gc, raised_pinned);

        self.prev_gc_offset = self.safe_gc_offset;
        self.safe_gc_offset = certified_gc;

        GcCompactionPlan {
            prev_gc_offset: self.prev_gc_offset,
            safe_gc_offset: self.safe_gc_offset,
            min_pinned_cursor: raised_pinned,
            reclaimable_span: self.safe_gc_offset.saturating_sub(self.prev_gc_offset),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gc_watermark_respects_slowest_reader_and_advances_monotonically() {
        let mut planner = CheckpointGcPlanner::new();
        assert!(planner.upsert_reader_pin(1, 120));
        assert!(planner.upsert_reader_pin(2, 450));
        assert!(planner.record_checkpoint(CheckpointAnchor {
            log_offset: 300,
            state_digest_lo: 0xAA55,
        }));
        assert!(!gc_checkpoint_eligible(300, 120));

        // Reader 1 pins at 120, so GC stops at 120 even though checkpoint is at 300.
        let p1 = planner.plan_compaction(500);
        assert_eq!(p1.prev_gc_offset, 0);
        assert_eq!(p1.safe_gc_offset, 120);
        assert_eq!(p1.min_pinned_cursor, 120);
        assert_eq!(p1.reclaimable_span, 120);

        // Reader 1 advances to 350 -> GC advances to checkpoint 300.
        assert!(planner.upsert_reader_pin(1, 350));
        assert!(gc_checkpoint_eligible(300, 350));
        let p2 = planner.plan_compaction(500);
        assert_eq!(p2.prev_gc_offset, 120);
        assert_eq!(p2.safe_gc_offset, 300);
        assert_eq!(p2.reclaimable_span, 180);

        // Even if a new reader tries to pin at 50 (stale), it is clamped to safe_gc_offset=300.
        assert!(planner.upsert_reader_pin(3, 50));
        let p3 = planner.plan_compaction(500);
        assert_eq!(p3.safe_gc_offset, 300);
        assert_eq!(p3.reclaimable_span, 0);
    }

    #[test]
    fn releasing_blocking_reader_unblocks_checkpoint_gc() {
        let mut planner = CheckpointGcPlanner::new();
        assert!(planner.upsert_reader_pin(7, 40));
        assert!(planner.record_checkpoint(CheckpointAnchor {
            log_offset: 256,
            state_digest_lo: 1,
        }));
        assert_eq!(planner.plan_compaction(400).safe_gc_offset, 40);

        assert!(planner.release_reader_pin(7));
        let plan = planner.plan_compaction(400);
        assert_eq!(plan.prev_gc_offset, 40);
        assert_eq!(plan.safe_gc_offset, 256);
        assert_eq!(plan.reclaimable_span, 216);
    }
}
