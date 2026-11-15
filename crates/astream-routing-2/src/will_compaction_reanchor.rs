// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Live `/a/bind` & `/a/will` compaction re-anchor planner (`Astream.Broker.TlaWillCompactionReanchor`).
//!
//! Long-lived `aterm` sessions register `/a/bind` and `/a/will` control records near
//! the start of a broker log. Without copy-forward re-anchoring, those early offsets
//! block `retain_before(proposed_base)` indefinitely. This module plans bounded
//! copy-forward batches (`<= max_batch`) and monotonically advances `compacted_base`
//! only up to the lowest remaining un-reanchored control record.

#[cfg(clean_islands)]
#[path = "will_compaction_reanchor_island.rs"]
mod will_compaction_reanchor_island;
#[cfg(clean_islands)]
pub use will_compaction_reanchor_island::{reanchor_base_advance, reanchor_batch_clamp};

/// Default maximum control records copy-forwarded in one compaction turn.
pub const DEFAULT_MAX_REANCHOR_BATCH: u64 = 64;

#[cfg(not(clean_islands))]
/// Monotonically advance the broker's compacted base offset.
#[must_use]
pub const fn reanchor_base_advance(cur_base: u64, cand_base: u64) -> u64 {
    if cur_base < cand_base {
        cand_base
    } else {
        cur_base
    }
}

#[cfg(not(clean_islands))]
/// Clamp copy-forward batch count to `max_batch`.
#[must_use]
pub const fn reanchor_batch_clamp(cand_count: u64, max_batch: u64) -> u64 {
    if cand_count < max_batch {
        cand_count
    } else {
        max_batch
    }
}

contract_fn! {
    /// True iff `record_offset` sits strictly below `proposed_base` and blocks truncation.
    #[must_use]
    pub const fn offset_blocks_compaction(record_offset: u64, proposed_base: u64) -> bool
    clauses [ensures result == (record_offset < proposed_base)]
    {
        record_offset < proposed_base
    }
}

/// Kind of live control record anchored in the broker log.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PinnedControlKind {
    Bind,
    Will,
}

/// Descriptor for a live `/a/bind` or `/a/will` record at `offset`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PinnedControlRecord {
    pub conn_id: u64,
    pub offset: u64,
    pub kind: PinnedControlKind,
}

/// Output of one bounded compaction + re-anchor planning turn.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReanchorTurnPlan {
    /// Records selected to be copy-forwarded to the log tip in this turn (`len <= max_batch`).
    pub copy_forward: Vec<PinnedControlRecord>,
    /// Safe truncation offset achievable right now without losing any un-copied control record.
    pub safe_retain_before: u64,
    /// True iff all blockers below `proposed_base` fit in `copy_forward` so full truncation can proceed after append.
    pub unblocks_proposed_base: bool,
}

/// Stateful compaction re-anchor coordinator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WillCompactionReanchor {
    compacted_base: u64,
    last_batch_count: u64,
    max_batch: u64,
}

impl Default for WillCompactionReanchor {
    fn default() -> Self {
        Self::new(0, DEFAULT_MAX_REANCHOR_BATCH)
    }
}

impl WillCompactionReanchor {
    #[must_use]
    pub const fn new(initial_base: u64, max_batch: u64) -> Self {
        let cap = if max_batch == 0 {
            DEFAULT_MAX_REANCHOR_BATCH
        } else {
            max_batch
        };
        Self {
            compacted_base: initial_base,
            last_batch_count: 0,
            max_batch: cap,
        }
    }

    #[must_use]
    pub const fn compacted_base(&self) -> u64 {
        self.compacted_base
    }

    #[must_use]
    pub const fn last_batch_count(&self) -> u64 {
        self.last_batch_count
    }

    /// Plan which live `/a/bind` + `/a/will` records block `proposed_base`.
    pub fn plan_turn(
        &mut self,
        live_pins: &[PinnedControlRecord],
        proposed_base: u64,
    ) -> ReanchorTurnPlan {
        let mut copy_forward: Vec<PinnedControlRecord> = Vec::new();
        let mut lowest_uncopied_blocker: Option<u64> = None;
        let mut selected_count = 0u64;

        let mut rest = live_pins;
        while let &[pin, ref tail @ ..] = rest {
            if offset_blocks_compaction(pin.offset, proposed_base) {
                if selected_count < self.max_batch {
                    copy_forward.push(pin);
                    selected_count = selected_count.saturating_add(1);
                } else {
                    match lowest_uncopied_blocker {
                        None => lowest_uncopied_blocker = Some(pin.offset),
                        Some(cur_min) => {
                            if pin.offset < cur_min {
                                lowest_uncopied_blocker = Some(pin.offset);
                            }
                        }
                    }
                }
            }
            rest = tail;
        }

        self.last_batch_count = reanchor_batch_clamp(selected_count, self.max_batch);

        // Before the copy-forward batch is appended, truncation cannot cross the lowest blocker at all.
        let mut min_any_blocker = proposed_base;
        let mut scan = live_pins;
        while let &[pin, ref tail @ ..] = scan {
            if pin.offset < min_any_blocker {
                min_any_blocker = pin.offset;
            }
            scan = tail;
        }
        let safe_now = reanchor_base_advance(self.compacted_base, min_any_blocker);
        self.compacted_base = safe_now;

        ReanchorTurnPlan {
            copy_forward,
            safe_retain_before: safe_now,
            unblocks_proposed_base: lowest_uncopied_blocker.is_none(),
        }
    }

    /// Commit truncation up to `new_base` after all blocking pins below `new_base` have been re-anchored.
    pub fn commit_compaction(&mut self, new_base: u64) -> u64 {
        self.compacted_base = reanchor_base_advance(self.compacted_base, new_base);
        self.compacted_base
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plans_bounded_copy_forward_and_advances_compaction_safely() {
        let mut planner = WillCompactionReanchor::new(0, 2);
        let pins = [
            PinnedControlRecord {
                conn_id: 1,
                offset: 12,
                kind: PinnedControlKind::Bind,
            },
            PinnedControlRecord {
                conn_id: 1,
                offset: 15,
                kind: PinnedControlKind::Will,
            },
            PinnedControlRecord {
                conn_id: 2,
                offset: 40,
                kind: PinnedControlKind::Will,
            },
            PinnedControlRecord {
                conn_id: 3,
                offset: 150,
                kind: PinnedControlKind::Bind,
            },
        ];

        // Propose compacting up to offset 100 with max_batch = 2:
        // Offsets 12, 15, 40 block 100; first 2 (12, 15) are scheduled for copy-forward; safe_now = 12.
        let plan1 = planner.plan_turn(&pins, 100);
        assert_eq!(plan1.copy_forward.len(), 2);
        assert_eq!(plan1.safe_retain_before, 12);
        assert!(!plan1.unblocks_proposed_base);

        // After re-anchoring 12 -> 200 and 15 -> 201, only 40 blocks 100 (fits in batch of 2!)
        let pins_after_batch1 = [
            PinnedControlRecord {
                conn_id: 1,
                offset: 200,
                kind: PinnedControlKind::Bind,
            },
            PinnedControlRecord {
                conn_id: 1,
                offset: 201,
                kind: PinnedControlKind::Will,
            },
            PinnedControlRecord {
                conn_id: 2,
                offset: 40,
                kind: PinnedControlKind::Will,
            },
            PinnedControlRecord {
                conn_id: 3,
                offset: 150,
                kind: PinnedControlKind::Bind,
            },
        ];
        let plan2 = planner.plan_turn(&pins_after_batch1, 100);
        assert_eq!(plan2.copy_forward.len(), 1);
        assert_eq!(plan2.safe_retain_before, 40);
        assert!(plan2.unblocks_proposed_base);

        assert_eq!(planner.commit_compaction(100), 100);
    }
}
