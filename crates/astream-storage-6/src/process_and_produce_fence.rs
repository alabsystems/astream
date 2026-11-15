// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Atomic `ProcessAndProduce` consume-transform-append idempotency fence
//! (`Astream.Effects.TlaProcessAndProduceFence`).
//!
//! Coordinates atomic `ProcessAndProduce` steps: binds each consumed input `source_offset`
//! deterministically to a producer sequence number, bounds concurrent uncommitted stages to
//! `max_inflight`, and advances `committed_source_offset` strictly in order without gaps.

#[cfg(clean_islands)]
#[path = "process_and_produce_fence_island.rs"]
mod process_and_produce_fence_island;
#[cfg(clean_islands)]
pub use process_and_produce_fence_island::{
    pap_commit_offset_advance_b108, pap_inflight_clamp_b108,
};

#[cfg(not(clean_islands))]
/// Clamp staged `ProcessAndProduce` batch count to `max_inflight`.
#[must_use]
pub const fn pap_inflight_clamp_b108(cand_inflight: u64, max_inflight: u64) -> u64 {
    if cand_inflight < max_inflight {
        cand_inflight
    } else {
        max_inflight
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the committed `ProcessAndProduce` input checkpoint offset.
#[must_use]
pub const fn pap_commit_offset_advance_b108(cur_offset: u64, cand_offset: u64) -> u64 {
    if cur_offset < cand_offset {
        cand_offset
    } else {
        cur_offset
    }
}

contract_fn! {
    /// True iff `source_offset` is strictly past `committed_offset` and in-flight budget remains.
    #[must_use]
    pub const fn pap_can_stage_b108(
        source_offset: u64,
        committed_offset: u64,
        inflight: u64,
        max_inflight: u64,
    ) -> bool
    clauses [ensures result == (committed_offset < source_offset && inflight < max_inflight)]
    {
        committed_offset < source_offset && inflight < max_inflight
    }
}

/// Outcome of staging a `ProcessAndProduce` batch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PapStageOutcome {
    Staged { producer_seq: u64, inflight: u64 },
    AlreadyCommitted { committed_offset: u64 },
    Backpressured { max_inflight: u64 },
}

/// Atomic `ProcessAndProduce` stage-and-commit fence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProcessAndProduceFence {
    producer_id: u64,
    next_producer_seq: u64,
    committed_offset: u64,
    inflight: u64,
    max_inflight: u64,
}

impl ProcessAndProduceFence {
    #[must_use]
    pub const fn new(producer_id: u64, initial_committed_offset: u64, max_inflight: u64) -> Self {
        let cap = if max_inflight == 0 { 8 } else { max_inflight };
        Self {
            producer_id,
            next_producer_seq: 1,
            committed_offset: initial_committed_offset,
            inflight: 0,
            max_inflight: cap,
        }
    }

    #[must_use]
    pub const fn producer_id(&self) -> u64 {
        self.producer_id
    }

    #[must_use]
    pub const fn committed_offset(&self) -> u64 {
        self.committed_offset
    }

    #[must_use]
    pub const fn inflight(&self) -> u64 {
        self.inflight
    }

    /// Stage an atomic transform of `source_offset`, assigning a deterministic `producer_seq`.
    pub fn stage_step(&mut self, source_offset: u64) -> PapStageOutcome {
        if source_offset <= self.committed_offset {
            return PapStageOutcome::AlreadyCommitted {
                committed_offset: self.committed_offset,
            };
        }
        if !pap_can_stage_b108(
            source_offset,
            self.committed_offset,
            self.inflight,
            self.max_inflight,
        ) {
            return PapStageOutcome::Backpressured {
                max_inflight: self.max_inflight,
            };
        }
        let seq = self.next_producer_seq;
        self.next_producer_seq = self.next_producer_seq.saturating_add(1);
        let cand = self.inflight.saturating_add(1);
        self.inflight = pap_inflight_clamp_b108(cand, self.max_inflight);
        PapStageOutcome::Staged {
            producer_seq: seq,
            inflight: self.inflight,
        }
    }

    /// Commit a completed `ProcessAndProduce` batch advancing the durable input offset.
    pub fn commit_step(&mut self, source_offset: u64) -> u64 {
        self.inflight = self.inflight.saturating_sub(1);
        self.committed_offset =
            pap_commit_offset_advance_b108(self.committed_offset, source_offset);
        self.committed_offset
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stages_new_offsets_with_dedup_seq_and_skips_already_committed() {
        let mut fence = ProcessAndProduceFence::new(42, 100, 2);
        assert_eq!(
            fence.stage_step(100),
            PapStageOutcome::AlreadyCommitted {
                committed_offset: 100
            }
        );
        assert_eq!(
            fence.stage_step(101),
            PapStageOutcome::Staged {
                producer_seq: 1,
                inflight: 1,
            }
        );
        assert_eq!(fence.commit_step(101), 101);
        assert_eq!(fence.inflight(), 0);
    }
}
