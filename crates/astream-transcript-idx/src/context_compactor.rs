// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `/compact` context-window anchor planner preserving `USER_INPUT` requests, artifact paths, and
//! the recent live tail while summarizing middle trajectory steps (`Astream.Transcript.TlaContextCompactor`).

#[cfg(clean_islands)]
#[path = "context_compactor_island.rs"]
mod context_compactor_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tr_keep_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tr_compacted_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use context_compactor_island::{tr_compacted_advance, tr_keep_clamp};

/// Maximum live tail steps retained verbatim across `/compact`.
pub const MAX_RETAINED_TAIL_STEPS: u64 = 128;

contract_fn! {
    /// Verified post-compaction token fit (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `tr_fits_window_isl`.
    #[must_use]
    pub const fn tr_fits_window(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CompactionPlan {
    pub summarize_up_to_step: u64,
    pub retain_from_step: u64,
    pub estimated_post_tokens: u64,
}

/// Plans deterministic trajectory compaction boundaries.
#[derive(Debug, Clone, Default)]
pub struct TrajectoryCompactor {
    compaction_epoch: u64,
}

impl TrajectoryCompactor {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            compaction_epoch: 0,
        }
    }

    pub fn plan_compaction(
        &mut self,
        total_steps: u64,
        desired_tail_steps: u64,
        summary_tokens: u64,
        tail_tokens: u64,
        window_limit_tokens: u64,
    ) -> Result<CompactionPlan, &'static str> {
        if window_limit_tokens == 0 {
            return Err("context window limit must be non-zero");
        }
        let keep = tr_keep_clamp(desired_tail_steps, MAX_RETAINED_TAIL_STEPS);
        let retain_from = total_steps.saturating_sub(keep);
        let post = summary_tokens.saturating_add(tail_tokens);
        if !tr_fits_window(window_limit_tokens, post) {
            return Err("post-compaction summary + tail still exceeds context window limit");
        }
        self.compaction_epoch = tr_compacted_advance(
            self.compaction_epoch,
            self.compaction_epoch.saturating_add(1),
        );
        Ok(CompactionPlan {
            summarize_up_to_step: retain_from,
            retain_from_step: retain_from,
            estimated_post_tokens: post,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compactor_anchors_recent_tail_and_verifies_post_compaction_window_fit() {
        let mut c = TrajectoryCompactor::new();
        let plan = c.plan_compaction(500, 40, 8_000, 22_000, 128_000).unwrap();
        assert_eq!(plan.retain_from_step, 460);
        assert_eq!(plan.estimated_post_tokens, 30_000);
        assert!(c.plan_compaction(500, 40, 90_000, 50_000, 128_000).is_err());
    }
}
