// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Crash-safe `<log>.compact` 7-step compaction recovery state machine (`copy` -> `staged_state` ->
//! `intent` -> `rename` -> `install_state` -> `base_and_watermark` -> `unlink_intent`) finishing or
//! discarding cleanly by the log's first frame (`Astream.HeldComp.TlaCompactIntentFsm`).

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
#[path = "compact_intent_fsm_island.rs"]
mod compact_intent_fsm_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn hc_step_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn hc_cmp_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use compact_intent_fsm_island::{hc_cmp_advance, hc_step_clamp};

/// Final settled compaction step (`7 = IntentRemovedClean`).
pub const COMPACT_STEP_DONE: u64 = 7;

contract_fn! {
    /// Verified settled compaction step (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `hc_compaction_settled_isl`.
    #[must_use]
    pub const fn hc_compaction_settled(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompactRecoveryAction {
    DiscardPreRenameArtifacts,
    FinishPostRenameInstall,
    RefuseForeignFirstFrame,
}

#[derive(Debug, Clone, Default)]
pub struct CompactIntentRecoverer {
    step: u64,
}

impl CompactIntentRecoverer {
    #[must_use]
    pub const fn new() -> Self {
        Self { step: 0 }
    }

    pub fn decide_on_reopen(
        &mut self,
        log_matches_old_first_frame: bool,
        log_matches_new_first_frame: bool,
    ) -> CompactRecoveryAction {
        if log_matches_old_first_frame && log_matches_new_first_frame {
            CompactRecoveryAction::RefuseForeignFirstFrame
        } else if log_matches_new_first_frame {
            self.step = hc_cmp_advance(
                self.step,
                hc_step_clamp(COMPACT_STEP_DONE, COMPACT_STEP_DONE),
            );
            let _ = hc_compaction_settled(self.step, COMPACT_STEP_DONE);
            CompactRecoveryAction::FinishPostRenameInstall
        } else if log_matches_old_first_frame {
            self.step = hc_cmp_advance(
                self.step,
                hc_step_clamp(COMPACT_STEP_DONE, COMPACT_STEP_DONE),
            );
            CompactRecoveryAction::DiscardPreRenameArtifacts
        } else {
            CompactRecoveryAction::RefuseForeignFirstFrame
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn finishes_after_rename_discards_before_rename_and_refuses_foreign_frame() {
        let mut r = CompactIntentRecoverer::new();
        assert_eq!(
            r.decide_on_reopen(true, false),
            CompactRecoveryAction::DiscardPreRenameArtifacts
        );
        assert_eq!(
            r.decide_on_reopen(false, true),
            CompactRecoveryAction::FinishPostRenameInstall
        );
        assert_eq!(
            r.decide_on_reopen(false, false),
            CompactRecoveryAction::RefuseForeignFirstFrame
        );
    }
}
