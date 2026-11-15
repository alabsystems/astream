// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Per-producer `MAX_SUBJECTS_PER_PRODUCER` (`4096`) headroom guard & `Error 10` (`ERR_SUBJECT_BOUND`) classifier
//! (`docs/DESIGN-aterm-fabric.md` §5.2 lines 1052–1080; `Astream.Broker.TlaProducerSubjectBudgetHeadroom`).
//!
//! Protects essential session faces (`presence`, `ev`, and registered `Will`s) from starvation by
//! discretionary `ack/<B>` / `in/` subjects, and handles `Error 10` (`ERR_SUBJECT_BOUND`) without
//! head-of-line deadlock:
//! - Essential faces may use up to `max_subjects`, while discretionary new subjects require
//!   `remaining_slots > essential_reserve`,
//! - On `Error 10` (`ERR_SUBJECT_BOUND`), a cap-forced private `<src>` lane (which no other
//!   producer can ever introduce!) drops the record with reason instead of retrying forever,
//!   whereas a shared subject holds for another producer to introduce it first!

#[cfg(clean_islands)]
#[path = "producer_subject_budget_headroom_island.rs"]
mod producer_subject_budget_headroom_island;
#[cfg(clean_islands)]
pub use producer_subject_budget_headroom_island::{
    subj_budget_dropped_advance_b132, subj_budget_used_clamp_b132,
};

/// Default per-producer distinct-subject cap (`store.rs` `MAX_SUBJECTS_PER_PRODUCER`).
pub const DEFAULT_MAX_SUBJECTS_PER_PRODUCER: u64 = 4_096;

/// Default essential reserve kept for hosted sessions' `presence` + `ev` faces (`128`).
pub const DEFAULT_ESSENTIAL_HEADROOM: u64 = 128;

#[cfg(not(clean_islands))]
/// Clamp charged `(subjects + reserved)` count to `max_subjects`.
#[must_use]
pub const fn subj_budget_used_clamp_b132(cand_used: u64, max_subjects: u64) -> u64 {
    if cand_used < max_subjects {
        cand_used
    } else {
        max_subjects
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance count of private-lane records dropped on `Error 10`.
#[must_use]
pub const fn subj_budget_dropped_advance_b132(cur_dropped: u64, cand_dropped: u64) -> u64 {
    if cur_dropped < cand_dropped {
        cand_dropped
    } else {
        cur_dropped
    }
}

contract_fn! {
    /// True iff `remaining_slots > essential_reserve`.
    #[must_use]
    pub const fn subj_discretionary_admissible_b132(
        remaining_slots: u64,
        essential_reserve: u64,
    ) -> bool
    clauses [ensures result == (remaining_slots > essential_reserve)]
    {
        remaining_slots > essential_reserve
    }
}

/// Reaction to `Error 10` (`ERR_SUBJECT_BOUND`).
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum SubjectBoundReaction {
    /// Cap-forced `<src>` private lane: nobody else can introduce it -> drop with reason to prevent queue HOL block!
    DropPrivateWithReason,
    /// Shared subject: another producer can introduce it (making ours a free update) -> hold and retry later.
    HoldSharedForIntroduction,
}

/// Stateful bridge-side `Budget{subjects, reserved, max}` headroom planner.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ProducerSubjectBudgetHeadroom {
    max_subjects: u64,
    essential_reserve: u64,
    charged_total: u64,
    dropped_private_count: u64,
}

impl ProducerSubjectBudgetHeadroom {
    #[must_use]
    pub const fn new(max_subjects: u64, essential_reserve: u64) -> Self {
        Self {
            max_subjects,
            essential_reserve,
            charged_total: 0,
            dropped_private_count: 0,
        }
    }

    #[must_use]
    pub const fn with_defaults() -> Self {
        Self::new(
            DEFAULT_MAX_SUBJECTS_PER_PRODUCER,
            DEFAULT_ESSENTIAL_HEADROOM,
        )
    }

    #[must_use]
    pub const fn dropped_private_count(&self) -> u64 {
        self.dropped_private_count
    }

    /// Refresh from `Client::subject_budget` (`Budget{subjects, reserved, max}`).
    pub fn observe_broker_budget(&mut self, subjects: u64, reserved_wills: u64, max: u64) {
        self.max_subjects = max;
        let sum = subjects.saturating_add(reserved_wills);
        self.charged_total = subj_budget_used_clamp_b132(sum, self.max_subjects);
    }

    /// Check whether a new subject may be introduced (`is_essential` is true for `presence`/`ev`/wills).
    #[must_use]
    pub const fn may_introduce_subject(&self, is_essential: bool) -> bool {
        let remaining = self.max_subjects.saturating_sub(self.charged_total);
        if is_essential {
            remaining > 0
        } else {
            subj_discretionary_admissible_b132(remaining, self.essential_reserve)
        }
    }

    /// Classify an `Error 10` (`ERR_SUBJECT_BOUND`) refusal without stalling the queue.
    pub fn on_err_subject_bound(&mut self, cap_forces_private_src: bool) -> SubjectBoundReaction {
        if cap_forces_private_src {
            let cand = self.dropped_private_count.saturating_add(1);
            self.dropped_private_count =
                subj_budget_dropped_advance_b132(self.dropped_private_count, cand);
            SubjectBoundReaction::DropPrivateWithReason
        } else {
            SubjectBoundReaction::HoldSharedForIntroduction
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reserves_essential_headroom_and_drops_private_err10_without_hol_deadlock() {
        let mut h = ProducerSubjectBudgetHeadroom::with_defaults();
        h.observe_broker_budget(3_900, 68, 4_096); // remaining = 128 == reserve
        assert!(!h.may_introduce_subject(false)); // discretionary refused at reserve boundary!
        assert!(h.may_introduce_subject(true)); // essential `presence`/`ev` still admitted!

        h.observe_broker_budget(3_900, 67, 4_096); // remaining = 129 > 128
        assert!(h.may_introduce_subject(false));

        assert_eq!(
            h.on_err_subject_bound(true),
            SubjectBoundReaction::DropPrivateWithReason
        );
        assert_eq!(
            h.on_err_subject_bound(false),
            SubjectBoundReaction::HoldSharedForIntroduction
        );
        assert_eq!(h.dropped_private_count(), 1);
    }
}
