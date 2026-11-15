// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Premature completion-token emission suppressor (`Astream.Agent.TlaAtermTaskDoneTokenGuard`).
//!
//! Models strict completion-token discipline for continuous autonomous sessions:
//! blocks emitting terminal completion markers whenever answering a question, delivering an
//! audit/evaluation, proposing next steps, running an open-ended `/goal`, or while any
//! actionable work (`remaining_work > 0`) remains.

#[cfg(clean_islands)]
#[path = "aterm_task_done_token_guard_island.rs"]
mod aterm_task_done_token_guard_island;
#[cfg(clean_islands)]
pub use aterm_task_done_token_guard_island::{
    premature_done_clamp_b113, turn_audit_epoch_advance_b113,
};

#[cfg(not(clean_islands))]
/// Clamp suppressed premature-completion count to `max_suppressed`.
#[must_use]
pub const fn premature_done_clamp_b113(cand_suppressed: u64, max_suppressed: u64) -> u64 {
    if cand_suppressed < max_suppressed {
        cand_suppressed
    } else {
        max_suppressed
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the turn-completion audit epoch.
#[must_use]
pub const fn turn_audit_epoch_advance_b113(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `remaining_work == 0` and `in_flight_tasks == 0`.
    #[must_use]
    pub const fn all_finite_work_complete_b113(remaining_work: u64, in_flight_tasks: u64) -> bool
    clauses [ensures result == (remaining_work == 0 && in_flight_tasks == 0)]
    {
        remaining_work == 0 && in_flight_tasks == 0
    }
}

/// Nature of the current agent turn.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TurnResponseKind {
    QuestionAnswer,
    EvaluationOrAudit,
    NextStepsProposal,
    UnboundedForeverGoal,
    FiniteContinuousJobFinalStep,
}

/// Verdict on whether a terminal completion marker may be emitted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompletionTokenVerdict {
    OmitToken {
        suppressed_count: u64,
        audit_epoch: u64,
    },
    PermittedFinalCompletion {
        audit_epoch: u64,
    },
}

/// Guard preventing premature completion-token emission.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AtermTaskDoneTokenGuard {
    suppressed_count: u64,
    max_suppressed_cap: u64,
    audit_epoch: u64,
}

impl AtermTaskDoneTokenGuard {
    #[must_use]
    pub const fn new(max_suppressed_cap: u64) -> Self {
        let cap = if max_suppressed_cap == 0 {
            1024
        } else {
            max_suppressed_cap
        };
        Self {
            suppressed_count: 0,
            max_suppressed_cap: cap,
            audit_epoch: 0,
        }
    }

    #[must_use]
    pub const fn suppressed_count(&self) -> u64 {
        self.suppressed_count
    }

    /// Evaluate whether a terminal completion marker is permitted on this turn.
    pub fn check_emission(
        &mut self,
        kind: TurnResponseKind,
        remaining_work: u64,
        in_flight_tasks: u64,
        verified_100_pct: bool,
    ) -> CompletionTokenVerdict {
        let next_ep = self.audit_epoch.saturating_add(1);
        self.audit_epoch = turn_audit_epoch_advance_b113(self.audit_epoch, next_ep);

        let allowed = matches!(kind, TurnResponseKind::FiniteContinuousJobFinalStep)
            && verified_100_pct
            && all_finite_work_complete_b113(remaining_work, in_flight_tasks);

        if allowed {
            CompletionTokenVerdict::PermittedFinalCompletion {
                audit_epoch: self.audit_epoch,
            }
        } else {
            let cand = self.suppressed_count.saturating_add(1);
            self.suppressed_count = premature_done_clamp_b113(cand, self.max_suppressed_cap);
            CompletionTokenVerdict::OmitToken {
                suppressed_count: self.suppressed_count,
                audit_epoch: self.audit_epoch,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn omits_token_on_forever_goal_and_audits_allows_only_verified_finite_end() {
        let mut g = AtermTaskDoneTokenGuard::new(16);
        assert_eq!(
            g.check_emission(TurnResponseKind::UnboundedForeverGoal, 0, 0, true),
            CompletionTokenVerdict::OmitToken {
                suppressed_count: 1,
                audit_epoch: 1,
            }
        );
        assert_eq!(
            g.check_emission(TurnResponseKind::FiniteContinuousJobFinalStep, 0, 0, true),
            CompletionTokenVerdict::PermittedFinalCompletion { audit_epoch: 2 }
        );
    }
}
