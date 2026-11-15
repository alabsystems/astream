// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Strict `ATERM-TASK-DONE` discipline filter refusing completion-token emission when answering a
//! question, providing an audit, proposing next steps, or while background/actionable work remains
//! (`Astream.Autopilot.TlaDoneTokenGate`).

#[cfg(clean_islands)]
#[path = "done_token_gate_island.rs"]
mod done_token_gate_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ap_open_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ap_gate_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use done_token_gate_island::{ap_gate_advance, ap_open_clamp};

/// Maximum open work items counted in gate diagnostics.
pub const MAX_OPEN_WORK_ITEMS: u64 = 4_096;

contract_fn! {
    /// Verified zero-open-work check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ap_all_closed_isl`.
    #[must_use]
    pub const fn ap_all_closed(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TurnIntentKind {
    QuestionAnswer,
    AuditOrEvaluation,
    ProposingNextSteps,
    ContinuousGoalInProgress,
    FinalCompletedImplementation,
}

/// Enforces the global `Strict ATERM-TASK-DONE Discipline` rule.
#[derive(Debug, Clone, Default)]
pub struct TaskDoneTokenGate {
    evaluations: u64,
}

impl TaskDoneTokenGate {
    #[must_use]
    pub const fn new() -> Self {
        Self { evaluations: 0 }
    }

    pub fn may_emit_done_token(
        &mut self,
        intent: TurnIntentKind,
        open_tasks: u64,
        running_bg_jobs: u64,
    ) -> bool {
        self.evaluations = ap_gate_advance(self.evaluations, self.evaluations.saturating_add(1));
        if !matches!(intent, TurnIntentKind::FinalCompletedImplementation) {
            return false;
        }
        let blockers = ap_open_clamp(
            open_tasks.saturating_add(running_bg_jobs),
            MAX_OPEN_WORK_ITEMS,
        );
        ap_all_closed(0, blockers)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn done_gate_blocks_audits_questions_continuous_goals_and_running_bg_tasks() {
        let mut g = TaskDoneTokenGate::new();
        assert!(!g.may_emit_done_token(TurnIntentKind::AuditOrEvaluation, 0, 0));
        assert!(!g.may_emit_done_token(TurnIntentKind::ContinuousGoalInProgress, 0, 0));
        assert!(!g.may_emit_done_token(TurnIntentKind::FinalCompletedImplementation, 0, 1));
        assert!(g.may_emit_done_token(TurnIntentKind::FinalCompletedImplementation, 0, 0));
    }
}
