// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `autopilot=cruise` 6-stage continuation rotator & no-work anti-spin stop gate
//! (`aterm` primer; `Astream.Agent.TlaCruiseSixStageCycleGate`).
//!
//! Enforces `aterm`'s `autopilot=cruise` continuation semantics:
//! - Every turn end continues (including replies to the person's message, `NEEDS YOU:` reports,
//!   and turns ending while background jobs are still running -> check-background prompt).
//! - Each reply that claims the work is done receives one of six structured follow-up prompts in
//!   round-robin order (`WidestCheck -> HostileDiffReview -> OutOfScopeAudit -> MeasureAgainstMain
//!   -> NextOpenIssue -> LandSessionWork -> WidestCheck`).
//! - Only replies that repeat with NO real work (`identical_no_work_streak >= 2` or
//!   `consecutive_no_work_streak >= 6`) pause autopilot typing, until real work or someone else's
//!   turn resets the streak.

#[cfg(clean_islands)]
#[path = "cruise_six_stage_cycle_gate_island.rs"]
mod cruise_six_stage_cycle_gate_island;
#[cfg(clean_islands)]
pub use cruise_six_stage_cycle_gate_island::{
    cruise_stage_clamp_b125, cruise_turn_seq_advance_b125,
};

#[cfg(not(clean_islands))]
/// Clamp the 0-based `CruiseStage` index into `0..=max_stage` (`5`).
#[must_use]
pub const fn cruise_stage_clamp_b125(cand_stage: u64, max_stage: u64) -> u64 {
    if cand_stage < max_stage {
        cand_stage
    } else {
        max_stage
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the supervised turn sequence counter.
#[must_use]
pub const fn cruise_turn_seq_advance_b125(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}

contract_fn! {
    /// True iff no-work repetition should halt `cruise` typing (`same_streak >= 2 || total_streak >= 6`).
    #[must_use]
    pub const fn cruise_anti_spin_tripped_b125(same_streak: u64, total_streak: u64) -> bool
    clauses [ensures result == (same_streak >= 2 || total_streak >= 6)]
    {
        same_streak >= 2 || total_streak >= 6
    }
}

pub const CRUISE_MAX_STAGE_INDEX: u64 = 5;

/// The six rotating `autopilot=cruise` audit/work stages (`0..=5`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CruiseStage {
    WidestCheck,
    HostileDiffReview,
    OutOfScopeAudit,
    MeasureAgainstMain,
    NextOpenIssue,
    LandSessionWork,
}

impl CruiseStage {
    #[must_use]
    pub const fn from_index(idx: u64) -> Self {
        match idx {
            0 => Self::WidestCheck,
            1 => Self::HostileDiffReview,
            2 => Self::OutOfScopeAudit,
            3 => Self::MeasureAgainstMain,
            4 => Self::NextOpenIssue,
            _ => Self::LandSessionWork,
        }
    }
}

/// Action chosen by `autopilot=cruise` when an agent turn ends.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CruiseContinuation {
    /// Background task is still running: prompt agent to check background work and keep going.
    CheckBackgroundAndContinue { turn_seq: u64 },
    /// Work is still in progress (real work occurred, not claiming done): continue active thread.
    ContinueInProgressWork { turn_seq: u64 },
    /// Agent claimed work is done: inject the current stage prompt and advance stage `(i + 1) % 6`.
    PromptNextCruiseStage { stage: CruiseStage, turn_seq: u64 },
    /// Anti-spin tripped (`same >= 2` or `consecutive >= 6` no-work replies): stop typing until real work or external turn.
    PausedAntiSpin {
        same_reply_streak: u64,
        consecutive_no_work_streak: u64,
    },
}

/// Stateful `autopilot=cruise` 6-stage continuation & anti-spin gate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CruiseSixStageCycleGate {
    stage_idx: u64,
    turn_seq: u64,
    last_no_work_reply_fp: u64,
    same_reply_no_work_streak: u64,
    consecutive_no_work_streak: u64,
}

impl CruiseSixStageCycleGate {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            stage_idx: 0,
            turn_seq: 0,
            last_no_work_reply_fp: 0,
            same_reply_no_work_streak: 0,
            consecutive_no_work_streak: 0,
        }
    }

    #[must_use]
    pub const fn current_stage(&self) -> CruiseStage {
        CruiseStage::from_index(self.stage_idx)
    }

    /// Record someone else's turn (human or peer message), resetting any anti-spin pause.
    pub fn on_external_turn(&mut self) {
        self.turn_seq =
            cruise_turn_seq_advance_b125(self.turn_seq, self.turn_seq.saturating_add(1));
        self.last_no_work_reply_fp = 0;
        self.same_reply_no_work_streak = 0;
        self.consecutive_no_work_streak = 0;
    }

    /// Evaluate the end of an agent turn under `autopilot=cruise`.
    pub fn on_turn_end(
        &mut self,
        reply_fingerprint: u64,
        did_real_work: bool,
        background_jobs_running: bool,
        claims_work_done: bool,
    ) -> CruiseContinuation {
        self.turn_seq =
            cruise_turn_seq_advance_b125(self.turn_seq, self.turn_seq.saturating_add(1));

        if did_real_work {
            self.last_no_work_reply_fp = 0;
            self.same_reply_no_work_streak = 0;
            self.consecutive_no_work_streak = 0;
        } else {
            self.consecutive_no_work_streak = self.consecutive_no_work_streak.saturating_add(1);
            if self.consecutive_no_work_streak > 1
                && reply_fingerprint == self.last_no_work_reply_fp
            {
                self.same_reply_no_work_streak = self.same_reply_no_work_streak.saturating_add(1);
            } else {
                self.last_no_work_reply_fp = reply_fingerprint;
                self.same_reply_no_work_streak = 1;
            }
            if cruise_anti_spin_tripped_b125(
                self.same_reply_no_work_streak,
                self.consecutive_no_work_streak,
            ) {
                return CruiseContinuation::PausedAntiSpin {
                    same_reply_streak: self.same_reply_no_work_streak,
                    consecutive_no_work_streak: self.consecutive_no_work_streak,
                };
            }
        }

        if background_jobs_running {
            return CruiseContinuation::CheckBackgroundAndContinue {
                turn_seq: self.turn_seq,
            };
        }

        if claims_work_done {
            let emitted = CruiseStage::from_index(self.stage_idx);
            let next_raw = if self.stage_idx >= CRUISE_MAX_STAGE_INDEX {
                0
            } else {
                self.stage_idx.saturating_add(1)
            };
            self.stage_idx = cruise_stage_clamp_b125(next_raw, CRUISE_MAX_STAGE_INDEX);
            return CruiseContinuation::PromptNextCruiseStage {
                stage: emitted,
                turn_seq: self.turn_seq,
            };
        }

        CruiseContinuation::ContinueInProgressWork {
            turn_seq: self.turn_seq,
        }
    }
}

impl Default for CruiseSixStageCycleGate {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cycles_all_six_stages_and_halts_on_same_twice_or_six_distinct_no_work_replies() {
        let mut gate = CruiseSixStageCycleGate::new();

        // Turn ending with background work running prompts background check first.
        assert_eq!(
            gate.on_turn_end(0xAA, true, true, true),
            CruiseContinuation::CheckBackgroundAndContinue { turn_seq: 1 }
        );

        let expected = [
            CruiseStage::WidestCheck,
            CruiseStage::HostileDiffReview,
            CruiseStage::OutOfScopeAudit,
            CruiseStage::MeasureAgainstMain,
            CruiseStage::NextOpenIssue,
            CruiseStage::LandSessionWork,
            CruiseStage::WidestCheck,
        ];
        for (i, &stage) in expected.iter().enumerate() {
            assert_eq!(
                gate.on_turn_end(100 + i as u64, true, false, true),
                CruiseContinuation::PromptNextCruiseStage {
                    stage,
                    turn_seq: 2 + i as u64,
                }
            );
        }

        // Same reply twice with no work stops typing immediately.
        assert!(matches!(
            gate.on_turn_end(0xDEAD, false, false, true),
            CruiseContinuation::PromptNextCruiseStage { .. }
        ));
        assert_eq!(
            gate.on_turn_end(0xDEAD, false, false, true),
            CruiseContinuation::PausedAntiSpin {
                same_reply_streak: 2,
                consecutive_no_work_streak: 2,
            }
        );

        // External turn resets anti-spin; six distinct no-work replies also trip anti-spin.
        gate.on_external_turn();
        for fp in 1..=5 {
            assert!(matches!(
                gate.on_turn_end(fp, false, false, false),
                CruiseContinuation::ContinueInProgressWork { .. }
            ));
        }
        assert_eq!(
            gate.on_turn_end(6, false, false, false),
            CruiseContinuation::PausedAntiSpin {
                same_reply_streak: 1,
                consecutive_no_work_streak: 6,
            }
        );
    }
}
