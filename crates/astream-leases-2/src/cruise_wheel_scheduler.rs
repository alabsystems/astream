// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Deterministic `aterm` Autopilot `cruise` 6-stage review/expansion wheel and anti-stagnation
//! scheduler (`Astream.Agent.TlaCruiseWheelScheduler`, Island #287).
//!
//! Under `autopilot=cruise`, `aterm` never parks at turn end:
//! - If an agent's own background tasks are running, `cruise` prompts it to check on that
//!   background work and keep going without waiting idle.
//! - Each reply claiming work is done advances through the 6-stage wheel in order:
//!   1. [`CruisePromptKind::WidestCheck`] (stage 0)
//!   2. [`CruisePromptKind::HostileReview`] (stage 1)
//!   3. [`CruisePromptKind::OutOfScopeAudit`] (stage 2)
//!   4. [`CruisePromptKind::MainMeasurement`] (stage 3)
//!   5. [`CruisePromptKind::NextOpenIssue`] (stage 4)
//!   6. [`CruisePromptKind::LandSessionWork`] (stage 5)
//!
//!   and then wraps back to stage 0 (`WidestCheck`).
//! - Anti-stagnation halt: only replies that repeat with no real work (`same_reply_streak >= 2`
//!   or `no_work_streak >= 6`) pause typing until real work or an operator turn resets streaks.

#[cfg(clean_islands)]
#[path = "cruise_wheel_scheduler_island.rs"]
mod cruise_wheel_scheduler_island;
#[cfg(clean_islands)]
pub use cruise_wheel_scheduler_island::{cruise_stage_clamp, cruise_streak_clamp};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn cruise_stage_clamp(stage: u64, max_stage: u64) -> u64 {
    if stage < max_stage {
        stage
    } else {
        max_stage
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn cruise_streak_clamp(streak: u64, max_streak: u64) -> u64 {
    if streak < max_streak {
        streak
    } else {
        max_streak
    }
}

/// Maximum wheel index (`0..=5` = 6 stages).
pub const MAX_CRUISE_STAGE: u64 = 5;

/// Consecutive identical no-work replies before `cruise` halts typing (`2`).
pub const CRUISE_SAME_REPLY_LIMIT: u64 = 2;

/// Consecutive total no-work replies before `cruise` halts typing (`6`).
pub const CRUISE_NO_WORK_LIMIT: u64 = 6;

contract_fn! {
    /// Verified check whether consecutive no-work replies reached `max_streak`
    /// (`max_streak <= no_work_streak`), linked via `clean-kernel-defeq` to
    /// `cruise_no_work_halted_isl`.
    #[must_use]
    pub const fn cruise_no_work_halted(no_work_streak: u64, max_streak: u64) -> bool
    clauses [ensures result == (max_streak <= no_work_streak)]
    {
        max_streak <= no_work_streak
    }
}

/// Prompt category selected by Autopilot `cruise` on turn completion.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CruisePromptKind {
    /// Background task still running: check on background work and keep going.
    CheckBackgroundAndContinue,
    /// Wheel stage 0: run the widest verification check.
    WidestCheck,
    /// Wheel stage 1: conduct a hostile review of the landed diff.
    HostileReview,
    /// Wheel stage 2: audit and build what was previously called out of scope.
    OutOfScopeAudit,
    /// Wheel stage 3: measure behavior/performance/proof surface against `main`.
    MainMeasurement,
    /// Wheel stage 4: pick up and resolve the next open issue.
    NextOpenIssue,
    /// Wheel stage 5: land what this session made while leaving what it did not.
    LandSessionWork,
}

impl CruisePromptKind {
    /// Map bounded stage index `0..=5` to its canonical wheel prompt kind.
    #[must_use]
    pub const fn from_stage(stage: u64) -> Self {
        match stage {
            0 => Self::WidestCheck,
            1 => Self::HostileReview,
            2 => Self::OutOfScopeAudit,
            3 => Self::MainMeasurement,
            4 => Self::NextOpenIssue,
            _ => Self::LandSessionWork,
        }
    }
}

/// Decision returned by [`CruiseWheelScheduler::on_turn_end`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CruiseAction {
    /// Operator is actively typing or has unsent input; type nothing.
    HoldForUnsentOperatorInput,
    /// Anti-stagnation guard tripped (`same >= 2` or `no_work >= 6`); stop typing until real work
    /// or someone else's turn.
    HaltedByStagnation {
        same_reply_streak: u64,
        no_work_streak: u64,
    },
    /// Inject the chosen continuation prompt.
    ContinueWith(CruisePromptKind),
}

/// Stateful Autopilot `cruise` scheduler for a supervised agent tab.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CruiseWheelScheduler {
    stage: u64,
    same_reply_streak: u64,
    no_work_streak: u64,
    last_no_work_digest: Option<u64>,
}

impl Default for CruiseWheelScheduler {
    fn default() -> Self {
        Self::new()
    }
}

impl CruiseWheelScheduler {
    /// Create a fresh `cruise` scheduler starting at stage `0` (`WidestCheck`).
    #[must_use]
    pub const fn new() -> Self {
        Self {
            stage: 0,
            same_reply_streak: 0,
            no_work_streak: 0,
            last_no_work_digest: None,
        }
    }

    /// Current wheel stage (`0..=5`).
    #[must_use]
    pub const fn stage(&self) -> u64 {
        self.stage
    }

    /// Current consecutive identical no-work reply count.
    #[must_use]
    pub const fn same_reply_streak(&self) -> u64 {
        self.same_reply_streak
    }

    /// Current consecutive total no-work reply count.
    #[must_use]
    pub const fn no_work_streak(&self) -> u64 {
        self.no_work_streak
    }

    #[must_use]
    pub const fn last_no_work_digest(&self) -> Option<u64> {
        self.last_no_work_digest
    }

    /// Record an explicit operator turn, clearing stagnation streaks while preserving wheel stage.
    pub fn on_operator_turn(&mut self) {
        self.same_reply_streak = 0;
        self.no_work_streak = 0;
        self.last_no_work_digest = None;
    }

    /// Evaluate turn end and compute the next `cruise` action.
    #[allow(clippy::too_many_arguments)]
    pub fn on_turn_end(
        &mut self,
        operator_typing_or_unsent: bool,
        background_work_running: bool,
        did_real_work: bool,
        claimed_done: bool,
        reply_digest: u64,
    ) -> CruiseAction {
        if operator_typing_or_unsent {
            return CruiseAction::HoldForUnsentOperatorInput;
        }

        if did_real_work {
            self.same_reply_streak = 0;
            self.no_work_streak = 0;
            self.last_no_work_digest = None;
        } else {
            let next_no_work = self.no_work_streak.saturating_add(1);
            self.no_work_streak = cruise_streak_clamp(next_no_work, CRUISE_NO_WORK_LIMIT);
            if self.last_no_work_digest == Some(reply_digest) {
                let next_same = self.same_reply_streak.saturating_add(1);
                self.same_reply_streak = cruise_streak_clamp(next_same, CRUISE_SAME_REPLY_LIMIT);
            } else {
                self.same_reply_streak = 1;
                self.last_no_work_digest = Some(reply_digest);
            }

            if cruise_no_work_halted(self.same_reply_streak, CRUISE_SAME_REPLY_LIMIT)
                || cruise_no_work_halted(self.no_work_streak, CRUISE_NO_WORK_LIMIT)
            {
                return CruiseAction::HaltedByStagnation {
                    same_reply_streak: self.same_reply_streak,
                    no_work_streak: self.no_work_streak,
                };
            }
        }

        if background_work_running {
            return CruiseAction::ContinueWith(CruisePromptKind::CheckBackgroundAndContinue);
        }

        if claimed_done {
            let clamped = cruise_stage_clamp(self.stage, MAX_CRUISE_STAGE);
            let prompt = CruisePromptKind::from_stage(clamped);
            self.stage = if clamped < MAX_CRUISE_STAGE {
                cruise_stage_clamp(clamped.saturating_add(1), MAX_CRUISE_STAGE)
            } else {
                0
            };
            CruiseAction::ContinueWith(prompt)
        } else {
            CruiseAction::ContinueWith(CruisePromptKind::from_stage(cruise_stage_clamp(
                self.stage,
                MAX_CRUISE_STAGE,
            )))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wheel_rotates_all_six_stages_and_wraps() {
        let mut sched = CruiseWheelScheduler::new();
        let expected = [
            CruisePromptKind::WidestCheck,
            CruisePromptKind::HostileReview,
            CruisePromptKind::OutOfScopeAudit,
            CruisePromptKind::MainMeasurement,
            CruisePromptKind::NextOpenIssue,
            CruisePromptKind::LandSessionWork,
            CruisePromptKind::WidestCheck,
        ];
        for (i, want) in expected.iter().copied().enumerate() {
            let got = sched.on_turn_end(false, false, true, true, i as u64 + 100);
            assert_eq!(got, CruiseAction::ContinueWith(want));
        }
    }

    #[test]
    fn background_work_prompts_check_without_consuming_wheel_stage() {
        let mut sched = CruiseWheelScheduler::new();
        assert_eq!(
            sched.on_turn_end(false, true, true, true, 1),
            CruiseAction::ContinueWith(CruisePromptKind::CheckBackgroundAndContinue)
        );
        assert_eq!(sched.stage(), 0);
    }

    #[test]
    fn halts_on_same_no_work_reply_twice_and_resumes_on_operator_turn() {
        let mut sched = CruiseWheelScheduler::new();
        assert_eq!(
            sched.on_turn_end(false, false, false, true, 0xDEAD_BEEF),
            CruiseAction::ContinueWith(CruisePromptKind::WidestCheck)
        );
        assert_eq!(
            sched.on_turn_end(false, false, false, true, 0xDEAD_BEEF),
            CruiseAction::HaltedByStagnation {
                same_reply_streak: 2,
                no_work_streak: 2,
            }
        );
        sched.on_operator_turn();
        assert_eq!(
            sched.on_turn_end(false, false, true, true, 0xCAFE),
            CruiseAction::ContinueWith(CruisePromptKind::HostileReview)
        );
    }

    #[test]
    fn halts_after_six_distinct_no_work_replies() {
        let mut sched = CruiseWheelScheduler::new();
        for d in 1..=5 {
            assert!(matches!(
                sched.on_turn_end(false, false, false, true, d),
                CruiseAction::ContinueWith(_)
            ));
        }
        assert_eq!(
            sched.on_turn_end(false, false, false, true, 6),
            CruiseAction::HaltedByStagnation {
                same_reply_streak: 1,
                no_work_streak: 6,
            }
        );
    }
}
