// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Autopilot `cruise` 6-stage work-kind rotator & idle-repeat circuit breaker.
//!
//! Under `aterm` Autopilot `cruise`, every turn that reports completion receives the next
//! stage in a 6-part verification & landing ring:
//! 1. `WidestCheck` — run the widest test & formal verification suite.
//! 2. `HostileDiffReview` — perform a hostile review of the landed diff.
//! 3. `OutOfScopeAudit` — revisit items previously called out of scope.
//! 4. `MeasureAgainstMain` — benchmark / measure behavior against `main`.
//! 5. `NextOpenIssue` — pull and implement the next open roadmap/issue item.
//! 6. `LandSessionWork` — land what the session made while leaving peer work untouched.
//!
//! Typing pauses *only* when a no-work reply repeats identically twice in a row OR six
//! consecutive turns pass with no real work (`MAX_CONSECUTIVE_IDLE_REPLIES = 6`), resuming
//! immediately when real work or an operator turn occurs.
//!
//! Clean specification: `cruise_cadence_rotator_island.rs` (`Astream.Agent.TlaCruiseWorkRotator`).

#[cfg(clean_islands)]
#[path = "cruise_cadence_rotator_island.rs"]
mod cruise_cadence_rotator_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cruise_idle_streak_clamp(cand_streak: u64, max_streak: u64) -> u64 {
    if cand_streak < max_streak {
        cand_streak
    } else {
        max_streak
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cruise_turn_advance(cur_turn: u64, cand_turn: u64) -> u64 {
    if cur_turn < cand_turn {
        cand_turn
    } else {
        cur_turn
    }
}
#[cfg(clean_islands)]
pub use cruise_cadence_rotator_island::{cruise_idle_streak_clamp, cruise_turn_advance};

/// Hard ceiling on consecutive zero-work replies before Cruise stops typing (`6`).
pub const MAX_CONSECUTIVE_IDLE_REPLIES: u64 = 6;

contract_fn! {
    /// Kernel-certified check that `idle_streak <= max_streak`, linked via
    /// `clean-kernel-defeq` to `cruise_idle_within_cap_isl`.
    #[must_use]
    pub const fn cruise_idle_within_cap(idle_streak: u64, max_streak: u64) -> bool
    clauses [ensures result == (idle_streak <= max_streak)]
    {
        idle_streak <= max_streak
    }
}

/// The 6 canonical work-kind stages rotated by `aterm` Autopilot `cruise`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CruiseWorkStage {
    WidestCheck,
    HostileDiffReview,
    OutOfScopeAudit,
    MeasureAgainstMain,
    NextOpenIssue,
    LandSessionWork,
}

impl CruiseWorkStage {
    #[must_use]
    pub const fn next(self) -> Self {
        match self {
            Self::WidestCheck => Self::HostileDiffReview,
            Self::HostileDiffReview => Self::OutOfScopeAudit,
            Self::OutOfScopeAudit => Self::MeasureAgainstMain,
            Self::MeasureAgainstMain => Self::NextOpenIssue,
            Self::NextOpenIssue => Self::LandSessionWork,
            Self::LandSessionWork => Self::WidestCheck,
        }
    }
}

/// Action chosen by `CruiseCadenceRotator` when an agent turn ends.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CruiseAction {
    /// Agent still has background tasks running: prompt to check on them and continue.
    CheckBackgroundAndContinue { turn_seq: u64 },
    /// Prompt the agent with the next rotated `CruiseWorkStage`.
    PromptStage {
        turn_seq: u64,
        stage: CruiseWorkStage,
    },
    /// Stop typing because identical no-work reply repeated twice or 6 idle replies elapsed.
    ParkOnIdleRepeat {
        turn_seq: u64,
        idle_streak: u64,
        duplicate_reply: bool,
    },
}

fn fnv1a64_trimmed(text: &str) -> u64 {
    let trimmed = text.trim();
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    let mut cur = trimmed.as_bytes();
    while let &[b, ref rest @ ..] = cur {
        cur = rest;
        h = (h ^ (b as u64)).wrapping_mul(0x0100_0000_01b3);
    }
    h
}

/// Deterministic `aterm` Autopilot `cruise` scheduler state machine.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CruiseCadenceRotator {
    next_stage: CruiseWorkStage,
    idle_streak: u64,
    last_idle_digest: Option<u64>,
    turn_seq: u64,
}

impl Default for CruiseCadenceRotator {
    fn default() -> Self {
        Self::new()
    }
}

impl CruiseCadenceRotator {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            next_stage: CruiseWorkStage::WidestCheck,
            idle_streak: 0,
            last_idle_digest: None,
            turn_seq: 0,
        }
    }

    #[must_use]
    pub const fn idle_streak(&self) -> u64 {
        self.idle_streak
    }

    #[must_use]
    pub const fn turn_seq(&self) -> u64 {
        self.turn_seq
    }

    #[must_use]
    pub const fn peek_stage(&self) -> CruiseWorkStage {
        self.next_stage
    }

    /// Reset the idle streak when an operator sends a fresh message.
    pub fn on_operator_turn(&mut self) {
        self.idle_streak = 0;
        self.last_idle_digest = None;
    }

    /// Evaluate the end of an agent turn and select the next Cruise action.
    pub fn on_turn_end(
        &mut self,
        background_work_running: bool,
        did_real_work: bool,
        reply_text: &str,
    ) -> CruiseAction {
        let next_turn = cruise_turn_advance(self.turn_seq, self.turn_seq.saturating_add(1));
        self.turn_seq = next_turn;

        if background_work_running {
            if did_real_work {
                self.idle_streak = 0;
                self.last_idle_digest = None;
            }
            return CruiseAction::CheckBackgroundAndContinue {
                turn_seq: next_turn,
            };
        }

        if did_real_work {
            self.idle_streak = 0;
            self.last_idle_digest = None;
            let stage = self.next_stage;
            self.next_stage = stage.next();
            return CruiseAction::PromptStage {
                turn_seq: next_turn,
                stage,
            };
        }

        let digest = fnv1a64_trimmed(reply_text);
        let duplicate = self.last_idle_digest == Some(digest);
        self.last_idle_digest = Some(digest);

        let clamped_streak = cruise_idle_streak_clamp(
            self.idle_streak.saturating_add(1),
            MAX_CONSECUTIVE_IDLE_REPLIES,
        );
        let _ = cruise_idle_within_cap(clamped_streak, MAX_CONSECUTIVE_IDLE_REPLIES);
        self.idle_streak = clamped_streak;

        if duplicate || clamped_streak >= MAX_CONSECUTIVE_IDLE_REPLIES {
            return CruiseAction::ParkOnIdleRepeat {
                turn_seq: next_turn,
                idle_streak: clamped_streak,
                duplicate_reply: duplicate,
            };
        }

        let stage = self.next_stage;
        self.next_stage = stage.next();
        CruiseAction::PromptStage {
            turn_seq: next_turn,
            stage,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cycles_all_six_stages_and_stops_on_duplicate_or_six_idle_replies() {
        let mut rot = CruiseCadenceRotator::new();
        assert_eq!(
            rot.on_turn_end(true, true, "running build"),
            CruiseAction::CheckBackgroundAndContinue { turn_seq: 1 }
        );

        let expected = [
            CruiseWorkStage::WidestCheck,
            CruiseWorkStage::HostileDiffReview,
            CruiseWorkStage::OutOfScopeAudit,
            CruiseWorkStage::MeasureAgainstMain,
            CruiseWorkStage::NextOpenIssue,
            CruiseWorkStage::LandSessionWork,
            CruiseWorkStage::WidestCheck,
        ];
        for (i, &stage) in expected.iter().enumerate() {
            assert_eq!(
                rot.on_turn_end(false, true, "landed commit"),
                CruiseAction::PromptStage {
                    turn_seq: (i + 2) as u64,
                    stage,
                }
            );
        }

        // Two identical zero-work replies park immediately.
        let _ = rot.on_turn_end(false, false, "nothing left to do");
        assert_eq!(
            rot.on_turn_end(false, false, "  nothing left to do  "),
            CruiseAction::ParkOnIdleRepeat {
                turn_seq: 10,
                idle_streak: 2,
                duplicate_reply: true,
            }
        );

        // Operator turn clears idle state; 6 distinct idle replies park on streak == 6.
        rot.on_operator_turn();
        for k in 1..=5 {
            let msg = format!("distinct idle reply {k}");
            assert!(matches!(
                rot.on_turn_end(false, false, &msg),
                CruiseAction::PromptStage { .. }
            ));
        }
        assert_eq!(
            rot.on_turn_end(false, false, "distinct idle reply 6"),
            CruiseAction::ParkOnIdleRepeat {
                turn_seq: 16,
                idle_streak: 6,
                duplicate_reply: false,
            }
        );
    }
}
