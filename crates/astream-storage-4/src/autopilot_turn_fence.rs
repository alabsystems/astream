// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm` Autopilot (`off` / `land` / `cruise`) synthetic-continuation & human-input interlock
//! (`Astream.Host.TlaAutopilotTurnFence`).
//!
//! Enforces the `aterm` harness Autopilot invariants at turn boundaries:
//! 1. Never types while a person is typing or has unsent input (`human_unsent == true`).
//! 2. Under `Off`, never injects synthetic continuations.
//! 3. Under `Land`, stops once `nothing_left_verified && dirty_items == 0`, or when replying
//!    directly to a person's own message outside an active job within the 10-minute window.
//! 4. Under `Cruise`, rotates the 6-phase audit cycle and suppresses runaway idle loops when
//!    zero-work replies repeat (`same_reply_streak >= 2` or `zero_work_streak >= max_zero_work`).

#[cfg(clean_islands)]
#[path = "autopilot_turn_fence_island.rs"]
mod autopilot_turn_fence_island;
#[cfg(clean_islands)]
pub use autopilot_turn_fence_island::{autopilot_repeat_clamp, autopilot_turn_epoch_advance};

#[cfg(not(clean_islands))]
/// Clamp zero-work reply streak to `max_streak` (e.g., 6 under `aterm` Cruise).
#[must_use]
pub const fn autopilot_repeat_clamp(cand_streak: u64, max_streak: u64) -> u64 {
    if cand_streak < max_streak {
        cand_streak
    } else {
        max_streak
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the Autopilot turn epoch.
#[must_use]
pub const fn autopilot_turn_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff the zero-work repeat streak remains strictly below `max_streak`.
    #[must_use]
    pub const fn autopilot_streak_allows_continue(streak: u64, max_streak: u64) -> bool
    clauses [ensures result == (streak < max_streak)]
    {
        streak < max_streak
    }
}

/// `aterm` Autopilot operating mode (`autopilot=` in `aterm ctl @self status`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AutopilotMode {
    Off,
    Land,
    Cruise,
}

/// Decision at the end of an agent turn.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AutopilotTurnDecision {
    HoldForHumanInput,
    ParkedOff,
    LandedComplete,
    HoldHumanReplyWindow,
    ParkedRepeatThreshold,
    ContinueLand { turn_epoch: u64 },
    ContinueCruise { turn_epoch: u64, cruise_phase: u8 },
}

/// Turn-boundary interlock and Cruise 6-phase rotation tracker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AutopilotTurnFence {
    mode: AutopilotMode,
    max_zero_work_streak: u64,
    zero_work_streak: u64,
    last_reply_digest: u64,
    same_digest_streak: u64,
    cruise_phase: u8,
    turn_epoch: u64,
}

impl AutopilotTurnFence {
    #[must_use]
    pub const fn new(mode: AutopilotMode, max_zero_work_streak: u64) -> Self {
        let cap = if max_zero_work_streak == 0 {
            6
        } else {
            max_zero_work_streak
        };
        Self {
            mode,
            max_zero_work_streak: cap,
            zero_work_streak: 0,
            last_reply_digest: 0,
            same_digest_streak: 0,
            cruise_phase: 0,
            turn_epoch: 0,
        }
    }

    #[must_use]
    pub const fn turn_epoch(&self) -> u64 {
        self.turn_epoch
    }

    /// Reset repeat streaks when real work lands or a human initiates a new turn.
    pub fn notify_real_work_or_human_turn(&mut self) {
        self.zero_work_streak = 0;
        self.same_digest_streak = 0;
    }

    /// Evaluate whether Autopilot should inject a continuation prompt at turn end.
    pub fn on_turn_end(
        &mut self,
        human_typing_or_unsent: bool,
        did_work: bool,
        reply_digest: u64,
        dirty_or_unpushed_items: u64,
        nothing_left_verified: bool,
        direct_human_reply_within_10m: bool,
    ) -> AutopilotTurnDecision {
        let next_ep = self.turn_epoch.saturating_add(1);
        self.turn_epoch = autopilot_turn_epoch_advance(self.turn_epoch, next_ep);

        if human_typing_or_unsent {
            return AutopilotTurnDecision::HoldForHumanInput;
        }
        match self.mode {
            AutopilotMode::Off => AutopilotTurnDecision::ParkedOff,
            AutopilotMode::Land => {
                if direct_human_reply_within_10m {
                    return AutopilotTurnDecision::HoldHumanReplyWindow;
                }
                if nothing_left_verified && dirty_or_unpushed_items == 0 {
                    return AutopilotTurnDecision::LandedComplete;
                }
                AutopilotTurnDecision::ContinueLand {
                    turn_epoch: self.turn_epoch,
                }
            }
            AutopilotMode::Cruise => {
                if did_work {
                    self.zero_work_streak = 0;
                    self.same_digest_streak = 0;
                } else {
                    let cand = self.zero_work_streak.saturating_add(1);
                    self.zero_work_streak = autopilot_repeat_clamp(cand, self.max_zero_work_streak);
                    if reply_digest == self.last_reply_digest {
                        self.same_digest_streak = self.same_digest_streak.saturating_add(1);
                    } else {
                        self.same_digest_streak = 1;
                    }
                    self.last_reply_digest = reply_digest;
                    if self.same_digest_streak >= 2
                        || !autopilot_streak_allows_continue(
                            self.zero_work_streak,
                            self.max_zero_work_streak,
                        )
                    {
                        return AutopilotTurnDecision::ParkedRepeatThreshold;
                    }
                }
                let phase = self.cruise_phase;
                self.cruise_phase = self.cruise_phase.wrapping_add(1) % 6;
                AutopilotTurnDecision::ContinueCruise {
                    turn_epoch: self.turn_epoch,
                    cruise_phase: phase,
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cruise_rotates_six_phases_and_parks_on_duplicate_zero_work_replies() {
        let mut fence = AutopilotTurnFence::new(AutopilotMode::Cruise, 6);
        assert_eq!(
            fence.on_turn_end(false, true, 0xAA, 1, false, false),
            AutopilotTurnDecision::ContinueCruise {
                turn_epoch: 1,
                cruise_phase: 0,
            }
        );
        // Human unsent input always holds typing:
        assert_eq!(
            fence.on_turn_end(true, true, 0xBB, 1, false, false),
            AutopilotTurnDecision::HoldForHumanInput
        );
        // Two identical zero-work replies park Cruise until real work occurs:
        assert_eq!(
            fence.on_turn_end(false, false, 0xCC, 0, false, false),
            AutopilotTurnDecision::ContinueCruise {
                turn_epoch: 3,
                cruise_phase: 1,
            }
        );
        assert_eq!(
            fence.on_turn_end(false, false, 0xCC, 0, false, false),
            AutopilotTurnDecision::ParkedRepeatThreshold
        );
    }
}
