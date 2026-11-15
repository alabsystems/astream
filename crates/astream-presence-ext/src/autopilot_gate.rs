// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm` Autopilot (`off | land | cruise`) turn-continuation state machine, 6-kind `cruise`
//! work rotator, 10-minute human-question park rule under `land`, and identical/no-work
//! repeat-reply stopper (`Astream.Presence.TlaAutopilotGate`).
//!
//! Directly encodes the `aterm` primer rules:
//! - `off`: types nothing (`AutopilotDecision::ParkOff`).
//! - `land`: parks immediately if the human has unsent input, if answering a human's own message
//!   within `HUMAN_OWN_REPLY_WINDOW_MS = 600_000` (10 minutes) outside a continuing job, or once
//!   `reply` starts with `Nothing left:` and `git_clean` is true; otherwise continues landing!
//! - `cruise`: rotates through the 6 work prompts (`WidestCheck -> HostileReview -> OutOfScope ->
//!   MeasureAgainstMain -> NextOpenIssue -> LandSessionWork -> WidestCheck`), continues on
//!   `NEEDS YOU:` and running background work, and stops typing ONLY when a no-work reply
//!   repeats identically twice (`2` in a row via `Sha256` + `ct_eq`) or `6` no-work replies land
//!   in a row (`ap_streak_clamp` / `ap_should_park`).

use astream_digest::{ct_eq, Sha256};

#[cfg(clean_islands)]
#[path = "autopilot_gate_island.rs"]
mod autopilot_gate_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ap_streak_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ap_turn_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use autopilot_gate_island::{ap_streak_clamp, ap_turn_advance};

/// Six consecutive no-work replies stop `cruise` typing until real work or someone else's turn.
pub const MAX_IDLE_REPEAT_STREAK: u64 = 6;
/// Two identical no-work replies in a row stop `cruise` typing immediately.
pub const IDENTICAL_NO_WORK_LIMIT: u64 = 2;
/// Ten-minute window (`600_000 ms`) under `land` for a person's own question outside a job.
pub const HUMAN_OWN_REPLY_WINDOW_MS: u64 = 600_000;

contract_fn! {
    /// Verified threshold check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ap_should_park_isl`.
    #[must_use]
    pub const fn ap_should_park(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Configured `autopilot=` mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GateMode {
    Off,
    Land,
    Cruise,
}

/// Six rotating follow-up prompts under `autopilot=cruise`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CruisePromptKind {
    WidestCheck,
    HostileReview,
    OutOfScopeWork,
    MeasureAgainstMain,
    NextOpenIssue,
    LandSessionWork,
}

impl CruisePromptKind {
    #[must_use]
    pub const fn from_slot(slot: u64) -> Self {
        let q = slot / 6;
        let rem = slot.saturating_sub(q.saturating_mul(6));
        match rem {
            0 => Self::WidestCheck,
            1 => Self::HostileReview,
            2 => Self::OutOfScopeWork,
            3 => Self::MeasureAgainstMain,
            4 => Self::NextOpenIssue,
            _ => Self::LandSessionWork,
        }
    }
}

/// Decision emitted by [`AutopilotTurnGate::on_turn_end`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AutopilotContinuation {
    ParkOff,
    ParkHumanTyping,
    ParkHumanOwnReply,
    ParkLandedNothingLeft,
    ParkCruiseRepeatStop,
    ContinueCheckBackground,
    ContinueLandRemaining,
    ContinueCruise(CruisePromptKind),
}

/// Observation summarizing a completed agent turn.
#[derive(Debug, Clone, Copy)]
pub struct TurnEndSummary<'a> {
    pub reply_text: &'a str,
    pub human_typing_or_unsent: bool,
    pub background_work_running: bool,
    pub did_real_work: bool,
    pub git_nothing_left: bool,
    pub human_own_message_age_ms: Option<u64>,
    pub continuing_job: bool,
}

/// Deterministic `aterm` Autopilot continuation gate.
#[derive(Debug, Clone)]
pub struct AutopilotTurnGate {
    mode: GateMode,
    turn_seq: u64,
    cruise_cursor: u64,
    no_work_streak: u64,
    identical_no_work_streak: u64,
    last_reply_sha: Option<[u8; 32]>,
}

impl Default for AutopilotTurnGate {
    fn default() -> Self {
        Self::new()
    }
}

impl AutopilotTurnGate {
    #[must_use]
    pub const fn new() -> Self {
        Self::with_mode(GateMode::Cruise)
    }

    #[must_use]
    pub const fn with_mode(mode: GateMode) -> Self {
        Self {
            mode,
            turn_seq: 0,
            cruise_cursor: 0,
            no_work_streak: 0,
            identical_no_work_streak: 0,
            last_reply_sha: None,
        }
    }

    #[must_use]
    pub const fn turn_seq(&self) -> u64 {
        self.turn_seq
    }

    #[must_use]
    pub const fn no_work_streak(&self) -> u64 {
        self.no_work_streak
    }

    /// Resets repeat counters when an external human/peer turn arrives.
    pub fn notify_external_turn(&mut self) {
        self.no_work_streak = 0;
        self.identical_no_work_streak = 0;
        self.last_reply_sha = None;
    }

    /// Evaluates the exact `aterm` Autopilot continuation decision at turn end.
    pub fn on_turn_end(&mut self, obs: TurnEndSummary<'_>) -> AutopilotContinuation {
        self.turn_seq = ap_turn_advance(self.turn_seq, self.turn_seq.saturating_add(1));
        if obs.human_typing_or_unsent {
            return AutopilotContinuation::ParkHumanTyping;
        }
        match self.mode {
            GateMode::Off => AutopilotContinuation::ParkOff,
            GateMode::Land => {
                if !obs.continuing_job {
                    if let Some(age_ms) = obs.human_own_message_age_ms {
                        if !ap_should_park(age_ms, HUMAN_OWN_REPLY_WINDOW_MS.saturating_add(1)) {
                            return AutopilotContinuation::ParkHumanOwnReply;
                        }
                    }
                }
                if obs.background_work_running {
                    return AutopilotContinuation::ContinueCheckBackground;
                }
                if obs.git_nothing_left {
                    if let Some(after) = obs.reply_text.trim_start().strip_prefix("Nothing left:") {
                        if !after.trim().is_empty() {
                            return AutopilotContinuation::ParkLandedNothingLeft;
                        }
                    }
                }
                AutopilotContinuation::ContinueLandRemaining
            }
            GateMode::Cruise => {
                if obs.background_work_running {
                    return AutopilotContinuation::ContinueCheckBackground;
                }
                let digest = Sha256::digest_slice(obs.reply_text.trim().as_bytes());
                if obs.did_real_work {
                    self.no_work_streak = 0;
                    self.identical_no_work_streak = 0;
                    self.last_reply_sha = Some(digest);
                } else {
                    let next_nw = self.no_work_streak.saturating_add(1);
                    self.no_work_streak = ap_streak_clamp(next_nw, MAX_IDLE_REPEAT_STREAK);
                    let same = match self.last_reply_sha {
                        Some(prev) => ct_eq(&prev, &digest),
                        None => false,
                    };
                    self.identical_no_work_streak = if same {
                        ap_streak_clamp(
                            self.identical_no_work_streak.saturating_add(1),
                            MAX_IDLE_REPEAT_STREAK,
                        )
                    } else {
                        1
                    };
                    self.last_reply_sha = Some(digest);
                    if ap_should_park(self.identical_no_work_streak, IDENTICAL_NO_WORK_LIMIT)
                        || ap_should_park(self.no_work_streak, MAX_IDLE_REPEAT_STREAK)
                    {
                        return AutopilotContinuation::ParkCruiseRepeatStop;
                    }
                }
                let kind = CruisePromptKind::from_slot(self.cruise_cursor);
                self.cruise_cursor = self.cruise_cursor.saturating_add(1);
                AutopilotContinuation::ContinueCruise(kind)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cruise_rotates_six_prompts_continues_background_and_stops_on_two_identical_or_six_idle() {
        let mut gate = AutopilotTurnGate::with_mode(GateMode::Cruise);
        // Background work running prompts immediate check-and-keep-going.
        assert_eq!(
            gate.on_turn_end(TurnEndSummary {
                reply_text: "NEEDS YOU: token",
                human_typing_or_unsent: false,
                background_work_running: true,
                did_real_work: true,
                git_nothing_left: false,
                human_own_message_age_ms: None,
                continuing_job: true,
            }),
            AutopilotContinuation::ContinueCheckBackground
        );

        // Two identical no-work replies stop cruise immediately.
        let r1 = gate.on_turn_end(TurnEndSummary {
            reply_text: "All done, nothing else.",
            human_typing_or_unsent: false,
            background_work_running: false,
            did_real_work: false,
            git_nothing_left: true,
            human_own_message_age_ms: None,
            continuing_job: true,
        });
        assert_eq!(
            r1,
            AutopilotContinuation::ContinueCruise(CruisePromptKind::WidestCheck)
        );
        let r2 = gate.on_turn_end(TurnEndSummary {
            reply_text: "All done, nothing else.",
            human_typing_or_unsent: false,
            background_work_running: false,
            did_real_work: false,
            git_nothing_left: true,
            human_own_message_age_ms: None,
            continuing_job: true,
        });
        assert_eq!(r2, AutopilotContinuation::ParkCruiseRepeatStop);

        // Land parks on `Nothing left:` iff git is clean, and respects 10m human own message.
        let mut land = AutopilotTurnGate::with_mode(GateMode::Land);
        assert_eq!(
            land.on_turn_end(TurnEndSummary {
                reply_text: "Here is the answer.",
                human_typing_or_unsent: false,
                background_work_running: false,
                did_real_work: false,
                git_nothing_left: false,
                human_own_message_age_ms: Some(120_000),
                continuing_job: false,
            }),
            AutopilotContinuation::ParkHumanOwnReply
        );
        assert_eq!(
            land.on_turn_end(TurnEndSummary {
                reply_text: "Nothing left: main is aligned at 2c42a8d.",
                human_typing_or_unsent: false,
                background_work_running: false,
                did_real_work: true,
                git_nothing_left: true,
                human_own_message_age_ms: None,
                continuing_job: true,
            }),
            AutopilotContinuation::ParkLandedNothingLeft
        );
    }
}
