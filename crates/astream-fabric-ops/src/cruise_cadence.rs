// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Autopilot `cruise` / `land` / `off` turn-continuation wheel & repeat-stop state machine
//! (`aterm` primer v45, `Astream.Broker.TlaCruiseCadence`).
//!
//! Models `aterm`'s Autopilot harness rules with Clean-certified bounds and `0 mandated`
//! obligations:
//! - Never types while the person has unsent input (`human_unsent_input == true`).
//! - Under `Off`: never types.
//! - Under `Land`: continues until `Nothing left:` starts the reply AND git state is clean
//!   (nothing uncommitted, unpushed, unmerged, or parked), while leaving direct replies to
//!   a person's own recent (<10 min) standalone question untouched.
//! - Under `Cruise`: cycles deterministically through the 6-rung inspection wheel
//!   (`WidestCheck` -> `HostileDiffReview` -> `OutOfScopeAudit` -> `MeasureAgainstMain` ->
//!   `NextOpenIssue` -> `LandCleanly` -> repeat), prompting background-task follow-up when
//!   background jobs are running, and parking ONLY when a no-work reply repeats (`same_reply_twice`
//!   or `6` consecutive no-work replies, verified by [`cruise_should_park`]).

use astream_wire::fnv1a_64;

#[cfg(clean_islands)]
#[path = "cruise_cadence_island.rs"]
mod cruise_cadence_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cruise_rung_clamp(rung: u64, max_rung: u64) -> u64 {
    if rung < max_rung {
        rung
    } else {
        max_rung
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cruise_no_work_clamp(streak: u64, max_streak: u64) -> u64 {
    if streak < max_streak {
        streak
    } else {
        max_streak
    }
}
#[cfg(clean_islands)]
pub use cruise_cadence_island::{cruise_no_work_clamp, cruise_rung_clamp};

/// Highest zero-based index on the 6-rung Cruise wheel (`0..=5`).
pub const MAX_CRUISE_RUNG_IDX: u64 = 5;

/// Number of consecutive no-work replies that stops Cruise typing until new work arrives.
pub const CRUISE_NO_WORK_STOP_LIMIT: u64 = 6;

contract_fn! {
    /// Verified check whether Cruise should stop typing due to repeated no-work replies
    /// (`same_reply_twice || streak >= limit`), linked via `clean-kernel-defeq` to
    /// `cruise_should_park_isl`.
    #[must_use]
    pub const fn cruise_should_park(same_reply_twice: bool, streak: u64, limit: u64) -> bool
    clauses [ensures result == (same_reply_twice || limit <= streak)]
    {
        same_reply_twice || limit <= streak
    }
}

/// Autopilot operating mode (`autopilot=off|land|cruise` in `aterm ctl @self status`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AutopilotMode {
    /// Types nothing.
    Off,
    /// Continues until all work is on remote `main` and a reply starting `Nothing left:` defends it.
    Land,
    /// Continues every turn end through the 6-rung Cruise wheel; stops only on repeated no-work.
    Cruise,
}

/// The six rotating prompts of `aterm` Autopilot `cruise` mode, in exact primer order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CruiseRung {
    /// 0: Run the widest verification check.
    WidestCheck,
    /// 1: Perform a hostile review of the landed diff.
    HostileDiffReview,
    /// 2: Implement what was previously called out of scope.
    OutOfScopeAudit,
    /// 3: Run a quantitative measurement against `main`.
    MeasureAgainstMain,
    /// 4: Tackle the next open issue.
    NextOpenIssue,
    /// 5: Land what this session made cleanly while leaving what it did not.
    LandCleanly,
}

impl CruiseRung {
    /// Map a clamped index `0..=5` to its [`CruiseRung`].
    #[must_use]
    pub const fn from_idx(idx: u64) -> Self {
        match idx {
            0 => Self::WidestCheck,
            1 => Self::HostileDiffReview,
            2 => Self::OutOfScopeAudit,
            3 => Self::MeasureAgainstMain,
            4 => Self::NextOpenIssue,
            _ => Self::LandCleanly,
        }
    }
}

/// Turn-end context evaluated by [`AutopilotCadence::on_turn_end`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TurnEndFacts<'a> {
    /// Text of the agent's reply that just ended the turn.
    pub reply_text: &'a str,
    /// True if the person is actively typing or has unsent input in the prompt box.
    pub human_unsent_input: bool,
    /// True if the session's own background tasks/jobs are still running.
    pub background_work_running: bool,
    /// True if the agent performed real code/verification work during this turn.
    pub did_real_work: bool,
    /// Under `Land`: true if git has zero uncommitted, unpushed, or unmerged changes.
    pub git_all_on_remote_main: bool,
    /// Under `Land`: true if this turn answered a standalone human message outside an active job within 10m.
    pub standalone_human_qa_within_10m: bool,
}

/// Action chosen by [`AutopilotCadence`] when an agent turn ends.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CadenceDecision {
    /// Do not type anything (human typing, `Off`, `Land` complete, or repeated no-work stop).
    HoldSilent,
    /// Prompt the agent to check on its running background work and keep going.
    PromptCheckBackgroundWork,
    /// Under `Land`: prompt the agent to finish landing/pushing remaining work to remote `main`.
    PromptContinueLanding,
    /// Under `Cruise`: continue active implementation before rotating the done-wheel.
    PromptKeepGoing,
    /// Under `Cruise`: issue the next rotating rung prompt from the 6-rung wheel.
    PromptCruiseRung(CruiseRung),
}

/// Stateful Autopilot `off` / `land` / `cruise` cadence engine.
#[derive(Debug, Clone)]
pub struct AutopilotCadence {
    mode: AutopilotMode,
    rung_idx: u64,
    no_work_streak: u64,
    last_no_work_hash: Option<u64>,
}

impl AutopilotCadence {
    /// Construct a cadence state machine starting at rung `0` (`WidestCheck`).
    #[must_use]
    pub const fn new(mode: AutopilotMode) -> Self {
        Self {
            mode,
            rung_idx: 0,
            no_work_streak: 0,
            last_no_work_hash: None,
        }
    }

    /// Current Autopilot mode.
    #[must_use]
    pub const fn mode(&self) -> AutopilotMode {
        self.mode
    }

    /// Reset repeat-stop counters when someone else's turn or new real work arrives.
    pub fn notify_external_turn(&mut self) {
        self.no_work_streak = 0;
        self.last_no_work_hash = None;
    }

    /// Decide what Autopilot types (if anything) when a turn ends.
    pub fn on_turn_end(&mut self, facts: TurnEndFacts<'_>) -> CadenceDecision {
        // Law: Nothing is EVER typed while the person types or has input unsent.
        if facts.human_unsent_input {
            return CadenceDecision::HoldSilent;
        }
        match self.mode {
            AutopilotMode::Off => CadenceDecision::HoldSilent,
            AutopilotMode::Land => {
                if facts.standalone_human_qa_within_10m {
                    return CadenceDecision::HoldSilent;
                }
                if facts.background_work_running {
                    return CadenceDecision::PromptCheckBackgroundWork;
                }
                let trimmed = facts.reply_text.trim_start();
                if trimmed.starts_with("Nothing left:") && facts.git_all_on_remote_main {
                    CadenceDecision::HoldSilent
                } else {
                    CadenceDecision::PromptContinueLanding
                }
            }
            AutopilotMode::Cruise => {
                if facts.background_work_running {
                    if facts.did_real_work {
                        self.no_work_streak = 0;
                        self.last_no_work_hash = None;
                    }
                    return CadenceDecision::PromptCheckBackgroundWork;
                }
                let norm_hash = fnv1a_64(facts.reply_text.trim().as_bytes());
                if facts.did_real_work {
                    self.no_work_streak = 0;
                    self.last_no_work_hash = None;
                } else {
                    let same_twice = self.last_no_work_hash == Some(norm_hash);
                    let raw_next = self.no_work_streak.saturating_add(1);
                    self.no_work_streak = cruise_no_work_clamp(raw_next, CRUISE_NO_WORK_STOP_LIMIT);
                    self.last_no_work_hash = Some(norm_hash);
                    if cruise_should_park(
                        same_twice,
                        self.no_work_streak,
                        CRUISE_NO_WORK_STOP_LIMIT,
                    ) {
                        return CadenceDecision::HoldSilent;
                    }
                }

                if reply_claims_done(facts.reply_text) {
                    let clamped_idx = cruise_rung_clamp(self.rung_idx, MAX_CRUISE_RUNG_IDX);
                    let rung = CruiseRung::from_idx(clamped_idx);
                    let next_idx = if clamped_idx >= MAX_CRUISE_RUNG_IDX {
                        0
                    } else {
                        clamped_idx.saturating_add(1)
                    };
                    self.rung_idx = cruise_rung_clamp(next_idx, MAX_CRUISE_RUNG_IDX);
                    CadenceDecision::PromptCruiseRung(rung)
                } else {
                    CadenceDecision::PromptKeepGoing
                }
            }
        }
    }
}

fn reply_claims_done(text: &str) -> bool {
    let t = text.trim_start();
    t.starts_with("Nothing left:")
        || text.contains("All tasks complete")
        || text.contains("work is done")
        || text.contains("completed and pushed")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cruise_rotates_all_six_rungs_and_parks_on_duplicate_or_six_no_work_replies() {
        let mut cad = AutopilotCadence::new(AutopilotMode::Cruise);

        let expected = [
            CruiseRung::WidestCheck,
            CruiseRung::HostileDiffReview,
            CruiseRung::OutOfScopeAudit,
            CruiseRung::MeasureAgainstMain,
            CruiseRung::NextOpenIssue,
            CruiseRung::LandCleanly,
            CruiseRung::WidestCheck,
        ];
        for (i, &exp) in expected.iter().enumerate() {
            let reply = format!("Batch {i} completed and pushed.");
            let dec = cad.on_turn_end(TurnEndFacts {
                reply_text: &reply,
                human_unsent_input: false,
                background_work_running: false,
                did_real_work: true,
                git_all_on_remote_main: true,
                standalone_human_qa_within_10m: false,
            });
            assert_eq!(dec, CadenceDecision::PromptCruiseRung(exp));
        }

        // Unsent human input always suppresses typing.
        assert_eq!(
            cad.on_turn_end(TurnEndFacts {
                reply_text: "done",
                human_unsent_input: true,
                background_work_running: true,
                did_real_work: true,
                git_all_on_remote_main: false,
                standalone_human_qa_within_10m: false,
            }),
            CadenceDecision::HoldSilent
        );

        // Same no-work reply twice stops Cruise immediately!
        let d1 = cad.on_turn_end(TurnEndFacts {
            reply_text: "No changes found.",
            human_unsent_input: false,
            background_work_running: false,
            did_real_work: false,
            git_all_on_remote_main: true,
            standalone_human_qa_within_10m: false,
        });
        assert_eq!(d1, CadenceDecision::PromptKeepGoing);
        let d2 = cad.on_turn_end(TurnEndFacts {
            reply_text: "No changes found.",
            human_unsent_input: false,
            background_work_running: false,
            did_real_work: false,
            git_all_on_remote_main: true,
            standalone_human_qa_within_10m: false,
        });
        assert_eq!(d2, CadenceDecision::HoldSilent);
    }
}
