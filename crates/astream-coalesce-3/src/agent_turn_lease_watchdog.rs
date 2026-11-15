// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm` Autopilot (`off` / `land` / `cruise`) Turn-Ownership & Human-Reply Watchdog.
//!
//! Models the exact `aterm` Autopilot turn-end arbitration rules:
//! - Never type while a person is actively typing or has unsent input in the prompt buffer.
//! - Under `off`, never type automatically.
//! - Under `land`:
//!   - A reply to a person's own message outside an active harness job, answered within the
//!     10-minute (`600_000 ms`) human window, belongs to the person: type nothing after it.
//!   - A clean `Nothing left:` defense with clean `git` state parks the session cleanly.
//!   - Otherwise continue landing work onto `origin/main`.
//! - Under `cruise`:
//!   - Continue every turn end (including background-work wakeup and rotating audit prompts),
//!     stopping only if identical no-work replies repeat twice (`>= 2`) or six no-work replies
//!     occur in a row (`>= 6`).
//!
//! Backed by Clean TLA+ Island `Astream.Agent.TlaTurnLeaseWatchdog`
//! (`agent_turn_lease_watchdog_island.rs`), proving `elapsedMs <= windowCapMs` and
//! `typedPrompts <= turnCount`.

#[cfg(clean_islands)]
#[path = "agent_turn_lease_watchdog_island.rs"]
mod island;
#[cfg(clean_islands)]
pub use island::{watchdog_elapsed_clamp, watchdog_typed_clamp};

#[cfg(not(clean_islands))]
#[inline]
pub const fn watchdog_elapsed_clamp(elapsed_ms: u64, window_cap_ms: u64) -> u64 {
    if elapsed_ms < window_cap_ms {
        elapsed_ms
    } else {
        window_cap_ms
    }
}

#[cfg(not(clean_islands))]
#[inline]
pub const fn watchdog_typed_clamp(typed_prompts: u64, turn_count: u64) -> u64 {
    if typed_prompts < turn_count {
        typed_prompts
    } else {
        turn_count
    }
}

contract_fn! {
    /// Kernel-certified check whether `elapsed_ms` falls within `window_ms` (e.g. 10-minute
    /// `land` human-reply ownership window).
    #[must_use]
    #[inline]
    pub const fn watchdog_within_person_window(elapsed_ms: u64, window_ms: u64) -> bool
    clauses [ensures result == (elapsed_ms <= window_ms)]
    {
        elapsed_ms <= window_ms
    }
}

/// Default `aterm` `land` human-message reply ownership window: 10 minutes (`600_000 ms`).
pub const PERSON_REPLY_WINDOW_MS: u64 = 600_000;

/// Maximum elapsed window tracked before clamping (`24` hours in ms).
pub const DEFAULT_WINDOW_CAP_MS: u64 = 86_400_000;

/// `aterm` Autopilot operating mode (`autopilot=` in `aterm ctl @self status`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AutopilotLane {
    Off,
    Land,
    Cruise,
}

/// Six-way `cruise` audit rotation cycle after a turn claims work is done.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum CruisePromptKind {
    WidestCheck = 0,
    HostileDiffReview = 1,
    OutOfScopeSweep = 2,
    MeasureAgainstMain = 3,
    NextOpenIssue = 4,
    LandSessionWork = 5,
}

impl CruisePromptKind {
    #[inline]
    pub const fn from_index(idx: u64) -> Self {
        match idx % 6 {
            0 => Self::WidestCheck,
            1 => Self::HostileDiffReview,
            2 => Self::OutOfScopeSweep,
            3 => Self::MeasureAgainstMain,
            4 => Self::NextOpenIssue,
            _ => Self::LandSessionWork,
        }
    }
}

/// Snapshot of session state at the end of an agent turn.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TurnEndObservation {
    /// True if the operator is actively typing or has unsent input in the terminal buffer.
    pub person_has_unsent_input: bool,
    /// True if this turn directly answered the person's own message outside a harness job.
    pub replied_to_person_outside_job: bool,
    /// Elapsed milliseconds since the person sent that message.
    pub elapsed_since_person_msg_ms: u64,
    /// True if background tasks owned by this session are still running.
    pub background_work_running: bool,
    /// True under `land` when the reply starts `Nothing left:` and `git` working state is clean.
    pub nothing_left_verified: bool,
    /// True if the turn produced zero repository/task progress (`no-work` reply).
    pub no_work_reply: bool,
    /// Hash of the normalized reply body used to detect consecutive identical `no-work` replies.
    pub reply_fingerprint: u64,
}

/// Decision returned by `TurnLeaseWatchdog::evaluate_turn_end`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WatchdogDecision {
    /// Hold typing because the person is typing or has unsent input.
    HoldForUnsentPersonInput,
    /// Autopilot is `off`.
    ParkedOff,
    /// Under `land`, reply answered the person's own prompt within 10 minutes: leave it theirs.
    YieldToPersonReply,
    /// Under `land`, all work is on `origin/main` and `Nothing left:` verified.
    ParkedLandComplete,
    /// Under `cruise`, repeated no-work replies (`2` identical or `6` consecutive) tripped stop.
    ParkedCruiseNoWorkStop,
    /// Prompt the agent to check running background work and keep going without waiting idle.
    ContinueCheckBackgroundWork,
    /// Under `land`, continue driving uncommitted/unpushed/unmerged work to `origin/main`.
    ContinueLandToMain,
    /// Under `cruise`, type the next rotating review/expansion prompt.
    ContinueCruise(CruisePromptKind),
}

/// Stateful `aterm` Autopilot turn-lease watchdog certified by `TlaTurnLeaseWatchdog`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TurnLeaseWatchdog {
    lane: AutopilotLane,
    window_cap_ms: u64,
    elapsed_ms: u64,
    turn_count: u64,
    typed_prompts: u64,
    cruise_rotation_idx: u64,
    consecutive_no_work: u8,
    last_no_work_fingerprint: Option<u64>,
}

impl TurnLeaseWatchdog {
    #[inline]
    pub const fn new(lane: AutopilotLane, window_cap_ms: u64) -> Self {
        let cap = if window_cap_ms == 0 {
            DEFAULT_WINDOW_CAP_MS
        } else {
            window_cap_ms
        };
        Self {
            lane,
            window_cap_ms: cap,
            elapsed_ms: 0,
            turn_count: 0,
            typed_prompts: 0,
            cruise_rotation_idx: 0,
            consecutive_no_work: 0,
            last_no_work_fingerprint: None,
        }
    }

    #[inline]
    pub const fn lane(&self) -> AutopilotLane {
        self.lane
    }

    #[inline]
    pub fn set_lane(&mut self, lane: AutopilotLane) {
        self.lane = lane;
    }

    #[inline]
    pub const fn elapsed_ms(&self) -> u64 {
        self.elapsed_ms
    }

    #[inline]
    pub const fn window_cap_ms(&self) -> u64 {
        self.window_cap_ms
    }

    #[inline]
    pub const fn turn_count(&self) -> u64 {
        self.turn_count
    }

    #[inline]
    pub const fn typed_prompts(&self) -> u64 {
        self.typed_prompts
    }

    /// Resets the `cruise` no-work repetition breaker when real work or a human turn occurs.
    pub fn note_real_activity(&mut self) {
        self.consecutive_no_work = 0;
        self.last_no_work_fingerprint = None;
    }

    /// Evaluates `EvaluateTurnEnd` (`Astream.Agent.TlaTurnLeaseWatchdog`), updating certified
    /// counters (`elapsed_ms <= window_cap_ms`, `typed_prompts <= turn_count`) and returning
    /// the exact harness continuation or park decision.
    pub fn evaluate_turn_end(&mut self, obs: TurnEndObservation) -> WatchdogDecision {
        let next_turns = self.turn_count.saturating_add(1);
        self.elapsed_ms =
            watchdog_elapsed_clamp(obs.elapsed_since_person_msg_ms, self.window_cap_ms);

        if obs.person_has_unsent_input {
            self.turn_count = next_turns;
            self.typed_prompts = watchdog_typed_clamp(self.typed_prompts, next_turns);
            return WatchdogDecision::HoldForUnsentPersonInput;
        }

        let decision = match self.lane {
            AutopilotLane::Off => WatchdogDecision::ParkedOff,
            AutopilotLane::Land => {
                if obs.replied_to_person_outside_job
                    && watchdog_within_person_window(
                        obs.elapsed_since_person_msg_ms,
                        PERSON_REPLY_WINDOW_MS,
                    )
                {
                    WatchdogDecision::YieldToPersonReply
                } else if obs.background_work_running {
                    WatchdogDecision::ContinueCheckBackgroundWork
                } else if obs.nothing_left_verified {
                    WatchdogDecision::ParkedLandComplete
                } else {
                    WatchdogDecision::ContinueLandToMain
                }
            }
            AutopilotLane::Cruise => {
                if obs.background_work_running {
                    self.note_real_activity();
                    WatchdogDecision::ContinueCheckBackgroundWork
                } else if obs.no_work_reply {
                    let same_twice = match self.last_no_work_fingerprint {
                        Some(prev_fp) => prev_fp == obs.reply_fingerprint,
                        None => false,
                    };
                    self.consecutive_no_work = self.consecutive_no_work.saturating_add(1);
                    self.last_no_work_fingerprint = Some(obs.reply_fingerprint);
                    if same_twice || self.consecutive_no_work >= 6 {
                        WatchdogDecision::ParkedCruiseNoWorkStop
                    } else {
                        let kind = CruisePromptKind::from_index(self.cruise_rotation_idx);
                        self.cruise_rotation_idx = self.cruise_rotation_idx.saturating_add(1);
                        WatchdogDecision::ContinueCruise(kind)
                    }
                } else {
                    self.note_real_activity();
                    let kind = CruisePromptKind::from_index(self.cruise_rotation_idx);
                    self.cruise_rotation_idx = self.cruise_rotation_idx.saturating_add(1);
                    WatchdogDecision::ContinueCruise(kind)
                }
            }
        };

        let should_type = matches!(
            decision,
            WatchdogDecision::ContinueCheckBackgroundWork
                | WatchdogDecision::ContinueLandToMain
                | WatchdogDecision::ContinueCruise(_)
        );
        let raw_typed = if should_type {
            self.typed_prompts.saturating_add(1)
        } else {
            self.typed_prompts
        };
        self.turn_count = next_turns;
        self.typed_prompts = watchdog_typed_clamp(raw_typed, next_turns);
        decision
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn base_obs() -> TurnEndObservation {
        TurnEndObservation {
            person_has_unsent_input: false,
            replied_to_person_outside_job: false,
            elapsed_since_person_msg_ms: 15_000,
            background_work_running: false,
            nothing_left_verified: false,
            no_work_reply: false,
            reply_fingerprint: 1,
        }
    }

    #[test]
    fn land_respects_ten_minute_person_window_and_nothing_left() {
        let mut wd = TurnLeaseWatchdog::new(AutopilotLane::Land, DEFAULT_WINDOW_CAP_MS);

        // Person's own question answered in 45s -> theirs, nothing typed.
        let mut obs = base_obs();
        obs.replied_to_person_outside_job = true;
        obs.elapsed_since_person_msg_ms = 45_000;
        assert_eq!(
            wd.evaluate_turn_end(obs),
            WatchdogDecision::YieldToPersonReply
        );
        assert_eq!(wd.typed_prompts(), 0);
        assert_eq!(wd.turn_count(), 1);

        // Over 10 minutes (600_001ms) -> continues landing.
        obs.elapsed_since_person_msg_ms = 600_001;
        assert_eq!(
            wd.evaluate_turn_end(obs),
            WatchdogDecision::ContinueLandToMain
        );
        assert_eq!(wd.typed_prompts(), 1);

        // Verified `Nothing left:` -> parks cleanly.
        let mut done = base_obs();
        done.nothing_left_verified = true;
        assert_eq!(
            wd.evaluate_turn_end(done),
            WatchdogDecision::ParkedLandComplete
        );
        assert_eq!(wd.typed_prompts(), 1);
        assert_eq!(wd.turn_count(), 3);
    }

    #[test]
    fn cruise_rotates_six_prompts_and_stops_on_duplicate_or_six_no_work() {
        let mut wd = TurnLeaseWatchdog::new(AutopilotLane::Cruise, 100_000);

        // Unsent person input always blocks typing even in Cruise.
        let mut unsent = base_obs();
        unsent.person_has_unsent_input = true;
        assert_eq!(
            wd.evaluate_turn_end(unsent),
            WatchdogDecision::HoldForUnsentPersonInput
        );
        assert_eq!(wd.typed_prompts(), 0);

        // Background work running -> ContinueCheckBackgroundWork.
        let mut bg = base_obs();
        bg.background_work_running = true;
        bg.elapsed_since_person_msg_ms = 999_999;
        assert_eq!(
            wd.evaluate_turn_end(bg),
            WatchdogDecision::ContinueCheckBackgroundWork
        );
        assert_eq!(wd.elapsed_ms(), 100_000);

        // Same no-work reply twice in a row stops Cruise typing.
        let mut nw = base_obs();
        nw.no_work_reply = true;
        nw.reply_fingerprint = 0xDEAD_BEEF;
        assert_eq!(
            wd.evaluate_turn_end(nw),
            WatchdogDecision::ContinueCruise(CruisePromptKind::WidestCheck)
        );
        assert_eq!(
            wd.evaluate_turn_end(nw),
            WatchdogDecision::ParkedCruiseNoWorkStop
        );
        assert!(wd.typed_prompts() <= wd.turn_count());
    }
}
