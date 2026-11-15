// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Six-rung `autopilot=cruise` continuation wheel & anti-spin latch
//! (`Astream.Agent.TlaCruiseWorkWheel`).
//!
//! Implements the `aterm` Cruise continuation discipline:
//! - Rotates done-reports deterministically through the 6-kind inspection wheel (`WidestCheck`,
//!   `HostileReview`, `OutOfScopeAudit`, `MeasureAgainstMain`, `NextOpenIssue`,
//!   `LandOwnedWork`);
//! - Stops typing only when a no-work reply repeats identically twice in a row OR six consecutive
//!   turns report no work (`6 <= no_work_streak`), re-arming immediately upon real work or an
//!   external operator turn.

#[cfg(clean_islands)]
#[path = "cruise_work_wheel_island.rs"]
mod cruise_work_wheel_island;
#[cfg(clean_islands)]
pub use cruise_work_wheel_island::{cruise_no_work_clamp, cruise_turn_advance_b84};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cruise_no_work_clamp(cand_streak: u64, max_streak: u64) -> u64 {
    if cand_streak < max_streak {
        cand_streak
    } else {
        max_streak
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cruise_turn_advance_b84(cur_turn: u64, cand_turn: u64) -> u64 {
    if cur_turn < cand_turn {
        cand_turn
    } else {
        cur_turn
    }
}

contract_fn! {
    /// Verified check whether the six-in-a-row empty-turn limit has been reached
    /// (`6 <= no_work_streak`), linked via `clean-kernel-defeq` to
    /// `cruise_streak_exhausted_isl`.
    #[must_use]
    pub const fn cruise_streak_exhausted(no_work_streak: u64) -> bool
    clauses [ensures result == (6 <= no_work_streak)]
    {
        6 <= no_work_streak
    }
}

/// Maximum consecutive no-work turns before Cruise stops typing (`6`).
pub const MAX_CRUISE_NO_WORK_STREAK: u64 = 6;

/// Six-rung Cruise follow-up prompt kind (`aterm` primer).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CruiseRung {
    WidestCheck,
    HostileReview,
    OutOfScopeAudit,
    MeasureAgainstMain,
    NextOpenIssue,
    LandOwnedWork,
}

impl CruiseRung {
    #[must_use]
    pub const fn next(self) -> Self {
        match self {
            Self::WidestCheck => Self::HostileReview,
            Self::HostileReview => Self::OutOfScopeAudit,
            Self::OutOfScopeAudit => Self::MeasureAgainstMain,
            Self::MeasureAgainstMain => Self::NextOpenIssue,
            Self::NextOpenIssue => Self::LandOwnedWork,
            Self::LandOwnedWork => Self::WidestCheck,
        }
    }
}

/// Decision returned at turn end under `autopilot=cruise`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CruiseDecision {
    /// Emit the next rung prompt and advance the wheel.
    ContinueWith(CruiseRung),
    /// Identical no-work reply repeated twice or 6 no-work replies in a row; pause typing.
    StopTypingAntiSpin,
}

/// Stateful Cruise continuation wheel and anti-spin tracker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CruiseWorkWheel {
    turn_seq: u64,
    no_work_streak: u64,
    last_no_work_digest: Option<u64>,
    next_rung: CruiseRung,
}

impl Default for CruiseWorkWheel {
    fn default() -> Self {
        Self::new()
    }
}

impl CruiseWorkWheel {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            turn_seq: 0,
            no_work_streak: 0,
            last_no_work_digest: None,
            next_rung: CruiseRung::WidestCheck,
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

    /// Record an external operator/peer turn, resetting any anti-spin latch.
    pub fn on_external_turn(&mut self) {
        self.no_work_streak = 0;
        self.last_no_work_digest = None;
    }

    /// Evaluate the end of an agent turn given `(did_work, reply_digest)`.
    pub fn on_turn_end(&mut self, did_work: bool, reply_digest: u64) -> CruiseDecision {
        let next_turn = self.turn_seq.saturating_add(1);
        self.turn_seq = cruise_turn_advance_b84(self.turn_seq, next_turn);

        if did_work {
            self.no_work_streak = 0;
            self.last_no_work_digest = None;
            let chosen = self.next_rung;
            self.next_rung = self.next_rung.next();
            return CruiseDecision::ContinueWith(chosen);
        }

        let repeated_twice = self.last_no_work_digest == Some(reply_digest);
        self.last_no_work_digest = Some(reply_digest);
        let cand_streak = self.no_work_streak.saturating_add(1);
        self.no_work_streak = cruise_no_work_clamp(cand_streak, MAX_CRUISE_NO_WORK_STREAK);

        if repeated_twice || cruise_streak_exhausted(self.no_work_streak) {
            CruiseDecision::StopTypingAntiSpin
        } else {
            let chosen = self.next_rung;
            self.next_rung = self.next_rung.next();
            CruiseDecision::ContinueWith(chosen)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rotates_six_rungs_and_stops_on_duplicate_or_six_empty_turns() {
        let mut w = CruiseWorkWheel::new();
        assert_eq!(
            w.on_turn_end(true, 100),
            CruiseDecision::ContinueWith(CruiseRung::WidestCheck)
        );
        assert_eq!(
            w.on_turn_end(false, 201),
            CruiseDecision::ContinueWith(CruiseRung::HostileReview)
        );
        // Same no-work reply twice in a row stops immediately!
        assert_eq!(
            w.on_turn_end(false, 201),
            CruiseDecision::StopTypingAntiSpin
        );

        // External turn resets latch; 6 distinct no-work replies stop on the 6th.
        w.on_external_turn();
        for d in 1..6 {
            assert!(matches!(
                w.on_turn_end(false, d),
                CruiseDecision::ContinueWith(_)
            ));
        }
        assert_eq!(w.on_turn_end(false, 6), CruiseDecision::StopTypingAntiSpin);
        assert_eq!(w.no_work_streak(), 6);
    }
}
