// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `Autopilot Cruise` no-work repeat circuit breaker (`Astream.Agent.TlaCruiseRepeatStopper`).
//!
//! Enforces `aterm`'s `autopilot=cruise` stopping law:
//! *"Only replies that repeat with no work (the same one twice, or six in a row)
//! stop its typing, until real work or someone else's turn."*

#[cfg(clean_islands)]
#[path = "cruise_repeat_stopper_island.rs"]
mod cruise_repeat_stopper_island;
#[cfg(clean_islands)]
pub use cruise_repeat_stopper_island::{cruise_empty_streak_clamp_b95, cruise_turn_advance_b95};

/// Exact streak of consecutive zero-work replies that halts Cruise typing (`6`).
pub const CRUISE_MAX_NO_WORK_STREAK: u64 = 6;

const FNV_OFFSET_BASIS: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

#[cfg(not(clean_islands))]
/// Monotonically advance the Cruise turn evaluation counter.
#[must_use]
pub const fn cruise_turn_advance_b95(cur_turn: u64, cand_turn: u64) -> u64 {
    if cur_turn < cand_turn {
        cand_turn
    } else {
        cur_turn
    }
}

#[cfg(not(clean_islands))]
/// Clamp consecutive no-work reply streak to `max_streak`.
#[must_use]
pub const fn cruise_empty_streak_clamp_b95(cand_streak: u64, max_streak: u64) -> u64 {
    if cand_streak < max_streak {
        cand_streak
    } else {
        max_streak
    }
}

contract_fn! {
    /// True iff `cur_streak >= max_streak` (`6` no-work replies in a row).
    #[must_use]
    pub const fn cruise_streak_exhausted_b95(max_streak: u64, cur_streak: u64) -> bool
    clauses [ensures result == (max_streak <= cur_streak)]
    {
        max_streak <= cur_streak
    }
}

fn normalized_reply_digest(reply: &[u8]) -> u64 {
    let mut h = FNV_OFFSET_BASIS;
    let mut rest = reply;
    while let &[b, ref tail @ ..] = rest {
        if b != b' ' && b != b'\t' && b != b'\r' && b != b'\n' {
            h = (h ^ (b as u64)).wrapping_mul(FNV_PRIME);
        }
        rest = tail;
    }
    h
}

/// Decision for the Cruise harness at turn end.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CruiseDecision {
    ContinueTyping { turn_epoch: u64, empty_streak: u64 },
    StopSameNoWorkTwice { turn_epoch: u64 },
    StopSixNoWorkInARow { turn_epoch: u64 },
}

/// Stateful `autopilot=cruise` no-work repeat circuit breaker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CruiseRepeatStopper {
    turn_epoch: u64,
    empty_streak: u64,
    prev_empty_digest: Option<u64>,
    halted: bool,
}

impl Default for CruiseRepeatStopper {
    fn default() -> Self {
        Self::new()
    }
}

impl CruiseRepeatStopper {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            turn_epoch: 0,
            empty_streak: 0,
            prev_empty_digest: None,
            halted: false,
        }
    }

    #[must_use]
    pub const fn turn_epoch(&self) -> u64 {
        self.turn_epoch
    }

    #[must_use]
    pub const fn empty_streak(&self) -> u64 {
        self.empty_streak
    }

    #[must_use]
    pub const fn is_halted(&self) -> bool {
        self.halted
    }

    /// Resume Cruise typing when someone else takes a turn or real work lands.
    pub fn on_external_turn_or_work(&mut self) {
        self.empty_streak = 0;
        self.prev_empty_digest = None;
        self.halted = false;
    }

    /// Evaluate an agent reply (`did_real_work = true` if tools mutated state / commits / tests).
    pub fn on_turn_reply(&mut self, reply: &[u8], did_real_work: bool) -> CruiseDecision {
        let cand_t = self.turn_epoch.saturating_add(1);
        self.turn_epoch = cruise_turn_advance_b95(self.turn_epoch, cand_t);

        if did_real_work {
            self.on_external_turn_or_work();
            return CruiseDecision::ContinueTyping {
                turn_epoch: self.turn_epoch,
                empty_streak: 0,
            };
        }

        let digest = normalized_reply_digest(reply);
        let cand_s = self.empty_streak.saturating_add(1);
        self.empty_streak = cruise_empty_streak_clamp_b95(cand_s, CRUISE_MAX_NO_WORK_STREAK);

        if self.prev_empty_digest == Some(digest) {
            self.halted = true;
            return CruiseDecision::StopSameNoWorkTwice {
                turn_epoch: self.turn_epoch,
            };
        }
        self.prev_empty_digest = Some(digest);

        if cruise_streak_exhausted_b95(CRUISE_MAX_NO_WORK_STREAK, self.empty_streak) {
            self.halted = true;
            return CruiseDecision::StopSixNoWorkInARow {
                turn_epoch: self.turn_epoch,
            };
        }

        CruiseDecision::ContinueTyping {
            turn_epoch: self.turn_epoch,
            empty_streak: self.empty_streak,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stops_on_same_no_work_twice_or_six_distinct_in_a_row_and_resets_on_work() {
        let mut st = CruiseRepeatStopper::new();

        // Identical no-work reply twice stops immediately on turn 2!
        assert_eq!(
            st.on_turn_reply(b"Nothing new.", false),
            CruiseDecision::ContinueTyping {
                turn_epoch: 1,
                empty_streak: 1,
            }
        );
        assert_eq!(
            st.on_turn_reply(b"  Nothing new.\n", false),
            CruiseDecision::StopSameNoWorkTwice { turn_epoch: 2 }
        );
        assert!(st.is_halted());

        // Real work resets streak and unhalts!
        assert_eq!(
            st.on_turn_reply(b"Landed commit abc.", true),
            CruiseDecision::ContinueTyping {
                turn_epoch: 3,
                empty_streak: 0,
            }
        );
        assert!(!st.is_halted());

        // Six distinct zero-work replies stop on the 6th
        let msgs: [&[u8]; 6] = [b"m1", b"m2", b"m3", b"m4", b"m5", b"m6"];
        for (idx, m) in msgs.iter().enumerate() {
            let d = st.on_turn_reply(m, false);
            if idx < 5 {
                assert!(matches!(d, CruiseDecision::ContinueTyping { .. }));
            } else {
                assert_eq!(d, CruiseDecision::StopSixNoWorkInARow { turn_epoch: 9 });
            }
        }
    }
}
