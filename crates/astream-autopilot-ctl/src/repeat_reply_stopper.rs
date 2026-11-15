// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `autopilot=cruise` no-work loop breaker stopping automated typing only when replies repeat with
//! no work (the exact same reply twice, or `6` no-work replies in a row), resetting on real work
//! or someone else's turn (`Astream.Autopilot.TlaRepeatReplyStopper`).

use astream_digest::{ct_eq, Sha256};

#[cfg(clean_islands)]
#[path = "repeat_reply_stopper_island.rs"]
mod repeat_reply_stopper_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn w16_ap_streak_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn w16_ap_turn_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use repeat_reply_stopper_island::{w16_ap_streak_clamp, w16_ap_turn_advance};

/// Consecutive no-work reply ceiling (`6` in a row stops Autopilot typing).
pub const MAX_NO_WORK_STREAK: u64 = 6;

contract_fn! {
    /// Verified stop threshold (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ap_should_stop_isl`.
    #[must_use]
    pub const fn ap_should_stop(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Evaluates whether `autopilot=cruise` should pause typing due to repeated no-work replies.
#[derive(Debug, Clone, Default)]
pub struct CruiseLoopBreaker {
    last_no_work_digest: Option<[u8; 32]>,
    no_work_streak: u64,
    turns_seen: u64,
    stopped: bool,
}

impl CruiseLoopBreaker {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            last_no_work_digest: None,
            no_work_streak: 0,
            turns_seen: 0,
            stopped: false,
        }
    }

    /// Returns `true` iff Autopilot should STOP typing until real work or another turn arrives.
    pub fn on_turn_end(&mut self, reply_text: &str, did_real_work: bool) -> bool {
        self.turns_seen = w16_ap_turn_advance(self.turns_seen, self.turns_seen.saturating_add(1));
        if did_real_work {
            self.last_no_work_digest = None;
            self.no_work_streak = 0;
            self.stopped = false;
            return false;
        }
        if self.stopped {
            return true;
        }
        let digest = Sha256::digest_slice(reply_text.trim().as_bytes());
        let same_twice = match &self.last_no_work_digest {
            Some(prev) => ct_eq(prev, &digest),
            None => false,
        };
        self.last_no_work_digest = Some(digest);
        self.no_work_streak =
            w16_ap_streak_clamp(self.no_work_streak.saturating_add(1), MAX_NO_WORK_STREAK);
        let should_stop = same_twice || ap_should_stop(self.no_work_streak, MAX_NO_WORK_STREAK);
        if should_stop {
            self.stopped = true;
        }
        should_stop
    }

    pub fn on_external_turn(&mut self) {
        self.last_no_work_digest = None;
        self.no_work_streak = 0;
        self.stopped = false;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn loop_breaker_stops_on_duplicate_no_work_or_six_distinct_no_work_replies() {
        let mut b = CruiseLoopBreaker::new();
        assert!(!b.on_turn_end("Nothing to change.", false));
        assert!(b.on_turn_end("Nothing to change.", false));

        b.on_external_turn();
        for i in 1..6 {
            assert!(!b.on_turn_end(&format!("Distinct idle reply {i}"), false));
        }
        assert!(b.on_turn_end("Distinct idle reply 6", false));
    }
}
