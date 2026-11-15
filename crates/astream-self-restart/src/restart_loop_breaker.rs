// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Sliding-window `@self restart` storm breaker refusing automated restart loops if an updated
//! agent binary crashes or restarts repeatedly within `5` minutes (`Astream.SelfRst.TlaRestartLoopBreaker`).

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "restart_loop_breaker_island.rs"]
mod restart_loop_breaker_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sr_cnt_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sr_win_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use restart_loop_breaker_island::{sr_cnt_clamp, sr_win_advance};

/// Maximum `@self restart` calls permitted per 5-minute window (`3`).
pub const MAX_RESTARTS_PER_WINDOW: u64 = 3;

contract_fn! {
    /// Verified burst headroom (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sr_within_burst_cap_isl`.
    #[must_use]
    pub const fn sr_within_burst_cap(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct RestartLoopBreaker {
    window_start_ms: u64,
    window_ms: u64,
    restarts_in_window: u64,
}

impl RestartLoopBreaker {
    #[must_use]
    pub const fn new(window_ms: u64) -> Self {
        Self {
            window_start_ms: 0,
            window_ms: if window_ms == 0 { 300_000 } else { window_ms },
            restarts_in_window: 0,
        }
    }

    pub fn try_admit_restart(&mut self, now_ms: u64) -> bool {
        if self.restarts_in_window == 0
            || now_ms.saturating_sub(self.window_start_ms) >= self.window_ms
        {
            self.window_start_ms = sr_win_advance(self.window_start_ms, now_ms);
            self.restarts_in_window = 0;
        }
        let next = sr_cnt_clamp(self.restarts_in_window.saturating_add(1), 64);
        if sr_within_burst_cap(MAX_RESTARTS_PER_WINDOW, next) {
            self.restarts_in_window = next;
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_fourth_restart_in_same_window_and_resets_after_cooldown() {
        let mut b = RestartLoopBreaker::new(300_000);
        assert!(b.try_admit_restart(1_000));
        assert!(b.try_admit_restart(2_000));
        assert!(b.try_admit_restart(3_000));
        assert!(!b.try_admit_restart(4_000));
        assert!(b.try_admit_restart(305_000));
    }
}
