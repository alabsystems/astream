// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm ctl @self await sys` quiet-machine hysteresis gate requiring `K` consecutive quiet
//! windows before launching timing-sensitive benchmarks (`Astream.SysTel.TlaQuietMachineAwait`).

#[cfg(clean_islands)]
#[path = "quiet_machine_await_island.rs"]
mod quiet_machine_await_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sys_streak_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sys_window_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use quiet_machine_await_island::{sys_streak_clamp, sys_window_advance};

/// Maximum hysteresis streak length.
pub const MAX_QUIET_STREAK: u64 = 64;

contract_fn! {
    /// Verified quiet-streak readiness (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sys_quiet_met_isl`.
    #[must_use]
    pub const fn sys_quiet_met(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Evaluates `await sys` readiness across consecutive CPU + disk-free observations.
#[derive(Debug, Clone)]
pub struct QuietMachineWaiter {
    max_busy_mc: u64,
    min_free_disk_mb: u64,
    required_streak: u64,
    current_streak: u64,
    windows_polled: u64,
}

impl QuietMachineWaiter {
    #[must_use]
    pub const fn new(max_busy_mc: u64, min_free_disk_mb: u64, required_streak: u64) -> Self {
        let req = if required_streak == 0 {
            1
        } else {
            required_streak
        };
        Self {
            max_busy_mc,
            min_free_disk_mb,
            required_streak: sys_streak_clamp(req, MAX_QUIET_STREAK),
            current_streak: 0,
            windows_polled: 0,
        }
    }

    pub fn observe_window(&mut self, busy_mc: u64, free_disk_mb: u64) -> bool {
        self.windows_polled =
            sys_window_advance(self.windows_polled, self.windows_polled.saturating_add(1));
        if busy_mc <= self.max_busy_mc && free_disk_mb >= self.min_free_disk_mb {
            self.current_streak =
                sys_streak_clamp(self.current_streak.saturating_add(1), self.required_streak);
        } else {
            self.current_streak = 0;
        }
        sys_quiet_met(self.current_streak, self.required_streak)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn quiet_waiter_requires_consecutive_calm_windows_and_resets_on_load_spike() {
        let mut w = QuietMachineWaiter::new(2_000, 10_240, 2);
        assert!(!w.observe_window(1_200, 20_000));
        assert!(!w.observe_window(9_000, 20_000));
        assert!(!w.observe_window(1_100, 20_000));
        assert!(w.observe_window(900, 20_000));
    }
}
