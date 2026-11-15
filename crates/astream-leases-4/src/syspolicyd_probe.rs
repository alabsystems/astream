// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! macOS `syspolicyd=stuck` kernel-upcall deadlock detector
//! (`Astream.Host.TlaSyspolicydProbe`; `aterm ctl @self status` `syspolicyd=stuck`).
//!
//! On macOS, when `syspolicyd` / `amfid` deadlocks on its exec assessment gate, every new
//! non-Apple binary hangs inside `posix_spawn` / `execve` before entering `main`, while
//! Apple platform binaries (`/usr/bin/true`) continue to start immediately. Retrying
//! `targo` or `git` under a `syspolicyd=stuck` deadlock only piles up unkillable tasks
//! until the Mac restarts (`NEEDS YOU: restart the Mac`).
//!
//! [`SyspolicydDetector`] contrasts non-Apple spawn timeouts against Apple platform-binary
//! probe health so ordinary system-wide CPU/IO overload (where Apple binaries are *also*
//! slow) is classified as [`SyspolicydHealth::SystemBusy`] rather than falsely latching
//! [`SyspolicydHealth::Stuck`]. Once `hang_streak >= stuck_threshold` while Apple probes
//! succeed, `stuck` latches monotonically via Clean-origin [`syspolicy_probe_stuck_latch`].

#[cfg(clean_islands)]
#[path = "syspolicyd_probe_island.rs"]
mod syspolicyd_probe_island;
#[cfg(clean_islands)]
pub use syspolicyd_probe_island::{syspolicy_probe_hang_clamp, syspolicy_probe_stuck_latch};

/// Mirror of Clean's `syspolicy_probe_hang_clamp` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn syspolicy_probe_hang_clamp(streak: u64, cap: u64) -> u64 {
    if streak < cap {
        streak
    } else {
        cap
    }
}

/// Mirror of Clean's `syspolicy_probe_stuck_latch` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn syspolicy_probe_stuck_latch(cur_stuck: u64, cand_stuck: u64) -> u64 {
    if cur_stuck < cand_stuck {
        cand_stuck
    } else {
        cur_stuck
    }
}

contract_fn! {
    /// Kernel-certified check that the monotone `stuck` latch is set (`stuck_flag == 1`),
    /// linked via `clean-kernel-defeq` to `syspolicy_probe_is_stuck_isl`.
    #[must_use]
    pub const fn syspolicy_probe_is_stuck(stuck_flag: u64) -> bool
    clauses [ensures result == (stuck_flag == 1)]
    {
        stuck_flag == 1
    }
}

/// Maximum consecutive non-Apple spawn-hang count tracked (`64`).
pub const MAX_HANG_STREAK_CAP: u64 = 64;

/// Default consecutive non-Apple pre-main spawn hangs (with healthy Apple control probe)
/// required to latch `syspolicyd=stuck` (`2`).
pub const DEFAULT_STUCK_THRESHOLD: u64 = 2;

/// Canonical `NEEDS YOU:` line required by the `aterm` primer when `syspolicyd=stuck`.
pub const NEEDS_YOU_RESTART_MAC: &str = "NEEDS YOU: restart the Mac";

/// Diagnosed state of macOS's `syspolicyd` exec gate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyspolicydHealth {
    /// Non-Apple programs are starting normally (`syspolicyd=ok`).
    Healthy,
    /// Non-Apple spawn timed out, and the Apple control binary also timed out — machine is
    /// overloaded/throttled rather than `syspolicyd`-deadlocked.
    SystemBusy { hang_streak: u64 },
    /// One non-Apple hang observed while Apple control probe succeeded; watching for confirmation.
    Suspect { hang_streak: u64 },
    /// Confirmed `syspolicyd=stuck` deadlock (latched until reboot): stop retrying spawns
    /// and surface [`NEEDS_YOU_RESTART_MAC`].
    Stuck,
}

impl SyspolicydHealth {
    /// Status token reported in `aterm ctl @self status` (`ok`, `busy`, `suspect`, `stuck`).
    #[must_use]
    pub const fn status_token(self) -> &'static str {
        match self {
            Self::Healthy => "ok",
            Self::SystemBusy { .. } => "busy",
            Self::Suspect { .. } => "suspect",
            Self::Stuck => "stuck",
        }
    }

    /// Required `NEEDS YOU:` banner line when `self == Self::Stuck`, or `None` otherwise.
    #[must_use]
    pub const fn needs_you_banner(self) -> Option<&'static str> {
        if matches!(self, Self::Stuck) {
            Some(NEEDS_YOU_RESTART_MAC)
        } else {
            None
        }
    }
}

/// Stateful detector contrasting non-Apple spawn outcomes with Apple platform-binary probes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SyspolicydDetector {
    hang_streak: u64,
    stuck_threshold: u64,
    stuck_flag: u64,
}

impl Default for SyspolicydDetector {
    fn default() -> Self {
        Self::new(DEFAULT_STUCK_THRESHOLD)
    }
}

impl SyspolicydDetector {
    /// Create a detector with `stuck_threshold` clamped into `1..=MAX_HANG_STREAK_CAP`.
    #[must_use]
    pub const fn new(stuck_threshold: u64) -> Self {
        let clamped = syspolicy_probe_hang_clamp(stuck_threshold, MAX_HANG_STREAK_CAP);
        Self {
            hang_streak: 0,
            stuck_threshold: if clamped == 0 { 1 } else { clamped },
            stuck_flag: 0,
        }
    }

    /// Configured streak threshold required to latch `syspolicyd=stuck`.
    #[must_use]
    pub const fn stuck_threshold(&self) -> u64 {
        self.stuck_threshold
    }

    /// Whether `syspolicyd=stuck` has latched.
    #[must_use]
    pub const fn is_stuck(&self) -> bool {
        syspolicy_probe_is_stuck(self.stuck_flag)
    }

    /// Current consecutive non-Apple pre-main hang streak (`0..=MAX_HANG_STREAK_CAP`).
    #[must_use]
    pub const fn hang_streak(&self) -> u64 {
        self.hang_streak
    }

    /// Record that a non-Apple binary started normally (`execve` reached user code).
    pub fn record_non_apple_ok(&mut self) -> SyspolicydHealth {
        if self.is_stuck() {
            return SyspolicydHealth::Stuck;
        }
        self.hang_streak = 0;
        SyspolicydHealth::Healthy
    }

    /// Record that a non-Apple binary hung before starting, paired with whether an Apple
    /// platform control probe (`/usr/bin/true`) completed promptly (`apple_control_ok`).
    pub fn record_non_apple_hang(&mut self, apple_control_ok: bool) -> SyspolicydHealth {
        if self.is_stuck() {
            return SyspolicydHealth::Stuck;
        }
        if !apple_control_ok {
            let next =
                syspolicy_probe_hang_clamp(self.hang_streak.saturating_add(1), MAX_HANG_STREAK_CAP);
            self.hang_streak = next;
            return SyspolicydHealth::SystemBusy { hang_streak: next };
        }
        let next =
            syspolicy_probe_hang_clamp(self.hang_streak.saturating_add(1), MAX_HANG_STREAK_CAP);
        self.hang_streak = next;
        let cand_stuck = u64::from(next >= self.stuck_threshold);
        self.stuck_flag = syspolicy_probe_stuck_latch(self.stuck_flag, cand_stuck);
        if self.is_stuck() {
            SyspolicydHealth::Stuck
        } else {
            SyspolicydHealth::Suspect { hang_streak: next }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn syspolicyd_distinguishes_general_overload_from_deadlock_and_latches_stuck() {
        let mut det = SyspolicydDetector::new(2);
        assert_eq!(det.stuck_threshold(), 2);
        assert_eq!(det.record_non_apple_ok(), SyspolicydHealth::Healthy);

        assert_eq!(
            det.record_non_apple_hang(false),
            SyspolicydHealth::SystemBusy { hang_streak: 1 }
        );
        assert_eq!(
            det.record_non_apple_hang(false),
            SyspolicydHealth::SystemBusy { hang_streak: 2 }
        );
        assert!(!det.is_stuck());

        assert_eq!(det.record_non_apple_ok(), SyspolicydHealth::Healthy);
        assert_eq!(det.hang_streak(), 0);

        assert_eq!(
            det.record_non_apple_hang(true),
            SyspolicydHealth::Suspect { hang_streak: 1 }
        );
        let h = det.record_non_apple_hang(true);
        assert_eq!(h, SyspolicydHealth::Stuck);
        assert_eq!(h.status_token(), "stuck");
        assert_eq!(h.needs_you_banner(), Some("NEEDS YOU: restart the Mac"));
        assert!(det.is_stuck());

        assert_eq!(det.record_non_apple_ok(), SyspolicydHealth::Stuck);
    }
}
