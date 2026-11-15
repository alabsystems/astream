// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! macOS `syspolicyd` pre-exec deadlock circuit breaker (`Astream.Host.TlaSyspolicydGuard`).
//!
//! When macOS's `syspolicyd` user-space code-evaluation daemon deadlocks (`syspolicyd=stuck`
//! in `aterm ctl @self status`), every new non-platform `execve` / `posix_spawn` hangs in the
//! kernel before `main` starts and cannot be killed or unstuck without a Mac reboot. Retrying
//! non-platform spawns only accumulates unkillable kernel-wedged processes.
//!
//! [`SyspolicydExecGuard`] enforces a formally bounded pre-exec circuit breaker:
//! 1. Pure lexical platform-binary classification ([`is_macos_platform_binary`]): base OS
//!    Apple binaries in `/bin/*`, `/sbin/*`, `/usr/bin/*`, and `/usr/sbin/*` remain runnable
//!    for diagnostics even while `syspolicyd` is wedged, whereas non-platform binaries
//!    (`~/.local/bin/*`, `target/*`, `/opt/*`, `/usr/local/*`, `/Applications/*`) are gated.
//! 2. Consecutive pre-exec startup timeouts increment `hang_streak` via Clean-origin
//!    [`syspolicy_hang_clamp`], tripping the breaker once
//!    [`syspolicy_breaker_tripped`]`(hang_streak, trip_cap)` holds (or immediately when
//!    [`SyspolicydExecGuard::observe_aterm_status`] sees `syspolicyd=stuck`).
//! 3. Once tripped in boot epoch `E`, non-platform spawns fail fast with
//!    [`SyspolicydDecision::BlockedNeedsMacRestart`] and the canonical operator line
//!    [`NEEDS_YOU_MAC_RESTART_LINE`] (`"NEEDS YOU: restart the Mac"`) until a strictly
//!    greater boot epoch `E' > E` is witnessed via [`syspolicy_epoch_advance`].

#[cfg(clean_islands)]
#[path = "syspolicyd_guard_island.rs"]
mod syspolicyd_guard_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn syspolicy_hang_clamp(proposed_streak: u64, trip_cap: u64) -> u64 {
    if proposed_streak < trip_cap {
        proposed_streak
    } else {
        trip_cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn syspolicy_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}
#[cfg(clean_islands)]
pub use syspolicyd_guard_island::{syspolicy_epoch_advance, syspolicy_hang_clamp};

/// Canonical `aterm` operator escalation line when `syspolicyd` has deadlocked.
pub const NEEDS_YOU_MAC_RESTART_LINE: &str = "NEEDS YOU: restart the Mac";

/// Default consecutive pre-exec hang count that trips the `syspolicyd` breaker.
pub const DEFAULT_SYSPOLICY_TRIP_CAP: u64 = 2;

contract_fn! {
    /// Kernel-certified check whether `hang_streak` has reached `trip_cap`
    /// (`trip_cap <= hang_streak`), linked via `clean-kernel-defeq` to
    /// `syspolicy_breaker_tripped_isl`.
    #[must_use]
    pub const fn syspolicy_breaker_tripped(hang_streak: u64, trip_cap: u64) -> bool
    clauses [ensures result == (trip_cap <= hang_streak)]
    {
        trip_cap <= hang_streak
    }
}

/// Pre-spawn admission verdict from [`SyspolicydExecGuard::check_spawn`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyspolicydDecision {
    /// Normal operation: `syspolicyd` is healthy and any binary may be spawned.
    AllowHealthy,
    /// `syspolicyd` is tripped, so only base macOS platform binaries (`/bin`, `/usr/bin`, etc.)
    /// are permitted for status/diagnostic inspection.
    AllowPlatformDiagnosticOnly,
    /// `syspolicyd` is tripped and the target is a non-platform binary that would hang in
    /// kernel pre-exec validation; stop retrying and report [`NEEDS_YOU_MAC_RESTART_LINE`].
    BlockedNeedsMacRestart { boot_epoch: u64, hang_streak: u64 },
}

impl SyspolicydDecision {
    /// Returns the `NEEDS YOU:` operator report line if this spawn was blocked.
    #[must_use]
    pub const fn needs_you_line(self) -> Option<&'static str> {
        match self {
            Self::BlockedNeedsMacRestart { .. } => Some(NEEDS_YOU_MAC_RESTART_LINE),
            Self::AllowHealthy | Self::AllowPlatformDiagnosticOnly => None,
        }
    }
}

fn has_single_clean_basename(rest: &str) -> bool {
    if rest.is_empty() || rest == "." || rest == ".." {
        return false;
    }
    let mut cur = rest.as_bytes();
    while let &[b, ref tail @ ..] = cur {
        if b == b'/' || b == 0 {
            return false;
        }
        cur = tail;
    }
    true
}

/// Pure lexical check for base macOS platform binaries (`/bin/<name>`, `/sbin/<name>`,
/// `/usr/bin/<name>`, `/usr/sbin/<name>`) that carry Apple platform trust in the kernel image
/// cache and avoid third-party `syspolicyd` evaluation deadlocks.
///
/// Rejects path traversal (`..`), nested subdirectories, `/usr/local/*`, `/opt/*`, and
/// user-writable paths.
#[must_use]
pub fn is_macos_platform_binary(program_path: &str) -> bool {
    if let Some(rest) = program_path.strip_prefix("/bin/") {
        return has_single_clean_basename(rest);
    }
    if let Some(rest) = program_path.strip_prefix("/sbin/") {
        return has_single_clean_basename(rest);
    }
    if let Some(rest) = program_path.strip_prefix("/usr/bin/") {
        return has_single_clean_basename(rest);
    }
    if let Some(rest) = program_path.strip_prefix("/usr/sbin/") {
        return has_single_clean_basename(rest);
    }
    false
}

/// Stateful pre-exec deadlock circuit breaker backed by `Astream.Host.TlaSyspolicydGuard`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SyspolicydExecGuard {
    hang_streak: u64,
    trip_cap: u64,
    boot_epoch: u64,
    explicit_stuck: bool,
}

impl SyspolicydExecGuard {
    /// Create a new guard for `boot_epoch` with `trip_cap` (clamped to `>= 1`).
    #[must_use]
    pub const fn new(boot_epoch: u64, trip_cap: u64) -> Self {
        let effective_cap = if trip_cap == 0 { 1 } else { trip_cap };
        Self {
            hang_streak: 0,
            trip_cap: effective_cap,
            boot_epoch,
            explicit_stuck: false,
        }
    }

    /// Create a guard with [`DEFAULT_SYSPOLICY_TRIP_CAP`] (`2` consecutive pre-exec hangs).
    #[must_use]
    pub const fn with_defaults(boot_epoch: u64) -> Self {
        Self::new(boot_epoch, DEFAULT_SYSPOLICY_TRIP_CAP)
    }

    /// Current bounded pre-exec hang streak (`<= trip_cap`).
    #[must_use]
    pub const fn hang_streak(&self) -> u64 {
        self.hang_streak
    }

    /// Configured hang streak threshold (`>= 1`).
    #[must_use]
    pub const fn trip_cap(&self) -> u64 {
        self.trip_cap
    }

    /// Monotone host boot epoch tracked by the guard.
    #[must_use]
    pub const fn boot_epoch(&self) -> u64 {
        self.boot_epoch
    }

    /// Whether the `syspolicyd` circuit breaker is currently tripped.
    #[must_use]
    pub const fn is_tripped(&self) -> bool {
        self.explicit_stuck || syspolicy_breaker_tripped(self.hang_streak, self.trip_cap)
    }

    /// Record a non-platform child process that hung before completing `exec` startup.
    pub fn record_pre_exec_hang(&mut self) -> bool {
        let cand = self.hang_streak.saturating_add(1);
        self.hang_streak = syspolicy_hang_clamp(cand, self.trip_cap);
        self.is_tripped()
    }

    /// Record a non-platform child process that started cleanly: clears transient pre-trip
    /// streak, while keeping an already-tripped deadlock latched until a new boot epoch.
    pub fn record_non_platform_exec_ok(&mut self) {
        if !self.is_tripped() {
            self.hang_streak = 0;
        }
    }

    /// Ingest whitespace-delimited key-value output from `aterm ctl @self status` and latch
    /// immediately if `syspolicyd=stuck` appears.
    pub fn observe_aterm_status(&mut self, status_text: &str) -> bool {
        let bytes = status_text.as_bytes();
        let needle = b"syspolicyd=stuck";
        if bytes.len() < needle.len() {
            return self.is_tripped();
        }
        let limit = bytes.len().saturating_sub(needle.len());
        let mut i = 0usize;
        while i <= limit {
            let left_ok = if i == 0 {
                true
            } else {
                matches!(
                    bytes.get(i.saturating_sub(1)),
                    Some(b' ' | b'\t' | b'\n' | b'\r')
                )
            };
            let right_idx = i.saturating_add(needle.len());
            let right_ok = if right_idx >= bytes.len() {
                true
            } else {
                matches!(bytes.get(right_idx), Some(b' ' | b'\t' | b'\n' | b'\r'))
            };
            if left_ok && right_ok && bytes.get(i..right_idx) == Some(needle.as_slice()) {
                self.explicit_stuck = true;
                self.hang_streak = syspolicy_hang_clamp(self.trip_cap, self.trip_cap);
                return true;
            }
            i = i.saturating_add(1);
        }
        self.is_tripped()
    }

    /// Advance to a candidate host boot epoch via Clean-origin [`syspolicy_epoch_advance`].
    /// Only a strictly newer boot epoch (`cand_epoch > self.boot_epoch`) clears a latched
    /// `syspolicyd` deadlock (corresponding to an actual Mac reboot).
    pub fn observe_boot_epoch(&mut self, cand_epoch: u64) -> bool {
        let prev = self.boot_epoch;
        let next = syspolicy_epoch_advance(prev, cand_epoch);
        self.boot_epoch = next;
        if prev < next {
            self.hang_streak = 0;
            self.explicit_stuck = false;
            true
        } else {
            false
        }
    }

    /// Evaluate whether `program_path` may be spawned right now.
    #[must_use]
    pub fn check_spawn(&self, program_path: &str) -> SyspolicydDecision {
        if !self.is_tripped() {
            return SyspolicydDecision::AllowHealthy;
        }
        if is_macos_platform_binary(program_path) {
            SyspolicydDecision::AllowPlatformDiagnosticOnly
        } else {
            SyspolicydDecision::BlockedNeedsMacRestart {
                boot_epoch: self.boot_epoch,
                hang_streak: self.hang_streak,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lexical_platform_binary_classifier_rejects_non_platform_and_traversal() {
        assert!(is_macos_platform_binary("/bin/ps"));
        assert!(is_macos_platform_binary("/sbin/mount"));
        assert!(is_macos_platform_binary("/usr/bin/stat"));
        assert!(is_macos_platform_binary("/usr/sbin/sysctl"));

        assert!(!is_macos_platform_binary("/usr/local/bin/rg"));
        assert!(!is_macos_platform_binary("/opt/homebrew/bin/git"));
        assert!(!is_macos_platform_binary("/fixture-home/.local/bin/aterm"));
        assert!(!is_macos_platform_binary("/usr/bin/../local/bin/foo"));
        assert!(!is_macos_platform_binary("/usr/bin/sub/tool"));
        assert!(!is_macos_platform_binary("/usr/bin/"));
        assert!(!is_macos_platform_binary("cargo"));
    }

    #[test]
    fn consecutive_hangs_trip_breaker_and_only_new_boot_epoch_resets() {
        let mut guard = SyspolicydExecGuard::with_defaults(10);
        assert_eq!(
            guard.check_spawn("/fixture-home/.cargo/bin/targo"),
            SyspolicydDecision::AllowHealthy
        );

        assert!(!guard.record_pre_exec_hang());
        assert_eq!(guard.hang_streak(), 1);
        guard.record_non_platform_exec_ok();
        assert_eq!(guard.hang_streak(), 0);

        assert!(!guard.record_pre_exec_hang());
        assert!(guard.record_pre_exec_hang());
        // Additional hangs stay clamped at trip_cap (2).
        assert!(guard.record_pre_exec_hang());
        assert_eq!(guard.hang_streak(), 2);

        let blocked = guard.check_spawn("/fixture-home/.cargo/bin/targo");
        assert_eq!(
            blocked,
            SyspolicydDecision::BlockedNeedsMacRestart {
                boot_epoch: 10,
                hang_streak: 2,
            }
        );
        assert_eq!(blocked.needs_you_line(), Some(NEEDS_YOU_MAC_RESTART_LINE));
        assert_eq!(
            guard.check_spawn("/bin/ps"),
            SyspolicydDecision::AllowPlatformDiagnosticOnly
        );

        // Stale or equal boot epoch cannot clear a deadlocked Mac.
        assert!(!guard.observe_boot_epoch(9));
        assert!(!guard.observe_boot_epoch(10));
        assert!(guard.is_tripped());

        // Real reboot increments boot_epoch and clears the breaker.
        assert!(guard.observe_boot_epoch(11));
        assert!(!guard.is_tripped());
        assert_eq!(guard.boot_epoch(), 11);
        assert_eq!(guard.hang_streak(), 0);
        assert_eq!(
            guard.check_spawn("/fixture-home/.cargo/bin/targo"),
            SyspolicydDecision::AllowHealthy
        );
    }

    #[test]
    fn aterm_status_token_trips_immediately_without_false_substring_match() {
        let mut guard = SyspolicydExecGuard::with_defaults(42);
        assert!(!guard.observe_aterm_status("pid=123 syspolicyd=stuck_not_really ok=1"));
        assert!(!guard.is_tripped());

        assert!(guard.observe_aterm_status("pid=123 disk_free_mb=90000 syspolicyd=stuck\n"));
        assert!(guard.is_tripped());
        assert_eq!(guard.hang_streak(), 2);
    }
}
