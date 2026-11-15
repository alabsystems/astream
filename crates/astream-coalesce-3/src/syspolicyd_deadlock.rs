// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! macOS `syspolicyd=stuck` Pre-Main Spawn Deadlock Detector & Retry Circuit-Breaker.
//!
//! On macOS, when `syspolicyd` / `amfid` deadlocks, non-Apple binaries hang inside `execve` /
//! `posix_spawn` before entering `main` (never closing or writing their `CLOEXEC` exec-status
//! pipe within the startup deadline), while Apple platform binaries (`/bin/echo`,
//! `/usr/bin/true`) still start immediately. Retrying non-Apple spawns in a loop only piles up
//! unkillable kernel tasks until the Mac restarts.
//!
//! This module implements a pure, zero-syscall state machine that correlates consecutive
//! non-Apple pre-`main` spawn hangs against an Apple-platform control probe, tripping
//! `SyspolicyVerdict::DeadlockedNeedsMacRestart` (`NEEDS YOU: restart the Mac`) and halting
//! futile spawn retries.
//!
//! Backed by Clean TLA+ Island `Astream.Host.TlaSyspolicydDetector`
//! (`syspolicyd_deadlock_island.rs`), proving `stalledNonApple <= stallThresholdCap` and
//! `retryAttempts <= maxRetries`.

#[cfg(clean_islands)]
#[path = "syspolicyd_deadlock_island.rs"]
mod island;
#[cfg(clean_islands)]
pub use island::{syspolicy_retry_clamp, syspolicy_stall_clamp};

#[cfg(not(clean_islands))]
#[inline]
pub const fn syspolicy_stall_clamp(stalled_count: u64, threshold_cap: u64) -> u64 {
    if stalled_count < threshold_cap {
        stalled_count
    } else {
        threshold_cap
    }
}

#[cfg(not(clean_islands))]
#[inline]
pub const fn syspolicy_retry_clamp(retry_attempts: u64, max_retries: u64) -> u64 {
    if retry_attempts < max_retries {
        retry_attempts
    } else {
        max_retries
    }
}

contract_fn! {
    /// Kernel-certified check whether `stalled_count` has reached `threshold`.
    #[must_use]
    #[inline]
    pub const fn syspolicy_is_deadlocked(stalled_count: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= stalled_count)]
    {
        threshold <= stalled_count
    }
}

/// Canonical `aterm` operator escalation line when `syspolicyd` has deadlocked.
pub const NEEDS_YOU_RESTART_MAC: &str = "NEEDS YOU: restart the Mac";

/// Default consecutive non-Apple pre-`main` stalls required before confirming with control probe.
pub const DEFAULT_STALL_THRESHOLD: u64 = 2;

/// Default maximum non-Apple retry attempts allowed before circuit-breaker trips.
pub const DEFAULT_MAX_SPAWN_RETRIES: u64 = 2;

/// Binary provenance class for `execve` / `posix_spawn` telemetry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryProvenance {
    /// Apple-signed OS binary under `/bin/`, `/usr/bin/`, `/sbin/`, or `/usr/sbin/`.
    ApplePlatform,
    /// Developer / third-party / locally-built binary checked by `syspolicyd`.
    NonApple,
}

impl BinaryProvenance {
    /// Classifies an executable path lexically without touching the filesystem.
    #[must_use]
    pub fn classify_path(path: &str) -> Self {
        let p = path.as_bytes();
        if starts_with_bytes(p, b"/bin/")
            || starts_with_bytes(p, b"/sbin/")
            || starts_with_bytes(p, b"/usr/bin/")
            || starts_with_bytes(p, b"/usr/sbin/")
        {
            // Note: `/usr/bin/env` execs another target, so treat `/usr/bin/env` as NonApple
            // unless probing a direct platform binary like `/usr/bin/true`.
            if p == b"/usr/bin/env" {
                Self::NonApple
            } else {
                Self::ApplePlatform
            }
        } else {
            Self::NonApple
        }
    }
}

fn starts_with_bytes(hay: &[u8], prefix: &[u8]) -> bool {
    let mut hc = hay;
    let mut pc = prefix;
    while let (&[hb, ref hrest @ ..], &[pb, ref prest @ ..]) = (hc, pc) {
        if hb != pb {
            return false;
        }
        hc = hrest;
        pc = prest;
    }
    pc.is_empty()
}

/// Verdict emitted by `SyspolicydDeadlockDetector`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyspolicyVerdict {
    /// Program execution checks are healthy (`syspolicyd=ok`).
    Healthy,
    /// Non-Apple binary stalled pre-`main`; run one Apple platform control probe (`/usr/bin/true`)
    /// to distinguish `syspolicyd=stuck` from general kernel/disk starvation.
    ProbeAppleControl { stalled_non_apple: u64 },
    /// General system overload: even Apple platform binaries stalled; wait for load to clear.
    SystemOverloaded,
    /// Confirmed `syspolicyd=stuck` deadlock: Apple platform binaries start while non-Apple
    /// binaries hang pre-`main`. Stop retrying and emit `NEEDS YOU: restart the Mac`.
    DeadlockedNeedsMacRestart,
}

/// Stateful detector and spawn-retry circuit breaker certified by `TlaSyspolicydDetector`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SyspolicydDeadlockDetector {
    stalled_non_apple: u64,
    stall_threshold: u64,
    retry_attempts: u64,
    max_retries: u64,
    apple_control_succeeded_recently: bool,
    latched_deadlock: bool,
}

impl Default for SyspolicydDeadlockDetector {
    fn default() -> Self {
        Self::new(DEFAULT_STALL_THRESHOLD, DEFAULT_MAX_SPAWN_RETRIES)
    }
}

impl SyspolicydDeadlockDetector {
    #[inline]
    pub const fn new(stall_threshold: u64, max_retries: u64) -> Self {
        let thresh = if stall_threshold == 0 {
            1
        } else {
            stall_threshold
        };
        let retries = if max_retries == 0 { 1 } else { max_retries };
        Self {
            stalled_non_apple: 0,
            stall_threshold: thresh,
            retry_attempts: 0,
            max_retries: retries,
            apple_control_succeeded_recently: false,
            latched_deadlock: false,
        }
    }

    #[inline]
    pub const fn stalled_non_apple(&self) -> u64 {
        self.stalled_non_apple
    }

    #[inline]
    pub const fn retry_attempts(&self) -> u64 {
        self.retry_attempts
    }

    #[inline]
    pub const fn is_deadlocked(&self) -> bool {
        self.latched_deadlock
    }

    /// Returns `true` if another non-Apple spawn attempt is permitted (circuit closed).
    #[inline]
    pub const fn allow_non_apple_spawn(&self) -> bool {
        !self.latched_deadlock && self.retry_attempts <= self.max_retries
    }

    /// Records the outcome of a spawn attempt (`hung_pre_main == true` when the child process
    /// failed to pass `execve` within the startup timeout).
    pub fn record_spawn(
        &mut self,
        provenance: BinaryProvenance,
        hung_pre_main: bool,
    ) -> SyspolicyVerdict {
        match (provenance, hung_pre_main) {
            (BinaryProvenance::NonApple, false) => {
                // Non-Apple program started cleanly -> `syspolicyd` is NOT deadlocked!
                self.stalled_non_apple = 0;
                self.retry_attempts = 0;
                self.latched_deadlock = false;
                SyspolicyVerdict::Healthy
            }
            (BinaryProvenance::NonApple, true) => {
                let raw_stalls = self.stalled_non_apple.saturating_add(1);
                let raw_retries = self.retry_attempts.saturating_add(1);
                self.stalled_non_apple = syspolicy_stall_clamp(raw_stalls, self.stall_threshold);
                self.retry_attempts = syspolicy_retry_clamp(raw_retries, self.max_retries);

                if syspolicy_is_deadlocked(self.stalled_non_apple, self.stall_threshold) {
                    if self.apple_control_succeeded_recently {
                        self.latched_deadlock = true;
                        SyspolicyVerdict::DeadlockedNeedsMacRestart
                    } else {
                        SyspolicyVerdict::ProbeAppleControl {
                            stalled_non_apple: self.stalled_non_apple,
                        }
                    }
                } else {
                    SyspolicyVerdict::ProbeAppleControl {
                        stalled_non_apple: self.stalled_non_apple,
                    }
                }
            }
            (BinaryProvenance::ApplePlatform, false) => {
                self.apple_control_succeeded_recently = true;
                if syspolicy_is_deadlocked(self.stalled_non_apple, self.stall_threshold) {
                    self.latched_deadlock = true;
                    SyspolicyVerdict::DeadlockedNeedsMacRestart
                } else {
                    SyspolicyVerdict::Healthy
                }
            }
            (BinaryProvenance::ApplePlatform, true) => {
                self.apple_control_succeeded_recently = false;
                SyspolicyVerdict::SystemOverloaded
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_syspolicyd_deadlock_when_non_apple_hangs_and_apple_starts() {
        assert_eq!(
            BinaryProvenance::classify_path("/usr/bin/true"),
            BinaryProvenance::ApplePlatform
        );
        assert_eq!(
            BinaryProvenance::classify_path("/usr/bin/env"),
            BinaryProvenance::NonApple
        );
        assert_eq!(
            BinaryProvenance::classify_path("/fixture-home/.local/bin/targo"),
            BinaryProvenance::NonApple
        );

        let mut det = SyspolicydDeadlockDetector::new(2, 2);
        assert!(det.allow_non_apple_spawn());

        // 1st non-Apple hang -> asks for control probe, not latched yet.
        assert_eq!(
            det.record_spawn(BinaryProvenance::NonApple, true),
            SyspolicyVerdict::ProbeAppleControl {
                stalled_non_apple: 1
            }
        );
        // 2nd non-Apple hang -> hits threshold=2, asks for Apple control confirmation.
        assert_eq!(
            det.record_spawn(BinaryProvenance::NonApple, true),
            SyspolicyVerdict::ProbeAppleControl {
                stalled_non_apple: 2
            }
        );
        // `/usr/bin/true` starts cleanly -> confirms `syspolicyd=stuck`!
        assert_eq!(
            det.record_spawn(BinaryProvenance::ApplePlatform, false),
            SyspolicyVerdict::DeadlockedNeedsMacRestart
        );
        assert!(det.is_deadlocked());
        assert!(!det.allow_non_apple_spawn());
        assert_eq!(NEEDS_YOU_RESTART_MAC, "NEEDS YOU: restart the Mac");
    }

    #[test]
    fn distinguishes_system_overload_and_recovers_on_non_apple_success() {
        let mut det = SyspolicydDeadlockDetector::new(2, 3);
        let _ = det.record_spawn(BinaryProvenance::NonApple, true);
        let _ = det.record_spawn(BinaryProvenance::NonApple, true);
        // Apple binary ALSO hangs -> kernel/IO overload, NOT syspolicyd deadlock.
        assert_eq!(
            det.record_spawn(BinaryProvenance::ApplePlatform, true),
            SyspolicyVerdict::SystemOverloaded
        );
        assert!(!det.is_deadlocked());

        // Once load clears and non-Apple binary starts, counters reset cleanly.
        assert_eq!(
            det.record_spawn(BinaryProvenance::NonApple, false),
            SyspolicyVerdict::Healthy
        );
        assert_eq!(det.stalled_non_apple(), 0);
        assert_eq!(det.retry_attempts(), 0);
    }
}
