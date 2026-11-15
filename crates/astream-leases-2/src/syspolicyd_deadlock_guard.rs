// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! macOS `syspolicyd=stuck` exec-before-start deadlock detector and fail-closed spawn gate
//! (`Astream.Host.TlaSyspolicydDeadlockGuard`, Island #288).
//!
//! On macOS, when Apple's `syspolicyd` program check deadlocks in kernel space, non-Apple
//! binaries hang before entering `main` (`aterm ctl @self status` reports `syspolicyd=stuck`),
//! whereas Apple platform binaries (`/bin/*`, `/usr/bin/*` shipped with macOS) still start.
//! Retrying non-Apple launches leaks unkillable hung processes. [`SyspolicydDeadlockGuard`]
//! detects the deadlock, refuses further non-Apple spawns fail-closed while permitting Apple
//! platform binaries for status inspection, and emits `NEEDS YOU: restart the Mac`.

#[cfg(clean_islands)]
#[path = "syspolicyd_deadlock_guard_island.rs"]
mod syspolicyd_deadlock_guard_island;
#[cfg(clean_islands)]
pub use syspolicyd_deadlock_guard_island::{syspolicyd_hang_count_clamp, syspolicyd_wait_ms_clamp};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn syspolicyd_hang_count_clamp(hung: u64, max_hung: u64) -> u64 {
    if hung < max_hung {
        hung
    } else {
        max_hung
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn syspolicyd_wait_ms_clamp(wait_ms: u64, max_wait_ms: u64) -> u64 {
    if wait_ms < max_wait_ms {
        wait_ms
    } else {
        max_wait_ms
    }
}

/// Maximum tracked hung non-Apple spawns (`64`).
pub const MAX_TRACKED_SYSPOLICYD_HANGS: u64 = 64;

/// Maximum pre-`main` exec wait window tracked in milliseconds (`600_000` = 10 minutes).
pub const MAX_SYSPOLICYD_WAIT_MS: u64 = 600_000;

/// Default hung non-Apple spawn threshold to latch `syspolicyd=stuck` (`2`).
pub const DEFAULT_SYSPOLICYD_HANG_THRESHOLD: u64 = 2;

/// Default pre-`main` exec hang timeout in milliseconds (`15_000` = 15s).
pub const DEFAULT_EXEC_HANG_MS: u64 = 15_000;

/// Canonical operator escalation line emitted once `syspolicyd=stuck` latches.
pub const NEEDS_YOU_RESTART_MAC: &str = "NEEDS YOU: restart the Mac";

contract_fn! {
    /// Verified check whether hung pre-start spawns reached `threshold`
    /// (`threshold <= hung_spawns`), linked via `clean-kernel-defeq` to
    /// `syspolicyd_threshold_tripped_isl`.
    #[must_use]
    pub const fn syspolicyd_threshold_tripped(hung_spawns: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= hung_spawns)]
    {
        threshold <= hung_spawns
    }
}

/// Spawn gate verdict returned by [`SyspolicydDeadlockGuard::check_spawn`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyspolicydSpawnVerdict {
    /// Normal launch permitted.
    Allow,
    /// `syspolicyd=stuck`, but Apple platform binary permitted for minimal diagnostics.
    AllowApplePlatformDiagnostic,
    /// Non-Apple binary refused fail-closed until reboot (`NEEDS YOU: restart the Mac`).
    RefuseDeadlocked {
        hung_spawns: u64,
        needs_you: &'static str,
    },
}

/// Stateful detector for macOS `syspolicyd` pre-exec kernel deadlocks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyspolicydDeadlockGuard {
    hung_spawns: u64,
    longest_wait_ms: u64,
    hang_threshold: u64,
    exec_hang_ms: u64,
    latched_stuck: bool,
    boot_id: [u8; 16],
}

impl SyspolicydDeadlockGuard {
    /// Create a guard bound to the current `boot_id`.
    #[must_use]
    pub const fn new(boot_id: [u8; 16]) -> Self {
        Self {
            hung_spawns: 0,
            longest_wait_ms: 0,
            hang_threshold: DEFAULT_SYSPOLICYD_HANG_THRESHOLD,
            exec_hang_ms: DEFAULT_EXEC_HANG_MS,
            latched_stuck: false,
            boot_id,
        }
    }

    /// Override hang threshold and pre-`main` timeout (clamped to `[1, MAX_*]`).
    #[must_use]
    pub const fn with_thresholds(mut self, hang_threshold: u64, exec_hang_ms: u64) -> Self {
        let th = if hang_threshold == 0 {
            1
        } else {
            syspolicyd_hang_count_clamp(hang_threshold, MAX_TRACKED_SYSPOLICYD_HANGS)
        };
        let ms = if exec_hang_ms == 0 {
            1
        } else {
            syspolicyd_wait_ms_clamp(exec_hang_ms, MAX_SYSPOLICYD_WAIT_MS)
        };
        self.hang_threshold = th;
        self.exec_hang_ms = ms;
        self
    }

    /// True if `syspolicyd=stuck` has latched in this macOS boot session.
    #[must_use]
    pub const fn is_stuck(&self) -> bool {
        self.latched_stuck
    }

    /// Count of pre-start hung non-Apple spawns observed in this boot.
    #[must_use]
    pub const fn hung_spawns(&self) -> u64 {
        self.hung_spawns
    }

    /// Longest pre-start wait observed in milliseconds.
    #[must_use]
    pub const fn longest_wait_ms(&self) -> u64 {
        self.longest_wait_ms
    }

    #[must_use]
    pub const fn hang_threshold(&self) -> u64 {
        self.hang_threshold
    }

    #[must_use]
    pub const fn exec_hang_ms(&self) -> u64 {
        self.exec_hang_ms
    }

    #[must_use]
    pub const fn boot_id(&self) -> [u8; 16] {
        self.boot_id
    }

    /// Explicitly adopt `syspolicyd=stuck` reported by `aterm ctl @self status`.
    pub fn mark_reported_stuck(&mut self) {
        self.latched_stuck = true;
    }

    /// Observe a new `boot_id`: only a Mac reboot (`next_boot_id != self.boot_id`) clears a
    /// latched `syspolicyd` kernel deadlock.
    pub fn observe_boot(&mut self, next_boot_id: [u8; 16]) {
        if next_boot_id != self.boot_id {
            self.boot_id = next_boot_id;
            self.hung_spawns = 0;
            self.longest_wait_ms = 0;
            self.latched_stuck = false;
        }
    }

    /// Record a spawn probe outcome (`entered_main == false` after `pre_start_wait_ms`).
    pub fn observe_spawn_probe(
        &mut self,
        is_apple_platform_binary: bool,
        entered_main: bool,
        pre_start_wait_ms: u64,
    ) {
        let clamped_wait = syspolicyd_wait_ms_clamp(pre_start_wait_ms, MAX_SYSPOLICYD_WAIT_MS);
        if clamped_wait > self.longest_wait_ms {
            self.longest_wait_ms = clamped_wait;
        }
        if is_apple_platform_binary {
            return;
        }
        if entered_main {
            if !self.latched_stuck {
                self.hung_spawns = 0;
            }
            return;
        }
        if clamped_wait >= self.exec_hang_ms {
            self.hung_spawns = syspolicyd_hang_count_clamp(
                self.hung_spawns.saturating_add(1),
                MAX_TRACKED_SYSPOLICYD_HANGS,
            );
            if syspolicyd_threshold_tripped(self.hung_spawns, self.hang_threshold) {
                self.latched_stuck = true;
            }
        }
    }

    /// Check whether a new program may be spawned.
    #[must_use]
    pub const fn check_spawn(&self, is_apple_platform_binary: bool) -> SyspolicydSpawnVerdict {
        if !self.latched_stuck {
            SyspolicydSpawnVerdict::Allow
        } else if is_apple_platform_binary {
            SyspolicydSpawnVerdict::AllowApplePlatformDiagnostic
        } else {
            SyspolicydSpawnVerdict::RefuseDeadlocked {
                hung_spawns: self.hung_spawns,
                needs_you: NEEDS_YOU_RESTART_MAC,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn latches_after_hung_non_apple_spawns_and_only_clears_on_mac_reboot() {
        let mut g = SyspolicydDeadlockGuard::new([0x11; 16]);
        assert_eq!(g.check_spawn(false), SyspolicydSpawnVerdict::Allow);

        g.observe_spawn_probe(false, false, 16_000);
        assert!(!g.is_stuck());
        g.observe_spawn_probe(false, false, 20_000);
        assert!(g.is_stuck());

        assert_eq!(
            g.check_spawn(false),
            SyspolicydSpawnVerdict::RefuseDeadlocked {
                hung_spawns: 2,
                needs_you: NEEDS_YOU_RESTART_MAC,
            }
        );
        assert_eq!(
            g.check_spawn(true),
            SyspolicydSpawnVerdict::AllowApplePlatformDiagnostic
        );

        // Same boot does NOT clear latched kernel deadlock.
        g.observe_boot([0x11; 16]);
        assert!(g.is_stuck());

        // New Mac boot session clears the latch.
        g.observe_boot([0x22; 16]);
        assert!(!g.is_stuck());
        assert_eq!(g.check_spawn(false), SyspolicydSpawnVerdict::Allow);
    }
}
