// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! macOS `syspolicyd=stuck` pre-exec deadlock circuit breaker (`aterm help permissions`;
//! `Astream.Host.TlaSyspolicydCircuitBreaker`).
//!
//! When macOS's `syspolicyd` program check deadlocks, non-Apple binaries hang in `execve` /
//! `posix_spawn` before executing their first instruction, and retrying only piles up unkillable
//! pre-exec processes until the Mac restarts. [`SyspolicydCircuitBreaker`] latches `tripped = 1`
//! monotonically within a `boot_epoch` via [`syspolicyd_latch_advance_b121`] once pre-exec hangs
//! reach `hang_threshold` (or `aterm ctl @self status` reports `syspolicyd=stuck`), refusing
//! non-platform spawns (`NeedsYouRestartMac`) while still permitting Apple platform binaries.

#[cfg(clean_islands)]
#[path = "syspolicyd_launch_circuit_breaker_island.rs"]
mod syspolicyd_launch_circuit_breaker_island;
#[cfg(clean_islands)]
pub use syspolicyd_launch_circuit_breaker_island::{
    syspolicyd_hang_clamp_b121, syspolicyd_latch_advance_b121,
};

#[cfg(not(clean_islands))]
/// Clamp consecutive pre-exec hang count to `threshold`.
#[must_use]
pub const fn syspolicyd_hang_clamp_b121(cand_hangs: u64, threshold: u64) -> u64 {
    if cand_hangs < threshold {
        cand_hangs
    } else {
        threshold
    }
}

#[cfg(not(clean_islands))]
/// Monotonically latch `tripped` (`0 -> 1`) within a boot epoch.
#[must_use]
pub const fn syspolicyd_latch_advance_b121(cur_tripped: u64, cand_tripped: u64) -> u64 {
    if cur_tripped < cand_tripped {
        cand_tripped
    } else {
        cur_tripped
    }
}

contract_fn! {
    /// True iff `tripped == 0`.
    #[must_use]
    pub const fn syspolicyd_not_tripped_b121(tripped: u64) -> bool
    clauses [ensures result == (tripped == 0)]
    {
        tripped == 0
    }
}

/// Spawn gate verdict under macOS `syspolicyd` supervision.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyspolicydSpawnDecision {
    Admit,
    NeedsYouRestartMac { boot_epoch: u64, hang_count: u64 },
}

/// Per-boot circuit breaker for macOS `syspolicyd=stuck` pre-exec deadlocks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SyspolicydCircuitBreaker {
    boot_epoch: u64,
    hang_threshold: u64,
    hang_count: u64,
    tripped: u64,
}

impl SyspolicydCircuitBreaker {
    #[must_use]
    pub const fn new(boot_epoch: u64, hang_threshold: u64) -> Self {
        let thresh = if hang_threshold == 0 {
            1
        } else {
            hang_threshold
        };
        Self {
            boot_epoch,
            hang_threshold: thresh,
            hang_count: 0,
            tripped: 0,
        }
    }

    #[must_use]
    pub const fn is_stuck(&self) -> bool {
        self.tripped > 0
    }

    /// Record a pre-exec launch hang (no first instruction before timeout).
    pub fn record_pre_exec_hang(&mut self) -> bool {
        let next =
            syspolicyd_hang_clamp_b121(self.hang_count.saturating_add(1), self.hang_threshold);
        self.hang_count = next;
        if self.hang_count >= self.hang_threshold {
            self.tripped = syspolicyd_latch_advance_b121(self.tripped, 1);
        }
        self.is_stuck()
    }

    /// Latch `syspolicyd=stuck` directly from `aterm ctl @self status`.
    pub fn observe_status_stuck(&mut self) {
        self.hang_count = self.hang_threshold;
        self.tripped = syspolicyd_latch_advance_b121(self.tripped, 1);
    }

    /// Record a successful non-platform exec; clears transient pre-threshold hang count,
    /// but NEVER clears a latched `tripped == 1` within the same `boot_epoch`.
    pub fn record_non_platform_exec_ok(&mut self) {
        if self.tripped == 0 {
            self.hang_count = 0;
        }
    }

    /// Reset circuit breaker ONLY when the Mac restarts into a strictly newer `new_boot_epoch`.
    pub fn observe_mac_reboot(&mut self, new_boot_epoch: u64) -> bool {
        if new_boot_epoch > self.boot_epoch {
            self.boot_epoch = new_boot_epoch;
            self.hang_count = 0;
            self.tripped = 0;
            true
        } else {
            false
        }
    }

    /// Check whether a binary (`is_apple_platform_binary`: e.g. `/bin/ps`, `/usr/bin/true`) may spawn.
    #[must_use]
    pub const fn evaluate_spawn(&self, is_apple_platform_binary: bool) -> SyspolicydSpawnDecision {
        if syspolicyd_not_tripped_b121(self.tripped) || is_apple_platform_binary {
            SyspolicydSpawnDecision::Admit
        } else {
            SyspolicydSpawnDecision::NeedsYouRestartMac {
                boot_epoch: self.boot_epoch,
                hang_count: self.hang_count,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn syspolicyd_latch_blocks_non_platform_until_mac_reboot() {
        let mut cb = SyspolicydCircuitBreaker::new(42, 2);
        assert_eq!(cb.evaluate_spawn(false), SyspolicydSpawnDecision::Admit);

        assert!(!cb.record_pre_exec_hang());
        assert_eq!(cb.evaluate_spawn(false), SyspolicydSpawnDecision::Admit);

        // Second pre-exec hang trips `syspolicyd=stuck`!
        assert!(cb.record_pre_exec_hang());
        assert!(cb.is_stuck());
        assert_eq!(
            cb.evaluate_spawn(false),
            SyspolicydSpawnDecision::NeedsYouRestartMac {
                boot_epoch: 42,
                hang_count: 2
            }
        );
        // Apple platform binaries remain permitted for diagnostics.
        assert_eq!(cb.evaluate_spawn(true), SyspolicydSpawnDecision::Admit);

        // Same boot epoch cannot untrip.
        cb.record_non_platform_exec_ok();
        assert!(cb.is_stuck());
        assert!(!cb.observe_mac_reboot(42));

        // Mac reboot into epoch 43 clears the deadlock!
        assert!(cb.observe_mac_reboot(43));
        assert!(!cb.is_stuck());
        assert_eq!(cb.evaluate_spawn(false), SyspolicydSpawnDecision::Admit);
    }
}
