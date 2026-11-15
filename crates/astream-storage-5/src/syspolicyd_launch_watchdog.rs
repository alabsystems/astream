// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! macOS `syspolicyd=stuck` pre-start deadlock detector & circuit breaker
//! (`Astream.Host.TlaSyspolicydLaunchWatchdog`).
//!
//! Models `aterm` macOS execution-policy deadlock detection (`aterm help permissions`):
//! when non-Apple binaries hang before their first instruction (`syspolicyd=stuck`), retrying
//! spawns only piles up unkillable kernel-wait processes. Trips a fail-fast circuit breaker once
//! `hung_spawns >= trip_threshold` so the harness stops retrying non-platform binaries and emits
//! `NEEDS YOU: restart the Mac`.

#[cfg(clean_islands)]
#[path = "syspolicyd_launch_watchdog_island.rs"]
mod syspolicyd_launch_watchdog_island;
#[cfg(clean_islands)]
pub use syspolicyd_launch_watchdog_island::{syspolicyd_epoch_advance, syspolicyd_hang_clamp};

#[cfg(not(clean_islands))]
/// Clamp consecutive pre-start hung spawn count to `trip_threshold`.
#[must_use]
pub const fn syspolicyd_hang_clamp(cand_hangs: u64, trip_threshold: u64) -> u64 {
    if cand_hangs < trip_threshold {
        cand_hangs
    } else {
        trip_threshold
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the `syspolicyd` watchdog epoch.
#[must_use]
pub const fn syspolicyd_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `hung_spawns` has reached `trip_threshold`, indicating `syspolicyd=stuck`.
    #[must_use]
    pub const fn syspolicyd_is_stuck_b106(hung_spawns: u64, trip_threshold: u64) -> bool
    clauses [ensures result == (hung_spawns >= trip_threshold)]
    {
        hung_spawns >= trip_threshold
    }
}

/// Current macOS program-check subsystem health verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyspolicydHealth {
    Healthy { consecutive_hangs: u64 },
    DeadlockedNeedsMacRestart { watchdog_epoch: u64 },
}

/// Circuit breaker for macOS `syspolicyd` pre-exec deadlocks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SyspolicydLaunchWatchdog {
    trip_threshold: u64,
    hung_spawns: u64,
    explicit_stuck_flag: bool,
    watchdog_epoch: u64,
}

impl SyspolicydLaunchWatchdog {
    #[must_use]
    pub const fn new(trip_threshold: u64) -> Self {
        let thresh = if trip_threshold == 0 {
            2
        } else {
            trip_threshold
        };
        Self {
            trip_threshold: thresh,
            hung_spawns: 0,
            explicit_stuck_flag: false,
            watchdog_epoch: 0,
        }
    }

    #[must_use]
    pub const fn hung_spawns(&self) -> u64 {
        self.hung_spawns
    }

    #[must_use]
    pub const fn health(&self) -> SyspolicydHealth {
        if self.explicit_stuck_flag
            || syspolicyd_is_stuck_b106(self.hung_spawns, self.trip_threshold)
        {
            SyspolicydHealth::DeadlockedNeedsMacRestart {
                watchdog_epoch: self.watchdog_epoch,
            }
        } else {
            SyspolicydHealth::Healthy {
                consecutive_hangs: self.hung_spawns,
            }
        }
    }

    /// Check whether launching a binary (`is_macos_platform_binary == true` for `/bin/*`, `/usr/bin/*`)
    /// is permitted right now.
    #[must_use]
    pub const fn allow_spawn(&self, is_macos_platform_binary: bool) -> bool {
        if is_macos_platform_binary {
            return true;
        }
        !matches!(
            self.health(),
            SyspolicydHealth::DeadlockedNeedsMacRestart { .. }
        )
    }

    /// Record a non-platform binary successfully starting execution.
    pub fn record_non_platform_started(&mut self) {
        if !self.explicit_stuck_flag {
            self.hung_spawns = 0;
        }
    }

    /// Record a non-platform binary hanging before first instruction (`exec` policy check).
    pub fn record_pre_start_hang(&mut self) -> SyspolicydHealth {
        let next = self.hung_spawns.saturating_add(1);
        self.hung_spawns = syspolicyd_hang_clamp(next, self.trip_threshold);
        let next_ep = self.watchdog_epoch.saturating_add(1);
        self.watchdog_epoch = syspolicyd_epoch_advance(self.watchdog_epoch, next_ep);
        self.health()
    }

    /// Ingest `syspolicyd=stuck` directly from `aterm ctl @self status`.
    pub fn observe_status_stuck(&mut self, stuck: bool) -> SyspolicydHealth {
        self.explicit_stuck_flag = stuck;
        let next_ep = self.watchdog_epoch.saturating_add(1);
        self.watchdog_epoch = syspolicyd_epoch_advance(self.watchdog_epoch, next_ep);
        self.health()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trips_circuit_breaker_on_syspolicyd_hangs_while_allowing_platform_binaries() {
        let mut wd = SyspolicydLaunchWatchdog::new(2);
        assert!(wd.allow_spawn(false));
        assert_eq!(
            wd.record_pre_start_hang(),
            SyspolicydHealth::Healthy {
                consecutive_hangs: 1
            }
        );
        assert_eq!(
            wd.record_pre_start_hang(),
            SyspolicydHealth::DeadlockedNeedsMacRestart { watchdog_epoch: 2 }
        );
        assert!(!wd.allow_spawn(false));
        assert!(wd.allow_spawn(true));
    }
}
