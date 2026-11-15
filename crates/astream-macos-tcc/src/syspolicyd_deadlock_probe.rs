// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! macOS `syspolicyd=stuck` kernel-assessment deadlock detector halting futile retries and emitting
//! `NEEDS YOU: restart the Mac` immediately (`Astream.MacTcc.TlaSyspolicydDeadlockProbe`).

#[cfg(clean_islands)]
#[path = "syspolicyd_deadlock_probe_island.rs"]
mod syspolicyd_deadlock_probe_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tcc_hang_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tcc_pol_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use syspolicyd_deadlock_probe_island::{tcc_hang_clamp, tcc_pol_advance};

/// Maximum tracked pre-main `execve` hang count (`64`).
pub const MAX_SPAWN_HANGS: u64 = 64;

contract_fn! {
    /// Verified deadlock tripwire (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `tcc_needs_mac_restart_isl`.
    #[must_use]
    pub const fn tcc_needs_mac_restart(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct SyspolicydProbe {
    pre_main_hangs: u64,
    status_stuck: bool,
    trips: u64,
}

impl SyspolicydProbe {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            pre_main_hangs: 0,
            status_stuck: false,
            trips: 0,
        }
    }

    pub fn observe(&mut self, new_hangs: u64, syspolicyd_stuck_flag: bool) -> bool {
        self.pre_main_hangs = tcc_hang_clamp(
            self.pre_main_hangs.saturating_add(new_hangs),
            MAX_SPAWN_HANGS,
        );
        self.status_stuck = syspolicyd_stuck_flag;
        let score = if self.status_stuck && self.pre_main_hangs >= 1 {
            2u64
        } else {
            0u64
        };
        if tcc_needs_mac_restart(score, 2) {
            self.trips = tcc_pol_advance(self.trips, self.trips.saturating_add(1));
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
    fn trips_mac_restart_banner_when_spawn_hangs_and_syspolicyd_is_stuck() {
        let mut p = SyspolicydProbe::new();
        assert!(!p.observe(1, false));
        assert!(p.observe(0, true));
    }
}
