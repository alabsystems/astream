// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! macOS `syspolicyd=stuck` exec-hang circuit breaker halting doomed non-system process spawns
//! and emitting `NEEDS YOU: restart the Mac` (`aterm` primer, `Astream.Worktree.TlaSyspolicydCircuit`).

#[cfg(clean_islands)]
#[path = "syspolicyd_circuit_island.rs"]
mod syspolicyd_circuit_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn syspol_hangs_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn syspol_trip_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use syspolicyd_circuit_island::{syspol_hangs_clamp, syspol_trip_advance};

/// Consecutive pre-main exec hangs before latching `syspolicyd=stuck`.
pub const MAX_PRE_EXEC_HANGS: u64 = 3;

contract_fn! {
    /// Verified trip predicate (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `syspol_tripped_isl`.
    #[must_use]
    pub const fn syspol_tripped(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Circuit breaker protecting `aterm` agents from infinite retry loops when macOS `syspolicyd` deadlocks.
#[derive(Debug, Clone, Default)]
pub struct SyspolicydCircuitBreaker {
    pre_exec_hangs: u64,
    stuck_latched: u64,
}

impl SyspolicydCircuitBreaker {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            pre_exec_hangs: 0,
            stuck_latched: 0,
        }
    }

    pub fn observe_status_flag(&mut self, status_line: &str) -> bool {
        for t in status_line.split_ascii_whitespace() {
            if t == "syspolicyd=stuck" {
                self.stuck_latched = syspol_trip_advance(self.stuck_latched, 1);
                break;
            }
        }
        self.is_tripped()
    }

    pub fn record_spawn_outcome(&mut self, hung_before_main: bool) -> bool {
        if hung_before_main {
            let next = self.pre_exec_hangs.saturating_add(1);
            self.pre_exec_hangs = syspol_hangs_clamp(next, MAX_PRE_EXEC_HANGS);
            if syspol_tripped(self.pre_exec_hangs, MAX_PRE_EXEC_HANGS) {
                self.stuck_latched = syspol_trip_advance(self.stuck_latched, 1);
            }
        } else {
            self.pre_exec_hangs = 0;
        }
        self.is_tripped()
    }

    #[must_use]
    pub const fn is_tripped(&self) -> bool {
        syspol_tripped(self.stuck_latched, 1)
    }

    #[must_use]
    pub const fn needs_you_banner(&self) -> Option<&'static str> {
        if self.is_tripped() {
            Some("NEEDS YOU: restart the Mac")
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn syspolicyd_breaker_trips_on_status_flag_or_three_pre_main_hangs() {
        let mut cb = SyspolicydCircuitBreaker::new();
        assert!(!cb.record_spawn_outcome(true));
        assert!(!cb.record_spawn_outcome(true));
        assert!(cb.record_spawn_outcome(true));
        assert_eq!(cb.needs_you_banner(), Some("NEEDS YOU: restart the Mac"));
    }
}
