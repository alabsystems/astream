//! macOS `syspolicyd=stuck` pre-exec deadlock sentinel (`aterm ctl @self status`).

#[cfg(clean_islands)]
#[path = "syspolicyd_deadlock_sentinel_island.rs"]
mod syspolicyd_deadlock_sentinel_island;
#[cfg(clean_islands)]
pub use syspolicyd_deadlock_sentinel_island::{
    syspolicyd_hang_streak_clamp, syspolicyd_stuck_epoch_advance,
};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn syspolicyd_hang_streak_clamp(streak: u64) -> u64 {
    if streak < 8 {
        streak
    } else {
        8
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn syspolicyd_stuck_epoch_advance(prev_epoch: u64, next_epoch: u64) -> u64 {
    if prev_epoch < next_epoch {
        next_epoch
    } else {
        prev_epoch
    }
}

contract_fn! {
    #[must_use]
    pub const fn syspolicyd_streak_below_limit(streak: u64) -> bool
    clauses [ensures result == (streak < 3)]
    {
        streak < 3
    }
}

#[inline]
#[must_use]
pub const fn syspolicyd_admits_spawn(is_apple_bin: u64, stuck_flag: u64, streak: u64) -> bool {
    is_apple_bin >= 1 || (stuck_flag < 1 && syspolicyd_streak_below_limit(streak))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpawnGateVerdict {
    AdmitSpawn,
    NeedsMacRestart { stuck_epoch: u64, hang_streak: u64 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SyspolicydDeadlockSentinel {
    reported_stuck: bool,
    hang_streak: u64,
    stuck_epoch: u64,
}

impl SyspolicydDeadlockSentinel {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            reported_stuck: false,
            hang_streak: 0,
            stuck_epoch: 0,
        }
    }

    #[must_use]
    pub const fn reported_stuck(&self) -> bool {
        self.reported_stuck
    }

    #[must_use]
    pub const fn hang_streak(&self) -> u64 {
        self.hang_streak
    }

    #[must_use]
    pub const fn stuck_epoch(&self) -> u64 {
        self.stuck_epoch
    }

    pub fn observe_status(&mut self, reported_stuck: bool, epoch: u64) {
        self.reported_stuck = reported_stuck;
        if reported_stuck {
            self.stuck_epoch = syspolicyd_stuck_epoch_advance(self.stuck_epoch, epoch);
        }
    }

    pub fn record_pre_main_hang(&mut self, epoch: u64) {
        let next = self.hang_streak.saturating_add(1);
        self.hang_streak = syspolicyd_hang_streak_clamp(next);
        if self.hang_streak >= 3 {
            self.stuck_epoch = syspolicyd_stuck_epoch_advance(self.stuck_epoch, epoch);
        }
    }

    pub fn record_clean_start(&mut self) {
        if !self.reported_stuck {
            self.hang_streak = 0;
        }
    }

    #[must_use]
    pub const fn gate_spawn(&self, is_apple_platform_binary: bool) -> SpawnGateVerdict {
        let apple = if is_apple_platform_binary { 1 } else { 0 };
        let stuck = if self.reported_stuck { 1 } else { 0 };
        if syspolicyd_admits_spawn(apple, stuck, self.hang_streak) {
            SpawnGateVerdict::AdmitSpawn
        } else {
            SpawnGateVerdict::NeedsMacRestart {
                stuck_epoch: self.stuck_epoch,
                hang_streak: self.hang_streak,
            }
        }
    }
}

impl Default for SyspolicydDeadlockSentinel {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_non_apple_spawns_when_stuck_while_allowing_apple_diagnostics() {
        let mut s = SyspolicydDeadlockSentinel::new();
        assert!(!s.reported_stuck());
        assert_eq!(s.gate_spawn(false), SpawnGateVerdict::AdmitSpawn);
        s.observe_status(true, 42);
        assert!(s.reported_stuck());
        assert_eq!(s.stuck_epoch(), 42);
        assert_eq!(
            s.gate_spawn(false),
            SpawnGateVerdict::NeedsMacRestart {
                stuck_epoch: 42,
                hang_streak: 0,
            }
        );
        assert_eq!(s.gate_spawn(true), SpawnGateVerdict::AdmitSpawn);
    }

    #[test]
    fn three_pre_main_hangs_trip_restart_verdict_even_before_status_poll() {
        let mut s = SyspolicydDeadlockSentinel::new();
        s.record_pre_main_hang(10);
        s.record_pre_main_hang(11);
        assert_eq!(s.hang_streak(), 2);
        assert_eq!(s.gate_spawn(false), SpawnGateVerdict::AdmitSpawn);
        s.record_pre_main_hang(12);
        assert_eq!(
            s.gate_spawn(false),
            SpawnGateVerdict::NeedsMacRestart {
                stuck_epoch: 12,
                hang_streak: 3,
            }
        );
        assert_eq!(syspolicyd_hang_streak_clamp(99), 8);
        assert_eq!(syspolicyd_stuck_epoch_advance(10, 5), 10);
    }
}
