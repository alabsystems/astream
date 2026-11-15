//! `aterm ctl @self restart` supervised foreground PID & handoff-saved preflight.

#[cfg(clean_islands)]
#[path = "agent_restart_preflight_island.rs"]
mod agent_restart_preflight_island;
#[cfg(clean_islands)]
pub use agent_restart_preflight_island::{
    preflight_refusal_streak_clamp, preflight_restart_gen_advance,
};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn preflight_restart_gen_advance(prev_gen: u64, next_gen: u64) -> u64 {
    if prev_gen < next_gen {
        next_gen
    } else {
        prev_gen
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn preflight_refusal_streak_clamp(streak: u64) -> u64 {
    if streak < 8 {
        streak
    } else {
        8
    }
}

contract_fn! {
    #[must_use]
    pub const fn preflight_flag_is_set(flag: u64) -> bool
    clauses [ensures result == (1 <= flag)]
    {
        1 <= flag
    }
}

#[inline]
#[must_use]
pub const fn preflight_restart_ready(
    handoff_saved: u64,
    fg_matches: u64,
    not_supervisor: u64,
) -> bool {
    preflight_flag_is_set(handoff_saved)
        && preflight_flag_is_set(fg_matches)
        && preflight_flag_is_set(not_supervisor)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RestartRefusal {
    HandoffNotSaved,
    TargetIsSupervisorHostPid {
        supervisor_pid: u32,
    },
    ForegroundPidMismatch {
        expected_fg_pid: u32,
        requested_pid: u32,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AgentRestartPreflight {
    foreground_agent_pid: u32,
    supervisor_host_pid: u32,
    generation: u64,
    refusal_streak: u64,
}

impl AgentRestartPreflight {
    #[must_use]
    pub const fn new(foreground_agent_pid: u32, supervisor_host_pid: u32) -> Self {
        Self {
            foreground_agent_pid,
            supervisor_host_pid,
            generation: 0,
            refusal_streak: 0,
        }
    }

    #[must_use]
    pub const fn foreground_agent_pid(&self) -> u32 {
        self.foreground_agent_pid
    }

    #[must_use]
    pub const fn supervisor_host_pid(&self) -> u32 {
        self.supervisor_host_pid
    }

    #[must_use]
    pub const fn generation(&self) -> u64 {
        self.generation
    }

    #[must_use]
    pub const fn refusal_streak(&self) -> u64 {
        self.refusal_streak
    }

    pub fn validate_restart(
        &mut self,
        handoff_saved: bool,
        requested_pid: Option<u32>,
    ) -> Result<u64, RestartRefusal> {
        let target_pid = match requested_pid {
            Some(pid) => pid,
            None => self.foreground_agent_pid,
        };
        let handoff_ok = u64::from(handoff_saved);
        let not_sup = u64::from(target_pid != self.supervisor_host_pid);
        let fg_ok = u64::from(target_pid == self.foreground_agent_pid);
        if preflight_restart_ready(handoff_ok, fg_ok, not_sup) {
            self.refusal_streak = 0;
            let next = self.generation.saturating_add(1);
            self.generation = preflight_restart_gen_advance(self.generation, next);
            Ok(self.generation)
        } else {
            self.refusal_streak =
                preflight_refusal_streak_clamp(self.refusal_streak.saturating_add(1));
            if !handoff_saved {
                Err(RestartRefusal::HandoffNotSaved)
            } else if target_pid == self.supervisor_host_pid {
                Err(RestartRefusal::TargetIsSupervisorHostPid {
                    supervisor_pid: self.supervisor_host_pid,
                })
            } else {
                Err(RestartRefusal::ForegroundPidMismatch {
                    expected_fg_pid: self.foreground_agent_pid,
                    requested_pid: target_pid,
                })
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_supervisor_pid_and_unsaved_handoff_and_advances_generation_on_valid_fg_pid() {
        let mut v = AgentRestartPreflight::new(4100, 900);
        assert_eq!(v.foreground_agent_pid(), 4100);
        assert_eq!(v.supervisor_host_pid(), 900);
        assert_eq!(
            v.validate_restart(false, Some(4100)),
            Err(RestartRefusal::HandoffNotSaved)
        );
        assert_eq!(
            v.validate_restart(true, Some(900)),
            Err(RestartRefusal::TargetIsSupervisorHostPid {
                supervisor_pid: 900,
            })
        );
        assert_eq!(
            v.validate_restart(true, Some(9999)),
            Err(RestartRefusal::ForegroundPidMismatch {
                expected_fg_pid: 4100,
                requested_pid: 9999,
            })
        );
        assert_eq!(v.refusal_streak(), 3);
        assert_eq!(v.validate_restart(true, Some(4100)), Ok(1));
        assert_eq!(v.generation(), 1);
        assert_eq!(v.refusal_streak(), 0);
        assert_eq!(preflight_refusal_streak_clamp(99), 8);
    }
}
