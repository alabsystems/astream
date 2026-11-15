// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm ctl @self restart` supervised foreground validator
//! (`Astream.Host.TlaSupervisorRestartValidator`).
//!
//! Validates `aterm ctl @self restart [pid=<agent-pid>]`:
//! 1. Rejects `target_pid == supervisor_pid` (`supervisor=` names `aterm`'s host,
//!    never the supervised agent process).
//! 2. Verifies `target_pid` matches the recorded foreground agent PID.
//! 3. Requires a recorded resumable conversation/args snapshot.
//! 4. Enforces a bounded restart rate (`<= max_per_window`) to prevent crash loops.

#[cfg(clean_islands)]
#[path = "supervisor_restart_validator_island.rs"]
mod supervisor_restart_validator_island;
#[cfg(clean_islands)]
pub use supervisor_restart_validator_island::{restart_epoch_advance_b92, restart_window_clamp};

/// Default maximum self-restarts allowed inside one rate-limit window.
pub const DEFAULT_MAX_RESTARTS_PER_WINDOW: u64 = 4;

#[cfg(not(clean_islands))]
/// Monotonically advance the supervised agent restart epoch.
#[must_use]
pub const fn restart_epoch_advance_b92(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

#[cfg(not(clean_islands))]
/// Clamp restarts counted in the current window to `max_per_window`.
#[must_use]
pub const fn restart_window_clamp(cand_count: u64, max_per_window: u64) -> u64 {
    if cand_count < max_per_window {
        cand_count
    } else {
        max_per_window
    }
}

contract_fn! {
    /// True iff `target_pid != supervisor_pid`.
    #[must_use]
    pub const fn restart_pid_distinct_from_sup(supervisor_pid: u64, target_pid: u64) -> bool
    clauses [ensures result == (supervisor_pid != target_pid)]
    {
        supervisor_pid != target_pid
    }
}

/// Explicit refusal naming what prevents `aterm ctl @self restart`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RestartRefusal {
    ZeroOrInvalidPid,
    TargetIsSupervisorHost {
        supervisor_pid: u64,
    },
    ForegroundPidMismatch {
        expected_agent_pid: u64,
        requested_pid: u64,
    },
    MissingResumeSnapshot,
    RateLimitExceeded {
        max_per_window: u64,
    },
}

/// Stateful validator for `aterm ctl @self restart`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SupervisorRestartValidator {
    supervisor_pid: u64,
    foreground_agent_pid: u64,
    has_resume_snapshot: bool,
    restart_epoch: u64,
    window_start_ms: u64,
    window_duration_ms: u64,
    window_count: u64,
    max_per_window: u64,
}

impl SupervisorRestartValidator {
    #[must_use]
    pub const fn new(
        supervisor_pid: u64,
        foreground_agent_pid: u64,
        has_resume_snapshot: bool,
        window_duration_ms: u64,
        max_per_window: u64,
    ) -> Self {
        let cap = if max_per_window == 0 {
            DEFAULT_MAX_RESTARTS_PER_WINDOW
        } else {
            max_per_window
        };
        Self {
            supervisor_pid,
            foreground_agent_pid,
            has_resume_snapshot,
            restart_epoch: 0,
            window_start_ms: 0,
            window_duration_ms,
            window_count: 0,
            max_per_window: cap,
        }
    }

    #[must_use]
    pub const fn restart_epoch(&self) -> u64 {
        self.restart_epoch
    }

    #[must_use]
    pub const fn window_count(&self) -> u64 {
        self.window_count
    }

    /// Update the supervised foreground PID after a successful respawn.
    pub fn set_foreground_agent(&mut self, new_agent_pid: u64, has_resume_snapshot: bool) {
        self.foreground_agent_pid = new_agent_pid;
        self.has_resume_snapshot = has_resume_snapshot;
    }

    /// Validate and authorize a self-restart request (`requested_pid = None` defaults to foreground PID).
    pub fn validate_restart(
        &mut self,
        requested_pid: Option<u64>,
        now_ms: u64,
    ) -> Result<u64, RestartRefusal> {
        let target = match requested_pid {
            Some(p) => p,
            None => self.foreground_agent_pid,
        };
        if target == 0 || self.supervisor_pid == 0 {
            return Err(RestartRefusal::ZeroOrInvalidPid);
        }
        if !restart_pid_distinct_from_sup(self.supervisor_pid, target) {
            return Err(RestartRefusal::TargetIsSupervisorHost {
                supervisor_pid: self.supervisor_pid,
            });
        }
        if target != self.foreground_agent_pid {
            return Err(RestartRefusal::ForegroundPidMismatch {
                expected_agent_pid: self.foreground_agent_pid,
                requested_pid: target,
            });
        }
        if !self.has_resume_snapshot {
            return Err(RestartRefusal::MissingResumeSnapshot);
        }

        if now_ms.saturating_sub(self.window_start_ms) >= self.window_duration_ms {
            self.window_start_ms = now_ms;
            self.window_count = 0;
        }
        if self.window_count >= self.max_per_window {
            return Err(RestartRefusal::RateLimitExceeded {
                max_per_window: self.max_per_window,
            });
        }

        let cand_cnt = self.window_count.saturating_add(1);
        self.window_count = restart_window_clamp(cand_cnt, self.max_per_window);
        let cand_ep = self.restart_epoch.saturating_add(1);
        self.restart_epoch = restart_epoch_advance_b92(self.restart_epoch, cand_ep);
        Ok(self.restart_epoch)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_supervisor_pid_and_enforces_foreground_match_and_rate_cap() {
        let mut val = SupervisorRestartValidator::new(1000, 2050, true, 60_000, 2);

        // Passing supervisor=1000 as pid=1000 MUST be refused with explicit reason!
        assert_eq!(
            val.validate_restart(Some(1000), 5_000),
            Err(RestartRefusal::TargetIsSupervisorHost {
                supervisor_pid: 1000,
            })
        );
        // Wrong PID refused
        assert_eq!(
            val.validate_restart(Some(9999), 5_000),
            Err(RestartRefusal::ForegroundPidMismatch {
                expected_agent_pid: 2050,
                requested_pid: 9999,
            })
        );
        // Valid foreground agent restart succeeds!
        assert_eq!(val.validate_restart(Some(2050), 5_000), Ok(1));
        val.set_foreground_agent(3010, true);
        assert_eq!(val.validate_restart(None, 10_000), Ok(2));

        // 3rd restart inside 60s window hits rate limit
        val.set_foreground_agent(3020, true);
        assert_eq!(
            val.validate_restart(Some(3020), 20_000),
            Err(RestartRefusal::RateLimitExceeded { max_per_window: 2 })
        );
        // After 60s window rolls over, restart succeeds again
        assert_eq!(val.validate_restart(Some(3020), 70_000), Ok(3));
    }
}
