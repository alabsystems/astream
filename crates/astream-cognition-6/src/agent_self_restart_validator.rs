// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm ctl @self restart [pid=<agent-pid>]` foreground-process & handoff validator
//! (`Astream.Host.TlaAgentSelfRestartValidator`).
//!
//! Validates supervised agent restarts (`aterm ctl @self restart`):
//! - Rejects targeting `supervisor_pid` (`supervisor=` names `aterm`'s host, not the agent!),
//! - Rejects PID mismatches against the supervised foreground agent process,
//! - Rejects restarts without a recorded resume snapshot (args + cwd + env within budget),
//! - Monotonically advances `restart_generation` on every validated self-restart.

#[cfg(clean_islands)]
#[path = "agent_self_restart_validator_island.rs"]
mod agent_self_restart_validator_island;
#[cfg(clean_islands)]
pub use agent_self_restart_validator_island::{
    restart_args_len_clamp_b120, restart_gen_advance_b120,
};

#[cfg(not(clean_islands))]
/// Clamp recorded launch-spec byte length to `max_len`.
#[must_use]
pub const fn restart_args_len_clamp_b120(cand_len: u64, max_len: u64) -> u64 {
    if cand_len < max_len {
        cand_len
    } else {
        max_len
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `restart_generation`.
#[must_use]
pub const fn restart_gen_advance_b120(cur_gen: u64, cand_gen: u64) -> u64 {
    if cur_gen < cand_gen {
        cand_gen
    } else {
        cur_gen
    }
}

contract_fn! {
    /// True iff `target_pid` matches `fg_pid`.
    #[must_use]
    pub const fn restart_pid_matches_fg_b120(target_pid: u64, fg_pid: u64) -> bool
    clauses [ensures result == (target_pid == fg_pid)]
    {
        target_pid == fg_pid
    }
}

pub const MAX_RECORDED_RESUME_BYTES: u64 = 65_536;

/// Explicit refusal or approval for `aterm ctl @self restart`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RestartValidation {
    Approved {
        agent_pid: u64,
        restart_generation: u64,
        resume_spec_bytes: u64,
    },
    RefusedNoForegroundAgent,
    RefusedTargetedSupervisorHost {
        supervisor_pid: u64,
    },
    RefusedPidMismatch {
        requested_pid: u64,
        foreground_pid: u64,
    },
    RefusedMissingResumeSnapshot,
    RefusedResumeSpecOverBudget {
        actual_bytes: u64,
        max_bytes: u64,
    },
}

/// Supervised foreground restart validator for `aterm ctl @self restart`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AgentSelfRestartValidator {
    supervisor_pid: u64,
    foreground_agent_pid: u64,
    resume_spec_bytes: u64,
    restart_generation: u64,
}

impl Default for AgentSelfRestartValidator {
    fn default() -> Self {
        Self::new(1, 0)
    }
}

impl AgentSelfRestartValidator {
    #[must_use]
    pub const fn new(supervisor_pid: u64, foreground_agent_pid: u64) -> Self {
        Self {
            supervisor_pid,
            foreground_agent_pid,
            resume_spec_bytes: 0,
            restart_generation: 0,
        }
    }

    #[must_use]
    pub const fn restart_generation(&self) -> u64 {
        self.restart_generation
    }

    pub fn record_supervised_launch(&mut self, agent_pid: u64, raw_resume_bytes: u64) -> bool {
        if agent_pid == 0 || agent_pid == self.supervisor_pid {
            return false;
        }
        if raw_resume_bytes == 0 || raw_resume_bytes > MAX_RECORDED_RESUME_BYTES {
            return false;
        }
        self.foreground_agent_pid = agent_pid;
        self.resume_spec_bytes =
            restart_args_len_clamp_b120(raw_resume_bytes, MAX_RECORDED_RESUME_BYTES);
        true
    }

    /// Validate `aterm ctl @self restart` with optional `explicit_pid` (`None` uses foreground PID).
    pub fn validate_restart(&mut self, explicit_pid: Option<u64>) -> RestartValidation {
        if self.foreground_agent_pid == 0 {
            return RestartValidation::RefusedNoForegroundAgent;
        }
        let target = match explicit_pid {
            Some(p) => p,
            None => self.foreground_agent_pid,
        };
        if target == self.supervisor_pid {
            return RestartValidation::RefusedTargetedSupervisorHost {
                supervisor_pid: self.supervisor_pid,
            };
        }
        if !restart_pid_matches_fg_b120(target, self.foreground_agent_pid) {
            return RestartValidation::RefusedPidMismatch {
                requested_pid: target,
                foreground_pid: self.foreground_agent_pid,
            };
        }
        if self.resume_spec_bytes == 0 {
            return RestartValidation::RefusedMissingResumeSnapshot;
        }
        if self.resume_spec_bytes > MAX_RECORDED_RESUME_BYTES {
            return RestartValidation::RefusedResumeSpecOverBudget {
                actual_bytes: self.resume_spec_bytes,
                max_bytes: MAX_RECORDED_RESUME_BYTES,
            };
        }
        let clamped_bytes =
            restart_args_len_clamp_b120(self.resume_spec_bytes, MAX_RECORDED_RESUME_BYTES);
        let next_gen = self.restart_generation.saturating_add(1);
        self.restart_generation = restart_gen_advance_b120(self.restart_generation, next_gen);
        RestartValidation::Approved {
            agent_pid: self.foreground_agent_pid,
            restart_generation: self.restart_generation,
            resume_spec_bytes: clamped_bytes,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_supervisor_pid_and_approves_matching_foreground_agent_pid() {
        let mut v = AgentSelfRestartValidator::new(4100, 0);
        assert!(v.record_supervised_launch(4299, 2048));
        assert_eq!(
            v.validate_restart(Some(4100)),
            RestartValidation::RefusedTargetedSupervisorHost {
                supervisor_pid: 4100
            }
        );
        assert_eq!(
            v.validate_restart(Some(9999)),
            RestartValidation::RefusedPidMismatch {
                requested_pid: 9999,
                foreground_pid: 4299
            }
        );
        assert_eq!(
            v.validate_restart(Some(4299)),
            RestartValidation::Approved {
                agent_pid: 4299,
                restart_generation: 1,
                resume_spec_bytes: 2048,
            }
        );
    }
}
