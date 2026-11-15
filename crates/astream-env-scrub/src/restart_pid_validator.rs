// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Supervised foreground agent validator for `aterm ctl @self restart pid=<agent-pid>` ensuring
//! `pid` names the supervised foreground agent rather than `supervisor=` (`aterm`'s host)
//! (`Astream.EnvScrub.TlaRestartPidValidator`).

#[cfg(clean_islands)]
#[path = "restart_pid_validator_island.rs"]
mod restart_pid_validator_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn rst_procs_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn rst_epoch_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use restart_pid_validator_island::{rst_epoch_advance, rst_procs_clamp};

/// Maximum foreground process candidates inspected in a session process group.
pub const MAX_SESSION_PROCS: u64 = 64;

contract_fn! {
    /// Verified foreground-match predicate (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `rst_pid_matches_fg_isl`.
    #[must_use]
    pub const fn rst_pid_matches_fg(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Validates `aterm ctl @self restart pid=<candidate>` before ending the current agent process.
#[derive(Debug, Clone)]
pub struct AgentRestartValidator {
    supervisor_pid: u64,
    foreground_agent_pid: u64,
    restart_epoch: u64,
}

impl AgentRestartValidator {
    #[must_use]
    pub const fn new(supervisor_pid: u64, foreground_agent_pid: u64) -> Self {
        Self {
            supervisor_pid,
            foreground_agent_pid,
            restart_epoch: 0,
        }
    }

    pub fn validate_restart_target(&mut self, candidate_pid: u64) -> Result<u64, &'static str> {
        let _ = rst_procs_clamp(2, MAX_SESSION_PROCS);
        if candidate_pid == 0
            || self.foreground_agent_pid == 0
            || self.supervisor_pid == self.foreground_agent_pid
        {
            return Err("refused: invalid or ambiguous pid configuration");
        }
        if candidate_pid == self.supervisor_pid {
            return Err("refused: pid names aterm's host supervisor=, not the foreground agent");
        }
        let matches = if candidate_pid == self.foreground_agent_pid {
            1u64
        } else {
            0u64
        };
        if !rst_pid_matches_fg(matches, 1) {
            return Err("refused: pid does not match supervised foreground agent process");
        }
        self.restart_epoch =
            rst_epoch_advance(self.restart_epoch, self.restart_epoch.saturating_add(1));
        Ok(self.restart_epoch)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn restart_validator_refuses_host_supervisor_pid_and_accepts_foreground_agent_pid() {
        let mut v = AgentRestartValidator::new(1001, 2048);
        assert!(v.validate_restart_target(1001).is_err());
        assert!(v.validate_restart_target(9999).is_err());
        assert_eq!(v.validate_restart_target(2048).unwrap(), 1);
    }
}
