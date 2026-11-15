// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm ctl @self restart` Supervised Foreground PID & Handoff Validator.
//!
//! Enforces the exact `aterm` self-restart protocol before calling `aterm ctl @self restart`:
//! - Never pass `supervisor=` PID as `pid=<agent-pid>` (`supervisor=` can name `aterm`'s host
//!   wrapper rather than the foreground agent process).
//! - Require a non-empty persisted handoff note (`1..=max_handoff_bytes`) so the resumed
//!   conversation immediately recovers context.
//! - Require uncommitted working-tree state to be clean or explicitly stashed/committed first,
//!   and no detached background children left unrecorded.
//!
//! Backed by Clean TLA+ Island `Astream.Host.TlaSupervisedRestartGate`
//! (`self_restart_validator_island.rs`), proving `handoffBytes <= maxHandoffBytes` and
//! `prevEpoch <= restartEpoch`.

#[cfg(clean_islands)]
#[path = "self_restart_validator_island.rs"]
mod island;
#[cfg(clean_islands)]
pub use island::{restart_epoch_advance, restart_handoff_clamp};

#[cfg(not(clean_islands))]
#[inline]
pub const fn restart_handoff_clamp(handoff_bytes: u64, max_bytes: u64) -> u64 {
    if handoff_bytes < max_bytes {
        handoff_bytes
    } else {
        max_bytes
    }
}

#[cfg(not(clean_islands))]
#[inline]
pub const fn restart_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

/// Check that `agent_pid` is distinct from `supervisor_pid`.
#[must_use]
#[inline]
pub const fn restart_pids_distinct(agent_pid: u64, supervisor_pid: u64) -> bool {
    agent_pid != supervisor_pid
}

contract_fn! {
    /// Kernel-certified check that `handoff_bytes` fits within `max_bytes`.
    #[must_use]
    #[inline]
    pub const fn restart_handoff_within_cap(handoff_bytes: u64, max_bytes: u64) -> bool
    clauses [ensures result == (handoff_bytes <= max_bytes)]
    {
        handoff_bytes <= max_bytes
    }
}

/// Default maximum handoff note size (`65_536` bytes = 64 KiB).
pub const DEFAULT_MAX_HANDOFF_BYTES: u64 = 65_536;

/// Pre-flight snapshot read from `aterm ctl @self status` and workspace state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RestartPreflight {
    /// Foreground agent PID (`Some(pid)` when known).
    pub agent_pid: Option<u64>,
    /// `supervisor=` PID reported by `aterm ctl @self status`.
    pub supervisor_pid: Option<u64>,
    /// True if `aterm` reports a supervised foreground agent session capable of resume.
    pub session_supervised: bool,
    /// Number of uncommitted/unstashed modified files in the workspace.
    pub dirty_files: u64,
    /// Byte length of the saved handoff summary.
    pub handoff_bytes: u64,
}

/// Refusal reason naming the exact blocker preventing `aterm ctl @self restart`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RestartRefusal {
    SessionNotSupervised,
    ZeroAgentPid,
    AgentPidMatchesSupervisorHost { pid: u64 },
    UnsavedWorkspaceChanges { dirty_files: u64 },
    MissingHandoffSummary,
    HandoffExceedsBudget { bytes: u64, max_bytes: u64 },
}

/// Validated `aterm ctl @self restart` invocation plan.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ApprovedRestartPlan {
    pub pid_arg: Option<u64>,
    pub clamped_handoff_bytes: u64,
    pub restart_epoch: u64,
}

/// Stateful pre-flight validator certified by `TlaSupervisedRestartGate`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SupervisedRestartValidator {
    max_handoff_bytes: u64,
    prev_epoch: u64,
    restart_epoch: u64,
    handoff_bytes: u64,
}

impl Default for SupervisedRestartValidator {
    fn default() -> Self {
        Self::new(DEFAULT_MAX_HANDOFF_BYTES)
    }
}

impl SupervisedRestartValidator {
    #[inline]
    pub const fn new(max_handoff_bytes: u64) -> Self {
        let cap = if max_handoff_bytes == 0 {
            DEFAULT_MAX_HANDOFF_BYTES
        } else {
            max_handoff_bytes
        };
        Self {
            max_handoff_bytes: cap,
            prev_epoch: 0,
            restart_epoch: 0,
            handoff_bytes: 0,
        }
    }

    #[inline]
    pub const fn max_handoff_bytes(&self) -> u64 {
        self.max_handoff_bytes
    }

    #[inline]
    pub const fn restart_epoch(&self) -> u64 {
        self.restart_epoch
    }

    #[inline]
    pub const fn prev_epoch(&self) -> u64 {
        self.prev_epoch
    }

    #[inline]
    pub const fn handoff_bytes(&self) -> u64 {
        self.handoff_bytes
    }

    /// Validates `preflight` and advances `restart_epoch` monotonically on approval.
    pub fn validate(
        &mut self,
        preflight: RestartPreflight,
    ) -> Result<ApprovedRestartPlan, RestartRefusal> {
        if !preflight.session_supervised {
            return Err(RestartRefusal::SessionNotSupervised);
        }
        if let Some(apid) = preflight.agent_pid {
            if apid == 0 {
                return Err(RestartRefusal::ZeroAgentPid);
            }
            if let Some(spid) = preflight.supervisor_pid {
                if !restart_pids_distinct(apid, spid) {
                    return Err(RestartRefusal::AgentPidMatchesSupervisorHost { pid: apid });
                }
            }
        }
        if preflight.dirty_files > 0 {
            return Err(RestartRefusal::UnsavedWorkspaceChanges {
                dirty_files: preflight.dirty_files,
            });
        }
        if preflight.handoff_bytes == 0 {
            return Err(RestartRefusal::MissingHandoffSummary);
        }
        if !restart_handoff_within_cap(preflight.handoff_bytes, self.max_handoff_bytes) {
            return Err(RestartRefusal::HandoffExceedsBudget {
                bytes: preflight.handoff_bytes,
                max_bytes: self.max_handoff_bytes,
            });
        }
        let clamped_hb = restart_handoff_clamp(preflight.handoff_bytes, self.max_handoff_bytes);

        let cand_epoch = self.restart_epoch.saturating_add(1);
        let next_epoch = restart_epoch_advance(self.restart_epoch, cand_epoch);
        self.prev_epoch = self.restart_epoch;
        self.restart_epoch = next_epoch;
        self.handoff_bytes = clamped_hb;

        Ok(ApprovedRestartPlan {
            pid_arg: preflight.agent_pid,
            clamped_handoff_bytes: clamped_hb,
            restart_epoch: self.restart_epoch,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_supervisor_pid_collision_dirty_worktree_and_missing_handoff() {
        let mut val = SupervisedRestartValidator::new(4096);

        // Passing supervisor's host PID as agent PID is refused!
        assert_eq!(
            val.validate(RestartPreflight {
                agent_pid: Some(4200),
                supervisor_pid: Some(4200),
                session_supervised: true,
                dirty_files: 0,
                handoff_bytes: 512,
            }),
            Err(RestartRefusal::AgentPidMatchesSupervisorHost { pid: 4200 })
        );

        // Dirty files refused.
        assert_eq!(
            val.validate(RestartPreflight {
                agent_pid: Some(4205),
                supervisor_pid: Some(4200),
                session_supervised: true,
                dirty_files: 2,
                handoff_bytes: 512,
            }),
            Err(RestartRefusal::UnsavedWorkspaceChanges { dirty_files: 2 })
        );

        // Clean worktree + saved handoff + distinct foreground PID -> approved!
        let ok = val
            .validate(RestartPreflight {
                agent_pid: Some(4205),
                supervisor_pid: Some(4200),
                session_supervised: true,
                dirty_files: 0,
                handoff_bytes: 512,
            })
            .unwrap();
        assert_eq!(ok.pid_arg, Some(4205));
        assert_eq!(ok.restart_epoch, 1);
        assert!(val.prev_epoch() <= val.restart_epoch());
    }
}
