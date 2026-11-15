// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm ctl @self restart pid=<agent-pid>` preflight checklist & PID-mismatch fence
//! (`Astream.Agent.TlaAtermSelfRestartHandoffFence`).
//!
//! Enforces the `aterm` self-restart protocol:
//! 1. Work saved & handoff persisted (`handoff_rev` monotonically advanced).
//! 2. `aterm ctl @self status` and `aterm ctl help restart` read in the current session.
//! 3. `agent_pid != 0` and `agent_pid != supervisor_host_pid` (`supervisor=` can name `aterm`'s
//!    host process rather than the supervised foreground agent!).

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "aterm_self_restart_handoff_fence_island.rs"]
mod aterm_self_restart_handoff_fence_island;
#[cfg(clean_islands)]
pub use aterm_self_restart_handoff_fence_island::{
    handoff_rev_advance_b109, restart_refusal_clamp_b109,
};

#[cfg(not(clean_islands))]
/// Clamp refused self-restart attempt count to `max_refusals`.
#[must_use]
pub const fn restart_refusal_clamp_b109(cand_refusals: u64, max_refusals: u64) -> u64 {
    if cand_refusals < max_refusals {
        cand_refusals
    } else {
        max_refusals
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the saved handoff revision before `aterm ctl @self restart`.
#[must_use]
pub const fn handoff_rev_advance_b109(cur_rev: u64, cand_rev: u64) -> u64 {
    if cur_rev < cand_rev {
        cand_rev
    } else {
        cur_rev
    }
}

contract_fn! {
    /// True iff `agent_pid` is non-zero and distinct from `supervisor_host_pid`.
    #[must_use]
    pub const fn restart_pid_distinct_from_supervisor_b109(
        agent_pid: u64,
        supervisor_host_pid: u64,
    ) -> bool
    clauses [ensures result == (0 < agent_pid && agent_pid != supervisor_host_pid)]
    {
        0 < agent_pid && agent_pid != supervisor_host_pid
    }
}

/// Verdict of validating a proposed `aterm ctl @self restart pid=<agent-pid>` invocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SelfRestartValidation {
    ReadyToExecRestart {
        agent_pid: u64,
        handoff_rev: u64,
    },
    RefusedWorkOrHandoffUnsaved,
    RefusedDocsUnread,
    RefusedInvalidOrSupervisorPid {
        proposed_pid: u64,
        supervisor_pid: u64,
    },
}

/// Stateful preflight validator for `aterm ctl @self restart`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AtermSelfRestartHandoffFence {
    work_and_handoff_saved: bool,
    status_read: bool,
    help_restart_read: bool,
    handoff_rev: u64,
    refusals: u64,
    max_refusals: u64,
}

impl AtermSelfRestartHandoffFence {
    #[must_use]
    pub const fn new(max_refusals: u64) -> Self {
        let cap = if max_refusals == 0 { 16 } else { max_refusals };
        Self {
            work_and_handoff_saved: false,
            status_read: false,
            help_restart_read: false,
            handoff_rev: 0,
            refusals: 0,
            max_refusals: cap,
        }
    }

    #[must_use]
    pub const fn refusals(&self) -> u64 {
        self.refusals
    }

    pub fn record_handoff_saved(&mut self, rev: u64) {
        let rev_floor = if rev > 1 { rev } else { 1 };
        self.handoff_rev = handoff_rev_advance_b109(self.handoff_rev, rev_floor);
        self.work_and_handoff_saved = true;
    }

    pub fn record_status_and_help_read(&mut self) {
        self.status_read = true;
        self.help_restart_read = true;
    }

    /// Validate all preconditions before running `aterm ctl @self restart pid=<agent_pid>`.
    pub fn validate_restart(
        &mut self,
        agent_pid: u64,
        supervisor_host_pid: u64,
    ) -> SelfRestartValidation {
        if !self.work_and_handoff_saved {
            let cand = self.refusals.saturating_add(1);
            self.refusals = restart_refusal_clamp_b109(cand, self.max_refusals);
            return SelfRestartValidation::RefusedWorkOrHandoffUnsaved;
        }
        if !self.status_read || !self.help_restart_read {
            let cand = self.refusals.saturating_add(1);
            self.refusals = restart_refusal_clamp_b109(cand, self.max_refusals);
            return SelfRestartValidation::RefusedDocsUnread;
        }
        if !restart_pid_distinct_from_supervisor_b109(agent_pid, supervisor_host_pid) {
            let cand = self.refusals.saturating_add(1);
            self.refusals = restart_refusal_clamp_b109(cand, self.max_refusals);
            return SelfRestartValidation::RefusedInvalidOrSupervisorPid {
                proposed_pid: agent_pid,
                supervisor_pid: supervisor_host_pid,
            };
        }
        SelfRestartValidation::ReadyToExecRestart {
            agent_pid,
            handoff_rev: self.handoff_rev,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_supervisor_pid_and_accepts_foreground_agent_pid_after_handoff() {
        let mut fence = AtermSelfRestartHandoffFence::new(8);
        fence.record_handoff_saved(3);
        fence.record_status_and_help_read();
        assert_eq!(
            fence.validate_restart(9000, 9000),
            SelfRestartValidation::RefusedInvalidOrSupervisorPid {
                proposed_pid: 9000,
                supervisor_pid: 9000,
            }
        );
        assert_eq!(
            fence.validate_restart(9412, 9000),
            SelfRestartValidation::ReadyToExecRestart {
                agent_pid: 9412,
                handoff_rev: 3,
            }
        );
    }
}
