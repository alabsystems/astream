// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Supervised foreground PID disambiguator (`aterm` primer: *"add `pid=<agent-pid>` when known;
//! `supervisor=` can name aterm's host, not the agent"*) rejecting `@self restart` calls that pass
//! the supervisor host PID as `pid=` (`Astream.SelfRst.TlaSupervisorVsAgentPid`).

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
#[path = "supervisor_vs_agent_pid_island.rs"]
mod supervisor_vs_agent_pid_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sr_pid_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sr_val_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use supervisor_vs_agent_pid_island::{sr_pid_clamp, sr_val_advance};

/// Maximum POSIX PID (`4_194_304`).
pub const MAX_AGENT_PID: u64 = 4_194_304;

contract_fn! {
    /// Verified distinct valid agent PID (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sr_pid_distinct_isl`.
    #[must_use]
    pub const fn sr_pid_distinct(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct RestartPidDisambiguator {
    validations: u64,
}

impl RestartPidDisambiguator {
    #[must_use]
    pub const fn new() -> Self {
        Self { validations: 0 }
    }

    pub fn validate_agent_pid(&mut self, agent_pid: u64, supervisor_pid: u64) -> bool {
        self.validations = sr_val_advance(self.validations, self.validations.saturating_add(1));
        if agent_pid > MAX_AGENT_PID || supervisor_pid > MAX_AGENT_PID || supervisor_pid == 0 {
            return false;
        }
        let a = sr_pid_clamp(agent_pid, MAX_AGENT_PID);
        let s = sr_pid_clamp(supervisor_pid, MAX_AGENT_PID);
        let ok = a >= 2 && a != s;
        sr_pid_distinct(if ok { 1 } else { 0 }, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_supervisor_host_pid_and_accepts_distinct_foreground_agent_pid() {
        let mut d = RestartPidDisambiguator::new();
        assert!(!d.validate_agent_pid(800, 800));
        assert!(!d.validate_agent_pid(1, 800));
        assert!(d.validate_agent_pid(1420, 800));
    }
}
