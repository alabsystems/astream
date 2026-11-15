// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Revision-fenced worker wakeup matcher for `aterm ctl await task @<sid>:<rev>` exiting as soon
//! as a worker reaches `Done`, `Exited`, `Stalled`, or `NeedsPerson` strictly past `since_rev`
//! (`Astream.Autopilot.TlaWorkerAwaitRev`).

#[cfg(clean_islands)]
#[path = "worker_await_rev_island.rs"]
mod worker_await_rev_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ap_workers_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ap_rev_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use worker_await_rev_island::{ap_rev_advance, ap_workers_clamp};

/// Maximum peer `@<sid>` workers awaited in a single `await task` call.
pub const MAX_AWAITED_WORKERS: u64 = 64;

contract_fn! {
    /// Verified revision advance (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ap_rev_advanced_isl`.
    #[must_use]
    pub const fn ap_rev_advanced(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WorkerTaskPhase {
    Running,
    DoneLanded,
    Exited,
    Stalled,
    NeedsPerson,
}

impl WorkerTaskPhase {
    #[must_use]
    pub const fn is_terminal_or_actionable(self) -> bool {
        !matches!(self, Self::Running)
    }
}

/// Evaluates `@<sid>:<since_rev>` wakeup readiness across spawned worker tabs.
#[derive(Debug, Clone, Default)]
pub struct WorkerAwaitMatcher {
    high_rev: u64,
}

impl WorkerAwaitMatcher {
    #[must_use]
    pub const fn new() -> Self {
        Self { high_rev: 0 }
    }

    pub fn poll_workers(
        &mut self,
        targets: &[(u64, u64, u64, WorkerTaskPhase)],
    ) -> Option<(u64, u64)> {
        let lim = ap_workers_clamp(targets.len() as u64, MAX_AWAITED_WORKERS) as usize;
        let mut idx = 0usize;
        while idx < lim {
            let Some(&(sid, since_rev, cur_rev, phase)) = targets.get(idx) else {
                break;
            };
            self.high_rev = ap_rev_advance(self.high_rev, cur_rev);
            if phase.is_terminal_or_actionable()
                && ap_rev_advanced(cur_rev, since_rev.saturating_add(1))
            {
                return Some((sid, cur_rev));
            }
            idx = idx.saturating_add(1);
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn worker_matcher_wakes_only_when_actionable_state_exceeds_since_rev() {
        let mut m = WorkerAwaitMatcher::new();
        assert_eq!(
            m.poll_workers(&[
                (2, 5, 5, WorkerTaskPhase::DoneLanded),
                (3, 0, 4, WorkerTaskPhase::Running),
            ]),
            None
        );
        assert_eq!(
            m.poll_workers(&[(2, 5, 6, WorkerTaskPhase::DoneLanded)]),
            Some((2, 6))
        );
    }
}
