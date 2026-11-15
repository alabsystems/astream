// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm ctl await task @<sid>:<rev>` multi-worker revision coordinator
//! (`Astream.Agent.TlaWorkerAwaitRevCoordinator`).
//!
//! Coordinates background `aterm ctl await task @<sid>,... since=<rev>` wakes across spawned
//! Autopilot Land workers (`aterm ctl @self spawn agent=claude -`): tracks up to 16 worker
//! sessions on the stack and triggers an immediate edge-triggered wake as soon as any worker's
//! `observed_rev > awaited_rev` with a terminal/attention state (`Done`, `Exited`, `Stalled`,
//! `NeedsPerson`).

#[cfg(clean_islands)]
#[path = "worker_await_rev_coordinator_island.rs"]
mod worker_await_rev_coordinator_island;
#[cfg(clean_islands)]
pub use worker_await_rev_coordinator_island::{
    worker_rev_advance_b118, worker_slot_count_clamp_b118,
};

#[cfg(not(clean_islands))]
/// Clamp registered worker slot count to `max_workers`.
#[must_use]
pub const fn worker_slot_count_clamp_b118(cand_workers: u64, max_workers: u64) -> u64 {
    if cand_workers < max_workers {
        cand_workers
    } else {
        max_workers
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance a worker's `observed_rev`.
#[must_use]
pub const fn worker_rev_advance_b118(cur_rev: u64, cand_rev: u64) -> u64 {
    if cur_rev < cand_rev {
        cand_rev
    } else {
        cur_rev
    }
}

contract_fn! {
    /// True iff `observed_rev` is strictly newer than `awaited_rev` (`since=<awaited_rev>`).
    #[must_use]
    pub const fn worker_has_unseen_rev_b118(awaited_rev: u64, observed_rev: u64) -> bool
    clauses [ensures result == (awaited_rev < observed_rev)]
    {
        awaited_rev < observed_rev
    }
}

pub const MAX_AWAITED_WORKERS: usize = 16;

/// Lifecycle state reported by `aterm ctl await task`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WorkerTaskState {
    Running,
    DoneLanded,
    Exited,
    Stalled,
    NeedsPerson,
}

impl WorkerTaskState {
    #[must_use]
    pub const fn wakes_supervisor(self) -> bool {
        !matches!(self, Self::Running)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct WorkerWatchSlot {
    active: bool,
    sid_hash: u64,
    awaited_rev: u64,
    observed_rev: u64,
    state: WorkerTaskState,
}

impl WorkerWatchSlot {
    const EMPTY: Self = Self {
        active: false,
        sid_hash: 0,
        awaited_rev: 0,
        observed_rev: 0,
        state: WorkerTaskState::Running,
    };
}

/// Event returned when a watched worker crosses `since=<rev>` into a wakeable state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WorkerWakeNotice {
    pub sid_hash: u64,
    pub observed_rev: u64,
    pub state: WorkerTaskState,
}

/// Stack-allocated coordinator for `aterm ctl await task @<sid>:<rev>`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WorkerAwaitRevCoordinator {
    slots: [WorkerWatchSlot; MAX_AWAITED_WORKERS],
    active_workers: u64,
}

impl Default for WorkerAwaitRevCoordinator {
    fn default() -> Self {
        Self::new()
    }
}

impl WorkerAwaitRevCoordinator {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            slots: [WorkerWatchSlot::EMPTY; MAX_AWAITED_WORKERS],
            active_workers: 0,
        }
    }

    #[must_use]
    pub const fn active_workers(&self) -> u64 {
        self.active_workers
    }

    /// Register or re-arm `@<sid>:<since_rev>` (`since=0` on initial spawn).
    pub fn watch_worker(&mut self, sid_hash: u64, since_rev: u64) -> bool {
        let mut idx = 0usize;
        let mut free_idx: Option<usize> = None;
        while let Some(slot) = self.slots.get_mut(idx) {
            if slot.active {
                if slot.sid_hash == sid_hash {
                    slot.awaited_rev = worker_rev_advance_b118(slot.awaited_rev, since_rev);
                    return true;
                }
            } else if free_idx.is_none() {
                free_idx = Some(idx);
            }
            idx = idx.saturating_add(1);
        }
        if let Some(target) = free_idx {
            if let Some(slot) = self.slots.get_mut(target) {
                *slot = WorkerWatchSlot {
                    active: true,
                    sid_hash,
                    awaited_rev: since_rev,
                    observed_rev: since_rev,
                    state: WorkerTaskState::Running,
                };
                let cand = self.active_workers.saturating_add(1);
                self.active_workers =
                    worker_slot_count_clamp_b118(cand, MAX_AWAITED_WORKERS as u64);
                return true;
            }
        }
        false
    }

    /// Ingest a status update `(rev, state)` for `sid_hash` and return a wake notice if ready.
    pub fn observe_worker_status(
        &mut self,
        sid_hash: u64,
        rev: u64,
        state: WorkerTaskState,
    ) -> Option<WorkerWakeNotice> {
        let mut idx = 0usize;
        while let Some(slot) = self.slots.get_mut(idx) {
            if slot.active && slot.sid_hash == sid_hash {
                slot.observed_rev = worker_rev_advance_b118(slot.observed_rev, rev);
                slot.state = state;
                if state.wakes_supervisor()
                    && worker_has_unseen_rev_b118(slot.awaited_rev, slot.observed_rev)
                {
                    slot.awaited_rev = slot.observed_rev;
                    return Some(WorkerWakeNotice {
                        sid_hash,
                        observed_rev: slot.observed_rev,
                        state,
                    });
                }
                return None;
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
    fn wakes_once_per_new_revision_and_rearms_cleanly() {
        let mut c = WorkerAwaitRevCoordinator::new();
        assert!(c.watch_worker(0x1234, 0));
        assert_eq!(
            c.observe_worker_status(0x1234, 1, WorkerTaskState::Running),
            None
        );
        assert_eq!(
            c.observe_worker_status(0x1234, 2, WorkerTaskState::DoneLanded),
            Some(WorkerWakeNotice {
                sid_hash: 0x1234,
                observed_rev: 2,
                state: WorkerTaskState::DoneLanded,
            })
        );
        // Duplicate delivery of rev=2 does not double-wake (`awaited_rev` advanced to 2):
        assert_eq!(
            c.observe_worker_status(0x1234, 2, WorkerTaskState::DoneLanded),
            None
        );
    }
}
