// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Multi-worker `aterm ctl @self spawn` + `aterm ctl await task @<sid>:<rev>`
//! fleet coordinator (`Astream.Agent.TlaWorkerSpawnRevTracker`).
//!
//! Tracks up to 8 spawned Autopilot Land workers (`Claude Code`, `codex-alab`,
//! `agy`, `Muse Code`) on the stack, advancing per-worker `acked_rev <= live_rev`
//! watermarks so subsequent `await task @<sid>:<rev>` calls never miss an exit,
//! stall, landed result, or `NEEDS YOU` transition, and never spin on an already
//! consumed revision.

#[cfg(clean_islands)]
#[path = "worker_spawn_rev_tracker_island.rs"]
mod worker_spawn_rev_tracker_island;
#[cfg(clean_islands)]
pub use worker_spawn_rev_tracker_island::{worker_ack_clamp, worker_rev_advance_b100};

/// Maximum concurrent spawned Autopilot Land workers tracked in stack table (`8`).
pub const MAX_TRACKED_WORKERS: usize = 8;

#[cfg(not(clean_islands))]
/// Monotonically advance a worker's live revision counter.
#[must_use]
pub const fn worker_rev_advance_b100(cur_rev: u64, cand_rev: u64) -> u64 {
    if cur_rev < cand_rev {
        cand_rev
    } else {
        cur_rev
    }
}

#[cfg(not(clean_islands))]
/// Clamp acknowledged `since=<rev>` cursor so `acked_rev <= live_rev`.
#[must_use]
pub const fn worker_ack_clamp(cand_ack: u64, live_rev: u64) -> u64 {
    if cand_ack < live_rev {
        cand_ack
    } else {
        live_rev
    }
}

contract_fn! {
    /// True iff `acked_rev < live_rev` (worker has an unconsumed state transition).
    #[must_use]
    pub const fn worker_has_event(acked_rev: u64, live_rev: u64) -> bool
    clauses [ensures result == (acked_rev < live_rev)]
    {
        acked_rev < live_rev
    }
}

/// Lifecycle state reported by `aterm ctl await task` / `aterm ctl @<sid> result`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WorkerTaskState {
    Running,
    Landed,
    Exited,
    Stalled,
    NeedsPerson,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct WorkerSlot {
    sid_tag: u64,
    acked_rev: u64,
    live_rev: u64,
    state: WorkerTaskState,
}

impl WorkerSlot {
    const EMPTY: Self = Self {
        sid_tag: 0,
        acked_rev: 0,
        live_rev: 0,
        state: WorkerTaskState::Running,
    };
}

/// Errors when registering or updating a spawned worker slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WorkerTrackerError {
    ZeroSessionId,
    TableFull,
    UnknownSessionId,
}

/// Stack 8-worker revision tracker for `aterm ctl await task @<sid>:<rev>`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WorkerSpawnRevTracker {
    slots: [WorkerSlot; MAX_TRACKED_WORKERS],
    active_count: usize,
}

impl Default for WorkerSpawnRevTracker {
    fn default() -> Self {
        Self::new()
    }
}

impl WorkerSpawnRevTracker {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            slots: [WorkerSlot::EMPTY; MAX_TRACKED_WORKERS],
            active_count: 0,
        }
    }

    #[must_use]
    pub const fn active_count(&self) -> usize {
        self.active_count
    }

    /// Register a newly spawned worker (`since=0`).
    pub fn register_spawn(&mut self, sid_tag: u64) -> Result<(), WorkerTrackerError> {
        if sid_tag == 0 {
            return Err(WorkerTrackerError::ZeroSessionId);
        }
        for slot in &mut self.slots {
            if slot.sid_tag == sid_tag {
                slot.acked_rev = 0;
                slot.live_rev = 0;
                slot.state = WorkerTaskState::Running;
                return Ok(());
            }
        }
        for slot in &mut self.slots {
            if slot.sid_tag == 0 {
                *slot = WorkerSlot {
                    sid_tag,
                    acked_rev: 0,
                    live_rev: 0,
                    state: WorkerTaskState::Running,
                };
                self.active_count = self.active_count.saturating_add(1);
                return Ok(());
            }
        }
        Err(WorkerTrackerError::TableFull)
    }

    /// Record a worker state transition at `new_rev`.
    pub fn record_transition(
        &mut self,
        sid_tag: u64,
        new_rev: u64,
        new_state: WorkerTaskState,
    ) -> Result<u64, WorkerTrackerError> {
        for slot in &mut self.slots {
            if slot.sid_tag == sid_tag && sid_tag != 0 {
                slot.live_rev = worker_rev_advance_b100(slot.live_rev, new_rev);
                slot.acked_rev = worker_ack_clamp(slot.acked_rev, slot.live_rev);
                slot.state = new_state;
                return Ok(slot.live_rev);
            }
        }
        Err(WorkerTrackerError::UnknownSessionId)
    }

    /// Consume the next unacknowledged worker wakeup (`(sid_tag, new_acked_rev, state)`).
    pub fn poll_ready(&mut self) -> Option<(u64, u64, WorkerTaskState)> {
        for slot in &mut self.slots {
            if slot.sid_tag != 0 && worker_has_event(slot.acked_rev, slot.live_rev) {
                let next_ack = worker_rev_advance_b100(slot.acked_rev, slot.live_rev);
                slot.acked_rev = worker_ack_clamp(next_ack, slot.live_rev);
                return Some((slot.sid_tag, slot.acked_rev, slot.state));
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn delivers_each_worker_revision_once_and_preserves_since_cursor() {
        let mut tracker = WorkerSpawnRevTracker::new();
        tracker.register_spawn(101).unwrap();
        tracker.register_spawn(202).unwrap();
        assert_eq!(tracker.poll_ready(), None);

        tracker
            .record_transition(202, 3, WorkerTaskState::NeedsPerson)
            .unwrap();
        assert_eq!(
            tracker.poll_ready(),
            Some((202, 3, WorkerTaskState::NeedsPerson))
        );
        // Same rev `3` never re-fires!
        assert_eq!(tracker.poll_ready(), None);

        // Next rev `4` (`Landed`) wakes cleanly:
        tracker
            .record_transition(202, 4, WorkerTaskState::Landed)
            .unwrap();
        assert_eq!(
            tracker.poll_ready(),
            Some((202, 4, WorkerTaskState::Landed))
        );
    }
}
