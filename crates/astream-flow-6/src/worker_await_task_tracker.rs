// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm ctl await task @<sid>:<rev>` worker swarm wakeup tracker
//! (`Astream.Agent.TlaWorkerAwaitTaskTracker`, Island #278).

#[cfg(clean_islands)]
#[path = "worker_await_task_tracker_island.rs"]
mod worker_await_task_tracker_island;
#[cfg(clean_islands)]
pub use worker_await_task_tracker_island::{await_tracker_rev_advance, await_tracker_watch_clamp};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn await_tracker_rev_advance(cur_rev: u64, next_rev: u64) -> u64 {
    if cur_rev < next_rev {
        next_rev
    } else {
        cur_rev
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn await_tracker_watch_clamp(count: u64, max_watched: u64) -> u64 {
    if count < max_watched {
        count
    } else {
        max_watched
    }
}

/// Maximum number of worker sessions watched in a single `await task` set (`64`).
pub const MAX_WATCHED_WORKERS: usize = 64;

/// State code `0`: worker is actively running and making progress.
pub const WORKER_STATE_RUNNING: u64 = 0;
/// State code `1`: worker's task landed cleanly.
pub const WORKER_STATE_LANDED: u64 = 1;
/// State code `2`: worker process exited.
pub const WORKER_STATE_EXITED: u64 = 2;
/// State code `3`: worker stalled without progress.
pub const WORKER_STATE_STALLED: u64 = 3;
/// State code `4`: worker raised a `NEEDS YOU:` item requiring a person.
pub const WORKER_STATE_NEEDS_PERSON: u64 = 4;

contract_fn! {
    /// Verified check that a worker revision strictly advanced past `since_rev` (`since_rev < cur_rev`),
    /// linked via `clean-kernel-defeq` to `worker_rev_advanced_isl`.
    #[must_use]
    pub const fn worker_rev_advanced(since_rev: u64, cur_rev: u64) -> bool
    clauses [ensures result == (since_rev < cur_rev)]
    {
        since_rev < cur_rev
    }
}

/// Check that a worker transitioned past `since_rev` into a non-running actionable state.
#[inline]
#[must_use]
pub const fn worker_event_is_wakeable(since_rev: u64, cur_rev: u64, state_code: u64) -> bool {
    worker_rev_advanced(since_rev, cur_rev) && state_code != 0
}

/// Typed worker lifecycle state surfaced by `aterm ctl await task`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WorkerTaskState {
    Running,
    Landed,
    Exited,
    Stalled,
    NeedsPerson,
}

impl WorkerTaskState {
    #[must_use]
    pub const fn code(self) -> u64 {
        match self {
            Self::Running => WORKER_STATE_RUNNING,
            Self::Landed => WORKER_STATE_LANDED,
            Self::Exited => WORKER_STATE_EXITED,
            Self::Stalled => WORKER_STATE_STALLED,
            Self::NeedsPerson => WORKER_STATE_NEEDS_PERSON,
        }
    }
}

/// Per-worker watch entry (`@<sid>:<since_rev>`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WorkerWatchSlot {
    pub sid: u64,
    pub since_rev: u64,
    pub cur_rev: u64,
    pub state: WorkerTaskState,
}

/// Wakeup notification returned by [`WorkerAwaitTracker::poll_ready`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WorkerWakeup {
    pub sid: u64,
    pub next_since_rev: u64,
    pub state: WorkerTaskState,
}

/// Bounded `@<sid>:<rev>` worker swarm await tracker.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WorkerAwaitTracker {
    slots: Vec<WorkerWatchSlot>,
}

impl Default for WorkerAwaitTracker {
    fn default() -> Self {
        Self::new()
    }
}

impl WorkerAwaitTracker {
    #[must_use]
    pub const fn new() -> Self {
        Self { slots: Vec::new() }
    }

    #[must_use]
    pub fn watched_count(&self) -> usize {
        await_tracker_watch_clamp(self.slots.len() as u64, MAX_WATCHED_WORKERS as u64) as usize
    }

    /// Register or update the `since_rev` cursor for worker `sid`.
    pub fn watch(&mut self, sid: u64, since_rev: u64) -> bool {
        for slot in &mut self.slots {
            if slot.sid == sid {
                slot.since_rev = since_rev;
                slot.cur_rev = await_tracker_rev_advance(slot.cur_rev, since_rev);
                return true;
            }
        }
        if self.slots.len() >= MAX_WATCHED_WORKERS {
            return false;
        }
        self.slots.push(WorkerWatchSlot {
            sid,
            since_rev,
            cur_rev: since_rev,
            state: WorkerTaskState::Running,
        });
        true
    }

    /// Record a worker state transition at `proposed_rev`.
    pub fn record_transition(
        &mut self,
        sid: u64,
        proposed_rev: u64,
        state: WorkerTaskState,
    ) -> bool {
        for slot in &mut self.slots {
            if slot.sid == sid {
                slot.cur_rev = await_tracker_rev_advance(slot.cur_rev, proposed_rev);
                slot.state = state;
                return true;
            }
        }
        false
    }

    /// Consume and return the first wakeable worker event, advancing its `since_rev` cursor
    /// to `cur_rev` so a subsequent `await task @<sid>:<cur_rev>` waits only for newer events.
    pub fn poll_ready(&mut self) -> Option<WorkerWakeup> {
        for slot in &mut self.slots {
            if worker_event_is_wakeable(slot.since_rev, slot.cur_rev, slot.state.code()) {
                slot.since_rev = slot.cur_rev;
                return Some(WorkerWakeup {
                    sid: slot.sid,
                    next_since_rev: slot.cur_rev,
                    state: slot.state,
                });
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn await_wakes_only_past_since_rev_on_actionable_state_and_advances_cursor() {
        let mut t = WorkerAwaitTracker::new();
        assert!(t.watch(101, 0));
        assert!(t.watch(102, 5));
        assert_eq!(t.watched_count(), 2);

        assert!(t.record_transition(101, 2, WorkerTaskState::Running));
        assert_eq!(t.poll_ready(), None);

        assert!(t.record_transition(102, 5, WorkerTaskState::Landed));
        assert_eq!(t.poll_ready(), None);

        assert!(t.record_transition(102, 6, WorkerTaskState::Landed));
        assert_eq!(
            t.poll_ready(),
            Some(WorkerWakeup {
                sid: 102,
                next_since_rev: 6,
                state: WorkerTaskState::Landed,
            })
        );
        assert_eq!(t.poll_ready(), None);

        assert!(t.record_transition(101, 3, WorkerTaskState::NeedsPerson));
        assert_eq!(
            t.poll_ready(),
            Some(WorkerWakeup {
                sid: 101,
                next_since_rev: 3,
                state: WorkerTaskState::NeedsPerson,
            })
        );
    }
}
