// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Edge-triggered `aterm ctl await task @<sid>:<rev>` wakeup gate
//! (`Astream.Agent.TlaAwaitTaskRevGate`).
//!
//! Models multi-worker supervision (`aterm ctl await task @<sid>,... since=0` and
//! subsequent `@<sid>:<rev>` waits): wakes the parent immediately ONLY when at least
//! one watched worker is in a terminal/actionable state (`Landed`, `Exited`,
//! `Stalled`, `NeedsPerson`) AT a revision strictly newer than its recorded `since_rev`.

#[cfg(clean_islands)]
#[path = "await_task_rev_gate_island.rs"]
mod await_task_rev_gate_island;
#[cfg(clean_islands)]
pub use await_task_rev_gate_island::{await_rev_advance, await_targets_clamp};

/// Maximum sibling worker sessions watched in a single `await task` set.
pub const MAX_AWAIT_TARGETS: usize = 64;

#[cfg(not(clean_islands))]
/// Monotonically advance a watched worker's acknowledged revision cursor.
#[must_use]
pub const fn await_rev_advance(cur_rev: u64, cand_rev: u64) -> u64 {
    if cur_rev < cand_rev {
        cand_rev
    } else {
        cur_rev
    }
}

#[cfg(not(clean_islands))]
/// Clamp watched worker count to `max_targets`.
#[must_use]
pub const fn await_targets_clamp(cand_targets: u64, max_targets: u64) -> u64 {
    if cand_targets < max_targets {
        cand_targets
    } else {
        max_targets
    }
}

contract_fn! {
    /// True iff `current_rev` is strictly newer than `since_rev`.
    #[must_use]
    pub const fn await_rev_unseen(since_rev: u64, current_rev: u64) -> bool
    clauses [ensures result == (since_rev < current_rev)]
    {
        since_rev < current_rev
    }
}

/// Worker lifecycle states evaluated by `aterm ctl await task`.
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
    pub const fn triggers_await(self) -> bool {
        !matches!(self, Self::Running)
    }
}

/// Per-worker watch entry (`@<sid>:<since_rev>`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WatchedWorker {
    pub sid: u64,
    pub since_rev: u64,
}

/// Live status snapshot of a worker session.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WorkerLiveSnapshot {
    pub sid: u64,
    pub rev: u64,
    pub state: WorkerTaskState,
}

/// Wakeup event returned to the parent orchestrator with the updated `@<sid>:<rev>` cursor.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AwaitWakeEvent {
    pub sid: u64,
    pub new_rev: u64,
    pub state: WorkerTaskState,
}

/// Bounded `@<sid>:<rev>` watch set for `await task`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AwaitTaskRevGate {
    targets: Vec<WatchedWorker>,
}

impl Default for AwaitTaskRevGate {
    fn default() -> Self {
        Self::new()
    }
}

impl AwaitTaskRevGate {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            targets: Vec::new(),
        }
    }

    #[must_use]
    pub fn target_count(&self) -> usize {
        await_targets_clamp(self.targets.len() as u64, MAX_AWAIT_TARGETS as u64) as usize
    }

    /// Register or advance `@<sid>:<since_rev>` in the watch set (`false` if full).
    pub fn watch(&mut self, sid: u64, since_rev: u64) -> bool {
        for entry in &mut self.targets {
            if entry.sid == sid {
                entry.since_rev = await_rev_advance(entry.since_rev, since_rev);
                return true;
            }
        }
        if self.targets.len() >= MAX_AWAIT_TARGETS {
            return false;
        }
        self.targets.push(WatchedWorker { sid, since_rev });
        true
    }

    /// Poll `snapshots`: if any watched worker has `state.triggers_await()` at `rev > since_rev`,
    /// advance that worker's `since_rev` cursor to `rev` and return the edge-triggered wakeup.
    pub fn poll_wakeup(&mut self, snapshots: &[WorkerLiveSnapshot]) -> Option<AwaitWakeEvent> {
        for snap in snapshots {
            if snap.state.triggers_await() {
                for target in &mut self.targets {
                    if target.sid == snap.sid && await_rev_unseen(target.since_rev, snap.rev) {
                        target.since_rev = await_rev_advance(target.since_rev, snap.rev);
                        return Some(AwaitWakeEvent {
                            sid: snap.sid,
                            new_rev: target.since_rev,
                            state: snap.state,
                        });
                    }
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fires_once_per_new_revision_and_never_busy_loops_on_same_rev() {
        let mut gate = AwaitTaskRevGate::new();
        assert!(gate.watch(10, 0));
        assert!(gate.watch(20, 0));

        // Both running at rev 1 -> no wakeup
        let running = [
            WorkerLiveSnapshot {
                sid: 10,
                rev: 1,
                state: WorkerTaskState::Running,
            },
            WorkerLiveSnapshot {
                sid: 20,
                rev: 1,
                state: WorkerTaskState::Running,
            },
        ];
        assert_eq!(gate.poll_wakeup(&running), None);

        // Worker 20 stalls at rev 2 -> wakes once and advances @20:2!
        let stalled = [
            WorkerLiveSnapshot {
                sid: 10,
                rev: 1,
                state: WorkerTaskState::Running,
            },
            WorkerLiveSnapshot {
                sid: 20,
                rev: 2,
                state: WorkerTaskState::Stalled,
            },
        ];
        assert_eq!(
            gate.poll_wakeup(&stalled),
            Some(AwaitWakeEvent {
                sid: 20,
                new_rev: 2,
                state: WorkerTaskState::Stalled,
            })
        );
        // Re-polling at rev 2 does NOT re-fire!
        assert_eq!(gate.poll_wakeup(&stalled), None);

        // Worker 20 lands at rev 3 -> fires again with @20:3!
        let landed = [WorkerLiveSnapshot {
            sid: 20,
            rev: 3,
            state: WorkerTaskState::Landed,
        }];
        assert_eq!(
            gate.poll_wakeup(&landed),
            Some(AwaitWakeEvent {
                sid: 20,
                new_rev: 3,
                state: WorkerTaskState::Landed,
            })
        );
    }
}
