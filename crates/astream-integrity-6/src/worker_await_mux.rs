// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Multi-worker revision-watermarked task multiplexer (`aterm ctl await task @<sid>:<rev>,...`).
//!
//! Models the reactive wakeup and revision-cursor protocol used by `aterm` supervisors
//! waiting on spawned Claude Code / `codex-alab` / `agy` / Muse Code worker tabs:
//!
//! - Each watched worker `@<sid>` carries a per-session baseline `baseline_rev` (from
//!   `@<sid>:<rev>`, defaulting to `since_rev`) and its latest observed `(latest_rev, state)`.
//! - A worker triggers wakeup iff `worker_rev_is_unseen(effective_baseline, latest_rev)`
//!   AND `state.is_wakeup_state()` (`DoneLanded`, `Exited`, `Stalled`, or `NeedsPerson`).
//! - When `acknowledge_next_wakeup` fires, it advances both the session's `baseline_rev`
//!   and the mux's global `seen_rev` monotonically through Clean-origin
//!   [`worker_rev_advance`], returning the exact next `@<sid>:<latest_rev>` cursor token
//!   so subsequent `await task` calls never double-fire or drop intermediate events.
//! - Zero closures (`0 mandated`), backed by Clean TLA+ island `Astream.Agent.TlaWorkerAwaitMux`.

#[cfg(clean_islands)]
#[path = "worker_await_mux_island.rs"]
mod worker_await_mux_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn worker_rev_advance(cur_rev: u64, proposed_rev: u64) -> u64 {
    if cur_rev < proposed_rev {
        proposed_rev
    } else {
        cur_rev
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn worker_watch_count_clamp(count: u64, max_watched: u64) -> u64 {
    if count < max_watched {
        count
    } else {
        max_watched
    }
}
#[cfg(clean_islands)]
pub use worker_await_mux_island::{worker_rev_advance, worker_watch_count_clamp};

contract_fn! {
    /// Kernel-certified check that `latest_rev` strictly exceeds `seen_rev`
    /// (`seen_rev < latest_rev`), linked via `clean-kernel-defeq` to
    /// `worker_rev_is_unseen_isl`.
    #[must_use]
    pub const fn worker_rev_is_unseen(seen_rev: u64, latest_rev: u64) -> bool
    clauses [ensures result == (seen_rev < latest_rev)]
    {
        seen_rev < latest_rev
    }
}

/// Maximum number of concurrent worker sessions watched by a single [`WorkerAwaitMux`].
pub const MAX_WATCHED_WORKERS: usize = 128;

/// Lifecycle state of a supervised worker tab (`aterm ctl await task`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WorkerTaskState {
    /// Worker is actively running tools / generating output.
    Running,
    /// Worker completed its Autopilot Land task (`Nothing left:` verified on remote `main`).
    DoneLanded,
    /// Foreground agent process exited.
    Exited { exit_code: i32 },
    /// Worker stopped making progress past stall threshold (`sys jobs`).
    Stalled,
    /// Worker emitted a `NEEDS YOU:` item requiring human input/credentials.
    NeedsPerson,
}

impl WorkerTaskState {
    /// Returns `true` when this state wakes `aterm ctl await task`.
    #[must_use]
    pub const fn is_wakeup_state(self) -> bool {
        !matches!(self, Self::Running)
    }
}

/// Snapshot of a single watched worker slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WatchedWorker {
    /// Session numeric identifier (`@<sid>`).
    pub sid: u64,
    /// Per-session acknowledged revision (`@<sid>:<rev>`).
    pub baseline_rev: u64,
    /// Latest revision reported for `@<sid>`.
    pub latest_rev: u64,
    /// Latest lifecycle state reported for `@<sid>`.
    pub state: WorkerTaskState,
}

/// Wakeup event emitted by [`WorkerAwaitMux::acknowledge_next_wakeup`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WorkerWakeup {
    /// Session identifier (`@<sid>`) that triggered the wakeup.
    pub sid: u64,
    /// Revision at which the wakeup state was observed (pass `@<sid>:<revision>` next wait).
    pub revision: u64,
    /// Terminal / attention state that woke the waiter.
    pub state: WorkerTaskState,
    /// Updated global mux high-water revision (`since=<mux_seen_rev>`).
    pub mux_seen_rev: u64,
}

/// Error returned when registering or updating a watched worker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WorkerMuxError {
    /// `sid == 0` is reserved.
    ZeroSessionId,
    /// Watch table already holds [`MAX_WATCHED_WORKERS`] distinct sessions.
    WatchTableFull,
    /// Attempted to update an unregistered `sid`.
    UnknownSession { sid: u64 },
}

/// Deterministic revision-watermarked multiplexer for `aterm ctl await task`.
#[derive(Debug, Clone)]
pub struct WorkerAwaitMux {
    max_watched: usize,
    seen_rev: u64,
    latest_rev: u64,
    slots: Vec<WatchedWorker>,
}

impl Default for WorkerAwaitMux {
    fn default() -> Self {
        Self::new(0, MAX_WATCHED_WORKERS)
    }
}

impl WorkerAwaitMux {
    /// Construct a [`WorkerAwaitMux`] with initial `since_rev` and `max_watched` cap.
    #[must_use]
    pub fn new(since_rev: u64, max_watched: usize) -> Self {
        let clamped_cap =
            worker_watch_count_clamp(max_watched as u64, MAX_WATCHED_WORKERS as u64) as usize;
        Self {
            max_watched: if clamped_cap > 1 { clamped_cap } else { 1 },
            seen_rev: since_rev,
            latest_rev: since_rev,
            slots: Vec::new(),
        }
    }

    /// Global acknowledged revision watermark.
    #[must_use]
    pub const fn seen_rev(&self) -> u64 {
        self.seen_rev
    }

    /// Highest revision observed across any watched worker.
    #[must_use]
    pub const fn latest_rev(&self) -> u64 {
        self.latest_rev
    }

    /// Number of watched worker sessions (`<= max_watched`).
    #[must_use]
    pub fn watched_count(&self) -> usize {
        self.slots.len()
    }

    /// Register `@<sid>` (or raise its `baseline_rev` if already registered).
    pub fn watch(
        &mut self,
        sid: u64,
        session_since_rev: Option<u64>,
    ) -> Result<(), WorkerMuxError> {
        if sid == 0 {
            return Err(WorkerMuxError::ZeroSessionId);
        }
        let base = match session_since_rev {
            Some(r) => r,
            None => self.seen_rev,
        };
        let mut cur = self.slots.as_mut_slice();
        while let [slot, rest @ ..] = cur {
            if slot.sid == sid {
                slot.baseline_rev = worker_rev_advance(slot.baseline_rev, base);
                slot.latest_rev = worker_rev_advance(slot.latest_rev, slot.baseline_rev);
                self.latest_rev = worker_rev_advance(self.latest_rev, slot.latest_rev);
                return Ok(());
            }
            cur = rest;
        }
        let proposed_count = self.slots.len().saturating_add(1) as u64;
        if worker_watch_count_clamp(proposed_count, self.max_watched as u64) < proposed_count {
            return Err(WorkerMuxError::WatchTableFull);
        }
        self.latest_rev = worker_rev_advance(self.latest_rev, base);
        self.slots.push(WatchedWorker {
            sid,
            baseline_rev: base,
            latest_rev: base,
            state: WorkerTaskState::Running,
        });
        Ok(())
    }

    /// Record an observed `(revision, state)` transition on watched worker `@<sid>`.
    pub fn observe(
        &mut self,
        sid: u64,
        revision: u64,
        state: WorkerTaskState,
    ) -> Result<(), WorkerMuxError> {
        let mut cur = self.slots.as_mut_slice();
        while let [slot, rest @ ..] = cur {
            if slot.sid == sid {
                let next_rev = worker_rev_advance(slot.latest_rev, revision);
                if next_rev == revision {
                    slot.latest_rev = next_rev;
                    slot.state = state;
                }
                self.latest_rev = worker_rev_advance(self.latest_rev, slot.latest_rev);
                return Ok(());
            }
            cur = rest;
        }
        Err(WorkerMuxError::UnknownSession { sid })
    }

    /// Return `true` without mutating watermarks if at least one watched worker has an
    /// unseen wakeup transition ready.
    #[must_use]
    pub fn has_ready_wakeup(&self) -> bool {
        let mut cur = self.slots.as_slice();
        while let &[slot, ref rest @ ..] = cur {
            if slot.state.is_wakeup_state()
                && worker_rev_is_unseen(slot.baseline_rev, slot.latest_rev)
            {
                return true;
            }
            cur = rest;
        }
        false
    }

    /// Pop/acknowledge the earliest-registered ready worker wakeup, advancing its
    /// `baseline_rev` to `latest_rev` so the same revision never wakes twice.
    pub fn acknowledge_next_wakeup(&mut self) -> Option<WorkerWakeup> {
        let mut cur = self.slots.as_mut_slice();
        while let [slot, rest @ ..] = cur {
            if slot.state.is_wakeup_state()
                && worker_rev_is_unseen(slot.baseline_rev, slot.latest_rev)
            {
                let latest = slot.latest_rev;
                let st = slot.state;
                let id = slot.sid;
                slot.baseline_rev = latest;
                self.seen_rev = worker_rev_advance(self.seen_rev, latest);
                return Some(WorkerWakeup {
                    sid: id,
                    revision: latest,
                    state: st,
                    mux_seen_rev: self.seen_rev,
                });
            }
            cur = rest;
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn worker_mux_wakes_only_on_unseen_terminal_or_attention_revisions() {
        let mut mux = WorkerAwaitMux::new(10, 4);
        mux.watch(101, None).unwrap();
        mux.watch(102, Some(15)).unwrap();

        // Running updates advance `latest_rev` without firing wakeup.
        mux.observe(101, 12, WorkerTaskState::Running).unwrap();
        assert!(!mux.has_ready_wakeup());
        assert_eq!(mux.acknowledge_next_wakeup(), None);

        // Stale revision `<= baseline_rev` on `@102:15` does NOT wake!
        mux.observe(102, 15, WorkerTaskState::DoneLanded).unwrap();
        assert_eq!(mux.acknowledge_next_wakeup(), None);

        // `@101` hits `NeedsPerson` at rev 14 -> wakes once, then suppresses rev 14!
        mux.observe(101, 14, WorkerTaskState::NeedsPerson).unwrap();
        assert_eq!(
            mux.acknowledge_next_wakeup(),
            Some(WorkerWakeup {
                sid: 101,
                revision: 14,
                state: WorkerTaskState::NeedsPerson,
                mux_seen_rev: 14,
            })
        );
        assert_eq!(mux.acknowledge_next_wakeup(), None);

        // `@102` lands at rev 19 -> wakes with `DoneLanded` and advances `seen_rev` to 19!
        mux.observe(102, 19, WorkerTaskState::DoneLanded).unwrap();
        assert_eq!(
            mux.acknowledge_next_wakeup(),
            Some(WorkerWakeup {
                sid: 102,
                revision: 19,
                state: WorkerTaskState::DoneLanded,
                mux_seen_rev: 19,
            })
        );
        assert_eq!(mux.seen_rev(), 19);
        assert_eq!(mux.latest_rev(), 19);
    }
}
