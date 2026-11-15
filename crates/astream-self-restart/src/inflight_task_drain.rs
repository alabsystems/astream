// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pre-restart background-task quiescence gate verifying `active_mutating_tasks == 0` so `@self
//! restart` never tears down a mid-flight `git push` or `targo` build (`Astream.SelfRst.TlaInflightTaskDrain`).

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
#[path = "inflight_task_drain_island.rs"]
mod inflight_task_drain_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sr_tasks_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sr_drain_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use inflight_task_drain_island::{sr_drain_advance, sr_tasks_clamp};

/// Maximum tracked background tasks (`128`).
pub const MAX_BG_TASKS: u64 = 128;

contract_fn! {
    /// Verified zero-active-task predicate (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `sr_tasks_quiesced_isl`.
    #[must_use]
    pub const fn sr_tasks_quiesced(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct InflightTaskDrain {
    active_tasks: u64,
    unbounded_active: u64,
    completed_tasks: u64,
}

impl InflightTaskDrain {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            active_tasks: 0,
            unbounded_active: 0,
            completed_tasks: 0,
        }
    }

    pub fn spawn_task(&mut self) {
        self.unbounded_active = self.unbounded_active.saturating_add(1);
        self.active_tasks = sr_tasks_clamp(self.unbounded_active, MAX_BG_TASKS);
    }

    pub fn finish_task(&mut self) {
        if self.unbounded_active > 0 {
            self.unbounded_active = self.unbounded_active.saturating_sub(1);
            self.active_tasks = sr_tasks_clamp(self.unbounded_active, MAX_BG_TASKS);
            self.completed_tasks =
                sr_drain_advance(self.completed_tasks, self.completed_tasks.saturating_add(1));
        }
    }

    #[must_use]
    pub const fn can_restart_cleanly(&self) -> bool {
        self.unbounded_active == 0 && sr_tasks_quiesced(0, self.active_tasks)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_restart_until_running_background_task_finishes() {
        let mut d = InflightTaskDrain::new();
        assert!(d.can_restart_cleanly());
        d.spawn_task();
        assert!(!d.can_restart_cleanly());
        d.finish_task();
        assert!(d.can_restart_cleanly());
    }
}
