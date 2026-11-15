// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Single-threaded `fork` + `PTRACE_TRACEME` + `execve` lineage tracker (`docs/ROADMAP.md` §4:
//! *"tracing a separately exec'd, unmodified binary (fork, `PTRACE_TRACEME`, `execve`),
//! single-threaded first"*, `Astream.SecReplay.TlaPtraceExecveLineage`).

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
#[path = "ptrace_execve_lineage_island.rs"]
mod ptrace_execve_lineage_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sec_tid_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sec_exec_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use ptrace_execve_lineage_island::{sec_exec_advance, sec_tid_clamp};

/// Single-threaded v1 tracee thread ceiling (`1`).
pub const SINGLE_THREAD_CAP: u64 = 1;

contract_fn! {
    /// Verified post-`execve` single-thread invariant (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `sec_single_threaded_isl`.
    #[must_use]
    pub const fn sec_single_threaded(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct PtraceExecveTracker {
    root_tid: u64,
    active_threads: u64,
    exec_epoch: u64,
}

impl PtraceExecveTracker {
    #[must_use]
    pub const fn new(root_tid: u64) -> Self {
        Self {
            root_tid,
            active_threads: 1,
            exec_epoch: 0,
        }
    }

    pub fn on_execve_stop(&mut self, tid: u64) -> bool {
        if self.root_tid == 0 || tid != self.root_tid {
            return false;
        }
        let clamped = sec_tid_clamp(self.active_threads, SINGLE_THREAD_CAP);
        if !sec_single_threaded(SINGLE_THREAD_CAP, self.active_threads) || clamped != 1 {
            return false;
        }
        self.exec_epoch = sec_exec_advance(self.exec_epoch, self.exec_epoch.saturating_add(1));
        true
    }

    pub fn on_clone_attempt(&mut self) -> bool {
        self.active_threads = self.active_threads.saturating_add(1);
        sec_single_threaded(SINGLE_THREAD_CAP, self.active_threads)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn admits_root_execve_and_refuses_multithreaded_clone_in_v1() {
        let mut t = PtraceExecveTracker::new(4242);
        assert!(t.on_execve_stop(4242));
        assert!(!t.on_clone_attempt());
        assert!(!t.on_execve_stop(4242));
    }
}
