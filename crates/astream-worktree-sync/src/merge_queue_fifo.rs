// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Deterministic FIFO rebase-and-CI landing queue serializing `origin/main` pushes across
//! `autopilot=land` worker tabs (`Astream.Worktree.TlaMergeQueueFifo`).

use std::collections::VecDeque;

#[cfg(clean_islands)]
#[path = "merge_queue_fifo_island.rs"]
mod merge_queue_fifo_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn mq_depth_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn mq_landed_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use merge_queue_fifo_island::{mq_depth_clamp, mq_landed_advance};

/// Maximum queued worker branches awaiting serialized rebase + push.
pub const MAX_MERGE_QUEUE_DEPTH: u64 = 64;

contract_fn! {
    /// Verified head-match check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `mq_head_ready_isl`.
    #[must_use]
    pub const fn mq_head_ready(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Serialized `origin/main` landing coordinator.
#[derive(Debug, Clone, Default)]
pub struct RebaseMergeQueue {
    main_gen: u64,
    queue: VecDeque<String>,
}

impl RebaseMergeQueue {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            main_gen: 0,
            queue: VecDeque::new(),
        }
    }

    pub fn enqueue_worker(&mut self, worker_sid: &str) -> Result<usize, &'static str> {
        if worker_sid.trim().is_empty() {
            return Err("empty worker session id");
        }
        let cap = mq_depth_clamp(MAX_MERGE_QUEUE_DEPTH, MAX_MERGE_QUEUE_DEPTH) as usize;
        for w in &self.queue {
            if w.as_str() == worker_sid {
                return Err("worker already queued");
            }
        }
        if self.queue.len() >= cap {
            return Err("merge queue full");
        }
        let mut owned = String::new();
        owned.push_str(worker_sid);
        self.queue.push_back(owned);
        Ok(self.queue.len())
    }

    #[must_use]
    pub fn active_lander(&self) -> Option<&str> {
        match self.queue.front() {
            Some(s) => Some(s.as_str()),
            None => None,
        }
    }

    pub fn complete_landing(
        &mut self,
        worker_sid: &str,
        tested_against_gen: u64,
    ) -> Result<u64, &'static str> {
        if self.active_lander() != Some(worker_sid) {
            return Err("worker is not at head of merge queue");
        }
        if !mq_head_ready(tested_against_gen, self.main_gen) {
            return Err("stale rebase base: re-rebase onto latest main_gen");
        }
        self.queue.pop_front();
        self.main_gen = mq_landed_advance(self.main_gen, self.main_gen.saturating_add(1));
        Ok(self.main_gen)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn merge_queue_serializes_landings_and_rejects_stale_rebase_generation() {
        let mut mq = RebaseMergeQueue::new();
        mq.enqueue_worker("@w1").unwrap();
        mq.enqueue_worker("@w2").unwrap();
        assert!(mq.complete_landing("@w2", 0).is_err());
        assert_eq!(mq.complete_landing("@w1", 0).unwrap(), 1);
        // @w2 tested against gen 0 before @w1 landed -> must re-rebase onto gen 1!
        assert!(mq.complete_landing("@w2", 0).is_err());
        assert_eq!(mq.complete_landing("@w2", 1).unwrap(), 2);
    }
}
