// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bounded `(producer_id, producer_seq) -> Offset` dedup-table compaction planner
//! (`Astream.Broker.TlaDedupRingCompactor`).
//!
//! Prevents `BrokerLog.dedup` from growing without bound across multi-day `aterm`
//! runs: evicts entries whose log `offset < compacted_base` AND whose sequence sits
//! strictly below the producer's active pipelined retry window (`producer_max_seq - retry_window`),
//! preserving idempotence for in-flight retries while capping per-turn sweep work.

#[cfg(clean_islands)]
#[path = "dedup_ring_compactor_island.rs"]
mod dedup_ring_compactor_island;
#[cfg(clean_islands)]
pub use dedup_ring_compactor_island::{dedup_evict_clamp, dedup_horizon_advance};

/// Default per-producer recent sequence window protected even across log compaction.
pub const DEFAULT_PROTECTED_SEQ_WINDOW: u64 = 256;

/// Default maximum dedup keys evicted in one maintenance turn.
pub const DEFAULT_MAX_DEDUP_EVICT_BATCH: u64 = 512;

#[cfg(not(clean_islands))]
/// Monotonically advance the dedup table's compacted log-offset horizon.
#[must_use]
pub const fn dedup_horizon_advance(cur_horizon: u64, cand_horizon: u64) -> u64 {
    if cur_horizon < cand_horizon {
        cand_horizon
    } else {
        cur_horizon
    }
}

#[cfg(not(clean_islands))]
/// Clamp evicted dedup entry count per maintenance turn to `max_batch`.
#[must_use]
pub const fn dedup_evict_clamp(cand_evicted: u64, max_batch: u64) -> u64 {
    if cand_evicted < max_batch {
        cand_evicted
    } else {
        max_batch
    }
}

contract_fn! {
    /// True iff `entry_offset` lies strictly below `compacted_base`.
    #[must_use]
    pub const fn dedup_entry_evictable(entry_offset: u64, compacted_base: u64) -> bool
    clauses [ensures result == (entry_offset < compacted_base)]
    {
        entry_offset < compacted_base
    }
}

/// Snapshot of one `(producer_id, producer_seq) -> offset` row plus the producer's tip sequence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DedupCandidate {
    pub producer_id: u64,
    pub producer_seq: u64,
    pub producer_tip_seq: u64,
    pub log_offset: u64,
}

/// Stateful dedup-table eviction coordinator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DedupRingCompactor {
    compacted_horizon: u64,
    protected_seq_window: u64,
    max_evict_batch: u64,
    last_evicted: u64,
}

impl Default for DedupRingCompactor {
    fn default() -> Self {
        Self::new(DEFAULT_PROTECTED_SEQ_WINDOW, DEFAULT_MAX_DEDUP_EVICT_BATCH)
    }
}

impl DedupRingCompactor {
    #[must_use]
    pub const fn new(protected_seq_window: u64, max_evict_batch: u64) -> Self {
        let cap = if max_evict_batch == 0 {
            DEFAULT_MAX_DEDUP_EVICT_BATCH
        } else {
            max_evict_batch
        };
        Self {
            compacted_horizon: 0,
            protected_seq_window,
            max_evict_batch: cap,
            last_evicted: 0,
        }
    }

    #[must_use]
    pub const fn compacted_horizon(&self) -> u64 {
        self.compacted_horizon
    }

    #[must_use]
    pub const fn last_evicted(&self) -> u64 {
        self.last_evicted
    }

    /// Select up to `max_evict_batch` `(producer_id, producer_seq)` keys safe to evict at `compacted_base`.
    pub fn select_evictions(
        &mut self,
        compacted_base: u64,
        candidates: &[DedupCandidate],
    ) -> Vec<(u64, u64)> {
        let horizon = dedup_horizon_advance(self.compacted_horizon, compacted_base);
        self.compacted_horizon = horizon;

        let mut evicted: Vec<(u64, u64)> = Vec::new();
        let mut count = 0u64;
        let mut rest = candidates;
        while let &[cand, ref tail @ ..] = rest {
            if count >= self.max_evict_batch {
                break;
            }
            let min_protected_seq = cand
                .producer_tip_seq
                .saturating_sub(self.protected_seq_window);
            if dedup_entry_evictable(cand.log_offset, horizon)
                && cand.producer_seq < min_protected_seq
            {
                evicted.push((cand.producer_id, cand.producer_seq));
                count = count.saturating_add(1);
            }
            rest = tail;
        }
        self.last_evicted = dedup_evict_clamp(count, self.max_evict_batch);
        evicted
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn evicts_only_compacted_entries_outside_active_retry_window() {
        let mut comp = DedupRingCompactor::new(10, 2);
        let cands = [
            // Offset 5 < 100 and seq 1 < (50 - 10 = 40) -> EVICT
            DedupCandidate {
                producer_id: 7,
                producer_seq: 1,
                producer_tip_seq: 50,
                log_offset: 5,
            },
            // Offset 20 < 100, BUT seq 45 >= 40 (inside active retry window!) -> KEEP
            DedupCandidate {
                producer_id: 7,
                producer_seq: 45,
                producer_tip_seq: 50,
                log_offset: 20,
            },
            // Offset 120 >= 100 (still in retained log!) -> KEEP
            DedupCandidate {
                producer_id: 8,
                producer_seq: 1,
                producer_tip_seq: 100,
                log_offset: 120,
            },
        ];

        let out = comp.select_evictions(100, &cands);
        assert_eq!(out, vec![(7, 1)]);
        assert_eq!(comp.compacted_horizon(), 100);
        assert_eq!(comp.last_evicted(), 1);
    }
}
