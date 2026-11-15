// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bounded producer `(producer_id, seq) -> Offset` deduplication ring with compaction eviction
//! (`Astream.Broker.TlaDedupWindowRingEvictor`).
//!
//! Prevents unbounded RAM growth in `BrokerLog::dedup` across multi-day `aterm` fabric uptime:
//! evicts producer entries below `retain_before` horizon and bounds active deduplication slots
//! to `MAX_DEDUP_RING_SLOTS` on the stack.

#[cfg(clean_islands)]
#[path = "dedup_window_ring_evictor_island.rs"]
mod dedup_window_ring_evictor_island;
#[cfg(clean_islands)]
pub use dedup_window_ring_evictor_island::{dedup_entries_clamp_b110, evict_horizon_advance_b110};

#[cfg(not(clean_islands))]
/// Clamp active deduplication ring entries to `max_entries`.
#[must_use]
pub const fn dedup_entries_clamp_b110(cand_entries: u64, max_entries: u64) -> u64 {
    if cand_entries < max_entries {
        cand_entries
    } else {
        max_entries
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the deduplication compaction eviction horizon.
#[must_use]
pub const fn evict_horizon_advance_b110(cur_horizon: u64, cand_horizon: u64) -> u64 {
    if cur_horizon < cand_horizon {
        cand_horizon
    } else {
        cur_horizon
    }
}

contract_fn! {
    /// True iff a deduplication entry at `entry_offset` remains at or above `evict_horizon`.
    #[must_use]
    pub const fn dedup_entry_retained_b110(entry_offset: u64, evict_horizon: u64) -> bool
    clauses [ensures result == (evict_horizon <= entry_offset)]
    {
        evict_horizon <= entry_offset
    }
}

/// Stack ring capacity per shard deduplication window.
pub const MAX_DEDUP_RING_SLOTS: usize = 32;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct DedupSlot {
    active: bool,
    producer_id: u64,
    seq: u64,
    offset: u64,
}

impl DedupSlot {
    const EMPTY: Self = Self {
        active: false,
        producer_id: 0,
        seq: 0,
        offset: 0,
    };
}

/// Bounded producer idempotency ring with `retain_before` horizon pruning.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DedupWindowRingEvictor {
    slots: [DedupSlot; MAX_DEDUP_RING_SLOTS],
    write_hand: usize,
    active_entries: u64,
    evict_horizon: u64,
}

impl Default for DedupWindowRingEvictor {
    fn default() -> Self {
        Self::new()
    }
}

impl DedupWindowRingEvictor {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            slots: [DedupSlot::EMPTY; MAX_DEDUP_RING_SLOTS],
            write_hand: 0,
            active_entries: 0,
            evict_horizon: 0,
        }
    }

    #[must_use]
    pub const fn active_entries(&self) -> u64 {
        self.active_entries
    }

    #[must_use]
    pub const fn evict_horizon(&self) -> u64 {
        self.evict_horizon
    }

    /// Look up an existing `(producer_id, seq)` above `evict_horizon`.
    #[must_use]
    pub fn check_duplicate(&self, producer_id: u64, seq: u64) -> Option<u64> {
        let mut rest: &[DedupSlot] = &self.slots;
        while let [s, tail @ ..] = rest {
            if s.active
                && s.producer_id == producer_id
                && s.seq == seq
                && dedup_entry_retained_b110(s.offset, self.evict_horizon)
            {
                return Some(s.offset);
            }
            rest = tail;
        }
        None
    }

    /// Record `(producer_id, seq) -> offset`, overwriting the oldest ring slot if full.
    pub fn record_append(&mut self, producer_id: u64, seq: u64, offset: u64) {
        let target = self.write_hand % MAX_DEDUP_RING_SLOTS;
        let mut was_active = true;
        if let Some(slot) = self.slots.get_mut(target) {
            was_active = slot.active;
            *slot = DedupSlot {
                active: true,
                producer_id,
                seq,
                offset,
            };
        }
        self.write_hand = target.wrapping_add(1) % MAX_DEDUP_RING_SLOTS;
        if !was_active {
            let cand = self.active_entries.saturating_add(1);
            self.active_entries = dedup_entries_clamp_b110(cand, MAX_DEDUP_RING_SLOTS as u64);
        }
    }

    /// Prune all deduplication entries strictly older than `new_horizon` (`retain_before`).
    pub fn evict_below(&mut self, new_horizon: u64) -> u64 {
        self.evict_horizon = evict_horizon_advance_b110(self.evict_horizon, new_horizon);
        let mut pruned = 0u64;
        let mut idx = 0usize;
        while let Some(slot_ref) = self.slots.get_mut(idx) {
            let s = *slot_ref;
            if s.active && !dedup_entry_retained_b110(s.offset, self.evict_horizon) {
                *slot_ref = DedupSlot::EMPTY;
                self.active_entries = self.active_entries.saturating_sub(1);
                pruned = pruned.saturating_add(1);
            }
            idx = idx.saturating_add(1);
        }
        pruned
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deduplicates_live_offsets_and_evicts_compacted_horizon() {
        let mut ring = DedupWindowRingEvictor::new();
        ring.record_append(9, 1, 10);
        ring.record_append(9, 2, 25);
        assert_eq!(ring.check_duplicate(9, 1), Some(10));
        assert_eq!(ring.evict_below(20), 1);
        assert_eq!(ring.check_duplicate(9, 1), None);
        assert_eq!(ring.check_duplicate(9, 2), Some(25));
    }
}
