// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Multi-day fleet RAM residency & sealed cold-segment page evictor
//! (`Astream.Broker.TlaColdSegmentMmapEvictor`).
//!
//! Bounds `BrokerLog` resident RAM across multi-day `aterm` fleet runs: once WAL segments are
//! durably sealed below `hot_tail_floor`, evicts their in-RAM payload buffers down to
//! `max_hot_ram_bytes` while advancing `evicted_segment_floor <= sealed_segment_hw` monotonically.

#[cfg(clean_islands)]
#[path = "cold_segment_mmap_evictor_island.rs"]
mod cold_segment_mmap_evictor_island;
#[cfg(clean_islands)]
pub use cold_segment_mmap_evictor_island::{
    cold_evicted_floor_advance_b116, cold_hot_ram_clamp_b116,
};

#[cfg(not(clean_islands))]
/// Clamp resident hot-tail RAM byte footprint to `max_hot_ram_bytes`.
#[must_use]
pub const fn cold_hot_ram_clamp_b116(cand_ram_bytes: u64, max_hot_ram_bytes: u64) -> u64 {
    if cand_ram_bytes < max_hot_ram_bytes {
        cand_ram_bytes
    } else {
        max_hot_ram_bytes
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `evicted_segment_floor`.
#[must_use]
pub const fn cold_evicted_floor_advance_b116(cur_floor: u64, cand_floor: u64) -> u64 {
    if cur_floor < cand_floor {
        cand_floor
    } else {
        cur_floor
    }
}

contract_fn! {
    /// True iff `cand_floor` does not overtake `sealed_segment_hw`.
    #[must_use]
    pub const fn cold_floor_within_sealed_b116(cand_floor: u64, sealed_segment_hw: u64) -> bool
    clauses [ensures result == (cand_floor <= sealed_segment_hw)]
    {
        cand_floor <= sealed_segment_hw
    }
}

/// Decision emitted by `ColdSegmentMmapEvictor::on_append_and_seal`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ColdEvictDecision {
    WithinHotRamBudget {
        hot_ram_bytes: u64,
        evicted_floor: u64,
    },
    EvictSealedPrefix {
        new_evicted_floor: u64,
        reclaimed_bytes: u64,
        hot_ram_bytes: u64,
    },
}

/// Bounded hot-RAM vs cold-on-disk segment residency controller.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ColdSegmentMmapEvictor {
    hot_ram_bytes: u64,
    max_hot_ram_bytes: u64,
    evicted_segment_floor: u64,
    sealed_segment_hw: u64,
}

impl ColdSegmentMmapEvictor {
    #[must_use]
    pub const fn new(max_hot_ram_bytes: u64) -> Self {
        let cap = if max_hot_ram_bytes == 0 {
            16 * 1024 * 1024
        } else {
            max_hot_ram_bytes
        };
        Self {
            hot_ram_bytes: 0,
            max_hot_ram_bytes: cap,
            evicted_segment_floor: 0,
            sealed_segment_hw: 0,
        }
    }

    #[must_use]
    pub const fn hot_ram_bytes(&self) -> u64 {
        self.hot_ram_bytes
    }

    #[must_use]
    pub const fn evicted_segment_floor(&self) -> u64 {
        self.evicted_segment_floor
    }

    /// Record appended `added_bytes`, latest `sealed_hw`, and evict `reclaimable_bytes` up to
    /// `cand_evict_floor` when resident RAM would exceed `max_hot_ram_bytes`.
    pub fn on_append_and_seal(
        &mut self,
        added_bytes: u64,
        sealed_hw: u64,
        cand_evict_floor: u64,
        reclaimable_bytes: u64,
    ) -> ColdEvictDecision {
        self.sealed_segment_hw = cold_evicted_floor_advance_b116(self.sealed_segment_hw, sealed_hw);
        let proposed_ram = self.hot_ram_bytes.saturating_add(added_bytes);
        if proposed_ram <= self.max_hot_ram_bytes {
            self.hot_ram_bytes = cold_hot_ram_clamp_b116(proposed_ram, self.max_hot_ram_bytes);
            return ColdEvictDecision::WithinHotRamBudget {
                hot_ram_bytes: self.hot_ram_bytes,
                evicted_floor: self.evicted_segment_floor,
            };
        }
        if cold_floor_within_sealed_b116(cand_evict_floor, self.sealed_segment_hw)
            && cand_evict_floor > self.evicted_segment_floor
        {
            self.evicted_segment_floor =
                cold_evicted_floor_advance_b116(self.evicted_segment_floor, cand_evict_floor);
            let after_reclaim = proposed_ram.saturating_sub(reclaimable_bytes);
            self.hot_ram_bytes = cold_hot_ram_clamp_b116(after_reclaim, self.max_hot_ram_bytes);
            ColdEvictDecision::EvictSealedPrefix {
                new_evicted_floor: self.evicted_segment_floor,
                reclaimed_bytes: reclaimable_bytes,
                hot_ram_bytes: self.hot_ram_bytes,
            }
        } else {
            self.hot_ram_bytes = cold_hot_ram_clamp_b116(proposed_ram, self.max_hot_ram_bytes);
            ColdEvictDecision::WithinHotRamBudget {
                hot_ram_bytes: self.hot_ram_bytes,
                evicted_floor: self.evicted_segment_floor,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn evicts_sealed_cold_segments_when_hot_ram_exceeds_budget() {
        let mut ev = ColdSegmentMmapEvictor::new(10_000);
        assert_eq!(
            ev.on_append_and_seal(6_000, 1, 0, 0),
            ColdEvictDecision::WithinHotRamBudget {
                hot_ram_bytes: 6_000,
                evicted_floor: 0,
            }
        );
        assert_eq!(
            ev.on_append_and_seal(6_000, 2, 2, 5_000),
            ColdEvictDecision::EvictSealedPrefix {
                new_evicted_floor: 2,
                reclaimed_bytes: 5_000,
                hot_ram_bytes: 7_000,
            }
        );
    }
}
