// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Shared-volume `aterm ctl @self await sys 'free>=room'` unowned build-cache reclaimer
//! (`Astream.Host.TlaDiskRoomReclaimer`, Island #290).

#[cfg(clean_islands)]
#[path = "disk_room_reclaimer_island.rs"]
mod disk_room_reclaimer_island;
#[cfg(clean_islands)]
pub use disk_room_reclaimer_island::{reclaimer_candidates_clamp, reclaimer_free_mb_clamp};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn reclaimer_free_mb_clamp(free_mb: u64, total_mb: u64) -> u64 {
    if free_mb < total_mb {
        free_mb
    } else {
        total_mb
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn reclaimer_candidates_clamp(count: u64, max_count: u64) -> u64 {
    if count < max_count {
        count
    } else {
        max_count
    }
}

/// Maximum candidate cache directories inspected in a single reclamation sweep (`256`).
pub const MAX_RECLAIM_CANDIDATES: u64 = 256;

contract_fn! {
    /// Verified check whether shared volume free space meets `room_floor_mb`
    /// (`room_floor_mb <= free_mb`), linked via `clean-kernel-defeq` to `reclaimer_has_room_isl`.
    #[must_use]
    pub const fn reclaimer_has_room(free_mb: u64, room_floor_mb: u64) -> bool
    clauses [ensures result == (room_floor_mb <= free_mb)]
    {
        room_floor_mb <= free_mb
    }
}

/// Metadata for a candidate build cache directory on the shared volume.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BuildCacheEntry {
    pub cache_id: u64,
    pub size_mb: u64,
    pub active_leases: u32,
}

/// Outcome of a [`DiskRoomReclaimer::plan_sweep`] pass.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReclaimSweepPlan {
    pub evicted_cache_ids: Vec<u64>,
    pub projected_free_mb: u64,
    pub room_satisfied: bool,
}

/// Planner for shared-volume `free>=room` build-cache reclamation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DiskRoomReclaimer {
    total_mb: u64,
    room_floor_mb: u64,
}

impl DiskRoomReclaimer {
    /// Create a reclaimer for a volume of `total_mb` with target headroom `room_floor_mb`.
    #[must_use]
    pub const fn new(total_mb: u64, room_floor_mb: u64) -> Self {
        Self {
            total_mb,
            room_floor_mb: reclaimer_free_mb_clamp(room_floor_mb, total_mb),
        }
    }

    #[must_use]
    pub const fn total_mb(&self) -> u64 {
        self.total_mb
    }

    #[must_use]
    pub const fn room_floor_mb(&self) -> u64 {
        self.room_floor_mb
    }

    /// Plan an eviction sweep starting from `current_free_mb` across `candidates` (ordered
    /// stalest-first by caller), touching only entries with `active_leases == 0`.
    #[must_use]
    pub fn plan_sweep(
        &self,
        current_free_mb: u64,
        candidates: &[BuildCacheEntry],
    ) -> ReclaimSweepPlan {
        let mut free_mb = reclaimer_free_mb_clamp(current_free_mb, self.total_mb);
        let mut evicted = Vec::new();
        let limit =
            reclaimer_candidates_clamp(candidates.len() as u64, MAX_RECLAIM_CANDIDATES) as usize;

        let mut rest = candidates;
        let mut idx = 0usize;
        while idx < limit && !reclaimer_has_room(free_mb, self.room_floor_mb) {
            let [entry, tail @ ..] = rest else {
                break;
            };
            rest = tail;
            if entry.active_leases == 0 && entry.size_mb > 0 {
                evicted.push(entry.cache_id);
                free_mb =
                    reclaimer_free_mb_clamp(free_mb.saturating_add(entry.size_mb), self.total_mb);
            }
            idx = idx.saturating_add(1);
        }

        let room_satisfied = reclaimer_has_room(free_mb, self.room_floor_mb);
        ReclaimSweepPlan {
            evicted_cache_ids: evicted,
            projected_free_mb: free_mb,
            room_satisfied,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reclaims_only_unleased_caches_and_stops_once_room_met() {
        let reclaimer = DiskRoomReclaimer::new(500_000, 30_000);
        assert_eq!(reclaimer.total_mb(), 500_000);
        assert_eq!(reclaimer.room_floor_mb(), 30_000);
        let entries = [
            BuildCacheEntry {
                cache_id: 1,
                size_mb: 25_000,
                active_leases: 1,
            },
            BuildCacheEntry {
                cache_id: 2,
                size_mb: 12_000,
                active_leases: 0,
            },
            BuildCacheEntry {
                cache_id: 3,
                size_mb: 15_000,
                active_leases: 0,
            },
            BuildCacheEntry {
                cache_id: 4,
                size_mb: 20_000,
                active_leases: 0,
            },
        ];
        let plan = reclaimer.plan_sweep(10_000, &entries);
        assert_eq!(plan.evicted_cache_ids, vec![2, 3]);
        assert_eq!(plan.projected_free_mb, 37_000);
        assert!(plan.room_satisfied);
    }
}
