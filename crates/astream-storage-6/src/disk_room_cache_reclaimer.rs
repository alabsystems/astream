// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Shared-volume `free>=room` build-cache lease & reclamation planner
//! (`Astream.Host.TlaDiskRoomCacheReclaimer`).
//!
//! Models `aterm ctl @self await sys 'free>=room'`: tracks up to `MAX_CACHE_DIRS` shared
//! `.cargo-build` cache directories with active-session lease counts so `aterm` only evicts
//! unleased (`lease_count == 0`) build caches until `disk_free_mb >= room_target_mb`.

#[cfg(clean_islands)]
#[path = "disk_room_cache_reclaimer_island.rs"]
mod disk_room_cache_reclaimer_island;
#[cfg(clean_islands)]
pub use disk_room_cache_reclaimer_island::{reclaim_epoch_advance_b107, reclaim_evict_batch_clamp};

#[cfg(not(clean_islands))]
/// Clamp per-pass evicted cache directory count to `max_batch`.
#[must_use]
pub const fn reclaim_evict_batch_clamp(cand_evicted: u64, max_batch: u64) -> u64 {
    if cand_evicted < max_batch {
        cand_evicted
    } else {
        max_batch
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the volume cache-reclamation epoch.
#[must_use]
pub const fn reclaim_epoch_advance_b107(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `disk_free_mb` meets or exceeds the `free>=room` watermark `room_target_mb`.
    #[must_use]
    pub const fn disk_has_room_b107(disk_free_mb: u64, room_target_mb: u64) -> bool
    clauses [ensures result == (disk_free_mb >= room_target_mb)]
    {
        disk_free_mb >= room_target_mb
    }
}

/// Maximum `.cargo-build` cache entries tracked in a stack reclamation table.
pub const MAX_CACHE_DIRS: usize = 8;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CacheDirSlot {
    active: bool,
    cache_id: u64,
    size_mb: u64,
    lease_count: u32,
}

impl CacheDirSlot {
    const EMPTY: Self = Self {
        active: false,
        cache_id: 0,
        size_mb: 0,
        lease_count: 0,
    };
}

/// Result of a reclamation pass toward `free>=room`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReclaimPassReport {
    pub reclaim_epoch: u64,
    pub evicted_dirs: u64,
    pub reclaimed_mb: u64,
    pub room_satisfied: bool,
}

/// Lease-safe build-cache reclamation planner.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DiskRoomCacheReclaimer {
    slots: [CacheDirSlot; MAX_CACHE_DIRS],
    room_target_mb: u64,
    max_evict_batch: u64,
    reclaim_epoch: u64,
}

impl DiskRoomCacheReclaimer {
    #[must_use]
    pub const fn new(room_target_mb: u64, max_evict_batch: u64) -> Self {
        let room = if room_target_mb == 0 {
            16_384
        } else {
            room_target_mb
        };
        let batch = if max_evict_batch == 0 {
            4
        } else {
            max_evict_batch
        };
        Self {
            slots: [CacheDirSlot::EMPTY; MAX_CACHE_DIRS],
            room_target_mb: room,
            max_evict_batch: batch,
            reclaim_epoch: 0,
        }
    }

    /// Register or update a build-cache directory and its active session `lease_count`.
    pub fn upsert_cache(&mut self, cache_id: u64, size_mb: u64, lease_count: u32) -> bool {
        let mut idx = 0usize;
        let mut free_idx: Option<usize> = None;
        while let Some(slot) = self.slots.get_mut(idx) {
            if slot.active {
                if slot.cache_id == cache_id {
                    slot.size_mb = size_mb;
                    slot.lease_count = lease_count;
                    return true;
                }
            } else if free_idx.is_none() {
                free_idx = Some(idx);
            }
            idx = idx.saturating_add(1);
        }
        if let Some(target) = free_idx {
            if let Some(slot) = self.slots.get_mut(target) {
                *slot = CacheDirSlot {
                    active: true,
                    cache_id,
                    size_mb,
                    lease_count,
                };
                return true;
            }
        }
        false
    }

    /// Evict up to `max_evict_batch` unleased (`lease_count == 0`) caches until `free>=room`.
    pub fn reclaim_for_room(&mut self, mut disk_free_mb: u64) -> ReclaimPassReport {
        let next_ep = self.reclaim_epoch.saturating_add(1);
        self.reclaim_epoch = reclaim_epoch_advance_b107(self.reclaim_epoch, next_ep);
        let mut evicted = 0u64;
        let mut reclaimed_mb = 0u64;
        let mut idx = 0usize;
        while !disk_has_room_b107(disk_free_mb, self.room_target_mb)
            && evicted < self.max_evict_batch
        {
            let Some(slot_ref) = self.slots.get_mut(idx) else {
                break;
            };
            let slot = *slot_ref;
            if slot.active && slot.lease_count == 0 {
                *slot_ref = CacheDirSlot::EMPTY;
                disk_free_mb = disk_free_mb.saturating_add(slot.size_mb);
                reclaimed_mb = reclaimed_mb.saturating_add(slot.size_mb);
                let cand = evicted.saturating_add(1);
                evicted = reclaim_evict_batch_clamp(cand, self.max_evict_batch);
            }
            idx = idx.saturating_add(1);
        }
        ReclaimPassReport {
            reclaim_epoch: self.reclaim_epoch,
            evicted_dirs: evicted,
            reclaimed_mb,
            room_satisfied: disk_has_room_b107(disk_free_mb, self.room_target_mb),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn skips_leased_caches_and_evicts_idle_until_room_met() {
        let mut rec = DiskRoomCacheReclaimer::new(20_000, 4);
        assert!(rec.upsert_cache(1, 8_000, 1)); // leased by active build -> protected!
        assert!(rec.upsert_cache(2, 6_000, 0)); // idle -> evictable
        assert!(rec.upsert_cache(3, 5_000, 0)); // idle -> evictable
        let rep = rec.reclaim_for_room(10_000);
        assert_eq!(rep.evicted_dirs, 2);
        assert_eq!(rep.reclaimed_mb, 11_000);
        assert!(rep.room_satisfied);
    }
}
