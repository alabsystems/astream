// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Shared-volume `free>=room` build-cache reclaim planner (`Astream.Host.TlaDiskCacheReclaimGate`).
//!
//! Models `aterm ctl @self await sys 'free>=room'`: when `disk_free_mb < room_floor_mb`
//! on a volume shared across multiple `aterm` agent sessions, selects ONLY unheld
//! (`active_holders == 0`) build caches up to the deficit and `max_turn_mb`, never
//! evicting a `CARGO_TARGET_DIR` currently in use by a sibling `targo` / `cargo` build.

#[cfg(clean_islands)]
#[path = "disk_cache_reclaim_gate_island.rs"]
mod disk_cache_reclaim_gate_island;
#[cfg(clean_islands)]
pub use disk_cache_reclaim_gate_island::{reclaim_epoch_advance, reclaim_mb_clamp};

/// Default free-space room floor (`20_480 MB = 20 GiB`) for heavy Rust/Lean builds.
pub const DEFAULT_ROOM_FLOOR_MB: u64 = 20_480;

/// Default maximum MiB reclaimed in a single sweep turn (`32_768 MB = 32 GiB`).
pub const DEFAULT_MAX_RECLAIM_TURN_MB: u64 = 32_768;

#[cfg(not(clean_islands))]
/// Monotonically advance the shared-volume reclaim sweep epoch.
#[must_use]
pub const fn reclaim_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

#[cfg(not(clean_islands))]
/// Clamp MiB reclaimed in a single sweep turn to `max_turn_mb`.
#[must_use]
pub const fn reclaim_mb_clamp(cand_mb: u64, max_turn_mb: u64) -> u64 {
    if cand_mb < max_turn_mb {
        cand_mb
    } else {
        max_turn_mb
    }
}

contract_fn! {
    /// True iff `free_mb >= room_floor_mb`.
    #[must_use]
    pub const fn volume_has_room(room_floor_mb: u64, free_mb: u64) -> bool
    clauses [ensures result == (room_floor_mb <= free_mb)]
    {
        room_floor_mb <= free_mb
    }
}

/// Candidate build-cache directory on the shared volume (pre-sorted oldest-used first).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BuildCacheEntry {
    pub cache_id: u64,
    pub size_mb: u64,
    pub active_holders: u32,
}

/// Result of one `free>=room` evaluation / reclaim sweep plan.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReclaimSweepPlan {
    pub evicted_cache_ids: Vec<u64>,
    pub planned_reclaim_mb: u64,
    pub satisfies_room_after_sweep: bool,
}

/// Stateful shared-volume `free>=room` reclaim gate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DiskCacheReclaimGate {
    room_floor_mb: u64,
    max_turn_mb: u64,
    reclaim_epoch: u64,
    last_turn_mb: u64,
}

impl Default for DiskCacheReclaimGate {
    fn default() -> Self {
        Self::new(DEFAULT_ROOM_FLOOR_MB, DEFAULT_MAX_RECLAIM_TURN_MB)
    }
}

impl DiskCacheReclaimGate {
    #[must_use]
    pub const fn new(room_floor_mb: u64, max_turn_mb: u64) -> Self {
        let floor = if room_floor_mb == 0 {
            DEFAULT_ROOM_FLOOR_MB
        } else {
            room_floor_mb
        };
        let cap = if max_turn_mb == 0 {
            DEFAULT_MAX_RECLAIM_TURN_MB
        } else {
            max_turn_mb
        };
        Self {
            room_floor_mb: floor,
            max_turn_mb: cap,
            reclaim_epoch: 0,
            last_turn_mb: 0,
        }
    }

    #[must_use]
    pub const fn reclaim_epoch(&self) -> u64 {
        self.reclaim_epoch
    }

    #[must_use]
    pub const fn last_turn_mb(&self) -> u64 {
        self.last_turn_mb
    }

    /// Plan which unheld caches to evict when `disk_free_mb` is below `room_floor_mb`.
    pub fn plan_sweep(
        &mut self,
        disk_free_mb: u64,
        candidates_lru: &[BuildCacheEntry],
    ) -> ReclaimSweepPlan {
        if volume_has_room(self.room_floor_mb, disk_free_mb) {
            self.last_turn_mb = 0;
            return ReclaimSweepPlan {
                evicted_cache_ids: Vec::new(),
                planned_reclaim_mb: 0,
                satisfies_room_after_sweep: true,
            };
        }

        let cand_ep = self.reclaim_epoch.saturating_add(1);
        self.reclaim_epoch = reclaim_epoch_advance(self.reclaim_epoch, cand_ep);

        let mut evicted: Vec<u64> = Vec::new();
        let mut reclaimed = 0u64;
        let mut rest = candidates_lru;
        while let &[entry, ref tail @ ..] = rest {
            let projected_free = disk_free_mb.saturating_add(reclaimed);
            if volume_has_room(self.room_floor_mb, projected_free) || reclaimed >= self.max_turn_mb
            {
                break;
            }
            if entry.active_holders == 0 && entry.size_mb > 0 {
                let next_reclaimed = reclaimed.saturating_add(entry.size_mb);
                if next_reclaimed <= self.max_turn_mb || evicted.is_empty() {
                    evicted.push(entry.cache_id);
                    reclaimed = reclaim_mb_clamp(next_reclaimed, self.max_turn_mb);
                }
            }
            rest = tail;
        }

        self.last_turn_mb = reclaimed;
        let after_free = disk_free_mb.saturating_add(reclaimed);
        ReclaimSweepPlan {
            evicted_cache_ids: evicted,
            planned_reclaim_mb: reclaimed,
            satisfies_room_after_sweep: volume_has_room(self.room_floor_mb, after_free),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn skips_active_session_build_dirs_and_stops_once_room_reached() {
        let mut gate = DiskCacheReclaimGate::new(20_000, 30_000);
        let caches = [
            // Active Trust build dir -> MUST NOT be evicted!
            BuildCacheEntry {
                cache_id: 1,
                size_mb: 12_000,
                active_holders: 1,
            },
            // Idle stale build dir 2 -> evict (8_000 MB -> 18_000 MB free)
            BuildCacheEntry {
                cache_id: 2,
                size_mb: 8_000,
                active_holders: 0,
            },
            // Idle stale build dir 3 -> evict (5_000 MB -> 23_000 MB >= 20_000 MB -> stop!)
            BuildCacheEntry {
                cache_id: 3,
                size_mb: 5_000,
                active_holders: 0,
            },
            // Idle dir 4 -> untouched because room is already satisfied!
            BuildCacheEntry {
                cache_id: 4,
                size_mb: 6_000,
                active_holders: 0,
            },
        ];

        let plan = gate.plan_sweep(10_000, &caches);
        assert_eq!(plan.evicted_cache_ids, vec![2, 3]);
        assert_eq!(plan.planned_reclaim_mb, 13_000);
        assert!(plan.satisfies_room_after_sweep);
        assert_eq!(gate.reclaim_epoch(), 1);
    }
}
