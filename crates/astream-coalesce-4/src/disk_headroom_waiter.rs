// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Shared-Volume `disk_free_mb` Build Headroom Gate & Idle Cache Reclamation Planner.
//!
//! Models `aterm ctl @self await sys 'free>=room'`:
//! every session on the same volume shares free disk space (`disk_free_mb`). Before launching
//! a heavy `targo` / `cargo` build or verification run, this planner checks whether
//! `disk_free_mb >= required_room_mb` and, when short, selects LRU-ordered **idle** build
//! caches (never touching a `CARGO_TARGET_DIR` pinned by an active session) sufficient to cover
//! the bounded deficit (`deficit_mb <= required_room_mb`).
//!
//! Backed by Clean TLA+ Island `Astream.Host.TlaDiskHeadroomGate`
//! (`disk_headroom_waiter_island.rs`), proving `deficitMb <= requiredRoomMb` and
//! `evictedCaches <= idleCaches`.

#[cfg(clean_islands)]
#[path = "disk_headroom_waiter_island.rs"]
mod island;
#[cfg(clean_islands)]
pub use island::{disk_deficit_clamp, disk_evict_clamp};

#[cfg(not(clean_islands))]
#[inline]
pub const fn disk_deficit_clamp(deficit_mb: u64, required_mb: u64) -> u64 {
    if deficit_mb < required_mb {
        deficit_mb
    } else {
        required_mb
    }
}

#[cfg(not(clean_islands))]
#[inline]
pub const fn disk_evict_clamp(evicted: u64, idle_caches: u64) -> u64 {
    if evicted < idle_caches {
        evicted
    } else {
        idle_caches
    }
}

contract_fn! {
    /// Kernel-certified check that `free_mb` satisfies `required_mb` (`required_mb <= free_mb`).
    #[must_use]
    #[inline]
    pub const fn disk_free_meets_room(free_mb: u64, required_mb: u64) -> bool
    clauses [ensures result == (required_mb <= free_mb)]
    {
        required_mb <= free_mb
    }
}

/// Default minimum free disk space (`8_192 MiB` = 8 GiB) before starting a workspace build.
pub const DEFAULT_REQUIRED_ROOM_MB: u64 = 8_192;

/// Descriptor of a candidate build cache directory on the shared volume.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BuildCacheEntry {
    pub cache_id: u64,
    pub size_mb: u64,
    pub last_used_ms: u64,
    /// True when an active `aterm` session or background `targo` job holds this directory.
    pub in_use: bool,
}

/// Reclamation plan computed by `plan_disk_headroom`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiskReclaimPlan {
    pub satisfied_immediately: bool,
    pub deficit_mb: u64,
    pub idle_cache_count: u64,
    pub evicted_cache_ids: Vec<u64>,
    pub reclaimed_mb: u64,
    pub projected_free_mb: u64,
    pub meets_room_after_evict: bool,
}

/// Computes an LRU-first eviction plan over idle build caches when `free_mb < required_room_mb`.
#[must_use]
pub fn plan_disk_headroom(
    free_mb: u64,
    required_room_mb: u64,
    caches: &[BuildCacheEntry],
) -> DiskReclaimPlan {
    if disk_free_meets_room(free_mb, required_room_mb) {
        let mut idle_cnt: u64 = 0;
        let mut rest = caches;
        while let &[entry, ref tail @ ..] = rest {
            if !entry.in_use {
                idle_cnt = idle_cnt.saturating_add(1);
            }
            rest = tail;
        }
        return DiskReclaimPlan {
            satisfied_immediately: true,
            deficit_mb: 0,
            idle_cache_count: idle_cnt,
            evicted_cache_ids: Vec::new(),
            reclaimed_mb: 0,
            projected_free_mb: free_mb,
            meets_room_after_evict: true,
        };
    }

    let raw_deficit = required_room_mb.saturating_sub(free_mb);
    let deficit_mb = disk_deficit_clamp(raw_deficit, required_room_mb);

    // Collect only idle caches (`!in_use`) and sort oldest `last_used_ms` first via insertion sort.
    let mut idle: Vec<BuildCacheEntry> = Vec::new();
    let mut rest = caches;
    while let &[entry, ref tail @ ..] = rest {
        if !entry.in_use && entry.size_mb > 0 {
            idle.push(entry);
            let mut j = idle.len().saturating_sub(1);
            while j > 0 {
                let prev_idx = j - 1;
                let (Some(&cur), Some(&prev)) = (idle.get(j), idle.get(prev_idx)) else {
                    break;
                };
                if cur.last_used_ms < prev.last_used_ms {
                    if let Some(slot) = idle.get_mut(j) {
                        *slot = prev;
                    }
                    if let Some(slot) = idle.get_mut(prev_idx) {
                        *slot = cur;
                    }
                    j = prev_idx;
                } else {
                    break;
                }
            }
        }
        rest = tail;
    }

    let idle_count = idle.len() as u64;
    let mut evicted_ids = Vec::new();
    let mut reclaimed_mb: u64 = 0;
    let mut raw_evicted: u64 = 0;

    let mut idle_rest = idle.as_slice();
    while let &[entry, ref tail @ ..] = idle_rest {
        if reclaimed_mb >= deficit_mb {
            break;
        }
        evicted_ids.push(entry.cache_id);
        reclaimed_mb = reclaimed_mb.saturating_add(entry.size_mb);
        raw_evicted = raw_evicted.saturating_add(1);
        idle_rest = tail;
    }

    let clamped_evicted = disk_evict_clamp(raw_evicted, idle_count) as usize;
    evicted_ids.truncate(clamped_evicted);
    let projected_free = free_mb.saturating_add(reclaimed_mb);

    DiskReclaimPlan {
        satisfied_immediately: false,
        deficit_mb,
        idle_cache_count: idle_count,
        evicted_cache_ids: evicted_ids,
        reclaimed_mb,
        projected_free_mb: projected_free,
        meets_room_after_evict: disk_free_meets_room(projected_free, required_room_mb),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn evicts_oldest_idle_caches_until_room_met_and_never_touches_in_use_caches() {
        let caches = [
            BuildCacheEntry {
                cache_id: 10,
                size_mb: 9_000,
                last_used_ms: 100, // oldest, BUT in_use!
                in_use: true,
            },
            BuildCacheEntry {
                cache_id: 20,
                size_mb: 3_000,
                last_used_ms: 500,
                in_use: false,
            },
            BuildCacheEntry {
                cache_id: 30,
                size_mb: 4_500,
                last_used_ms: 200, // oldest idle -> evicted 1st!
                in_use: false,
            },
            BuildCacheEntry {
                cache_id: 40,
                size_mb: 5_000,
                last_used_ms: 900, // newest idle -> untouched once room met!
                in_use: false,
            },
        ];

        // Need 8_000 MB, currently 2_000 MB free -> deficit = 6_000 MB.
        let plan = plan_disk_headroom(2_000, 8_000, &caches);
        assert!(!plan.satisfied_immediately);
        assert_eq!(plan.deficit_mb, 6_000);
        assert_eq!(plan.idle_cache_count, 3);
        assert_eq!(plan.evicted_cache_ids, vec![30, 20]);
        assert_eq!(plan.reclaimed_mb, 7_500);
        assert_eq!(plan.projected_free_mb, 9_500);
        assert!(plan.meets_room_after_evict);
    }
}
