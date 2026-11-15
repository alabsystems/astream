// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Volume free-space admission gate & unheld `CACHEDIR.TAG` build-cache eviction planner
//! (`aterm ctl @self status` `disk_free_mb=` & `aterm ctl @self await sys 'free>=room'`,
//! `Astream.Host.TlaDiskRoomWatchdog`).
//!
//! Protects multi-session builds sharing one volume from ENOSPC mid-compilation:
//! - Classifies volume free space into `Room`, `Tight`, or `Critical` using Clean-verified
//!   [`disk_has_room`] and [`disk_free_mb_clamp`].
//! - Selects LRU eviction candidates ONLY among caches that carry a valid `CACHEDIR.TAG`
//!   signature AND have `active_holders == 0` (never evicting a directory in use by any
//!   live session), stopping as soon as projected free space meets `room_floor_mb` and
//!   advancing `total_reclaimed_mb` monotonically via Clean-origin [`disk_reclaimed_advance`].

#[cfg(clean_islands)]
#[path = "disk_room_island.rs"]
mod disk_room_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn disk_free_mb_clamp(free_mb: u64, max_mb: u64) -> u64 {
    if free_mb < max_mb {
        free_mb
    } else {
        max_mb
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn disk_reclaimed_advance(prev_mb: u64, cand_mb: u64) -> u64 {
    if prev_mb < cand_mb {
        cand_mb
    } else {
        prev_mb
    }
}
#[cfg(clean_islands)]
pub use disk_room_island::{disk_free_mb_clamp, disk_reclaimed_advance};

/// Canonical first-line signature required by `CACHEDIR.TAG` specification.
pub const CACHEDIR_TAG_SIGNATURE: &[u8] = b"Signature: 8a477f597d28d172789f06886806bc55";

/// Upper clamp for volume capacity accounting (`16 PiB` in MiB).
pub const MAX_VOLUME_MB: u64 = 16 * 1024 * 1024 * 1024;

contract_fn! {
    /// Verified check that `free_mb` meets or exceeds `room_floor_mb`,
    /// linked via `clean-kernel-defeq` to `disk_has_room_isl`.
    #[must_use]
    pub const fn disk_has_room(free_mb: u64, room_floor_mb: u64) -> bool
    clauses [ensures result == (room_floor_mb <= free_mb)]
    {
        room_floor_mb <= free_mb
    }
}

/// Volume free-space pressure classification (`await sys 'free>=room'`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiskPressureTier {
    /// `free_mb >= room_floor_mb` — builds may proceed immediately.
    Room,
    /// `critical_floor_mb <= free_mb < room_floor_mb` — reclaim unheld caches before starting new builds.
    Tight,
    /// `free_mb < critical_floor_mb` — pause heavy builds until reclamation restores room.
    Critical,
}

/// Candidate build-cache directory inspected by [`DiskRoomWatchdog`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BuildCacheEntry {
    /// Identifier / path string of the cache directory.
    pub cache_id: String,
    /// Estimated reclaimable size in MiB.
    pub size_mb: u64,
    /// Last-used monotone timestamp in milliseconds (lower = older / evicted first).
    pub last_used_ms: u64,
    /// Number of active sessions currently compiling in or holding this cache (`> 0` => NEVER evict!).
    pub active_holders: u32,
    /// Whether the directory carries a valid `CACHEDIR.TAG` header (`has_valid_cachedir_tag`).
    pub verified_cachedir_tag: bool,
}

/// Eviction plan computed by [`DiskRoomWatchdog::plan_reclaim`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReclaimPlan {
    /// Initial pressure tier before eviction.
    pub initial_tier: DiskPressureTier,
    /// Ordered list of `cache_id`s safe to remove (`active_holders == 0 && verified_cachedir_tag`).
    pub evict_ids: Vec<String>,
    /// Projected MiB reclaimed by removing `evict_ids`.
    pub planned_reclaim_mb: u64,
    /// Whether `free_mb + planned_reclaim_mb >= room_floor_mb`.
    pub reaches_room: bool,
}

/// Verify that the contents of a `CACHEDIR.TAG` file begin with the canonical 43-byte
/// `Signature: 8a477f597d28d172789f06886806bc55` first line.
#[must_use]
pub fn has_valid_cachedir_tag(file_bytes: &[u8]) -> bool {
    let mut end = file_bytes.len();
    let mut i = 0usize;
    while let Some(&b) = file_bytes.get(i) {
        if b == b'\n' || b == b'\r' {
            end = i;
            break;
        }
        i = i.saturating_add(1);
    }
    file_bytes.get(..end) == Some(CACHEDIR_TAG_SIGNATURE)
}

/// Stateful volume free-space watchdog & LRU build-cache reclamation planner.
#[derive(Debug, Clone)]
pub struct DiskRoomWatchdog {
    room_floor_mb: u64,
    critical_floor_mb: u64,
    last_free_mb: u64,
    total_reclaimed_mb: u64,
}

impl DiskRoomWatchdog {
    /// Construct a watchdog with `room_floor_mb` (e.g. `20_480` = 20 GiB) and `critical_floor_mb`
    /// (e.g. `4_096` = 4 GiB).
    #[must_use]
    pub fn new(room_floor_mb: u64, critical_floor_mb: u64) -> Self {
        let room = disk_free_mb_clamp(room_floor_mb, MAX_VOLUME_MB);
        let crit = disk_free_mb_clamp(critical_floor_mb, room);
        Self {
            room_floor_mb: room,
            critical_floor_mb: crit,
            last_free_mb: 0,
            total_reclaimed_mb: 0,
        }
    }

    /// Cumulative MiB reclaimed across recorded eviction runs.
    #[must_use]
    pub const fn total_reclaimed_mb(&self) -> u64 {
        self.total_reclaimed_mb
    }

    /// Classify `raw_free_mb` and update `last_free_mb`.
    pub fn observe_free_mb(&mut self, raw_free_mb: u64) -> DiskPressureTier {
        let free = disk_free_mb_clamp(raw_free_mb, MAX_VOLUME_MB);
        self.last_free_mb = free;
        if disk_has_room(free, self.room_floor_mb) {
            DiskPressureTier::Room
        } else if disk_has_room(free, self.critical_floor_mb) {
            DiskPressureTier::Tight
        } else {
            DiskPressureTier::Critical
        }
    }

    /// Compute a minimal, oldest-first (`last_used_ms` ascending) eviction plan over unheld,
    /// `CACHEDIR.TAG`-verified caches to bring `raw_free_mb` back to `room_floor_mb`.
    pub fn plan_reclaim(
        &mut self,
        raw_free_mb: u64,
        candidates: &[BuildCacheEntry],
    ) -> ReclaimPlan {
        let tier = self.observe_free_mb(raw_free_mb);
        let free = self.last_free_mb;
        if tier == DiskPressureTier::Room {
            return ReclaimPlan {
                initial_tier: tier,
                evict_ids: Vec::new(),
                planned_reclaim_mb: 0,
                reaches_room: true,
            };
        }

        // Collect eligible indices (`active_holders == 0 && verified_cachedir_tag && size_mb > 0`)
        // and insertion-sort them by `(last_used_ms ASC, size_mb DESC)` without closures or raw indexing!
        let cap = if candidates.len() < 256 {
            candidates.len()
        } else {
            256
        };
        let mut eligible: Vec<usize> = {
            let _ = cap;
            Vec::new()
        };
        let mut i = 0usize;
        while let Some(c) = candidates.get(i) {
            if c.active_holders == 0 && c.verified_cachedir_tag && c.size_mb > 0 {
                eligible.push(i);
                let mut pos = eligible.len().saturating_sub(1);
                while pos > 0 {
                    let prev_pos = pos - 1;
                    let Some(&prev_idx) = eligible.get(prev_pos) else {
                        break;
                    };
                    let Some(prev) = candidates.get(prev_idx) else {
                        break;
                    };
                    let comes_before = if c.last_used_ms != prev.last_used_ms {
                        c.last_used_ms < prev.last_used_ms
                    } else {
                        c.size_mb > prev.size_mb
                    };
                    if comes_before {
                        if let Some(slot_hi) = eligible.get_mut(pos) {
                            *slot_hi = prev_idx;
                        }
                        if let Some(slot_lo) = eligible.get_mut(prev_pos) {
                            *slot_lo = i;
                        }
                        pos = prev_pos;
                    } else {
                        break;
                    }
                }
            }
            i = i.saturating_add(1);
        }

        let mut evict_ids = Vec::new();
        let mut reclaimed = 0u64;
        let mut k = 0usize;
        while let Some(&cand_idx) = eligible.get(k) {
            if disk_has_room(free.saturating_add(reclaimed), self.room_floor_mb) {
                break;
            }
            if let Some(entry) = candidates.get(cand_idx) {
                evict_ids.push(entry.cache_id.clone());
                reclaimed = reclaimed.saturating_add(entry.size_mb);
            }
            k = k.saturating_add(1);
        }

        let reaches_room = disk_has_room(free.saturating_add(reclaimed), self.room_floor_mb);
        ReclaimPlan {
            initial_tier: tier,
            evict_ids,
            planned_reclaim_mb: reclaimed,
            reaches_room,
        }
    }

    /// Record MiB actually freed on disk, monotonically advancing `total_reclaimed_mb`.
    pub fn record_reclaimed(&mut self, freed_mb: u64) -> u64 {
        let cand = self.total_reclaimed_mb.saturating_add(freed_mb);
        self.total_reclaimed_mb = disk_reclaimed_advance(self.total_reclaimed_mb, cand);
        self.total_reclaimed_mb
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn evicts_only_unheld_cachedir_tagged_caches_in_lru_order_until_room_reached() {
        assert!(has_valid_cachedir_tag(
            b"Signature: 8a477f597d28d172789f06886806bc55\n# Created by cargo\n"
        ));
        assert!(!has_valid_cachedir_tag(b"Signature: wrong\n"));

        let mut dog = DiskRoomWatchdog::new(20_000, 5_000);
        let caches = vec![
            BuildCacheEntry {
                cache_id: "active-session-cache".to_string(),
                size_mb: 15_000,
                last_used_ms: 10, // oldest, BUT held by an active session!
                active_holders: 1,
                verified_cachedir_tag: true,
            },
            BuildCacheEntry {
                cache_id: "untagged-dir".to_string(),
                size_mb: 15_000,
                last_used_ms: 20, // unheld, BUT missing CACHEDIR.TAG!
                active_holders: 0,
                verified_cachedir_tag: false,
            },
            BuildCacheEntry {
                cache_id: "stale-wt-2".to_string(),
                size_mb: 6_000,
                last_used_ms: 200,
                active_holders: 0,
                verified_cachedir_tag: true,
            },
            BuildCacheEntry {
                cache_id: "stale-wt-1".to_string(),
                size_mb: 7_000,
                last_used_ms: 100, // oldest eligible
                active_holders: 0,
                verified_cachedir_tag: true,
            },
            BuildCacheEntry {
                cache_id: "stale-wt-3".to_string(),
                size_mb: 9_000,
                last_used_ms: 300, // should NOT be evicted once 8k + 7k + 6k >= 20k!
                active_holders: 0,
                verified_cachedir_tag: true,
            },
        ];

        let plan = dog.plan_reclaim(8_000, &caches);
        assert_eq!(plan.initial_tier, DiskPressureTier::Tight);
        assert_eq!(
            plan.evict_ids,
            vec!["stale-wt-1".to_string(), "stale-wt-2".to_string()]
        );
        assert_eq!(plan.planned_reclaim_mb, 13_000);
        assert!(plan.reaches_room);
        assert_eq!(dog.record_reclaimed(13_000), 13_000);
    }
}
