// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm ctl @self await sys 'free>=room'` LRU unreferenced build-cache reclamation planner
//! (`aterm` primer, `Astream.Worktree.TlaPkgCacheReclaim`).

#[cfg(clean_islands)]
#[path = "pkg_cache_reclaim_island.rs"]
mod pkg_cache_reclaim_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn reclaim_dirs_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn reclaim_freed_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use pkg_cache_reclaim_island::{reclaim_dirs_clamp, reclaim_freed_advance};

/// Maximum candidate build directories scanned per eviction pass.
pub const MAX_SCAN_CACHE_DIRS: u64 = 512;

contract_fn! {
    /// Verified free-space check (`threshold <= observed`, i.e. `room_mb <= disk_free_mb`),
    /// linked via `clean-kernel-defeq` to `reclaim_room_met_isl`.
    #[must_use]
    pub const fn reclaim_room_met(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BuildCacheCandidate {
    pub path: String,
    pub size_mb: u64,
    pub last_used_ms: u64,
    pub in_use_by_live_session: bool,
}

/// Selects oldest unused build caches until `disk_free_mb + freed_mb >= room_mb`.
#[derive(Debug, Clone, Default)]
pub struct CacheReclaimPlanner {
    cumulative_freed_mb: u64,
}

impl CacheReclaimPlanner {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            cumulative_freed_mb: 0,
        }
    }

    pub fn plan_evictions(
        &mut self,
        disk_free_mb: u64,
        room_mb: u64,
        candidates: &[BuildCacheCandidate],
    ) -> Vec<String> {
        if reclaim_room_met(disk_free_mb, room_mb) {
            return Vec::new();
        }
        let lim = reclaim_dirs_clamp(candidates.len() as u64, MAX_SCAN_CACHE_DIRS) as usize;
        let mut idle: Vec<&BuildCacheCandidate> = Vec::new();
        let mut idx = 0usize;
        while idx < lim {
            let Some(c) = candidates.get(idx) else {
                break;
            };
            if !c.in_use_by_live_session && c.size_mb > 0 && !c.path.is_empty() {
                let mut pos = idle.len();
                let mut scan = 0usize;
                while scan < idle.len() {
                    if let Some(existing) = idle.get(scan) {
                        if c.last_used_ms < existing.last_used_ms {
                            pos = scan;
                            break;
                        }
                    }
                    scan = scan.saturating_add(1);
                }
                idle.push(c);
                let mut cur = idle.len().saturating_sub(1);
                while cur > pos {
                    let prev = cur.saturating_sub(1);
                    if let (Some(&a), Some(&b)) = (idle.get(prev), idle.get(cur)) {
                        if let Some(slot_prev) = idle.get_mut(prev) {
                            *slot_prev = b;
                        }
                        if let Some(slot_cur) = idle.get_mut(cur) {
                            *slot_cur = a;
                        }
                    }
                    cur = prev;
                }
            }
            idx = idx.saturating_add(1);
        }

        let mut projected = disk_free_mb;
        let mut evicted = Vec::new();
        for c in idle {
            if reclaim_room_met(projected, room_mb) {
                break;
            }
            projected = projected.saturating_add(c.size_mb);
            self.cumulative_freed_mb = reclaim_freed_advance(
                self.cumulative_freed_mb,
                self.cumulative_freed_mb.saturating_add(c.size_mb),
            );
            evicted.push(c.path.clone());
        }
        evicted
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cache_reclaimer_skips_live_sessions_and_frees_lru_until_room_met() {
        let mut p = CacheReclaimPlanner::new();
        let cands = vec![
            BuildCacheCandidate {
                path: "live-target".to_owned(),
                size_mb: 20_000,
                last_used_ms: 10,
                in_use_by_live_session: true,
            },
            BuildCacheCandidate {
                path: "stale-new".to_owned(),
                size_mb: 5_000,
                last_used_ms: 500,
                in_use_by_live_session: false,
            },
            BuildCacheCandidate {
                path: "stale-old".to_owned(),
                size_mb: 8_000,
                last_used_ms: 100,
                in_use_by_live_session: false,
            },
        ];
        let plan = p.plan_evictions(4_000, 10_000, &cands);
        assert_eq!(plan, vec!["stale-old".to_owned()]);
    }
}
