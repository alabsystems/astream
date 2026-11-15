// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Shared volume free-space monitor coordinating `aterm ctl @self await sys 'free>=room'` unused
//! build-cache reclamation before starting heavy `targo` builds (`Astream.AtpkgTc.TlaBuildCacheReclaimer`).

#[cfg(clean_islands)]
#[path = "build_cache_reclaimer_island.rs"]
mod build_cache_reclaimer_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tc_mb_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tc_reclaim_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use build_cache_reclaimer_island::{tc_mb_clamp, tc_reclaim_advance};

/// Maximum tracked volume free space (`16_777_216` MiB = 16 TiB).
pub const MAX_DISK_FREE_MB: u64 = 16_777_216;

contract_fn! {
    /// Verified volume room predicate (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `tc_free_has_room_isl`.
    #[must_use]
    pub const fn tc_free_has_room(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct VolumeRoomGate {
    room_floor_mb: u64,
    awaits_triggered: u64,
}

impl VolumeRoomGate {
    #[must_use]
    pub const fn new(room_floor_mb: u64) -> Self {
        Self {
            room_floor_mb: tc_mb_clamp(room_floor_mb, MAX_DISK_FREE_MB),
            awaits_triggered: 0,
        }
    }

    pub fn check_disk_free_mb(&mut self, disk_free_mb: u64) -> bool {
        let free = tc_mb_clamp(disk_free_mb, MAX_DISK_FREE_MB);
        if tc_free_has_room(free, self.room_floor_mb) {
            true
        } else {
            self.awaits_triggered = tc_reclaim_advance(
                self.awaits_triggered,
                self.awaits_triggered.saturating_add(1),
            );
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn requests_await_sys_free_room_when_disk_free_mb_is_below_floor() {
        let mut g = VolumeRoomGate::new(20_480);
        assert!(!g.check_disk_free_mb(12_000));
        assert!(g.check_disk_free_mb(45_000));
    }
}
