// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Shared volume free-space hysteresis & idle build-cache eviction planner
//! (`Astream.Broker.TlaBuildDiskRoom`; `aterm ctl @self status` `disk_free_mb=` &
//! `aterm ctl @self await sys 'free>=room'`).
//!
//! Because every `aterm` session on a volume shares its free disk space, resuming builds
//! at the exact same threshold that triggered eviction causes oscillating thrash across
//! concurrent `targo` tabs. [`VolumeRoomLedger`] enforces a certified hysteresis band
//! (`low_room_mb <= resume_room_mb` via Clean-origin [`room_resume_floor`]), clamps raw
//! `statvfs` free-space telemetry against `total_mb` via [`room_free_clamp`], and selects
//! only unpinned, unlocked build caches in oldest-access order until `free_mb >= resume_room_mb`.

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "volume_room_hysteresis_island.rs"]
mod volume_room_hysteresis_island;
#[cfg(clean_islands)]
pub use volume_room_hysteresis_island::{room_free_clamp, room_resume_floor};

/// Mirror of Clean's `room_free_clamp` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn room_free_clamp(free_mb: u64, total_mb: u64) -> u64 {
    if free_mb < total_mb {
        free_mb
    } else {
        total_mb
    }
}

/// Mirror of Clean's `room_resume_floor` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn room_resume_floor(low_mb: u64, resume_mb: u64) -> u64 {
    if low_mb < resume_mb {
        resume_mb
    } else {
        low_mb
    }
}

contract_fn! {
    /// Kernel-certified check that `free_mb` meets or exceeds `floor_mb` (`floor_mb <= free_mb`),
    /// linked via `clean-kernel-defeq` to `room_satisfies_floor_isl`.
    #[must_use]
    pub const fn room_satisfies_floor(free_mb: u64, floor_mb: u64) -> bool
    clauses [ensures result == (floor_mb <= free_mb)]
    {
        floor_mb <= free_mb
    }
}

/// Default low-space trigger (`16 GiB == 16_384 MiB`).
pub const DEFAULT_LOW_ROOM_MB: u64 = 16_384;

/// Default resume watermark (`24 GiB == 24_576 MiB`).
pub const DEFAULT_RESUME_ROOM_MB: u64 = 24_576;

/// Candidate build-cache directory inspected during free-space reclamation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BuildCacheCandidate {
    /// Stable cache identifier or path label.
    pub cache_id: String,
    /// Estimated reclaimable size in MiB.
    pub size_mb: u64,
    /// Monotone timestamp (ms) when a session last touched this cache.
    pub last_used_ms: u64,
    /// `true` when an active session/compiler holds a Cargo or Targo lock inside it.
    pub in_use_by_live_session: bool,
}

/// Verdict for `aterm ctl @self await sys 'free>=room'`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RoomState {
    /// Volume has comfortable room (`free_mb >= resume_room_mb`, or `>= low_room_mb` while not draining).
    HasRoom { free_mb: u64 },
    /// Volume dropped below `low_room_mb` and has not yet recovered to `resume_room_mb`.
    WaitingForRoom {
        free_mb: u64,
        needed_to_resume_mb: u64,
    },
}

/// Per-volume hysteresis tracker and LRU idle-cache eviction selector.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VolumeRoomLedger {
    low_room_mb: u64,
    resume_room_mb: u64,
    free_mb: u64,
    total_mb: u64,
    draining: bool,
}

impl VolumeRoomLedger {
    /// Construct a volume ledger with certified `low_room_mb <= resume_room_mb`.
    #[must_use]
    pub const fn new(
        low_room_mb: u64,
        req_resume_mb: u64,
        init_free_mb: u64,
        total_mb: u64,
    ) -> Self {
        let resume = room_resume_floor(low_room_mb, req_resume_mb);
        let free = room_free_clamp(init_free_mb, total_mb);
        let draining = !room_satisfies_floor(free, low_room_mb);
        Self {
            low_room_mb,
            resume_room_mb: resume,
            free_mb: free,
            total_mb,
            draining,
        }
    }

    /// Lower trigger watermark (`low_room_mb`).
    #[must_use]
    pub const fn low_room_mb(&self) -> u64 {
        self.low_room_mb
    }

    /// Upper recovery watermark (`resume_room_mb >= low_room_mb`).
    #[must_use]
    pub const fn resume_room_mb(&self) -> u64 {
        self.resume_room_mb
    }

    /// Most recently observed clamped free disk space (`MiB`).
    #[must_use]
    pub const fn free_mb(&self) -> u64 {
        self.free_mb
    }

    /// Total volume capacity (`MiB`).
    #[must_use]
    pub const fn total_mb(&self) -> u64 {
        self.total_mb
    }

    /// Whether the volume is currently inside the hysteresis drain band.
    #[must_use]
    pub const fn is_draining(&self) -> bool {
        self.draining
    }

    /// Update the volume's observed free space (`MiB`) and return the hysteresis verdict.
    pub fn observe_free_mb(&mut self, raw_free_mb: u64) -> RoomState {
        let free = room_free_clamp(raw_free_mb, self.total_mb);
        self.free_mb = free;
        if self.draining {
            if room_satisfies_floor(free, self.resume_room_mb) {
                self.draining = false;
                RoomState::HasRoom { free_mb: free }
            } else {
                RoomState::WaitingForRoom {
                    free_mb: free,
                    needed_to_resume_mb: self.resume_room_mb.saturating_sub(free),
                }
            }
        } else if !room_satisfies_floor(free, self.low_room_mb) {
            self.draining = true;
            RoomState::WaitingForRoom {
                free_mb: free,
                needed_to_resume_mb: self.resume_room_mb.saturating_sub(free),
            }
        } else {
            RoomState::HasRoom { free_mb: free }
        }
    }

    /// Plan an ordered list of idle cache IDs (`!in_use_by_live_session`, oldest `last_used_ms`
    /// first) whose eviction raises projected free space to `resume_room_mb`.
    #[must_use]
    pub fn plan_idle_cache_eviction(&self, candidates: &[BuildCacheCandidate]) -> Vec<String> {
        if !self.draining && room_satisfies_floor(self.free_mb, self.low_room_mb) {
            return Vec::new();
        }
        let mut eligible: Vec<usize> = Vec::new();
        let mut i = 0usize;
        while i < candidates.len() {
            if let Some(c) = candidates.get(i) {
                if !c.in_use_by_live_session && c.size_mb > 0 {
                    eligible.push(i);
                }
            }
            i = i.saturating_add(1);
        }
        let mut a = 1usize;
        while a < eligible.len() {
            let Some(&key_idx) = eligible.get(a) else {
                break;
            };
            let mut b = a;
            while b > 0 {
                let Some(&prev_idx) = eligible.get(b.saturating_sub(1)) else {
                    break;
                };
                let (Some(prev_c), Some(key_c)) =
                    (candidates.get(prev_idx), candidates.get(key_idx))
                else {
                    break;
                };
                let out_of_order = if prev_c.last_used_ms != key_c.last_used_ms {
                    prev_c.last_used_ms > key_c.last_used_ms
                } else {
                    prev_c.cache_id > key_c.cache_id
                };
                if !out_of_order {
                    break;
                }
                if let Some(slot) = eligible.get_mut(b) {
                    *slot = prev_idx;
                }
                b = b.saturating_sub(1);
            }
            if let Some(slot) = eligible.get_mut(b) {
                *slot = key_idx;
            }
            a = a.saturating_add(1);
        }

        let mut projected = self.free_mb;
        let mut evicted: Vec<String> = Vec::new();
        let mut k = 0usize;
        while k < eligible.len() && !room_satisfies_floor(projected, self.resume_room_mb) {
            if let Some(&idx) = eligible.get(k) {
                if let Some(c) = candidates.get(idx) {
                    let mut cid = String::new();
                    cid.push_str(&c.cache_id);
                    evicted.push(cid);
                    projected = room_free_clamp(projected.saturating_add(c.size_mb), self.total_mb);
                }
            }
            k = k.saturating_add(1);
        }
        evicted
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hysteresis_prevents_thrash_and_evicts_only_idle_lru_caches() {
        let clamped = VolumeRoomLedger::new(16_000, 10_000, 50_000, 100_000);
        assert_eq!(clamped.resume_room_mb(), 16_000);
        assert_eq!(clamped.low_room_mb(), 16_000);
        assert_eq!(clamped.total_mb(), 100_000);

        let mut ledger = VolumeRoomLedger::new(16_000, 24_000, 30_000, 100_000);
        assert_eq!(
            ledger.observe_free_mb(18_000),
            RoomState::HasRoom { free_mb: 18_000 }
        );
        assert_eq!(
            ledger.observe_free_mb(14_000),
            RoomState::WaitingForRoom {
                free_mb: 14_000,
                needed_to_resume_mb: 10_000,
            }
        );
        assert!(ledger.is_draining());
        assert_eq!(ledger.free_mb(), 14_000);
        assert_eq!(
            ledger.observe_free_mb(20_000),
            RoomState::WaitingForRoom {
                free_mb: 20_000,
                needed_to_resume_mb: 4_000,
            }
        );

        let caches = vec![
            BuildCacheCandidate {
                cache_id: "active-tab-cache".to_string(),
                size_mb: 12_000,
                last_used_ms: 10,
                in_use_by_live_session: true,
            },
            BuildCacheCandidate {
                cache_id: "newer-idle".to_string(),
                size_mb: 5_000,
                last_used_ms: 500,
                in_use_by_live_session: false,
            },
            BuildCacheCandidate {
                cache_id: "oldest-idle".to_string(),
                size_mb: 3_000,
                last_used_ms: 100,
                in_use_by_live_session: false,
            },
        ];
        assert_eq!(
            ledger.plan_idle_cache_eviction(&caches),
            vec!["oldest-idle".to_string(), "newer-idle".to_string()]
        );

        assert_eq!(
            ledger.observe_free_mb(25_000),
            RoomState::HasRoom { free_mb: 25_000 }
        );
    }
}
