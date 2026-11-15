// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Memory-aware `VERIFY_JOBS` (`1..=18`) parallel `targo trust` shard slot pool sizing worker
//! concurrency so `N * 2.5 GiB <= available_ram` without serializing independent shards
//! (`Astream.SmtGov.TlaParallelShardSlots`).

#[cfg(clean_islands)]
#[path = "parallel_shard_slots_island.rs"]
mod parallel_shard_slots_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn smt_slots_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn smt_batch_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use parallel_shard_slots_island::{smt_batch_advance, smt_slots_clamp};

/// Maximum parallel `targo trust` shard processes (`18` on an 18-core Apple Silicon host).
pub const MAX_VERIFY_SHARD_SLOTS: u64 = 18;

contract_fn! {
    /// Verified slot availability (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `smt_slot_granted_isl`.
    #[must_use]
    pub const fn smt_slot_granted(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Governs concurrent `targo trust` shard processes bounded by both CPU cores and RAM (`2560` MiB/slot).
#[derive(Debug, Clone)]
pub struct VerifyShardPool {
    max_slots: u64,
    in_use: u64,
    dispatched: u64,
}

impl VerifyShardPool {
    #[must_use]
    pub const fn from_host(cpu_cores: u64, free_ram_mb: u64) -> Self {
        let by_ram = free_ram_mb / 2_560;
        let raw = if by_ram < cpu_cores {
            by_ram
        } else {
            cpu_cores
        };
        let non_zero = if raw == 0 { 1 } else { raw };
        Self {
            max_slots: smt_slots_clamp(non_zero, MAX_VERIFY_SHARD_SLOTS),
            in_use: 0,
            dispatched: 0,
        }
    }

    pub fn try_acquire(&mut self) -> bool {
        let needed = self.in_use.saturating_add(1);
        if !smt_slot_granted(self.max_slots, needed) {
            return false;
        }
        self.in_use = needed;
        self.dispatched = smt_batch_advance(self.dispatched, self.dispatched.saturating_add(1));
        true
    }

    pub fn release(&mut self) {
        self.in_use = self.in_use.saturating_sub(1);
    }

    #[must_use]
    pub const fn max_slots(&self) -> u64 {
        self.max_slots
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shard_pool_caps_slots_by_ram_and_cores_and_recycles_released_slots() {
        let mut p = VerifyShardPool::from_host(18, 6_000);
        assert_eq!(p.max_slots(), 2);
        assert!(p.try_acquire());
        assert!(p.try_acquire());
        assert!(!p.try_acquire());
        p.release();
        assert!(p.try_acquire());
    }
}
