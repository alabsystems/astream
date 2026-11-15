// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Permanent stale-leader (`zombie`) write/replicate fence (`failover_fences_stale`,
//! `Astream.LeaseFail.TlaZombieLeaderFence`) rejecting any frame bearing an epoch below
//! the follower's highest witnessed epoch.

#[cfg(clean_islands)]
#[path = "zombie_leader_fence_island.rs"]
mod zombie_leader_fence_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lhf_req_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lhf_fenced_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use zombie_leader_fence_island::{lhf_fenced_advance, lhf_req_clamp};

/// Maximum batch records inspected per replicate frame (`4096`).
pub const MAX_REPLICATE_RECORDS: u64 = 4096;

contract_fn! {
    /// Verified non-stale leader epoch (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `lhf_epoch_current_isl`.
    #[must_use]
    pub const fn lhf_epoch_current(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct ZombieLeaderFence {
    fenced_epoch: u64,
    rejected_batches: u64,
}

impl ZombieLeaderFence {
    #[must_use]
    pub const fn new(initial_epoch: u64) -> Self {
        Self {
            fenced_epoch: initial_epoch,
            rejected_batches: 0,
        }
    }

    pub fn admit_replicate(&mut self, writer_epoch: u64, record_count: u64) -> Option<u64> {
        if !lhf_epoch_current(writer_epoch, self.fenced_epoch) {
            self.rejected_batches = self.rejected_batches.saturating_add(1);
            return None;
        }
        self.fenced_epoch = lhf_fenced_advance(self.fenced_epoch, writer_epoch);
        Some(lhf_req_clamp(record_count, MAX_REPLICATE_RECORDS))
    }

    #[must_use]
    pub const fn rejected_batches(&self) -> u64 {
        self.rejected_batches
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn permanently_fences_old_leader_after_higher_epoch_witnessed() {
        let mut f = ZombieLeaderFence::new(3);
        assert_eq!(f.admit_replicate(3, 12), Some(12));
        assert_eq!(f.admit_replicate(4, 8), Some(8));
        assert_eq!(f.admit_replicate(3, 5), None);
        assert_eq!(f.rejected_batches(), 1);
    }
}
