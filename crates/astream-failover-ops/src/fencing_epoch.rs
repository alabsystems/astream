// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Monotone `(epoch, op_seq)` Kleppmann fencing-token issuer and zombie-leader write barrier
//! (`Astream.Failover.TlaFencingEpoch`).
//!
//! Guarantees split-brain immunity across arbitrary GC pauses or network partitions:
//! - Every promoted leader mints fencing tokens under its strictly higher `epoch`.
//! - Every follower/storage target latches `min_epoch = fence_token_advance(min_epoch, tok.epoch)`
//!   and rejects any write carrying `tok.epoch < min_epoch` (`!fence_admits_epoch`).

use std::collections::BTreeMap;

#[cfg(clean_islands)]
#[path = "fencing_epoch_island.rs"]
mod fencing_epoch_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn fence_epoch_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn fence_token_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use fencing_epoch_island::{fence_epoch_clamp, fence_token_advance};

/// Maximum follower fencing barriers tracked in one coordinator view.
pub const MAX_TRACKED_FOLLOWERS: u64 = 32;

contract_fn! {
    /// Verified epoch admission check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `fence_admits_epoch_isl`.
    #[must_use]
    pub const fn fence_admits_epoch(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Lexicographically ordered `(epoch, seq)` fencing token attached to replicated batches.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct FencingToken {
    pub epoch: u64,
    pub seq: u64,
}

/// Write-admission verdict at a fenced follower or storage target.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FenceAdmission {
    Admitted { latched_epoch: u64 },
    FencedStaleEpoch { min_epoch: u64 },
    FencedOutOfOrderSeq { last_seq: u64 },
}

/// Multi-follower fencing barrier ledger.
#[derive(Debug, Clone)]
pub struct FencingEpochLedger {
    max_followers: u64,
    global_min_epoch: u64,
    followers: BTreeMap<u64, FencingToken>,
}

impl Default for FencingEpochLedger {
    fn default() -> Self {
        Self::new()
    }
}

impl FencingEpochLedger {
    #[must_use]
    pub fn new() -> Self {
        Self {
            max_followers: fence_epoch_clamp(MAX_TRACKED_FOLLOWERS, MAX_TRACKED_FOLLOWERS),
            global_min_epoch: 0,
            followers: BTreeMap::new(),
        }
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.followers.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.followers.is_empty()
    }

    /// Evaluates `tok` at `follower_id`, latching any higher epoch and rejecting zombie leaders.
    pub fn check_and_latch(&mut self, follower_id: u64, tok: FencingToken) -> FenceAdmission {
        if let Some(&cur) = self.followers.get(&follower_id) {
            if !fence_admits_epoch(tok.epoch, cur.epoch) {
                return FenceAdmission::FencedStaleEpoch {
                    min_epoch: cur.epoch,
                };
            }
            if tok.epoch == cur.epoch && tok.seq <= cur.seq {
                return FenceAdmission::FencedOutOfOrderSeq { last_seq: cur.seq };
            }
        } else if (self.followers.len() as u64) >= self.max_followers {
            return FenceAdmission::FencedStaleEpoch {
                min_epoch: self.global_min_epoch,
            };
        }
        let prev_epoch = match self.followers.get(&follower_id) {
            Some(t) => t.epoch,
            None => 0,
        };
        let latched = fence_token_advance(prev_epoch, tok.epoch);
        self.global_min_epoch = fence_token_advance(self.global_min_epoch, latched);
        self.followers.insert(
            follower_id,
            FencingToken {
                epoch: latched,
                seq: tok.seq,
            },
        );
        FenceAdmission::Admitted {
            latched_epoch: latched,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fencing_token_latches_higher_epoch_and_permanently_blocks_deposed_leader() {
        let mut ledger = FencingEpochLedger::new();
        assert_eq!(
            ledger.check_and_latch(1, FencingToken { epoch: 2, seq: 10 }),
            FenceAdmission::Admitted { latched_epoch: 2 }
        );
        assert_eq!(
            ledger.check_and_latch(1, FencingToken { epoch: 3, seq: 1 }),
            FenceAdmission::Admitted { latched_epoch: 3 }
        );
        // Zombie leader from epoch 2 wakes from GC pause -> permanently fenced!
        assert_eq!(
            ledger.check_and_latch(1, FencingToken { epoch: 2, seq: 11 }),
            FenceAdmission::FencedStaleEpoch { min_epoch: 3 }
        );
        assert_eq!(
            ledger.check_and_latch(1, FencingToken { epoch: 3, seq: 1 }),
            FenceAdmission::FencedOutOfOrderSeq { last_seq: 1 }
        );
    }
}
