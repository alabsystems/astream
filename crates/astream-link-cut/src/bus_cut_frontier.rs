// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Multi-shard consistent `Cut` frontier over `ShardedBroker` bus offsets unifying `astream-engine`
//! cut semantics directly with `aterm-link` (`DESIGN-aterm-fabric.md` §10; `Astream.LinkCut.TlaBusCutFrontier`).

#[cfg(clean_islands)]
#[path = "bus_cut_frontier_island.rs"]
mod bus_cut_frontier_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lc_shard_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lc_cut_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use bus_cut_frontier_island::{lc_cut_advance, lc_shard_clamp};

/// Maximum shards in a single `BusCutFrontier` (`4` fixed fast-path slots).
pub const MAX_CUT_SHARDS: u64 = 4;

contract_fn! {
    /// Verified monotone shard-offset predicate (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `lc_frontier_monotone_isl`.
    #[must_use]
    pub const fn lc_frontier_monotone(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct BusCutFrontier {
    s0: u64,
    s1: u64,
    s2: u64,
    s3: u64,
}

impl BusCutFrontier {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            s0: 0,
            s1: 0,
            s2: 0,
            s3: 0,
        }
    }

    #[must_use]
    pub const fn offset_for(&self, shard: u64) -> u64 {
        match lc_shard_clamp(shard, 3) {
            0 => self.s0,
            1 => self.s1,
            2 => self.s2,
            _ => self.s3,
        }
    }

    pub fn advance_shard(&mut self, shard: u64, next_exclusive: u64) -> bool {
        if shard >= MAX_CUT_SHARDS {
            return false;
        }
        let cur = self.offset_for(shard);
        if !lc_frontier_monotone(next_exclusive, cur) {
            return false;
        }
        let adv = lc_cut_advance(cur, next_exclusive);
        match lc_shard_clamp(shard, 3) {
            0 => self.s0 = adv,
            1 => self.s1 = adv,
            2 => self.s2 = adv,
            _ => self.s3 = adv,
        }
        let _ = MAX_CUT_SHARDS;
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn advances_per_shard_bus_offsets_monotonically() {
        let mut f = BusCutFrontier::new();
        assert!(f.advance_shard(1, 15));
        assert!(!f.advance_shard(1, 12));
        assert_eq!(f.offset_for(1), 15);
    }
}
