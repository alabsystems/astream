// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Consistent-hash virtual-node shard ring & live shard-split drain fence (`astream-broker`).
//!
//! Extends `sharded.rs` horizontal subject partitioning with:
//! 1. **Deterministic virtual-node consistent hashing ([`ConsistentShardRing`]):** maps
//!    subject routing keys across `0..shard_count` via FNV-1a-64 virtual tokens so adding
//!    a shard moves only `~1/N` of subjects rather than reshuffling `hash % N`.
//! 2. **Order-preserving shard-split drain barrier ([`ShardMigrationFence`]):** while
//!    migrating a hash range `[token_lo, token_hi]` from `src_shard` to `dst_shard`, pins
//!    `barrier_offset` on `src_shard` and withholds direct `dst_shard` tail cutover until
//!    `shard_drain_complete(drained_offset, barrier_offset)` holds, preserving per-subject
//!    FIFO causal order across live shard splits!
//!
//! Backed by Clean TLA+ island `Astream.Broker.TlaShardedRingMigration`.

#![allow(clippy::manual_clamp)]

#[cfg(clean_islands)]
#[path = "sharded_ring_rebalancer_island.rs"]
mod sharded_ring_rebalancer_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn ring_shard_idx_clamp(shard_idx: u64, max_shard_idx: u64) -> u64 {
    if shard_idx < max_shard_idx {
        shard_idx
    } else {
        max_shard_idx
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ring_drain_offset_clamp(drained_off: u64, barrier_off: u64) -> u64 {
    if drained_off < barrier_off {
        drained_off
    } else {
        barrier_off
    }
}
#[cfg(clean_islands)]
pub use sharded_ring_rebalancer_island::{ring_drain_offset_clamp, ring_shard_idx_clamp};

contract_fn! {
    /// Kernel-certified check that `src_shard` has drained all pre-split records up to
    /// `barrier_off` (`barrier_off <= drained_off`), linked via `clean-kernel-defeq`
    /// to `shard_drain_complete_isl`.
    #[must_use]
    pub const fn shard_drain_complete(drained_off: u64, barrier_off: u64) -> bool
    clauses [ensures result == (barrier_off <= drained_off)]
    {
        barrier_off <= drained_off
    }
}

/// Maximum physical shards in a single [`ConsistentShardRing`].
pub const MAX_RING_SHARDS: usize = 256;
/// Default virtual ring tokens per physical shard (`32`).
pub const DEFAULT_VNODES_PER_SHARD: usize = 32;

const fn fnv1a_64_pair(a: &[u8], b: &[u8]) -> u64 {
    const OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
    const PRIME: u64 = 0x0000_0100_0000_01b3;
    let mut h = OFFSET;
    let mut cur_a = a;
    while let &[byte, ref rest @ ..] = cur_a {
        h = (h ^ (byte as u64)).wrapping_mul(PRIME);
        cur_a = rest;
    }
    let mut cur_b = b;
    while let &[byte, ref rest @ ..] = cur_b {
        h = (h ^ (byte as u64)).wrapping_mul(PRIME);
        cur_b = rest;
    }
    h
}

/// Virtual token entry `(token_hash, shard_id)` sorted in ascending `(token_hash, shard_id)` order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RingPoint {
    token: u64,
    shard: usize,
}

/// Deterministic virtual-node consistent-hash ring over `1..=MAX_RING_SHARDS` shards.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConsistentShardRing {
    shard_count: usize,
    vnodes_per_shard: usize,
    points: Vec<RingPoint>,
}

impl ConsistentShardRing {
    /// Build a sorted consistent-hash ring for `shard_count` (`1..=MAX_RING_SHARDS`) shards.
    #[must_use]
    pub fn new(shard_count: usize, vnodes_per_shard: usize) -> Self {
        let count = if shard_count < 1 {
            1
        } else if shard_count > MAX_RING_SHARDS {
            MAX_RING_SHARDS
        } else {
            shard_count
        };
        let vnodes = if vnodes_per_shard < 1 {
            1
        } else if vnodes_per_shard > 128 {
            128
        } else {
            vnodes_per_shard
        };
        let max_idx = count.saturating_sub(1) as u64;
        let raw_pts_cap = count.saturating_mul(vnodes);
        let pts_cap = if raw_pts_cap < 65_536 {
            raw_pts_cap
        } else {
            65_536
        };
        let mut points = {
            let _ = pts_cap;
            Vec::new()
        };

        let mut s = 0usize;
        while s < count {
            let clamped_s = ring_shard_idx_clamp(s as u64, max_idx) as usize;
            let mut v = 0usize;
            while v < vnodes {
                let [s0, s1, s2, s3, s4, s5, s6, s7] = (clamped_s as u64).to_le_bytes();
                let [v0, v1, v2, v3, v4, v5, v6, v7] = (v as u64).to_le_bytes();
                let key_buf = [
                    s0, s1, s2, s3, s4, s5, s6, s7, v0, v1, v2, v3, v4, v5, v6, v7,
                ];
                let token = fnv1a_64_pair(b"astream-ring-vnode/v1:", &key_buf);
                points.push(RingPoint {
                    token,
                    shard: clamped_s,
                });
                v = v.saturating_add(1);
            }
            s = s.saturating_add(1);
        }

        // Insertion sort (bounded `<= 256 * 128 = 32768`, zero closures!).
        let mut i = 1usize;
        while let Some(&cur) = points.get(i) {
            let mut j = i;
            while j > 0 {
                let Some(&prev) = points.get(j.saturating_sub(1)) else {
                    break;
                };
                let greater =
                    prev.token > cur.token || (prev.token == cur.token && prev.shard > cur.shard);
                if !greater {
                    break;
                }
                if let Some(slot) = points.get_mut(j) {
                    *slot = prev;
                }
                j = j.saturating_sub(1);
            }
            if let Some(slot) = points.get_mut(j) {
                *slot = cur;
            }
            i = i.saturating_add(1);
        }

        Self {
            shard_count: count,
            vnodes_per_shard: vnodes,
            points,
        }
    }

    /// Number of physical shards (`1..=MAX_RING_SHARDS`).
    #[must_use]
    pub const fn shard_count(&self) -> usize {
        self.shard_count
    }

    /// Configured virtual tokens per physical shard (`1..=128`).
    #[must_use]
    pub const fn vnodes_per_shard(&self) -> usize {
        self.vnodes_per_shard
    }

    /// Compute the 64-bit ring token for `routing_key`.
    #[must_use]
    pub const fn key_token(routing_key: &str) -> u64 {
        fnv1a_64_pair(b"astream-ring-key/v1:", routing_key.as_bytes())
    }

    /// Route `routing_key` clockwise to its owning shard in `0..self.shard_count`.
    #[must_use]
    pub fn route(&self, routing_key: &str) -> usize {
        let tok = Self::key_token(routing_key);
        let mut lo = 0usize;
        let mut hi = self.points.len();
        while lo < hi {
            let mid = lo.saturating_add(hi.saturating_sub(lo) / 2);
            let Some(&mid_pt) = self.points.get(mid) else {
                break;
            };
            if mid_pt.token < tok {
                lo = mid.saturating_add(1);
            } else {
                hi = mid;
            }
        }
        let chosen = match self.points.get(lo) {
            Some(p) => p.shard,
            None => match self.points.first() {
                Some(p0) => p0.shard,
                None => 0,
            },
        };
        let max_idx = self.shard_count.saturating_sub(1) as u64;
        ring_shard_idx_clamp(chosen as u64, max_idx) as usize
    }
}

/// Live drain fence governing an in-flight range migration from `src_shard` to `dst_shard`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ShardMigrationFence {
    /// Inclusive lower ring token being migrated.
    pub token_lo: u64,
    /// Inclusive upper ring token being migrated.
    pub token_hi: u64,
    /// Previous owner shard (`< shard_count`).
    pub src_shard: usize,
    /// New owner shard (`< shard_count`).
    pub dst_shard: usize,
    /// Offset on `src_shard` at which new writes stopped entering `src_shard`.
    pub barrier_offset: u64,
    /// Clamped offset on `src_shard` already copied/replayed to `dst_shard` (`<= barrier_offset`).
    pub drained_offset: u64,
}

impl ShardMigrationFence {
    /// Construct a new [`ShardMigrationFence`] anchored at `barrier_offset`.
    #[must_use]
    pub fn new(
        shard_count: usize,
        token_lo: u64,
        token_hi: u64,
        src_shard: usize,
        dst_shard: usize,
        barrier_offset: u64,
    ) -> Self {
        let bounded_shards = if shard_count < 1 {
            1
        } else if shard_count > MAX_RING_SHARDS {
            MAX_RING_SHARDS
        } else {
            shard_count
        };
        let max_idx = bounded_shards.saturating_sub(1) as u64;
        Self {
            token_lo,
            token_hi,
            src_shard: ring_shard_idx_clamp(src_shard as u64, max_idx) as usize,
            dst_shard: ring_shard_idx_clamp(dst_shard as u64, max_idx) as usize,
            barrier_offset,
            drained_offset: 0,
        }
    }

    /// Advance the drained source offset monotonically toward `barrier_offset`.
    pub fn advance_drain(&mut self, newly_drained_offset: u64) -> bool {
        let clamped = ring_drain_offset_clamp(newly_drained_offset, self.barrier_offset);
        if clamped > self.drained_offset {
            self.drained_offset = clamped;
        }
        self.is_cutover_ready()
    }

    /// True once `drained_offset` has reached `barrier_offset` (`shard_drain_complete`).
    #[must_use]
    pub const fn is_cutover_ready(&self) -> bool {
        shard_drain_complete(self.drained_offset, self.barrier_offset)
    }

    /// Resolve which shard a reader should read `routing_key` from: keeps reading `src_shard`
    /// while `[token_lo, token_hi]` is still draining below `barrier_offset`, then switches
    /// cleanly to `dst_shard`!
    #[must_use]
    pub fn resolve_read_shard(&self, ring: &ConsistentShardRing, routing_key: &str) -> usize {
        let tok = ConsistentShardRing::key_token(routing_key);
        if tok >= self.token_lo && tok <= self.token_hi {
            if self.is_cutover_ready() {
                self.dst_shard
            } else {
                self.src_shard
            }
        } else {
            ring.route(routing_key)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn consistent_ring_minimizes_remapping_and_drain_fence_preserves_fifo_cutover() {
        let r4 = ConsistentShardRing::new(4, 32);
        let r5 = ConsistentShardRing::new(5, 32);

        let mut moved = 0usize;
        for i in 0..200u32 {
            let key = format!("/a/session/{i}/out");
            let s4 = r4.route(&key);
            let s5 = r5.route(&key);
            assert!(s4 < 4 && s5 < 5);
            if s4 != s5 {
                moved += 1;
            }
        }
        // Adding a 5th shard moves roughly ~20% of keys, far less than modulo reshuffling (>75%)!
        assert!(moved > 0 && moved < 90, "moved={moved}");

        let key = "/a/session/42/out";
        let tok = ConsistentShardRing::key_token(key);
        let mut fence = ShardMigrationFence::new(5, tok, tok, 1, 4, 150);
        assert!(!fence.is_cutover_ready());
        assert_eq!(fence.resolve_read_shard(&r5, key), 1);

        assert!(!fence.advance_drain(149));
        assert_eq!(fence.resolve_read_shard(&r5, key), 1);

        assert!(fence.advance_drain(150));
        assert_eq!(fence.resolve_read_shard(&r5, key), 4);
    }
}
