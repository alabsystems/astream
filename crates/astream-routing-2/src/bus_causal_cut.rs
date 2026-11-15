// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Transport-agnostic broker bus causal cut verifier (`Astream.Engine.TlaBusCausalCutB88`).
//!
//! Closes the `DESIGN-aterm-fabric.md` §10 gap where `aterm-link` previously had to
//! maintain its own `Cut::is_consistent` check over broker bus records because
//! `astream-engine` only modeled host envelope logs. Given per-shard frontier offsets
//! and cross-shard causal edges `(origin_shard, origin_offset) -> (target_shard, target_offset)`,
//! verifies Mattern/Chandy-Lamport causal consistency (`e2 in C /\ e1 -> e2 => e1 in C`).

#[cfg(clean_islands)]
#[path = "bus_causal_cut_island.rs"]
mod bus_causal_cut_island;
#[cfg(clean_islands)]
pub use bus_causal_cut_island::{cut_frontier_advance, cut_shards_clamp};

/// Hard upper bound on shards tracked in a single `BusCausalCut`.
pub const MAX_CUT_SHARDS: usize = 64;

#[cfg(not(clean_islands))]
/// Monotonically advance a shard's included frontier offset in a causal cut.
#[must_use]
pub const fn cut_frontier_advance(cur_off: u64, cand_off: u64) -> u64 {
    if cur_off < cand_off {
        cand_off
    } else {
        cur_off
    }
}

#[cfg(not(clean_islands))]
/// Clamp tracked shard count to `max_shards`.
#[must_use]
pub const fn cut_shards_clamp(cand_shards: u64, max_shards: u64) -> u64 {
    if cand_shards < max_shards {
        cand_shards
    } else {
        max_shards
    }
}

contract_fn! {
    /// True iff `origin_off` is included within `origin_frontier`.
    #[must_use]
    pub const fn dep_satisfied_in_cut(origin_off: u64, origin_frontier: u64) -> bool
    clauses [ensures result == (origin_off <= origin_frontier)]
    {
        origin_off <= origin_frontier
    }
}

/// Cross-shard happens-before edge observed on a broker bus record (`cause -> effect`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BusCausalEdge {
    pub origin_shard: u32,
    pub origin_offset: u64,
    pub target_shard: u32,
    pub target_offset: u64,
}

/// Violation witness when a cut includes `target` without its causal `origin`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CausalCutError {
    TooManyShards {
        max_shards: usize,
    },
    MissingOriginShard {
        edge: BusCausalEdge,
    },
    OrphanEffect {
        edge: BusCausalEdge,
        origin_frontier: u64,
    },
}

/// Per-shard `(shard_id, inclusive_frontier_offset)` entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ShardFrontier {
    pub shard_id: u32,
    pub inclusive_offset: u64,
}

/// Bounded multi-shard causal cut over broker bus offsets.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BusCausalCut {
    shards: Vec<ShardFrontier>,
}

impl Default for BusCausalCut {
    fn default() -> Self {
        Self::new()
    }
}

impl BusCausalCut {
    #[must_use]
    pub const fn new() -> Self {
        Self { shards: Vec::new() }
    }

    #[must_use]
    pub fn shard_count(&self) -> usize {
        cut_shards_clamp(self.shards.len() as u64, MAX_CUT_SHARDS as u64) as usize
    }

    /// Look up the inclusive frontier offset for `shard_id`, if present in the cut.
    #[must_use]
    pub fn frontier_of(&self, shard_id: u32) -> Option<u64> {
        let mut rest = self.shards.as_slice();
        while let &[entry, ref tail @ ..] = rest {
            if entry.shard_id == shard_id {
                return Some(entry.inclusive_offset);
            }
            rest = tail;
        }
        None
    }

    /// Insert or monotonically advance `shard_id`'s frontier to at least `cand_offset`.
    pub fn advance_shard(
        &mut self,
        shard_id: u32,
        cand_offset: u64,
    ) -> Result<u64, CausalCutError> {
        for entry in &mut self.shards {
            if entry.shard_id == shard_id {
                entry.inclusive_offset = cut_frontier_advance(entry.inclusive_offset, cand_offset);
                return Ok(entry.inclusive_offset);
            }
        }
        if self.shards.len() >= MAX_CUT_SHARDS {
            return Err(CausalCutError::TooManyShards {
                max_shards: MAX_CUT_SHARDS,
            });
        }
        self.shards.push(ShardFrontier {
            shard_id,
            inclusive_offset: cand_offset,
        });
        Ok(cand_offset)
    }

    /// Verify Chandy-Lamport consistency across all observed cross-shard `edges`.
    pub fn verify_consistent(&self, edges: &[BusCausalEdge]) -> Result<(), CausalCutError> {
        let mut rest = edges;
        while let &[edge, ref tail @ ..] = rest {
            if let Some(target_front) = self.frontier_of(edge.target_shard) {
                if edge.target_offset <= target_front {
                    match self.frontier_of(edge.origin_shard) {
                        None => return Err(CausalCutError::MissingOriginShard { edge }),
                        Some(origin_front) => {
                            if !dep_satisfied_in_cut(edge.origin_offset, origin_front) {
                                return Err(CausalCutError::OrphanEffect {
                                    edge,
                                    origin_frontier: origin_front,
                                });
                            }
                        }
                    }
                }
            }
            rest = tail;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_orphan_effect_and_accepts_closed_causal_cut() {
        let mut cut = BusCausalCut::new();
        cut.advance_shard(0, 10).unwrap();
        cut.advance_shard(1, 25).unwrap();

        let edges = [BusCausalEdge {
            origin_shard: 0,
            origin_offset: 12,
            target_shard: 1,
            target_offset: 20,
        }];

        // Target (1, 20) is inside shard 1's frontier (25), but origin (0, 12) > 10 -> orphan!
        assert_eq!(
            cut.verify_consistent(&edges),
            Err(CausalCutError::OrphanEffect {
                edge: edges[0],
                origin_frontier: 10,
            })
        );

        // Advancing shard 0 to 12 closes the cut cleanly
        cut.advance_shard(0, 12).unwrap();
        assert_eq!(cut.verify_consistent(&edges), Ok(()));
    }
}
