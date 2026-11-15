// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Session-fork causal lineage anchor & bounded fork-depth fence
//! (`Astream.Engine.TlaForkLineageAnchorFence`).
//!
//! Guarantees that every forked `aterm` agent/terminal session anchors at an
//! already-committed parent offset (`fork_anchor <= parent_hw`), strictly bounds
//! nested fork depth (`fork_depth <= max_fork_depth`), and monotonically
//! advances the child's own high-water mark from `fork_anchor`.

#[cfg(clean_islands)]
#[path = "fork_lineage_anchor_fence_island.rs"]
mod fork_lineage_anchor_fence_island;
#[cfg(clean_islands)]
pub use fork_lineage_anchor_fence_island::{branch_hw_advance, fork_depth_clamp};

/// Default maximum nested session-fork depth (`64`).
pub const MAX_SESSION_FORK_DEPTH: u64 = 64;

#[cfg(not(clean_islands))]
/// Clamp fork depth to `max_depth`.
#[must_use]
pub const fn fork_depth_clamp(cand_depth: u64, max_depth: u64) -> u64 {
    if cand_depth < max_depth {
        cand_depth
    } else {
        max_depth
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance child branch high-water offset above `fork_anchor`.
#[must_use]
pub const fn branch_hw_advance(cur_hw: u64, cand_hw: u64) -> u64 {
    if cur_hw < cand_hw {
        cand_hw
    } else {
        cur_hw
    }
}

contract_fn! {
    /// True iff `fork_anchor <= parent_hw` and `next_depth <= max_depth`.
    #[must_use]
    pub const fn fork_admissible(fork_anchor: u64,
        parent_hw: u64,
        next_depth: u64,
        max_depth: u64,) -> bool
    clauses [ensures result == (fork_anchor <= parent_hw && next_depth <= max_depth)]
    {
        fork_anchor <= parent_hw && next_depth <= max_depth
    }
}

/// Refusal reasons when attempting to fork an `astream-engine` session log.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ForkLineageError {
    AnchorBeyondParentHw { fork_anchor: u64, parent_hw: u64 },
    ForkDepthExceeded { next_depth: u64, max_depth: u64 },
}

/// Pure stack causal lineage guard for forked session branches.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ForkLineageAnchorFence {
    max_depth: u64,
    fork_depth: u64,
    fork_anchor: u64,
    branch_hw: u64,
}

impl ForkLineageAnchorFence {
    #[must_use]
    pub const fn root(initial_hw: u64, max_depth: u64) -> Self {
        let cap = if max_depth == 0 {
            MAX_SESSION_FORK_DEPTH
        } else {
            max_depth
        };
        Self {
            max_depth: cap,
            fork_depth: 0,
            fork_anchor: 0,
            branch_hw: initial_hw,
        }
    }

    #[must_use]
    pub const fn fork_depth(&self) -> u64 {
        self.fork_depth
    }

    #[must_use]
    pub const fn fork_anchor(&self) -> u64 {
        self.fork_anchor
    }

    #[must_use]
    pub const fn branch_hw(&self) -> u64 {
        self.branch_hw
    }

    /// Derive a child branch anchored at `fork_anchor` along `self`.
    pub fn fork_at(&self, fork_anchor: u64) -> Result<Self, ForkLineageError> {
        let next_depth = self.fork_depth.saturating_add(1);
        if !fork_admissible(fork_anchor, self.branch_hw, next_depth, self.max_depth) {
            if fork_anchor > self.branch_hw {
                return Err(ForkLineageError::AnchorBeyondParentHw {
                    fork_anchor,
                    parent_hw: self.branch_hw,
                });
            }
            return Err(ForkLineageError::ForkDepthExceeded {
                next_depth,
                max_depth: self.max_depth,
            });
        }
        Ok(Self {
            max_depth: self.max_depth,
            fork_depth: fork_depth_clamp(next_depth, self.max_depth),
            fork_anchor,
            branch_hw: fork_anchor,
        })
    }

    /// Advance this branch's committed high-water offset.
    pub fn advance_hw(&mut self, cand_hw: u64) -> u64 {
        self.branch_hw = branch_hw_advance(self.branch_hw, cand_hw);
        self.branch_hw
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_parent_hw_anchor_and_max_fork_depth() {
        let mut root = ForkLineageAnchorFence::root(0, 2);
        assert_eq!(root.advance_hw(42), 42);
        assert_eq!(
            root.fork_at(43),
            Err(ForkLineageError::AnchorBeyondParentHw {
                fork_anchor: 43,
                parent_hw: 42,
            })
        );
        let mut c1 = root.fork_at(20).unwrap();
        assert_eq!(c1.fork_depth(), 1);
        assert_eq!(c1.advance_hw(30), 30);
        let c2 = c1.fork_at(25).unwrap();
        assert_eq!(c2.fork_depth(), 2);
        assert_eq!(
            c2.fork_at(25),
            Err(ForkLineageError::ForkDepthExceeded {
                next_depth: 3,
                max_depth: 2,
            })
        );
    }
}
