// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bounded subagent recursion depth (`<= 4`) and per-parent fanout cap (`<= 16`) preventing
//! recursive `invoke_subagent` fork-bombs (`Astream.Subagent.TlaDepthFanoutCap`).

#[cfg(clean_islands)]
#[path = "depth_fanout_cap_island.rs"]
mod depth_fanout_cap_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sub_fanout_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sub_spawned_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use depth_fanout_cap_island::{sub_fanout_clamp, sub_spawned_advance};

/// Maximum recursion depth (`root = 0`, max descendant depth `= 4`).
pub const MAX_SUBAGENT_DEPTH: u64 = 4;
/// Maximum direct children per conversation.
pub const MAX_DIRECT_SUBAGENTS: u64 = 16;

contract_fn! {
    /// Verified depth guard (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sub_depth_allowed_isl`.
    #[must_use]
    pub const fn sub_depth_allowed(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Enforces bounded depth and fanout for `EnableSubagentTools`.
#[derive(Debug, Clone)]
pub struct SubagentSpawnBudget {
    depth: u64,
    max_children: u64,
    spawned: u64,
}

impl SubagentSpawnBudget {
    #[must_use]
    pub const fn new(depth: u64, max_children: u64) -> Self {
        Self {
            depth,
            max_children: sub_fanout_clamp(max_children, MAX_DIRECT_SUBAGENTS),
            spawned: 0,
        }
    }

    pub fn admit_child_spawn(&mut self) -> Result<Self, &'static str> {
        let child_depth = self.depth.saturating_add(1);
        if !sub_depth_allowed(MAX_SUBAGENT_DEPTH, child_depth) {
            return Err("subagent recursion depth ceiling reached");
        }
        if self.spawned >= self.max_children {
            return Err("direct subagent fanout ceiling reached");
        }
        self.spawned = sub_spawned_advance(self.spawned, self.spawned.saturating_add(1));
        Ok(Self::new(child_depth, self.max_children))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn spawn_budget_blocks_depth_past_4_and_fanout_past_cap() {
        let mut root = SubagentSpawnBudget::new(0, 2);
        let mut c1 = root.admit_child_spawn().unwrap();
        let _c2 = root.admit_child_spawn().unwrap();
        assert!(root.admit_child_spawn().is_err());

        let mut d2 = c1.admit_child_spawn().unwrap();
        let mut d3 = d2.admit_child_spawn().unwrap();
        let mut d4 = d3.admit_child_spawn().unwrap();
        assert!(d4.admit_child_spawn().is_err());
    }
}
