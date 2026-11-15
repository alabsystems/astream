// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bottom-up post-order subagent cascade killer (`manage_subagents kill` / `kill_all`) ensuring
//! children and branched workspaces terminate before their parent (`Astream.Subagent.TlaDescendantReaper`).

use std::collections::{BTreeMap, BTreeSet};

#[cfg(clean_islands)]
#[path = "descendant_reaper_island.rs"]
mod descendant_reaper_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sub_nodes_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sub_reaped_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use descendant_reaper_island::{sub_nodes_clamp, sub_reaped_advance};

/// Maximum nodes in one subagent conversation tree.
pub const MAX_REAPER_NODES: u64 = 256;

contract_fn! {
    /// Verified quiescence check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sub_tree_quiesced_isl`.
    #[must_use]
    pub const fn sub_tree_quiesced(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

fn copy_str(s: &str) -> String {
    let mut out = String::new();
    out.push_str(s);
    out
}

/// Tracks parent->children edges and computes post-order (leaf-first) kill sequences.
#[derive(Debug, Clone, Default)]
pub struct SubagentReaperTree {
    children: BTreeMap<String, Vec<String>>,
    parents: BTreeMap<String, String>,
    reaped_total: u64,
}

impl SubagentReaperTree {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            children: BTreeMap::new(),
            parents: BTreeMap::new(),
            reaped_total: 0,
        }
    }

    pub fn register_spawn(&mut self, parent: &str, child: &str) -> bool {
        if parent.trim().is_empty() || child.trim().is_empty() || parent == child {
            return false;
        }
        let cap = sub_nodes_clamp(MAX_REAPER_NODES, MAX_REAPER_NODES) as usize;
        if self.parents.len() >= cap || self.parents.contains_key(child) {
            return false;
        }
        let mut cursor = parent;
        let mut steps = 0usize;
        while let Some(anc) = self.parents.get(cursor) {
            if anc.as_str() == child || steps >= cap {
                return false;
            }
            cursor = anc.as_str();
            steps = steps.saturating_add(1);
        }
        self.parents.insert(copy_str(child), copy_str(parent));
        self.children
            .entry(copy_str(parent))
            .or_default()
            .push(copy_str(child));
        true
    }

    /// Returns leaf-first kill order so grandchildren die before children!
    #[allow(clippy::vec_init_then_push)]
    pub fn plan_bottom_up_kill(&mut self, root_target: &str) -> Vec<String> {
        if root_target.trim().is_empty() {
            return Vec::new();
        }
        let mut visited = BTreeSet::new();
        let mut stack = Vec::new();
        stack.push((copy_str(root_target), false));
        let mut post_order = Vec::new();
        while let Some((node, expanded)) = stack.pop() {
            if expanded {
                post_order.push(node);
                continue;
            }
            if !visited.insert(node.clone()) {
                continue;
            }
            stack.push((node.clone(), true));
            if let Some(kids) = self.children.get(&node) {
                let mut idx = kids.len();
                while idx > 0 {
                    idx = idx.saturating_sub(1);
                    if let Some(k) = kids.get(idx) {
                        stack.push((k.clone(), false));
                    }
                }
            }
        }
        let next = self.reaped_total.saturating_add(post_order.len() as u64);
        self.reaped_total = sub_reaped_advance(self.reaped_total, next);
        let _ = sub_tree_quiesced(self.reaped_total, 0);
        post_order
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reaper_plans_strict_leaf_first_postorder_termination() {
        let mut t = SubagentReaperTree::new();
        t.register_spawn("c-parent", "c-kid-1");
        t.register_spawn("c-kid-1", "c-grandkid");
        t.register_spawn("c-parent", "c-kid-2");
        assert_eq!(
            t.plan_bottom_up_kill("c-parent"),
            vec!["c-grandkid", "c-kid-1", "c-kid-2", "c-parent"]
        );
    }
}
