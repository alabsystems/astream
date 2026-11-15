// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Supervised subagent `parent=<sid>` hierarchy acyclicity and cascading cancel frontier
//! (`DESIGN-aterm-fabric.md` §4.2 line 4041, `Astream.Presence.TlaParentTree`).
//!
//! Models `aterm`'s subagent supervision tree (`manage_subagents`: killing a subagent kills
//! its descendants and deletes their branched workspaces):
//! - Rejects self-parenting and cycle creation before mutating the parent map.
//! - Enforces maximum tree depth (`<= MAX_SUPERVISED_TREE_DEPTH`) via Clean-origin `tree_depth_clamp`.
//! - Computes deterministic breadth-first `cascade_kill_order(root_sid)` and advances
//!   `cancel_epoch` monotonically via `tree_cancel_advance`.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

#[cfg(clean_islands)]
#[path = "parent_tree_island.rs"]
mod parent_tree_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tree_depth_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tree_cancel_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use parent_tree_island::{tree_cancel_advance, tree_depth_clamp};

/// Maximum nesting depth of spawned subagents (`self -> worker -> sub-worker ...`).
pub const MAX_SUPERVISED_TREE_DEPTH: u64 = 16;

contract_fn! {
    /// Verified depth check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `tree_within_max_depth_isl`.
    #[must_use]
    pub const fn tree_within_max_depth(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Maximum total supervised sessions tracked in one tree.
pub const MAX_SUPERVISED_SESSIONS: usize = 1024;

fn clone_str(s: &str) -> String {
    let mut out = String::new();
    out.push_str(s);
    out
}

/// Acyclic supervised session tree.
#[derive(Debug, Clone)]
pub struct SupervisedParentTree {
    max_depth: u64,
    cancel_epoch: u64,
    parents: BTreeMap<String, Option<String>>,
}

impl Default for SupervisedParentTree {
    fn default() -> Self {
        Self::new()
    }
}

impl SupervisedParentTree {
    #[must_use]
    pub fn new() -> Self {
        Self::with_max_depth(MAX_SUPERVISED_TREE_DEPTH)
    }

    #[must_use]
    pub fn with_max_depth(max_depth: u64) -> Self {
        let cap = tree_depth_clamp(max_depth, MAX_SUPERVISED_TREE_DEPTH);
        Self {
            max_depth: if cap == 0 { 1 } else { cap },
            cancel_epoch: 0,
            parents: BTreeMap::new(),
        }
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.parents.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.parents.is_empty()
    }

    #[must_use]
    pub const fn cancel_epoch(&self) -> u64 {
        self.cancel_epoch
    }

    fn max_descendant_height(&self, root_sid: &str) -> u64 {
        if !self.parents.contains_key(root_sid) {
            return 0;
        }
        let mut max_h = 0u64;
        let mut q: VecDeque<(String, u64)> = VecDeque::new();
        q.push_back((clone_str(root_sid), 0));
        while let Some((cur, h)) = q.pop_front() {
            if h > max_h {
                max_h = h;
            }
            for (cand, par) in &self.parents {
                if par.as_deref() == Some(cur.as_str()) {
                    q.push_back((cand.clone(), h.saturating_add(1)));
                }
            }
        }
        max_h
    }

    /// Registers or reparents `sid` under `parent`, rejecting cycles, unknown parents, or depth overflow.
    #[allow(clippy::manual_map)]
    pub fn register_session(
        &mut self,
        sid: &str,
        parent: Option<&str>,
    ) -> Result<u64, &'static str> {
        if sid.is_empty() {
            return Err("empty session id");
        }
        if !self.parents.contains_key(sid) && self.parents.len() >= MAX_SUPERVISED_SESSIONS {
            return Err("supervised session table full");
        }
        let mut depth = 0u64;
        if let Some(p) = parent {
            if p == sid {
                return Err("self-parenting cycle");
            }
            if !self.parents.contains_key(p) {
                return Err("parent session not registered");
            }
            let mut cur: Option<&str> = Some(p);
            while let Some(node) = cur {
                if node == sid {
                    return Err("reparent would introduce cycle");
                }
                depth = depth.saturating_add(1);
                if !tree_within_max_depth(self.max_depth, depth) {
                    return Err("subagent supervision depth exceeded");
                }
                cur = match self.parents.get(node) {
                    Some(Some(parent_str)) => Some(parent_str.as_str()),
                    _ => None,
                };
            }
        }
        let sub_height = self.max_descendant_height(sid);
        if !tree_within_max_depth(self.max_depth, depth.saturating_add(sub_height)) {
            return Err("subagent subtree depth exceeded");
        }
        let par_owned = match parent {
            Some(p) => Some(clone_str(p)),
            None => None,
        };
        self.parents.insert(clone_str(sid), par_owned);
        Ok(depth)
    }

    /// Removes `target_sid` and all of its transitive descendants in deterministic BFS order.
    pub fn cascade_kill(&mut self, target_sid: &str) -> Vec<String> {
        if !self.parents.contains_key(target_sid) {
            return Vec::new();
        }
        let mut killed = Vec::new();
        let mut visited = BTreeSet::new();
        let mut q = VecDeque::new();
        q.push_back(clone_str(target_sid));
        visited.insert(clone_str(target_sid));

        while let Some(cur) = q.pop_front() {
            for (cand, par) in &self.parents {
                if par.as_deref() == Some(cur.as_str()) && visited.insert(cand.clone()) {
                    q.push_back(cand.clone());
                }
            }
            killed.push(cur);
        }
        for sid in &killed {
            self.parents.remove(sid);
        }
        self.cancel_epoch =
            tree_cancel_advance(self.cancel_epoch, self.cancel_epoch.saturating_add(1));
        killed
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parent_tree_rejects_cycles_bounds_depth_and_cascades_kills_to_descendants() {
        let mut tree = SupervisedParentTree::with_max_depth(3);
        assert_eq!(tree.register_session("s-root", None).unwrap(), 0);
        assert_eq!(tree.register_session("s-w1", Some("s-root")).unwrap(), 1);
        assert_eq!(tree.register_session("s-w2", Some("s-root")).unwrap(), 1);
        assert_eq!(tree.register_session("s-sub1", Some("s-w1")).unwrap(), 2);
        assert_eq!(tree.register_session("s-leaf", Some("s-sub1")).unwrap(), 3);
        // Depth 4 > max_depth 3 refused!
        assert!(tree.register_session("s-too-deep", Some("s-leaf")).is_err());
        // Reparenting root under leaf would form a cycle -> refused!
        assert!(tree.register_session("s-root", Some("s-leaf")).is_err());

        let killed = tree.cascade_kill("s-w1");
        assert_eq!(killed, vec!["s-w1", "s-sub1", "s-leaf"]);
        assert_eq!(tree.len(), 2); // s-root and s-w2 untouched!
        assert_eq!(tree.cancel_epoch(), 1);
    }
}
