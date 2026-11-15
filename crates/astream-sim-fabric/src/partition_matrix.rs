// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Directed asymmetric network-partition matrix (`Healthy`, `Blackhole`, `HalfOpenRst`) between
//! simulated `aterm` / `astream` nodes (`Astream.SimFabric.TlaPartitionMatrix`).

use std::collections::BTreeMap;

#[cfg(clean_islands)]
#[path = "partition_matrix_island.rs"]
mod partition_matrix_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sim_nodes_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sim_epoch_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use partition_matrix_island::{sim_epoch_advance, sim_nodes_clamp};

/// Maximum simulated nodes in one partition matrix (`64`).
pub const MAX_SIM_NODES: u64 = 64;

contract_fn! {
    /// Verified link reachability (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sim_link_up_isl`.
    #[must_use]
    pub const fn sim_link_up(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LinkFaultMode {
    Healthy,
    SilentDrop,
    ImmediateReset,
}

/// Directed `(src -> dst)` link fault matrix for split-brain & asymmetric-cut testing.
#[derive(Debug, Clone)]
pub struct AsymmetricPartitionMatrix {
    node_count: u64,
    epoch: u64,
    cuts: BTreeMap<(u64, u64), LinkFaultMode>,
}

impl AsymmetricPartitionMatrix {
    #[must_use]
    pub const fn new(node_count: u64) -> Self {
        Self {
            node_count: sim_nodes_clamp(node_count, MAX_SIM_NODES),
            epoch: 0,
            cuts: BTreeMap::new(),
        }
    }

    pub fn set_directed_fault(&mut self, src: u64, dst: u64, mode: LinkFaultMode) {
        if src < self.node_count && dst < self.node_count {
            self.epoch = sim_epoch_advance(self.epoch, self.epoch.saturating_add(1));
            if matches!(mode, LinkFaultMode::Healthy) {
                self.cuts.remove(&(src, dst));
            } else {
                self.cuts.insert((src, dst), mode);
            }
        }
    }

    #[must_use]
    pub fn can_deliver(&self, src: u64, dst: u64) -> bool {
        if src >= self.node_count || dst >= self.node_count {
            return false;
        }
        let mode = match self.cuts.get(&(src, dst)) {
            Some(&m) => m,
            None => LinkFaultMode::Healthy,
        };
        sim_link_up(u64::from(matches!(mode, LinkFaultMode::Healthy)), 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn asymmetric_cut_drops_one_direction_while_preserving_reverse_direction() {
        let mut m = AsymmetricPartitionMatrix::new(4);
        m.set_directed_fault(0, 1, LinkFaultMode::SilentDrop);
        assert!(!m.can_deliver(0, 1));
        assert!(m.can_deliver(1, 0));
        m.set_directed_fault(0, 1, LinkFaultMode::Healthy);
        assert!(m.can_deliver(0, 1));
    }
}
