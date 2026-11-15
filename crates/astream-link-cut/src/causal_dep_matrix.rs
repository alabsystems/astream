// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pairwise causal dependency verifier checking `is_consistent` across bus records (`dep_offset <
//! cut.offset_for(dep_shard)` for every included message; `Astream.LinkCut.TlaCausalDepMatrix`).

#[cfg(clean_islands)]
#[path = "causal_dep_matrix_island.rs"]
mod causal_dep_matrix_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lc_deps_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lc_chk_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use causal_dep_matrix_island::{lc_chk_advance, lc_deps_clamp};

/// Maximum causal dependency edges per bus envelope (`64`).
pub const MAX_CAUSAL_DEPS: u64 = 64;

contract_fn! {
    /// Verified causal-inclusion predicate (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `lc_cut_consistent_isl`.
    #[must_use]
    pub const fn lc_cut_consistent(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct CausalCutChecker {
    edges_verified: u64,
}

impl CausalCutChecker {
    #[must_use]
    pub const fn new() -> Self {
        Self { edges_verified: 0 }
    }

    /// Checks whether a record depending on `dep_inclusive_offset` on a shard whose exclusive cut
    /// frontier is `cut_exclusive_offset` has its cause inside the cut.
    pub fn edge_satisfied(
        &mut self,
        dep_inclusive_offset: u64,
        cut_exclusive_offset: u64,
        dep_count: u64,
    ) -> bool {
        let _ = lc_deps_clamp(dep_count, MAX_CAUSAL_DEPS);
        self.edges_verified =
            lc_chk_advance(self.edges_verified, self.edges_verified.saturating_add(1));
        let req_exclusive = dep_inclusive_offset.saturating_add(1);
        lc_cut_consistent(cut_exclusive_offset, req_exclusive)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_missing_causal_predecessor_outside_cut_frontier() {
        let mut c = CausalCutChecker::new();
        assert!(c.edge_satisfied(9, 10, 1));
        assert!(!c.edge_satisfied(10, 10, 1));
    }
}
