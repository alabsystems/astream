// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Log-identity generation & boot-session incarnation guard re-anchoring `BusCutFrontier` cursors
//! to `min(cursor, common)` whenever `LogIdentity` advances after an unclean weak-tier reboot
//! (`Astream.LinkCut.TlaIncarnationLeaseCut`).

#[cfg(clean_islands)]
#[path = "incarnation_lease_cut_island.rs"]
mod incarnation_lease_cut_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lc_gen_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lc_lease_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use incarnation_lease_cut_island::{lc_gen_clamp, lc_lease_advance};

/// Maximum tracked generation delta (`1_000_000`).
pub const MAX_GEN_STEP: u64 = 1_000_000;

contract_fn! {
    /// Verified same-generation lease check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `lc_lease_intact_isl`.
    #[must_use]
    pub const fn lc_lease_intact(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct IncarnationCutPin {
    pinned_gen: u64,
}

impl IncarnationCutPin {
    #[must_use]
    pub const fn new(initial_gen: u64) -> Self {
        Self {
            pinned_gen: lc_gen_clamp(initial_gen, MAX_GEN_STEP),
        }
    }

    /// Reconciles `cursor` against a broker reporting `observed_gen` and `lineage_common`.
    pub fn reconcile_cursor(
        &mut self,
        cursor: u64,
        observed_gen: u64,
        lineage_common: u64,
    ) -> (u64, bool) {
        let obs = lc_gen_clamp(observed_gen, MAX_GEN_STEP);
        let unchanged = obs == self.pinned_gen;
        if obs > self.pinned_gen {
            self.pinned_gen = lc_lease_advance(self.pinned_gen, obs);
        }
        let intact = lc_lease_intact(if unchanged { 1 } else { 0 }, 1);
        let safe_cursor = if intact || cursor < lineage_common {
            cursor
        } else {
            lineage_common
        };
        (safe_cursor, intact)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rewinds_cursor_to_lineage_common_on_generation_move() {
        let mut pin = IncarnationCutPin::new(2);
        assert_eq!(pin.reconcile_cursor(50, 2, 50), (50, true));
        assert_eq!(pin.reconcile_cursor(50, 3, 42), (42, false));
    }
}
