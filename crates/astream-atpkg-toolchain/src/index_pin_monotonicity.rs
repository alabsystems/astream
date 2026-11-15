// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Monotone `atpkg` package-index revision guard preventing accidental rollback from a qualified
//! `trust/<build>` compiler snapshot (`Astream.AtpkgTc.TlaIndexPinMonotonicity`).

#[cfg(clean_islands)]
#[path = "index_pin_monotonicity_island.rs"]
mod index_pin_monotonicity_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tc_idx_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tc_idx_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use index_pin_monotonicity_island::{tc_idx_advance, tc_idx_clamp};

/// Maximum `atpkg` index generation (`1_000_000`).
pub const MAX_ATPKG_INDEX_GEN: u64 = 1_000_000;

contract_fn! {
    /// Verified non-decreasing index check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `tc_index_nondecreasing_isl`.
    #[must_use]
    pub const fn tc_index_nondecreasing(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct AtpkgIndexPin {
    current_index: u64,
    current_build: u64,
}

impl AtpkgIndexPin {
    #[must_use]
    pub const fn new(initial_index: u64, initial_build: u64) -> Self {
        Self {
            current_index: tc_idx_clamp(initial_index, MAX_ATPKG_INDEX_GEN),
            current_build: initial_build,
        }
    }

    pub fn try_advance(&mut self, cand_index: u64, cand_build: u64) -> bool {
        let clamped = tc_idx_clamp(cand_index, MAX_ATPKG_INDEX_GEN);
        if tc_index_nondecreasing(clamped, self.current_index)
            && tc_index_nondecreasing(cand_build, self.current_build)
        {
            self.current_index = tc_idx_advance(self.current_index, clamped);
            self.current_build = tc_idx_advance(self.current_build, cand_build);
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn allows_forward_index_and_trust_build_pins_and_rejects_downgrade() {
        let mut pin = AtpkgIndexPin::new(78, 15_698);
        assert!(!pin.try_advance(77, 15_698));
        assert!(!pin.try_advance(79, 15_600));
        assert!(pin.try_advance(79, 15_710));
    }
}
