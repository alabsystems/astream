// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Monotone Full Disk Access (`FDA`) grant epoch tracker recording user-granted TCC state changes
//! across protected macOS folders and volumes (`Astream.MacTcc.TlaFdaGrantEpoch`).

#[cfg(clean_islands)]
#[path = "fda_grant_epoch_island.rs"]
mod fda_grant_epoch_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tcc_fda_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tcc_grant_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use fda_grant_epoch_island::{tcc_fda_clamp, tcc_grant_advance};

/// Maximum scope mask (`3`: user folders + external volumes).
pub const FULL_FDA_MASK: u64 = 3;

contract_fn! {
    /// Verified FDA mask check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `tcc_fda_active_isl`.
    #[must_use]
    pub const fn tcc_fda_active(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct FdaEpochState {
    scope_mask: u64,
    epoch: u64,
}

impl FdaEpochState {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            scope_mask: 0,
            epoch: 0,
        }
    }

    pub fn update_grant(&mut self, raw_mask: u64) -> bool {
        self.scope_mask = tcc_fda_clamp(raw_mask, FULL_FDA_MASK);
        self.epoch = tcc_grant_advance(self.epoch, self.epoch.saturating_add(1));
        tcc_fda_active(self.scope_mask, FULL_FDA_MASK)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reports_active_only_when_both_folder_and_volume_bits_are_granted() {
        let mut s = FdaEpochState::new();
        assert!(!s.update_grant(1));
        assert!(s.update_grant(3));
    }
}
