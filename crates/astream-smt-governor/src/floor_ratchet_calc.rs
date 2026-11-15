// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Monotone `max(old_floor, (proved * 4) / 5)` (`80%`) floor ratchet calculator enforcing
//! `scripts/verify-ready.sh`'s never-lowered floor invariant (`Astream.SmtGov.TlaFloorRatchetCalc`).

#[cfg(clean_islands)]
#[path = "floor_ratchet_calc_island.rs"]
mod floor_ratchet_calc_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn smt_floor_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn smt_ratchet_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use floor_ratchet_calc_island::{smt_floor_clamp, smt_ratchet_advance};

/// Hard ceiling (`1_000_000`) on per-crate proved obligation counts.
pub const MAX_CRATE_PROVED_FLOOR: u64 = 1_000_000;

contract_fn! {
    /// Verified non-decreasing floor (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `smt_floor_nondecreasing_isl`.
    #[must_use]
    pub const fn smt_floor_nondecreasing(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Computes ratcheted `proved` floors while refusing `proved < old_floor`.
#[derive(Debug, Clone, Default)]
pub struct ProvedFloorRatchet {
    targets_ratcheted: u64,
}

impl ProvedFloorRatchet {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            targets_ratcheted: 0,
        }
    }

    pub fn compute_next_floor(
        &mut self,
        old_floor: u64,
        measured_proved: u64,
    ) -> Result<u64, &'static str> {
        if measured_proved < old_floor {
            return Err("measured proved obligations dropped below existing verify-ready.sh floor");
        }
        let eighty_pct =
            smt_floor_clamp(measured_proved, MAX_CRATE_PROVED_FLOOR).saturating_mul(4) / 5;
        let next_floor = smt_ratchet_advance(old_floor, eighty_pct);
        let _ = smt_floor_nondecreasing(next_floor, old_floor);
        self.targets_ratcheted = smt_ratchet_advance(
            self.targets_ratcheted,
            self.targets_ratcheted.saturating_add(1),
        );
        Ok(next_floor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ratchet_advances_to_eighty_percent_never_lowers_and_refuses_regression_below_floor() {
        let mut r = ProvedFloorRatchet::new();
        assert_eq!(r.compute_next_floor(100, 200).unwrap(), 160);
        assert_eq!(r.compute_next_floor(160, 180).unwrap(), 160);
        assert!(r.compute_next_floor(160, 159).is_err());
    }
}
