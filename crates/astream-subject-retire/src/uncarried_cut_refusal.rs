// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Uncarried retention-cut & replica retirement refusal gate (`is_retire_cut()`, `docs/ROADMAP.md`
//! §2: *"refuses on a replica (`ERR_REFUSED`) or an uncarried retention-cut log (`retain_before`,
//! `is_retire_cut()`), carries `last_owner` (`carried_charges`) across `retain_before_carrying_state`"*
//! `Astream.SubjRet.TlaUncarriedCutRefusal`).

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "uncarried_cut_refusal_island.rs"]
mod uncarried_cut_refusal_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn srb_base_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn srb_carry_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use uncarried_cut_refusal_island::{srb_base_clamp, srb_carry_advance};

/// Maximum log base offset inspected (`1 << 60`).
pub const MAX_LOG_BASE_OFFSET: u64 = 1u64 << 60;

contract_fn! {
    /// Verified carried-charge continuity up to log base (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `srb_charges_carried_isl`.
    #[must_use]
    pub const fn srb_charges_carried(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct RetireCutAdmission {
    is_replica: bool,
    log_base: u64,
    carried_charges_base: u64,
}

impl RetireCutAdmission {
    #[must_use]
    pub const fn new(is_replica: bool) -> Self {
        Self {
            is_replica,
            log_base: 0,
            carried_charges_base: 0,
        }
    }

    pub fn on_compaction(&mut self, new_base: u64, carried_state: bool) {
        let prev_log_base = self.log_base;
        let clamped = srb_base_clamp(new_base, MAX_LOG_BASE_OFFSET);
        if clamped > self.log_base {
            self.log_base = clamped;
        }
        if carried_state && self.carried_charges_base == prev_log_base {
            self.carried_charges_base = srb_carry_advance(self.carried_charges_base, self.log_base);
        }
    }

    #[must_use]
    pub const fn allows_retire(&self) -> bool {
        !self.is_replica && srb_charges_carried(self.carried_charges_base, self.log_base)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn allows_retire_across_state_carrying_compaction_and_refuses_uncarried_or_replica() {
        let mut leader = RetireCutAdmission::new(false);
        assert!(leader.allows_retire());
        leader.on_compaction(500, true);
        assert!(leader.allows_retire());
        leader.on_compaction(900, false);
        assert!(!leader.allows_retire());
        assert!(!RetireCutAdmission::new(true).allows_retire());
    }
}
