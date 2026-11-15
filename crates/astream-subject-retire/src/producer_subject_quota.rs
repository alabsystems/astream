// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Per-producer distinct-subject budget meter (`docs/ROADMAP.md` §2: *"Giving a distinct-subject
//! budget back. A producer can tell it is at its budget (`ERR_SUBJECT_BOUND`), read the count
//! (`Request::Budget`), and retire an exact subject"*, `Astream.SubjRet.TlaProducerSubjectQuota`).

#[cfg(clean_islands)]
#[path = "producer_subject_quota_island.rs"]
mod producer_subject_quota_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn srb_used_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn srb_freed_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use producer_subject_quota_island::{srb_freed_advance, srb_used_clamp};

/// Hard ceiling on per-producer distinct `Last` subjects (`65_536`).
pub const MAX_SUBJECTS_CEILING: u64 = 65_536;

contract_fn! {
    /// Verified available distinct-subject budget (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `srb_under_budget_isl`.
    #[must_use]
    pub const fn srb_under_budget(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct ProducerSubjectBudget {
    max_subjects: u64,
    charged: u64,
    total_retired: u64,
}

impl ProducerSubjectBudget {
    #[must_use]
    pub const fn new(max_subjects: u64) -> Self {
        Self {
            max_subjects: srb_used_clamp(max_subjects, MAX_SUBJECTS_CEILING),
            charged: 0,
            total_retired: 0,
        }
    }

    pub fn charge_new_subject(&mut self) -> bool {
        let next = self.charged.saturating_add(1);
        if !srb_under_budget(self.max_subjects, next) {
            return false;
        }
        self.charged = next;
        true
    }

    pub fn retire_charged_subject(&mut self) -> bool {
        if self.charged == 0 {
            return false;
        }
        self.charged = self.charged.saturating_sub(1);
        self.total_retired =
            srb_freed_advance(self.total_retired, self.total_retired.saturating_add(1));
        true
    }

    #[must_use]
    pub const fn remaining(&self) -> u64 {
        self.max_subjects.saturating_sub(self.charged)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn returns_subject_slot_to_producer_upon_retirement() {
        let mut b = ProducerSubjectBudget::new(2);
        assert!(b.charge_new_subject());
        assert!(b.charge_new_subject());
        assert!(!b.charge_new_subject());
        assert!(b.retire_charged_subject());
        assert_eq!(b.remaining(), 1);
        assert!(b.charge_new_subject());
    }
}
