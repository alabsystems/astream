// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Conditional & unconditioned subject retire (`TAG_RETIRE = 0x10`), `carried_charges` compaction,
//! & `uncarried_cut_tainted` refusal (`docs/DESIGN-aterm-fabric.md` §15 line 4065, `broker.subject-retire`,
//! astream `0440bc5`, aterm `673cb2a8eb`, `d49fdddfaa`;
//! `Astream.Broker.TlaConditionalRetireChargeTaintGate`).
//!
//! Models both faces of `broker.subject-retire`:
//! - **Unconditioned `Client::retire_subject`** (`expected_offset == None`, used by `mirror_retire_face`
//!   for a closed session's `ev` face): removes the subject from `Last` and refunds `1` subject charge
//!   when `!uncarried_cut_tainted`,
//! - **Conditional `Client::retire(subject, expected_offset)`** (`NonceExt` tag `0x03`, used by the
//!   ghost sweep `Bridge::reclaim_subjects` for a departed session's presence row and mail lanes):
//!   succeeds ONLY if `current_last_offset == Some(expected_offset)` AND `!uncarried_cut_tainted`;
//!   if a newer record landed (`current_last_offset != Some(expected_offset)`), refuses cleanly without
//!   touching the live row or refunding any charge!
//! - **Compaction taint**: `retain_before_carrying_state` (`carried_charges`) preserves charge ownership;
//!   an uncarried `retain_before` cut latches `uncarried_cut_tainted = true`, refusing retire so charge
//!   accounting can never underflow or mis-credit!

#[cfg(clean_islands)]
#[path = "conditional_retire_charge_taint_gate_island.rs"]
mod conditional_retire_charge_taint_gate_island;
#[cfg(clean_islands)]
pub use conditional_retire_charge_taint_gate_island::{
    charged_subjects_clamp_b137, retire_epoch_advance_b137,
};

/// Maximum charged subjects per producer (`4_096`).
pub const MAX_CHARGED_SUBJECTS: u64 = 4_096;

#[cfg(not(clean_islands))]
/// Clamp producer charged-subject count to `budget_cap`.
#[must_use]
pub const fn charged_subjects_clamp_b137(cand_charged: u64, budget_cap: u64) -> u64 {
    if cand_charged < budget_cap {
        cand_charged
    } else {
        budget_cap
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance retire sequence watermark.
#[must_use]
pub const fn retire_epoch_advance_b137(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `!uncarried_cut_tainted && subject_present && (!is_conditional || current_off == expected_off)`.
    #[must_use]
    pub const fn subject_retire_admissible_b137(
        uncarried_cut_tainted: bool,
        subject_present: bool,
        is_conditional: bool,
        current_off: u64,
        expected_off: u64,
    ) -> bool
    clauses [ensures result == (!uncarried_cut_tainted && subject_present && (!is_conditional || current_off == expected_off))]
    {
        !uncarried_cut_tainted
            && subject_present
            && (!is_conditional || current_off == expected_off)
    }
}

/// Outcome of a `TAG_RETIRE` (`retire_subject` or conditional `retire`) request.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum SubjectRetireVerdict {
    /// Subject removed from `Last` (historical records stay fetchable!) and `1` charge refunded.
    RetiredAndRefunded { remaining_charged: u64 },
    /// Subject already absent from `Last` (idempotent no-op when unconditioned).
    IdempotentAbsentNoop,
    /// Conditional `retire` refused: `current_last_offset != Some(expected_offset)` (newer write landed!).
    RefusedConditionMismatch,
    /// Refused: an uncarried `retain_before` cut tainted charge ownership (`uncarried_cut_tainted`)!
    RefusedUncarriedCutTainted,
}

/// Tracked subject + producer charge state machine across compactions and retires.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct SubjectRetireChargeGate {
    budget_cap: u64,
    charged_subjects: u64,
    uncarried_cut_tainted: bool,
    tracked_last_offset: Option<u64>,
    retire_epoch: u64,
}

impl SubjectRetireChargeGate {
    #[must_use]
    pub const fn new(budget_cap: u64) -> Self {
        let cap = if budget_cap == 0 {
            MAX_CHARGED_SUBJECTS
        } else {
            budget_cap
        };
        Self {
            budget_cap: cap,
            charged_subjects: 0,
            uncarried_cut_tainted: false,
            tracked_last_offset: None,
            retire_epoch: 0,
        }
    }

    #[must_use]
    pub const fn charged_subjects(&self) -> u64 {
        charged_subjects_clamp_b137(self.charged_subjects, self.budget_cap)
    }

    #[must_use]
    pub const fn is_tainted(&self) -> bool {
        self.uncarried_cut_tainted
    }

    /// Introduce or update the tracked subject at `offset`.
    pub fn on_publish_tracked_subject(&mut self, offset: u64) -> bool {
        if self.tracked_last_offset.is_none() {
            if self.charged_subjects >= self.budget_cap {
                return false;
            }
            self.charged_subjects = charged_subjects_clamp_b137(
                self.charged_subjects.saturating_add(1),
                self.budget_cap,
            );
        }
        self.tracked_last_offset = Some(offset);
        true
    }

    /// Apply compaction: `carrying_state == true` (`<log>.state` / `carried_charges`) preserves
    /// untainted retire eligibility; `carrying_state == false` permanently taints retire!
    pub fn on_compaction_cut(&mut self, carrying_state: bool) {
        if !carrying_state {
            self.uncarried_cut_tainted = true;
        }
    }

    /// Execute unconditioned (`None`) or conditional (`Some(expected_off)`) `TAG_RETIRE`.
    pub fn retire_tracked_subject(&mut self, expected_offset: Option<u64>) -> SubjectRetireVerdict {
        if self.uncarried_cut_tainted {
            return SubjectRetireVerdict::RefusedUncarriedCutTainted;
        }
        let Some(cur_off) = self.tracked_last_offset else {
            return match expected_offset {
                None => SubjectRetireVerdict::IdempotentAbsentNoop,
                Some(_) => SubjectRetireVerdict::RefusedConditionMismatch,
            };
        };
        let (is_cond, exp_off) = match expected_offset {
            Some(e) => (true, e),
            None => (false, cur_off),
        };
        if !subject_retire_admissible_b137(false, true, is_cond, cur_off, exp_off) {
            return SubjectRetireVerdict::RefusedConditionMismatch;
        }
        self.tracked_last_offset = None;
        self.charged_subjects = self.charged_subjects.saturating_sub(1);
        self.retire_epoch =
            retire_epoch_advance_b137(self.retire_epoch, self.retire_epoch.saturating_add(1));
        SubjectRetireVerdict::RetiredAndRefunded {
            remaining_charged: self.charged_subjects(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn conditional_retire_protects_newer_write_and_carried_compaction_preserves_refund() {
        let mut g = SubjectRetireChargeGate::new(4);
        assert!(g.on_publish_tracked_subject(100));
        assert_eq!(g.charged_subjects(), 1);
        // State-carrying compaction (`retain_before_carrying_state`) keeps `uncarried_cut_tainted == false`:
        g.on_compaction_cut(true);
        assert!(!g.is_tainted());
        // Newer write at 105 lands before ghost sweep's conditional `retire(expected = 100)`:
        assert!(g.on_publish_tracked_subject(105));
        assert_eq!(
            g.retire_tracked_subject(Some(100)),
            SubjectRetireVerdict::RefusedConditionMismatch
        );
        assert_eq!(g.charged_subjects(), 1);
        // Conditional `retire(expected = 105)` matches and refunds the budget slot:
        assert_eq!(
            g.retire_tracked_subject(Some(105)),
            SubjectRetireVerdict::RetiredAndRefunded {
                remaining_charged: 0
            }
        );
        // Uncarried cut taints retire and refuses cleanly:
        assert!(g.on_publish_tracked_subject(200));
        g.on_compaction_cut(false);
        assert_eq!(
            g.retire_tracked_subject(None),
            SubjectRetireVerdict::RefusedUncarriedCutTainted
        );
    }
}
