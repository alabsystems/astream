// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Producer distinct-subject budget (`MAX_SUBJECTS_PER_PRODUCER = 4096`) debit, will-reservation,
//! retirement credit, and `<log>.state` compaction carry ledger (`broker.subject-budget-read`,
//! `broker.subject-retire`, `Astream.Retire.TlaChargeReclaim`).
//!
//! Enforces the exact accounting law of `BrokerLog`:
//! - Introducing an absent subject charges `1` slot to `producer_id` (`introduced + reserved < max`).
//! - Updating an already-present subject charges `0` slots regardless of which producer updates it!
//! - Registering a `Will` on an unintroduced subject reserves `1` slot until the will fires or drops.
//! - Retiring a subject credits `1` slot back to its introducing `charged_owner`.

use std::collections::BTreeMap;

#[cfg(clean_islands)]
#[path = "charge_reclaim_island.rs"]
mod charge_reclaim_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn charge_used_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn charge_epoch_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use charge_reclaim_island::{charge_epoch_advance, charge_used_clamp};

/// Default per-producer distinct-subject cap matching `astream-broker`.
pub const MAX_PRODUCER_SUBJECT_BUDGET: u64 = 4096;

contract_fn! {
    /// Verified budget-room predicate (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `charge_has_room_isl`.
    #[must_use]
    pub const fn charge_has_room(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Snapshot of a producer's subject budget (`Request::Budget` / `Response::Budget`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProducerBudgetView {
    pub subjects: u64,
    pub reserved: u64,
    pub max: u64,
}

impl ProducerBudgetView {
    #[must_use]
    pub const fn remaining(&self) -> u64 {
        self.max
            .saturating_sub(self.subjects.saturating_add(self.reserved))
    }
}

/// Exact subject-charge and compaction-carry ledger.
#[derive(Debug, Clone)]
pub struct SubjectChargeLedger {
    max_per_producer: u64,
    compaction_epoch: u64,
    subject_owner: BTreeMap<String, u64>,
    producer_subjects: BTreeMap<u64, u64>,
    will_reservations: BTreeMap<u64, String>,
}

impl Default for SubjectChargeLedger {
    fn default() -> Self {
        Self::new()
    }
}

fn clone_str(s: &str) -> String {
    let mut out = String::new();
    out.push_str(s);
    out
}

impl SubjectChargeLedger {
    #[must_use]
    pub fn new() -> Self {
        Self::with_budget(MAX_PRODUCER_SUBJECT_BUDGET)
    }

    #[must_use]
    pub fn with_budget(max_per_producer: u64) -> Self {
        let cap = charge_used_clamp(max_per_producer, MAX_PRODUCER_SUBJECT_BUDGET);
        Self {
            max_per_producer: if cap == 0 { 1 } else { cap },
            compaction_epoch: 0,
            subject_owner: BTreeMap::new(),
            producer_subjects: BTreeMap::new(),
            will_reservations: BTreeMap::new(),
        }
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.subject_owner.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.subject_owner.is_empty()
    }

    /// Reads `(subjects, reserved, max)` for `producer_id`.
    #[must_use]
    pub fn budget_of(&self, producer_id: u64) -> ProducerBudgetView {
        let subjects = match self.producer_subjects.get(&producer_id) {
            Some(&n) => n,
            None => 0,
        };
        let mut reserved = 0u64;
        if let Some(subj) = self.will_reservations.get(&producer_id) {
            if !self.subject_owner.contains_key(subj) {
                reserved = 1;
            }
        }
        ProducerBudgetView {
            subjects,
            reserved,
            max: self.max_per_producer,
        }
    }

    /// Admits a publish on `subject` by `producer_id`. Updates of an existing subject spend `0`!
    pub fn stage_publish(&mut self, producer_id: u64, subject: &str) -> Result<u64, &'static str> {
        if subject.is_empty() {
            return Err("empty subject");
        }
        if let Some(&owner) = self.subject_owner.get(subject) {
            return Ok(owner);
        }
        let view = self.budget_of(producer_id);
        let own_will_covers = match self.will_reservations.get(&producer_id) {
            Some(s) => s == subject,
            None => false,
        };
        let needed = view
            .subjects
            .saturating_add(if own_will_covers { 0 } else { view.reserved })
            .saturating_add(1);
        if !charge_has_room(self.max_per_producer, needed) {
            return Err("ERR_SUBJECT_BOUND: producer distinct-subject budget exhausted");
        }
        self.subject_owner.insert(clone_str(subject), producer_id);
        let next = view.subjects.saturating_add(1);
        self.producer_subjects
            .insert(producer_id, charge_used_clamp(next, self.max_per_producer));
        Ok(producer_id)
    }

    /// Reserves a slot for a connection's `Will` if `subject` is not yet introduced.
    pub fn register_will(&mut self, producer_id: u64, subject: &str) -> Result<(), &'static str> {
        if subject.is_empty() {
            return Err("empty will subject");
        }
        if !self.subject_owner.contains_key(subject) {
            let subjects = match self.producer_subjects.get(&producer_id) {
                Some(&n) => n,
                None => 0,
            };
            let needed = subjects.saturating_add(1);
            if !charge_has_room(self.max_per_producer, needed) {
                return Err("ERR_SUBJECT_BOUND: cannot reserve will subject");
            }
        }
        self.will_reservations
            .insert(producer_id, clone_str(subject));
        Ok(())
    }

    /// Retires `subject` iff `producer_id` is its charged owner and no pending will targets it.
    pub fn retire_subject(&mut self, producer_id: u64, subject: &str) -> Result<(), &'static str> {
        let owner = match self.subject_owner.get(subject) {
            Some(&o) => o,
            None => return Err("subject not present"),
        };
        if owner != producer_id {
            return Err("producer is not charged owner");
        }
        for s in self.will_reservations.values() {
            if s == subject {
                return Err("subject targeted by active will");
            }
        }
        self.subject_owner.remove(subject);
        if let Some(cnt) = self.producer_subjects.get_mut(&owner) {
            *cnt = cnt.saturating_sub(1);
            if *cnt == 0 {
                self.producer_subjects.remove(&owner);
            }
        }
        self.compaction_epoch = charge_epoch_advance(
            self.compaction_epoch,
            self.compaction_epoch.saturating_add(1),
        );
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn producer_subject_budget_charges_introducer_reserves_wills_and_reclaims_on_retire() {
        let mut ledger = SubjectChargeLedger::with_budget(2);
        assert_eq!(ledger.stage_publish(1, "/f/a/s1").unwrap(), 1);
        // Producer 2 updating /f/a/s1 spends 0 of producer 2's budget!
        assert_eq!(ledger.stage_publish(2, "/f/a/s1").unwrap(), 1);
        assert_eq!(ledger.budget_of(2).subjects, 0);

        // Producer 1 reserves a will on /f/a/s2 -> uses 2nd slot (1 subject + 1 reserved = 2/2).
        ledger.register_will(1, "/f/a/s2").unwrap();
        assert_eq!(ledger.budget_of(1).remaining(), 0);
        assert!(ledger.stage_publish(1, "/f/a/s3").is_err());

        // Retiring /f/a/s1 gives 1 slot back to producer 1 so /f/a/s3 now succeeds!
        assert!(ledger.retire_subject(2, "/f/a/s1").is_err());
        ledger.retire_subject(1, "/f/a/s1").unwrap();
        assert_eq!(ledger.budget_of(1).remaining(), 1);
        assert_eq!(ledger.stage_publish(1, "/f/a/s3").unwrap(), 1);
    }
}
