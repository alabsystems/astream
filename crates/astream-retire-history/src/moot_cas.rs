// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Conditional `Request::Retire { producer_id, subject, offset, log }` compare-and-set vs
//! moot-supersede classifier (`broker.subject-retire`, `Astream.Retire.TlaMootCas`).
//!
//! Mirrors and verifies the exact decision table of conditional subject retirement over
//! [`astream_wire::LogIdentity`]:
//! - Mismatched `LogIdentity` -> `RefusedLogMismatch` (`ERR_RETIRE_REFUSED`).
//! - Subject currently absent:
//!   * `req_offset < head` -> `MootAlreadyAbsent` (`PublishAck { duplicate: true }`, 0 appends).
//!   * `req_offset >= head` -> `RefusedOffsetAtOrAboveHead`.
//! - Subject currently present at `(cur_offset, charged_producer)`:
//!   * `req_offset < cur_offset` -> `MootSuperseded` (`PublishAck { duplicate: true }`, keeps superseding row!).
//!   * `req_offset > cur_offset` -> `RefusedOffsetAheadOfCurrent`.
//!   * `req_offset == cur_offset`: requires `producer_id == charged_producer` and `!has_active_will`,
//!     otherwise refuses `RefusedNotChargedOwner` / `RefusedActiveWill`, else commits `AppendMarkedRetire`!

use astream_wire::LogIdentity;

#[cfg(clean_islands)]
#[path = "moot_cas_island.rs"]
mod moot_cas_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cas_attempts_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cas_head_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use moot_cas_island::{cas_attempts_clamp, cas_head_advance};

/// Maximum conditional retire operations evaluated in one writer batch.
pub const MAX_CAS_BATCH_OPS: u64 = 256;

contract_fn! {
    /// Verified ordering predicate (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `cas_matches_cur_isl`.
    #[must_use]
    pub const fn cas_matches_cur(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Live state of a target subject in `BrokerLog` when evaluating `Request::Retire`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubjectSlotState {
    Absent,
    Present {
        cur_offset: u64,
        charged_producer: u64,
        has_active_will: bool,
    },
}

/// Deterministic decision for a conditional `Request::Retire`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConditionalRetireOutcome {
    /// CAS matched `cur_offset == req_offset`; append `/a/retire` (`COMMIT_TAG_RETIRE = 2`) and credit budget.
    AppendMarkedRetire {
        credited_producer: u64,
    },
    /// Subject already retired below `head`; answer `PublishAck { duplicate: true }` with no append.
    MootAlreadyAbsent,
    /// Subject was updated at `cur_offset > req_offset`; answer `PublishAck { duplicate: true }` keeping new value!
    MootSuperseded {
        cur_offset: u64,
    },
    RefusedLogMismatch,
    RefusedOffsetAtOrAboveHead,
    RefusedOffsetAheadOfCurrent,
    RefusedNotChargedOwner,
    RefusedActiveWill,
}

/// Stateful classifier tracking monotone `log_head` (`cas_head_advance`) and batch evaluations.
#[derive(Debug, Clone)]
pub struct ConditionalRetireClassifier {
    log_id: LogIdentity,
    log_head: u64,
    evaluated_in_batch: u64,
}

impl ConditionalRetireClassifier {
    #[must_use]
    pub const fn new(log_id: LogIdentity, log_head: u64) -> Self {
        Self {
            log_id,
            log_head,
            evaluated_in_batch: 0,
        }
    }

    #[must_use]
    pub const fn log_head(&self) -> u64 {
        self.log_head
    }

    pub fn advance_head(&mut self, next_head: u64) -> u64 {
        self.log_head = cas_head_advance(self.log_head, next_head);
        self.log_head
    }

    /// Classifies a conditional `Request::Retire` against the current log identity, head, and slot state.
    pub fn classify(
        &mut self,
        req_log: &LogIdentity,
        req_producer: u64,
        req_offset: u64,
        slot: SubjectSlotState,
    ) -> ConditionalRetireOutcome {
        self.evaluated_in_batch =
            cas_attempts_clamp(self.evaluated_in_batch.saturating_add(1), MAX_CAS_BATCH_OPS);
        if *req_log != self.log_id {
            return ConditionalRetireOutcome::RefusedLogMismatch;
        }
        match slot {
            SubjectSlotState::Absent => {
                if cas_matches_cur(req_offset, self.log_head) {
                    ConditionalRetireOutcome::RefusedOffsetAtOrAboveHead
                } else {
                    ConditionalRetireOutcome::MootAlreadyAbsent
                }
            }
            SubjectSlotState::Present {
                cur_offset,
                charged_producer,
                has_active_will,
            } => {
                if req_offset < cur_offset {
                    ConditionalRetireOutcome::MootSuperseded { cur_offset }
                } else if req_offset > cur_offset {
                    ConditionalRetireOutcome::RefusedOffsetAheadOfCurrent
                } else if req_producer != charged_producer {
                    ConditionalRetireOutcome::RefusedNotChargedOwner
                } else if has_active_will {
                    ConditionalRetireOutcome::RefusedActiveWill
                } else {
                    ConditionalRetireOutcome::AppendMarkedRetire {
                        credited_producer: charged_producer,
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn conditional_retire_classifier_handles_cas_moot_supersede_and_refusals() {
        let lid = LogIdentity::parse("0123456789abcdef0123456789abcdef.1").unwrap();
        let wrong = LogIdentity::parse("0123456789abcdef0123456789abcdef.2").unwrap();
        let mut cls = ConditionalRetireClassifier::new(lid, 50);

        assert_eq!(
            cls.classify(&wrong, 7, 10, SubjectSlotState::Absent),
            ConditionalRetireOutcome::RefusedLogMismatch
        );
        assert_eq!(
            cls.classify(&lid, 7, 49, SubjectSlotState::Absent),
            ConditionalRetireOutcome::MootAlreadyAbsent
        );
        assert_eq!(
            cls.classify(&lid, 7, 50, SubjectSlotState::Absent),
            ConditionalRetireOutcome::RefusedOffsetAtOrAboveHead
        );

        let present = SubjectSlotState::Present {
            cur_offset: 30,
            charged_producer: 7,
            has_active_will: false,
        };
        assert_eq!(
            cls.classify(&lid, 7, 25, present),
            ConditionalRetireOutcome::MootSuperseded { cur_offset: 30 }
        );
        assert_eq!(
            cls.classify(&lid, 7, 31, present),
            ConditionalRetireOutcome::RefusedOffsetAheadOfCurrent
        );
        assert_eq!(
            cls.classify(&lid, 9, 30, present),
            ConditionalRetireOutcome::RefusedNotChargedOwner
        );
        assert_eq!(
            cls.classify(&lid, 7, 30, present),
            ConditionalRetireOutcome::AppendMarkedRetire {
                credited_producer: 7
            }
        );
    }
}
