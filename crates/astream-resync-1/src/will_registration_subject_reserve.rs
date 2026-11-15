// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Will-registration subject reservation, `ACK_SEQ_BASE` sequence fence, & connection producer pin
//! (`docs/DESIGN-aterm-fabric.md` §7.2 items c, d, f, g lines 1997–2039;
//! `Astream.Broker.TlaWillRegistrationSubjectReserve`).
//!
//! Models the exact durability & budget invariants governing `Will` registration and firing:
//! - **Item c (One producer id per connection)**: once a connection registers a will under `producer_id`,
//!   any second `Will` on that connection naming a DIFFERENT `producer_id` is refused (`ProducerMismatch`)
//!   rather than leaving a stale durable `/a/will` entry keyed by the prior producer on reopen.
//! - **Item d (Subject budget reserved at registration, exempt at firing)**: registering a will for an
//!   unlanded, unreserved subject checks `landed + reserved < MAX_SUBJECTS_PER_PRODUCER` (`4_096`) and
//!   atomically reserves `1` slot; `stage_will_fire` is exempt so a fire-and-forget goodbye can never
//!   silently drop at connection close or reopen. Landing an ordinary publish on a reserved subject
//!   transfers `1` slot from `reserved` to `landed` (`landed + reserved` stays unchanged).
//! - **Item f (`ACK_SEQ_BASE` two-sided fence)**: any will sequence `>= ACK_SEQ_BASE` (`1 << 63`) is
//!   refused (`SeqReserved`) so no will is unfenceable, and ack sequences (`>= ACK_SEQ_BASE`) never
//!   advance the per-producer high-water mark (`producer_hw`) that fences wills!
//! - **Item g (`local_only` leader commit ack)**: registration acks on the leader's local log commit
//!   (not the follower quorum watermark) so in-memory connection state and durable `/a/will` agree.

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
#[path = "will_registration_subject_reserve_island.rs"]
mod will_registration_subject_reserve_island;
#[cfg(clean_islands)]
pub use will_registration_subject_reserve_island::{will_budget_clamp_b134, will_hw_advance_b134};

/// Maximum distinct subjects (landed + reserved wills) per producer (`4_096`).
pub const MAX_SUBJECTS_PER_PRODUCER: u64 = 4_096;

/// Reserved upper sequence half (`2^63`) for broker/client acks (`StageErr::SeqReserved`).
pub const ACK_SEQ_BASE: u64 = 1_u64 << 63;

#[cfg(not(clean_islands))]
/// Clamp total accounted subjects (`landed + reserved`) to `budget_cap`.
#[must_use]
pub const fn will_budget_clamp_b134(cand_total: u64, budget_cap: u64) -> u64 {
    if cand_total < budget_cap {
        cand_total
    } else {
        budget_cap
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance non-ack producer high-water sequence.
#[must_use]
pub const fn will_hw_advance_b134(cur_hw: u64, cand_hw: u64) -> u64 {
    if cur_hw < cand_hw {
        cand_hw
    } else {
        cur_hw
    }
}

contract_fn! {
    /// True iff `will_seq < ACK_SEQ_BASE && total_accounted < budget_cap` (or subject already accounted).
    #[must_use]
    pub const fn will_reg_admissible_b134(
        will_seq_below_ack_base: bool,
        subject_already_accounted: bool,
        total_accounted: u64,
        budget_cap: u64,
    ) -> bool
    clauses [ensures result == (will_seq_below_ack_base && (subject_already_accounted || total_accounted < budget_cap))]
    {
        will_seq_below_ack_base && (subject_already_accounted || total_accounted < budget_cap)
    }
}

/// Outcome of `Will` registration on a connection.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum WillRegisterVerdict {
    /// Accepted and acked on leader `local_only` commit (`new_slot_reserved` indicates budget delta).
    RegisteredLocalOnlyAck { new_slot_reserved: bool },
    /// Refused: connection already registered a will under a different `producer_id` (§7.2c).
    RefusedProducerMismatch,
    /// Refused: `will_seq >= ACK_SEQ_BASE` (`StageErr::SeqReserved`, §7.2f).
    RefusedSeqReserved,
    /// Refused: `landed + reserved >= MAX_SUBJECTS_PER_PRODUCER` for a fresh subject (§7.2d).
    RefusedSubjectBudgetExhausted,
    /// Refused: log is a declared follower replica (`StageErr::Replica`).
    RefusedReplicaLog,
}

/// Outcome of attempting to fire a connection's or reopen's pending will.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum WillFireVerdict {
    /// Will appended (exempt from subject budget check because registration reserved it!).
    FiredAtSeq(u64),
    /// Suppressed: `has_hw && producer_hw >= will_seq` (graceful goodbye or `inc + 1` landed).
    SuppressedByHighWater,
    /// Suppressed: replica logs never fire wills (`StageErr::Replica`).
    RefusedOnReplica,
    /// Nothing registered on this connection.
    NoPendingWill,
}

/// Per-producer + per-connection will-registration & subject-reservation state machine.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct WillRegistrationGuard {
    is_replica: bool,
    budget_cap: u64,
    landed_subjects: u64,
    reserved_subjects: u64,
    has_producer_hw: bool,
    producer_hw: u64,
    conn_bound_producer: Option<u64>,
    conn_pending_will_seq: Option<u64>,
}

impl WillRegistrationGuard {
    #[must_use]
    pub const fn new(is_replica: bool, budget_cap: u64) -> Self {
        let cap = if budget_cap == 0 {
            MAX_SUBJECTS_PER_PRODUCER
        } else {
            budget_cap
        };
        Self {
            is_replica,
            budget_cap: cap,
            landed_subjects: 0,
            reserved_subjects: 0,
            has_producer_hw: false,
            producer_hw: 0,
            conn_bound_producer: None,
            conn_pending_will_seq: None,
        }
    }

    #[must_use]
    pub const fn total_accounted_subjects(&self) -> u64 {
        will_budget_clamp_b134(
            self.landed_subjects.saturating_add(self.reserved_subjects),
            self.budget_cap,
        )
    }

    #[must_use]
    pub const fn producer_hw(&self) -> Option<u64> {
        if self.has_producer_hw {
            Some(self.producer_hw)
        } else {
            None
        }
    }

    /// Stage a `Will` registration for `(producer_id, will_seq)`.
    pub fn register_will(
        &mut self,
        producer_id: u64,
        will_seq: u64,
        subject_already_landed: bool,
        subject_already_reserved: bool,
    ) -> WillRegisterVerdict {
        if self.is_replica {
            return WillRegisterVerdict::RefusedReplicaLog;
        }
        if let Some(bound) = self.conn_bound_producer {
            if bound != producer_id {
                return WillRegisterVerdict::RefusedProducerMismatch;
            }
        }
        let below_ack = will_seq < ACK_SEQ_BASE;
        let already_accounted = subject_already_landed || subject_already_reserved;
        let total = self.landed_subjects.saturating_add(self.reserved_subjects);
        if !below_ack {
            return WillRegisterVerdict::RefusedSeqReserved;
        }
        if !will_reg_admissible_b134(below_ack, already_accounted, total, self.budget_cap) {
            return WillRegisterVerdict::RefusedSubjectBudgetExhausted;
        }
        let new_slot = !already_accounted;
        if new_slot {
            self.reserved_subjects = self.reserved_subjects.saturating_add(1);
        }
        self.conn_bound_producer = Some(producer_id);
        self.conn_pending_will_seq = Some(will_seq);
        WillRegisterVerdict::RegisteredLocalOnlyAck {
            new_slot_reserved: new_slot,
        }
    }

    /// Record an ordinary publish landing under the producer.
    /// Sequences in `[ACK_SEQ_BASE, u64::MAX]` are excluded from `producer_hw` (§7.2f)!
    pub fn record_publish_landed(
        &mut self,
        producer_seq: u64,
        was_reserved_will_subject: bool,
        is_brand_new_unreserved_subject: bool,
    ) -> bool {
        if was_reserved_will_subject && self.reserved_subjects > 0 {
            // Release reservation into landed 1-for-1 without growing total accounted!
            self.reserved_subjects = self.reserved_subjects.saturating_sub(1);
            self.landed_subjects = self.landed_subjects.saturating_add(1);
        } else if is_brand_new_unreserved_subject {
            let total = self.landed_subjects.saturating_add(self.reserved_subjects);
            if total >= self.budget_cap {
                return false;
            }
            self.landed_subjects = self.landed_subjects.saturating_add(1);
        }
        if producer_seq < ACK_SEQ_BASE {
            self.producer_hw = if self.has_producer_hw {
                will_hw_advance_b134(self.producer_hw, producer_seq)
            } else {
                producer_seq
            };
            self.has_producer_hw = true;
        }
        true
    }

    /// Fire the pending will at connection close or owner-log reopen (exempt from budget check!).
    pub fn fire_pending_will(&mut self) -> WillFireVerdict {
        if self.is_replica {
            return WillFireVerdict::RefusedOnReplica;
        }
        let Some(will_seq) = core::mem::take(&mut self.conn_pending_will_seq) else {
            return WillFireVerdict::NoPendingWill;
        };
        if self.has_producer_hw && self.producer_hw >= will_seq {
            return WillFireVerdict::SuppressedByHighWater;
        }
        self.producer_hw = if self.has_producer_hw {
            will_hw_advance_b134(self.producer_hw, will_seq)
        } else {
            will_seq
        };
        self.has_producer_hw = true;
        if self.reserved_subjects > 0 {
            self.reserved_subjects = self.reserved_subjects.saturating_sub(1);
            self.landed_subjects = self.landed_subjects.saturating_add(1);
        }
        WillFireVerdict::FiredAtSeq(will_seq)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ack_sequences_refused_for_wills_and_excluded_from_fence_hw() {
        let mut g = WillRegistrationGuard::new(false, 4);
        assert_eq!(
            g.register_will(7, ACK_SEQ_BASE, false, false),
            WillRegisterVerdict::RefusedSeqReserved
        );
        let inc1_will = (1_u64 << 32) | 0xFFFF_FFFF;
        assert_eq!(
            g.register_will(7, inc1_will, false, false),
            WillRegisterVerdict::RegisteredLocalOnlyAck {
                new_slot_reserved: true
            }
        );
        // Publishing an ack (`>= ACK_SEQ_BASE`) MUST NOT fence the pending will!
        assert!(g.record_publish_landed(ACK_SEQ_BASE + 99, false, true));
        assert_eq!(g.producer_hw(), None);
        assert_eq!(
            g.fire_pending_will(),
            WillFireVerdict::FiredAtSeq(inc1_will)
        );
    }

    #[test]
    fn connection_producer_mismatch_and_subject_reservation_cap_hold() {
        let mut g = WillRegistrationGuard::new(false, 2);
        let w0 = 0xFFFF_FFFF;
        assert_eq!(
            g.register_will(42, w0, false, false),
            WillRegisterVerdict::RegisteredLocalOnlyAck {
                new_slot_reserved: true
            }
        );
        // Different producer on same connection is refused!
        assert_eq!(
            g.register_will(99, w0, false, false),
            WillRegisterVerdict::RefusedProducerMismatch
        );
        // Superseding with a second distinct subject under SAME producer takes 2nd slot:
        assert_eq!(
            g.register_will(42, w0, false, false),
            WillRegisterVerdict::RegisteredLocalOnlyAck {
                new_slot_reserved: true
            }
        );
        assert_eq!(g.total_accounted_subjects(), 2);
        // A 3rd distinct subject is refused at registration!
        assert_eq!(
            g.register_will(42, w0, false, false),
            WillRegisterVerdict::RefusedSubjectBudgetExhausted
        );
        // Reconnecting on `inc = 2` fences `w0` structurally!
        let inc2_live = 2_u64 << 32;
        assert!(g.record_publish_landed(inc2_live, true, false));
        assert_eq!(g.total_accounted_subjects(), 2);
        assert_eq!(
            g.fire_pending_will(),
            WillFireVerdict::SuppressedByHighWater
        );
    }
}
