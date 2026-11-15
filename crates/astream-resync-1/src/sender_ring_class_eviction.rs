// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Per-sender inbox ring quota (`SENDER_QUOTA = 64`) & class-ordered eviction (`evict_for`)
//! protecting human rows (`docs/DESIGN-aterm-fabric.md` §8.1 T9 line 2195, §6.7 line 1898;
//! `Astream.Agent.TlaSenderRingClassEviction`).
//!
//! Defends human attention and inbox availability against wake/mail flooding:
//! - Every relayed row (`via=`), unlisted `task`/`control`, or stray reply is demoted to `Note`
//!   before quota evaluation,
//! - Each cap-forced `<src>` principal is bounded to `SENDER_QUOTA = 64` unread rows,
//! - Global inbox ring (`RING_CAPACITY = 512`) evicts lowest-priority rows first (`Note` ->
//!   `Ask` -> `Answer` -> `ListedTaskControl` -> `Human`), NEVER evicting a `Human` (`h-*`) row
//!   to admit a non-human arrival!

#[cfg(clean_islands)]
#[path = "sender_ring_class_eviction_island.rs"]
mod sender_ring_class_eviction_island;
#[cfg(clean_islands)]
pub use sender_ring_class_eviction_island::{
    eviction_epoch_advance_b134, sender_unread_clamp_b134,
};

/// Maximum unread rows in the inbox ring per cap-forced `<src>` principal (`64`).
pub const SENDER_QUOTA: u64 = 64;

/// Total unread inbox ring capacity (`512` rows).
pub const INBOX_RING_CAPACITY: u64 = 512;

#[cfg(not(clean_islands))]
/// Clamp per-sender unread count to `SENDER_QUOTA` (`quota_cap`).
#[must_use]
pub const fn sender_unread_clamp_b134(cand_unread: u64, quota_cap: u64) -> u64 {
    if cand_unread < quota_cap {
        cand_unread
    } else {
        quota_cap
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance ring eviction counter.
#[must_use]
pub const fn eviction_epoch_advance_b134(cur_evicted: u64, cand_evicted: u64) -> u64 {
    if cur_evicted < cand_evicted {
        cand_evicted
    } else {
        cur_evicted
    }
}

contract_fn! {
    /// True iff `victim_rank <= incoming_rank && (victim_is_not_human || incoming_is_human)`.
    #[must_use]
    pub const fn class_eviction_permitted_b134(
        victim_rank: u8,
        incoming_rank: u8,
        victim_is_not_human: bool,
        incoming_is_human: bool,
    ) -> bool
    clauses [ensures result == (victim_rank <= incoming_rank && (victim_is_not_human || incoming_is_human))]
    {
        victim_rank <= incoming_rank && (victim_is_not_human || incoming_is_human)
    }
}

/// Canonical delivery priority class after `classify_delivery` demotion (`Note = 0` .. `Human = 4`).
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum DeliveryPriorityClass {
    /// `0`: ordinary `note`, relayed `via=`, unlisted `task`/`control`, or stray reply.
    Note,
    /// `1`: `ask` row.
    Ask,
    /// `2`: matched `answer` to an in-flight post.
    Answer,
    /// `3`: allowlisted peer `task` or `control`.
    ListedTaskControl,
    /// `4`: `h-*` human operator row — evicted LAST, never evicted for a non-human arrival!
    Human,
}

impl DeliveryPriorityClass {
    #[must_use]
    pub const fn rank(self) -> u8 {
        match self {
            Self::Note => 0,
            Self::Ask => 1,
            Self::Answer => 2,
            Self::ListedTaskControl => 3,
            Self::Human => 4,
        }
    }
}

/// Classify raw incoming delivery into its canonical priority class (§6.7, §8.1 T9).
#[must_use]
pub const fn classify_delivery_priority(
    sender_is_human: bool,
    has_via_relay: bool,
    sender_is_allowlisted: bool,
    raw_kind_is_task_or_control: bool,
    raw_kind_is_ask: bool,
    is_matched_answer: bool,
) -> DeliveryPriorityClass {
    if has_via_relay {
        // §6.7: relayed messages are ALWAYS demoted to `kind=note trust=relayed` regardless of allowlist!
        return DeliveryPriorityClass::Note;
    }
    if sender_is_human {
        return DeliveryPriorityClass::Human;
    }
    if is_matched_answer {
        return DeliveryPriorityClass::Answer;
    }
    if raw_kind_is_task_or_control {
        if sender_is_allowlisted {
            DeliveryPriorityClass::ListedTaskControl
        } else {
            DeliveryPriorityClass::Note
        }
    } else if raw_kind_is_ask {
        DeliveryPriorityClass::Ask
    } else {
        DeliveryPriorityClass::Note
    }
}

/// Admission verdict for an inbox ring arrival.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum InboxAdmissionVerdict {
    /// Appended directly into free ring + free sender quota space.
    AdmittedWithoutEviction,
    /// Admitted by evicting one lowest-rank eligible row (`Note`..`Human`).
    AdmittedEvictingClass(DeliveryPriorityClass),
    /// Dropped: sender quota (`64`) or ring (`512`) is full of strictly higher-priority (or protected `Human`) rows!
    DroppedHigherPriorityProtected,
}

/// Class-counted inbox ring + single tracked sender quota state machine.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct InboxClassEvictionRing {
    ring_cap: u64,
    sender_quota_cap: u64,
    note_rows: u64,
    ask_rows: u64,
    answer_rows: u64,
    listed_rows: u64,
    human_rows: u64,
    tracked_sender_unread: u64,
    tracked_sender_lowest_rank: u8,
    evictions_total: u64,
}

impl InboxClassEvictionRing {
    #[must_use]
    pub const fn new(ring_cap: u64, sender_quota_cap: u64) -> Self {
        let r_cap = if ring_cap == 0 {
            INBOX_RING_CAPACITY
        } else {
            ring_cap
        };
        let s_cap = if sender_quota_cap == 0 {
            SENDER_QUOTA
        } else {
            sender_quota_cap
        };
        Self {
            ring_cap: r_cap,
            sender_quota_cap: s_cap,
            note_rows: 0,
            ask_rows: 0,
            answer_rows: 0,
            listed_rows: 0,
            human_rows: 0,
            tracked_sender_unread: 0,
            tracked_sender_lowest_rank: 4,
            evictions_total: 0,
        }
    }

    #[must_use]
    pub const fn total_unread(&self) -> u64 {
        self.note_rows
            .saturating_add(self.ask_rows)
            .saturating_add(self.answer_rows)
            .saturating_add(self.listed_rows)
            .saturating_add(self.human_rows)
    }

    #[must_use]
    pub const fn tracked_sender_unread(&self) -> u64 {
        sender_unread_clamp_b134(self.tracked_sender_unread, self.sender_quota_cap)
    }

    #[must_use]
    pub const fn human_rows(&self) -> u64 {
        self.human_rows
    }

    fn increment_class(&mut self, cls: DeliveryPriorityClass) {
        match cls {
            DeliveryPriorityClass::Note => self.note_rows = self.note_rows.saturating_add(1),
            DeliveryPriorityClass::Ask => self.ask_rows = self.ask_rows.saturating_add(1),
            DeliveryPriorityClass::Answer => self.answer_rows = self.answer_rows.saturating_add(1),
            DeliveryPriorityClass::ListedTaskControl => {
                self.listed_rows = self.listed_rows.saturating_add(1);
            }
            DeliveryPriorityClass::Human => self.human_rows = self.human_rows.saturating_add(1),
        }
    }

    fn try_evict_lowest_for(
        &mut self,
        incoming: DeliveryPriorityClass,
    ) -> Option<DeliveryPriorityClass> {
        let in_rank = incoming.rank();
        let in_human = matches!(incoming, DeliveryPriorityClass::Human);
        if self.note_rows > 0 && class_eviction_permitted_b134(0, in_rank, true, in_human) {
            self.note_rows = self.note_rows.saturating_sub(1);
            return Some(DeliveryPriorityClass::Note);
        }
        if self.ask_rows > 0 && class_eviction_permitted_b134(1, in_rank, true, in_human) {
            self.ask_rows = self.ask_rows.saturating_sub(1);
            return Some(DeliveryPriorityClass::Ask);
        }
        if self.answer_rows > 0 && class_eviction_permitted_b134(2, in_rank, true, in_human) {
            self.answer_rows = self.answer_rows.saturating_sub(1);
            return Some(DeliveryPriorityClass::Answer);
        }
        if self.listed_rows > 0 && class_eviction_permitted_b134(3, in_rank, true, in_human) {
            self.listed_rows = self.listed_rows.saturating_sub(1);
            return Some(DeliveryPriorityClass::ListedTaskControl);
        }
        if self.human_rows > 0 && class_eviction_permitted_b134(4, in_rank, false, in_human) {
            self.human_rows = self.human_rows.saturating_sub(1);
            return Some(DeliveryPriorityClass::Human);
        }
        None
    }

    /// Admit an incoming row (`from_tracked_sender == true` enforces `sender_quota_cap`).
    pub fn admit_delivery(
        &mut self,
        cls: DeliveryPriorityClass,
        from_tracked_sender: bool,
    ) -> InboxAdmissionVerdict {
        let rank = cls.rank();
        let is_human = matches!(cls, DeliveryPriorityClass::Human);
        if from_tracked_sender && self.tracked_sender_unread >= self.sender_quota_cap {
            // Sender hit SENDER_QUOTA: can only replace own lowest row if permitted!
            let victim_not_human = self.tracked_sender_lowest_rank < 4;
            if !class_eviction_permitted_b134(
                self.tracked_sender_lowest_rank,
                rank,
                victim_not_human,
                is_human,
            ) {
                return InboxAdmissionVerdict::DroppedHigherPriorityProtected;
            }
            let Some(evicted) = self.try_evict_lowest_for(cls) else {
                return InboxAdmissionVerdict::DroppedHigherPriorityProtected;
            };
            self.increment_class(cls);
            self.evictions_total = eviction_epoch_advance_b134(
                self.evictions_total,
                self.evictions_total.saturating_add(1),
            );
            return InboxAdmissionVerdict::AdmittedEvictingClass(evicted);
        }

        if self.total_unread() >= self.ring_cap {
            let Some(evicted) = self.try_evict_lowest_for(cls) else {
                return InboxAdmissionVerdict::DroppedHigherPriorityProtected;
            };
            self.increment_class(cls);
            if from_tracked_sender {
                self.tracked_sender_unread = sender_unread_clamp_b134(
                    self.tracked_sender_unread.saturating_add(1),
                    self.sender_quota_cap,
                );
                if rank < self.tracked_sender_lowest_rank {
                    self.tracked_sender_lowest_rank = rank;
                }
            }
            self.evictions_total = eviction_epoch_advance_b134(
                self.evictions_total,
                self.evictions_total.saturating_add(1),
            );
            return InboxAdmissionVerdict::AdmittedEvictingClass(evicted);
        }

        self.increment_class(cls);
        if from_tracked_sender {
            self.tracked_sender_unread = sender_unread_clamp_b134(
                self.tracked_sender_unread.saturating_add(1),
                self.sender_quota_cap,
            );
            if rank < self.tracked_sender_lowest_rank {
                self.tracked_sender_lowest_rank = rank;
            }
        }
        InboxAdmissionVerdict::AdmittedWithoutEviction
    }

    /// Reading/consuming a row (`inbox get` / `inbox seen`) frees ring & sender quota slots.
    pub fn mark_seen(&mut self, cls: DeliveryPriorityClass, from_tracked_sender: bool) {
        match cls {
            DeliveryPriorityClass::Note => self.note_rows = self.note_rows.saturating_sub(1),
            DeliveryPriorityClass::Ask => self.ask_rows = self.ask_rows.saturating_sub(1),
            DeliveryPriorityClass::Answer => self.answer_rows = self.answer_rows.saturating_sub(1),
            DeliveryPriorityClass::ListedTaskControl => {
                self.listed_rows = self.listed_rows.saturating_sub(1);
            }
            DeliveryPriorityClass::Human => self.human_rows = self.human_rows.saturating_sub(1),
        }
        if from_tracked_sender {
            self.tracked_sender_unread = self.tracked_sender_unread.saturating_sub(1);
            if self.tracked_sender_unread == 0 {
                self.tracked_sender_lowest_rank = 4;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn relayed_via_and_unlisted_tasks_demote_to_note() {
        // Even a human principal claiming `via=` is demoted to `Note`!
        assert_eq!(
            classify_delivery_priority(true, true, true, true, false, false),
            DeliveryPriorityClass::Note
        );
        // Unlisted peer `task` demotes to `Note`, listed peer stays `ListedTaskControl`.
        assert_eq!(
            classify_delivery_priority(false, false, false, true, false, false),
            DeliveryPriorityClass::Note
        );
        assert_eq!(
            classify_delivery_priority(false, false, true, true, false, false),
            DeliveryPriorityClass::ListedTaskControl
        );
    }

    #[test]
    fn human_rows_never_evicted_by_agent_flood_and_sender_quota_caps_at_bound() {
        let mut ring = InboxClassEvictionRing::new(3, 2);
        assert_eq!(
            ring.admit_delivery(DeliveryPriorityClass::Human, false),
            InboxAdmissionVerdict::AdmittedWithoutEviction
        );
        assert_eq!(
            ring.admit_delivery(DeliveryPriorityClass::Human, false),
            InboxAdmissionVerdict::AdmittedWithoutEviction
        );
        assert_eq!(
            ring.admit_delivery(DeliveryPriorityClass::Note, true),
            InboxAdmissionVerdict::AdmittedWithoutEviction
        );
        // Listed peer task evicts the `Note`, leaving both `Human` rows untouched!
        assert_eq!(
            ring.admit_delivery(DeliveryPriorityClass::ListedTaskControl, false),
            InboxAdmissionVerdict::AdmittedEvictingClass(DeliveryPriorityClass::Note)
        );
        // Fill last slot with 3rd `Human` (evicts `ListedTaskControl`):
        assert_eq!(
            ring.admit_delivery(DeliveryPriorityClass::Human, false),
            InboxAdmissionVerdict::AdmittedEvictingClass(DeliveryPriorityClass::ListedTaskControl)
        );
        assert_eq!(ring.human_rows(), 3);
        // Now NO non-human arrival can evict any of the 3 `Human` rows!
        assert_eq!(
            ring.admit_delivery(DeliveryPriorityClass::ListedTaskControl, false),
            InboxAdmissionVerdict::DroppedHigherPriorityProtected
        );
        assert_eq!(ring.human_rows(), 3);
    }
}
