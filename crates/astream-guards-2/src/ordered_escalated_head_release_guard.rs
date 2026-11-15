// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Ordered-tier escalated visible-head hold, full-flush release, and failed-flush Lossy poison
//! guard (`evidence/manifest.toml` `broker.ordered-tier`;
//! `Astream.Broker.TlaOrderedEscalatedHeadReleaseGuard`).
//!
//! Enforces the `Durability::Ordered` / `Durability::Relaxed` escalation visibility invariant:
//! - Staging an ordinary batch advances `log_head` and `visible_head` when no escalated record
//!   is held,
//! - Staging an escalated record (`Subject`, `PrincipalPrefix` bound earlier in the same batch,
//!   or `Group` commit) holds `visible_head` at `held_at_offset` (`visible_head <= log_head`)
//!   and holds any escalated `group_start` update until `sync_full` completes,
//! - A successful `sync_full` advances `durable_head` and releases `visible_head` to `log_head`,
//! - A failed `sync_full` latches `lossy_strict_latched = true` and `poisoned = true`: a later
//!   `sync_full` success moves nothing, subscribers never read the unpersisted escalated record,
//!   and resends are refused instead of dedup-acking!

#[cfg(clean_islands)]
#[path = "ordered_escalated_head_release_guard_island.rs"]
mod ordered_escalated_head_release_guard_island;
#[cfg(clean_islands)]
pub use ordered_escalated_head_release_guard_island::{
    durable_head_advance_b147, visible_head_clamp_b147,
};

#[cfg(not(clean_islands))]
/// Clamp `visible_head` to never exceed `log_head`.
#[must_use]
pub const fn visible_head_clamp_b147(cand_visible: u64, log_head: u64) -> u64 {
    if cand_visible < log_head {
        cand_visible
    } else {
        log_head
    }
}

#[cfg(not(clean_islands))]
/// Advance `durable_head` monotonically upon verified full device flush.
#[must_use]
pub const fn durable_head_advance_b147(cur_durable: u64, cand_durable: u64) -> u64 {
    if cur_durable < cand_durable {
        cand_durable
    } else {
        cur_durable
    }
}

contract_fn! {
    /// True iff `offset` is strictly below `visible_head` and log is not poisoned.
    #[must_use]
    pub const fn escalated_offset_deliverable_b147(
        offset: u64,
        visible_head: u64,
        poisoned: bool,
    ) -> bool
    clauses [ensures result == (!poisoned && offset < visible_head)]
    {
        !poisoned && offset < visible_head
    }
}

/// Transition verdict for Ordered/Relaxed escalated batch staging and full-flush completion.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OrderedEscalationDecision {
    CommittedVisibleImmediately {
        visible_head: u64,
        log_head: u64,
    },
    HeldAtEscalatedOffset {
        visible_head: u64,
        owed_flush_to: u64,
    },
    ReleasedByFullFlush {
        visible_head: u64,
        durable_head: u64,
    },
    PoisonedLossyStrictOnFailedFlush {
        frozen_visible_head: u64,
        durable_head: u64,
    },
    RefusedLogPoisonedByFailedFlush,
}

/// Tracks `log_head`, `visible_head`, `durable_head`, held escalation ceiling, and Lossy poison.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OrderedEscalatedHeadGuard {
    log_head: u64,
    visible_head: u64,
    durable_head: u64,
    held_escalated_at: Option<u64>,
    lossy_strict_latched: bool,
    poisoned: bool,
}

impl OrderedEscalatedHeadGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            log_head: 0,
            visible_head: 0,
            durable_head: 0,
            held_escalated_at: None,
            lossy_strict_latched: false,
            poisoned: false,
        }
    }

    #[must_use]
    pub const fn visible_head(&self) -> u64 {
        visible_head_clamp_b147(self.visible_head, self.log_head)
    }

    #[must_use]
    pub const fn durable_head(&self) -> u64 {
        self.durable_head
    }

    #[must_use]
    pub const fn is_lossy_strict_latched(&self) -> bool {
        self.lossy_strict_latched
    }

    /// Stage and barrier-commit a batch `[prev_head .. batch_end_head)`, optionally holding at
    /// `first_escalated_offset` inside the batch.
    pub fn on_barrier_batch_committed(
        &mut self,
        batch_end_head: u64,
        first_escalated_offset: Option<u64>,
    ) -> OrderedEscalationDecision {
        if self.poisoned {
            return OrderedEscalationDecision::RefusedLogPoisonedByFailedFlush;
        }
        if batch_end_head > self.log_head {
            self.log_head = batch_end_head;
        }
        match (self.held_escalated_at, first_escalated_offset) {
            (Some(existing_hold), _) => OrderedEscalationDecision::HeldAtEscalatedOffset {
                visible_head: visible_head_clamp_b147(existing_hold, self.log_head),
                owed_flush_to: self.log_head,
            },
            (None, Some(esc_off)) => {
                let hold = visible_head_clamp_b147(esc_off, self.log_head);
                self.held_escalated_at = Some(hold);
                self.visible_head = hold;
                OrderedEscalationDecision::HeldAtEscalatedOffset {
                    visible_head: self.visible_head,
                    owed_flush_to: self.log_head,
                }
            }
            (None, None) => {
                self.visible_head = visible_head_clamp_b147(self.log_head, self.log_head);
                OrderedEscalationDecision::CommittedVisibleImmediately {
                    visible_head: self.visible_head,
                    log_head: self.log_head,
                }
            }
        }
    }

    /// Complete an outside-lock `sync_full` covering `flushed_to_head`.
    pub fn on_full_flush_result(
        &mut self,
        flushed_to_head: u64,
        flush_succeeded: bool,
    ) -> OrderedEscalationDecision {
        if self.poisoned {
            return OrderedEscalationDecision::RefusedLogPoisonedByFailedFlush;
        }
        if !flush_succeeded {
            self.lossy_strict_latched = true;
            self.poisoned = true;
            return OrderedEscalationDecision::PoisonedLossyStrictOnFailedFlush {
                frozen_visible_head: self.visible_head,
                durable_head: self.durable_head,
            };
        }
        let target = visible_head_clamp_b147(flushed_to_head, self.log_head);
        self.durable_head = durable_head_advance_b147(self.durable_head, target);
        if let Some(hold) = self.held_escalated_at {
            if self.durable_head > hold {
                self.held_escalated_at = None;
                self.visible_head = visible_head_clamp_b147(self.log_head, self.log_head);
            }
        }
        OrderedEscalationDecision::ReleasedByFullFlush {
            visible_head: self.visible_head,
            durable_head: self.durable_head,
        }
    }

    #[must_use]
    pub const fn can_deliver_offset(&self, offset: u64) -> bool {
        escalated_offset_deliverable_b147(offset, self.visible_head, self.poisoned)
    }
}

impl Default for OrderedEscalatedHeadGuard {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn holds_escalated_head_until_full_flush_and_poisons_permanently_on_flush_failure() {
        let mut g = OrderedEscalatedHeadGuard::new();
        // Batch [0..3) where offset 1 is escalated: offset 0 is visible, offsets 1..2 are held!
        assert_eq!(
            g.on_barrier_batch_committed(3, Some(1)),
            OrderedEscalationDecision::HeldAtEscalatedOffset {
                visible_head: 1,
                owed_flush_to: 3,
            }
        );
        assert!(g.can_deliver_offset(0));
        assert!(!g.can_deliver_offset(1));

        // Full flush succeeds -> durable_head = 3 and visible_head = 3!
        assert_eq!(
            g.on_full_flush_result(3, true),
            OrderedEscalationDecision::ReleasedByFullFlush {
                visible_head: 3,
                durable_head: 3,
            }
        );
        assert!(g.can_deliver_offset(2));

        // Next batch [3..5) with escalated offset 3 fails full flush -> poisons permanently!
        g.on_barrier_batch_committed(5, Some(3));
        assert_eq!(
            g.on_full_flush_result(5, false),
            OrderedEscalationDecision::PoisonedLossyStrictOnFailedFlush {
                frozen_visible_head: 3,
                durable_head: 3,
            }
        );
        assert!(g.is_lossy_strict_latched());
        // Even a subsequent "successful" flush moves nothing!
        assert_eq!(
            g.on_full_flush_result(5, true),
            OrderedEscalationDecision::RefusedLogPoisonedByFailedFlush
        );
    }
}
