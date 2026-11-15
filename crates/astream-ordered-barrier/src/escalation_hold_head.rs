// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Escalated-batch `visible_head` hold tracker (`broker.ordered-tier`: holding `visible_head` at
//! the first escalated record until the deferred full `fsync` completes outside the log lock;
//! `Astream.OrdBar.TlaEscalationHoldHead`).

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
#[path = "escalation_hold_head_island.rs"]
mod escalation_hold_head_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ob_off_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ob_vis_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use escalation_hold_head_island::{ob_off_clamp, ob_vis_advance};

/// Maximum log offset clamp (`1_000_000_000_000`).
pub const MAX_HOLD_OFFSET: u64 = 1_000_000_000_000;

contract_fn! {
    /// Verified durable-coverage release check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `ob_head_released_isl`.
    #[must_use]
    pub const fn ob_head_released(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct EscalationHeadHold {
    visible_head: u64,
    durable_head: u64,
    staged_head: u64,
    required_flush_to: Option<u64>,
}

impl EscalationHeadHold {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            visible_head: 0,
            durable_head: 0,
            staged_head: 0,
            required_flush_to: None,
        }
    }

    pub fn stage_batch(&mut self, batch_end: u64, first_escalated_at: Option<u64>) -> u64 {
        let end = ob_off_clamp(batch_end, MAX_HOLD_OFFSET);
        self.staged_head = ob_vis_advance(self.staged_head, end);
        if let Some(esc) = first_escalated_at {
            let clamped_esc = ob_off_clamp(esc, end);
            if self.required_flush_to.is_none() {
                self.visible_head = ob_vis_advance(self.visible_head, clamped_esc);
            }
            let next_req = match self.required_flush_to {
                Some(prev) => ob_vis_advance(prev, end),
                None => end,
            };
            self.required_flush_to = Some(next_req);
        } else if self.required_flush_to.is_none() {
            self.visible_head = ob_vis_advance(self.visible_head, end);
        }
        self.visible_head
    }

    pub fn complete_full_flush(&mut self, flushed_through: u64) -> u64 {
        let f = ob_off_clamp(flushed_through, MAX_HOLD_OFFSET);
        self.durable_head = ob_vis_advance(self.durable_head, f);
        if let Some(req) = self.required_flush_to {
            if ob_head_released(self.durable_head, req) {
                self.required_flush_to = None;
                let release_to = ob_vis_advance(self.staged_head, self.durable_head);
                self.visible_head = ob_vis_advance(self.visible_head, release_to);
            }
        } else {
            self.visible_head = ob_vis_advance(self.visible_head, self.durable_head);
        }
        self.visible_head
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn holds_visible_head_at_escalated_record_until_full_flush_lands() {
        let mut h = EscalationHeadHold::new();
        assert_eq!(h.stage_batch(5, None), 5);
        assert_eq!(h.stage_batch(9, Some(6)), 6);
        assert_eq!(h.stage_batch(12, None), 6);
        assert_eq!(h.complete_full_flush(12), 12);
    }
}
