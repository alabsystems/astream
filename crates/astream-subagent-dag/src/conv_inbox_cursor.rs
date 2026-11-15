// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Reactive subagent wakeup inbox & `TimerCondition` early-cancellation matcher
//! (`schedule` + `send_message`, `Astream.Subagent.TlaConvInboxCursor`).

#[cfg(clean_islands)]
#[path = "conv_inbox_cursor_island.rs"]
mod conv_inbox_cursor_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sub_inbox_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sub_seq_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use conv_inbox_cursor_island::{sub_inbox_clamp, sub_seq_advance};

/// Maximum queued unread wakeup messages per conversation.
pub const MAX_UNREAD_WAKEUPS: u64 = 256;

contract_fn! {
    /// Verified delivery cursor check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sub_timer_satisfied_isl`.
    #[must_use]
    pub const fn sub_timer_satisfied(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WakeupTimerCondition {
    Never,
    AnyMessage,
    Sender(String),
}

/// Reactive inbox matching incoming subagent/task messages against armed `TimerCondition`s.
#[derive(Debug, Clone)]
pub struct ReactiveInboxState {
    seq: u64,
    unread: u64,
    armed_condition: WakeupTimerCondition,
}

impl ReactiveInboxState {
    #[must_use]
    pub const fn new(cond: WakeupTimerCondition) -> Self {
        Self {
            seq: 0,
            unread: 0,
            armed_condition: cond,
        }
    }

    /// Delivers a message from `sender_id` and returns `true` iff an armed timer is cancelled early!
    pub fn on_message(&mut self, sender_id: &str) -> bool {
        if sender_id.trim().is_empty() {
            return false;
        }
        self.seq = sub_seq_advance(self.seq, self.seq.saturating_add(1));
        self.unread = sub_inbox_clamp(self.unread.saturating_add(1), MAX_UNREAD_WAKEUPS);
        let cancels = match &self.armed_condition {
            WakeupTimerCondition::Never => false,
            WakeupTimerCondition::AnyMessage => true,
            WakeupTimerCondition::Sender(expected) => {
                !expected.is_empty() && expected.as_str() == sender_id
            }
        };
        if cancels && sub_timer_satisfied(self.seq, 1) {
            self.armed_condition = WakeupTimerCondition::Never;
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sender_specific_timer_condition_cancels_only_on_matching_subagent_reply() {
        let mut ib =
            ReactiveInboxState::new(WakeupTimerCondition::Sender("conv-worker-7".to_owned()));
        assert!(!ib.on_message("conv-other"));
        assert!(ib.on_message("conv-worker-7"));
        assert!(!ib.on_message("conv-worker-7"));
    }
}
