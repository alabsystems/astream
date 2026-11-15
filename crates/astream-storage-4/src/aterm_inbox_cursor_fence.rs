// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm ctl @self inbox` monotonic mail cursor & unread-backlog fence
//! (`Astream.Host.TlaAtermInboxCursorFence`).
//!
//! Tracks `consumed_seq <= arrived_seq` and bounds unread peer-mail slots
//! (`unread_count <= max_unread`) so a chatty worker fleet cannot exhaust a
//! session's inbox memory while preserving exact gap/overflow counts.

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
#[path = "aterm_inbox_cursor_fence_island.rs"]
mod aterm_inbox_cursor_fence_island;
#[cfg(clean_islands)]
pub use aterm_inbox_cursor_fence_island::{inbox_seq_advance, inbox_unread_clamp};

#[cfg(not(clean_islands))]
/// Monotonically advance `aterm` inbox sequence watermark.
#[must_use]
pub const fn inbox_seq_advance(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}

#[cfg(not(clean_islands))]
/// Clamp buffered unread peer-mail count to `max_unread`.
#[must_use]
pub const fn inbox_unread_clamp(cand_unread: u64, max_unread: u64) -> u64 {
    if cand_unread < max_unread {
        cand_unread
    } else {
        max_unread
    }
}

contract_fn! {
    /// True iff `unread_count < max_unread` (inbox can buffer another mail item).
    #[must_use]
    pub const fn inbox_can_enqueue(unread_count: u64, max_unread: u64) -> bool
    clauses [ensures result == (unread_count < max_unread)]
    {
        unread_count < max_unread
    }
}

/// Result of delivering a peer mail message into a session's `aterm` inbox.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InboxEnqueueVerdict {
    Buffered { mail_seq: u64, unread_count: u64 },
    DroppedAtCap { mail_seq: u64, dropped_total: u64 },
}

/// Pure stack `aterm ctl @self inbox` cursor & backlog fence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AtermInboxCursorFence {
    max_unread: u64,
    arrived_seq: u64,
    consumed_seq: u64,
    unread_count: u64,
    dropped_total: u64,
}

impl AtermInboxCursorFence {
    #[must_use]
    pub const fn new(max_unread: u64) -> Self {
        let cap = if max_unread == 0 { 64 } else { max_unread };
        Self {
            max_unread: cap,
            arrived_seq: 0,
            consumed_seq: 0,
            unread_count: 0,
            dropped_total: 0,
        }
    }

    #[must_use]
    pub const fn arrived_seq(&self) -> u64 {
        self.arrived_seq
    }

    #[must_use]
    pub const fn consumed_seq(&self) -> u64 {
        self.consumed_seq
    }

    #[must_use]
    pub const fn unread_count(&self) -> u64 {
        self.unread_count
    }

    #[must_use]
    pub const fn dropped_total(&self) -> u64 {
        self.dropped_total
    }

    /// Record arrival of a new peer mail item.
    pub fn on_arrive(&mut self) -> InboxEnqueueVerdict {
        let cand_seq = self.arrived_seq.saturating_add(1);
        self.arrived_seq = inbox_seq_advance(self.arrived_seq, cand_seq);
        if inbox_can_enqueue(self.unread_count, self.max_unread) {
            let next_unread = self.unread_count.saturating_add(1);
            self.unread_count = inbox_unread_clamp(next_unread, self.max_unread);
            InboxEnqueueVerdict::Buffered {
                mail_seq: self.arrived_seq,
                unread_count: self.unread_count,
            }
        } else {
            self.dropped_total = self.dropped_total.saturating_add(1);
            InboxEnqueueVerdict::DroppedAtCap {
                mail_seq: self.arrived_seq,
                dropped_total: self.dropped_total,
            }
        }
    }

    /// Acknowledge `count` unread items read by `aterm ctl @self inbox`.
    pub fn on_consume(&mut self, count: u64) -> u64 {
        let drained = if count < self.unread_count {
            count
        } else {
            self.unread_count
        };
        self.unread_count =
            inbox_unread_clamp(self.unread_count.saturating_sub(drained), self.max_unread);
        self.consumed_seq = inbox_seq_advance(self.consumed_seq, self.arrived_seq);
        drained
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bounds_unread_peer_mail_and_tracks_overflows() {
        let mut fence = AtermInboxCursorFence::new(2);
        assert_eq!(
            fence.on_arrive(),
            InboxEnqueueVerdict::Buffered {
                mail_seq: 1,
                unread_count: 1,
            }
        );
        assert_eq!(
            fence.on_arrive(),
            InboxEnqueueVerdict::Buffered {
                mail_seq: 2,
                unread_count: 2,
            }
        );
        assert_eq!(
            fence.on_arrive(),
            InboxEnqueueVerdict::DroppedAtCap {
                mail_seq: 3,
                dropped_total: 1,
            }
        );
        assert_eq!(fence.on_consume(5), 2);
        assert_eq!(fence.unread_count(), 0);
        assert_eq!(fence.consumed_seq(), 3);
    }
}
