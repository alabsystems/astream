// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Monotone `@self inbox` read/acknowledge watermark preventing replayed or already-processed peer
//! mail deliveries (`Astream.FabMail.TlaInboxCursorAck`).

#[cfg(clean_islands)]
#[path = "inbox_cursor_ack_island.rs"]
mod inbox_cursor_ack_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn fm_batch_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn fm_ack_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use inbox_cursor_ack_island::{fm_ack_advance, fm_batch_clamp};

/// Maximum messages drained in a single `inbox` read (`256`).
pub const MAX_INBOX_DRAIN: u64 = 256;

contract_fn! {
    /// Verified fresh-sequence predicate (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `fm_cursor_monotone_isl`.
    #[must_use]
    pub const fn fm_cursor_monotone(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct InboxAckCursor {
    acked_seq: u64,
}

impl InboxAckCursor {
    #[must_use]
    pub const fn new() -> Self {
        Self { acked_seq: 0 }
    }

    pub fn accept_seq(&mut self, msg_seq: u64, drain_count: u64) -> bool {
        let _ = fm_batch_clamp(drain_count, MAX_INBOX_DRAIN);
        let min_next = self.acked_seq.saturating_add(1);
        if fm_cursor_monotone(msg_seq, min_next) {
            self.acked_seq = fm_ack_advance(self.acked_seq, msg_seq);
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
    fn accepts_strictly_increasing_mail_sequences_and_drops_replays() {
        let mut c = InboxAckCursor::new();
        assert!(c.accept_seq(1, 1));
        assert!(c.accept_seq(4, 3));
        assert!(!c.accept_seq(4, 1));
        assert!(!c.accept_seq(2, 1));
    }
}
