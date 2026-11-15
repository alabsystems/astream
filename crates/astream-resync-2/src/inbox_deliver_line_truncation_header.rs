// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Endpoint `inbox` `Lines`-framing header (`OK <n>`), `REQUEST_LINE_MAX` `deliver` truncation,
//! & `inbox seen <id> [verdict]` receipt gate (`docs/DESIGN-aterm-fabric.md` §9.1 lines 2486–2519,
//! §11.2 deviation 6, aterm `030ba1788`, `5951bd589`;
//! `Astream.Host.TlaInboxDeliverLineTruncationHeader`).
//!
//! Models the exact framing & truncation contract at the aterm control socket:
//! - `OK <n>` MUST count EVERY row emitted (`msg_rows + post_rows`) so `Lines`-framed clients never
//!   truncate trailing `post` rows (§11.2 deviation 6),
//! - Outbound `post` accepts up to `POST_BODY_MAX = 262_144` (`256 KiB`), whereas inbound `deliver`
//!   rides a single control request line capped at `DELIVER_BODY_MAX = 65_535` (`64 KiB - 1`),
//!   preserving `true_len` in `len=` while truncating stored bytes,
//! - Inline `inbox` list preview truncates at `INLINE_PREVIEW_MAX = 512` setting `more=1` iff
//!   `true_len > inline_len`,
//! - `inbox seen <id> handled|refused|deferred` advances `seen_watermark` monotonically (never on
//!   `--peek`!) and emits `kind=ack re=<off> verdict=<word>` iff `receipts_enabled && (ask || task)`.

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
#[path = "inbox_deliver_line_truncation_header_island.rs"]
mod inbox_deliver_line_truncation_header_island;
#[cfg(clean_islands)]
pub use inbox_deliver_line_truncation_header_island::{
    deliver_body_clamp_b135, seen_watermark_advance_b135,
};

/// Maximum outbound `post` payload accepted by the endpoint (`256 KiB`).
pub const POST_BODY_MAX: u64 = 262_144;

/// Maximum inbound `deliver` body carried on a single control request line (`64 KiB - 1`).
pub const DELIVER_BODY_MAX: u64 = 65_535;

/// Inline `inbox` `msg` line preview ceiling (`512` bytes before `more=1`).
pub const INLINE_PREVIEW_MAX: u64 = 512;

#[cfg(not(clean_islands))]
/// Clamp delivered body bytes to `line_cap` (`DELIVER_BODY_MAX = 65_535`).
#[must_use]
pub const fn deliver_body_clamp_b135(cand_bytes: u64, line_cap: u64) -> u64 {
    if cand_bytes < line_cap {
        cand_bytes
    } else {
        line_cap
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `seen` message ID watermark.
#[must_use]
pub const fn seen_watermark_advance_b135(cur_seen: u64, cand_seen: u64) -> u64 {
    if cur_seen < cand_seen {
        cand_seen
    } else {
        cur_seen
    }
}

contract_fn! {
    /// True iff `receipts_enabled && has_explicit_verdict && is_ask_or_task && !is_peek`.
    #[must_use]
    pub const fn seen_emits_sender_ack_b135(
        receipts_enabled: bool,
        has_explicit_verdict: bool,
        is_ask_or_task: bool,
        is_peek: bool,
    ) -> bool
    clauses [ensures result == (receipts_enabled && has_explicit_verdict && is_ask_or_task && !is_peek)]
    {
        receipts_enabled && has_explicit_verdict && is_ask_or_task && !is_peek
    }
}

/// Optional explicit verdict word supplied to `inbox seen <id> [verdict]`.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum SeenVerdictWord {
    Handled,
    Refused,
    Deferred,
}

/// Framed `deliver` sizing & `inbox` inline preview metadata.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct DeliveredBodySizing {
    pub true_len: u64,
    pub stored_deliver_len: u64,
    pub inline_preview_len: u64,
    pub more_flag: bool,
}

/// Compute `deliver` line truncation (`65_535 B`) and `inbox` preview (`512 B`, `more=1`).
#[must_use]
pub const fn compute_delivered_sizing(sender_body_len: u64) -> DeliveredBodySizing {
    let true_len = deliver_body_clamp_b135(sender_body_len, POST_BODY_MAX);
    let stored = deliver_body_clamp_b135(true_len, DELIVER_BODY_MAX);
    let preview = deliver_body_clamp_b135(stored, INLINE_PREVIEW_MAX);
    DeliveredBodySizing {
        true_len,
        stored_deliver_len: stored,
        inline_preview_len: preview,
        more_flag: true_len > preview,
    }
}

/// Endpoint `inbox` header & `seen` receipt state machine.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct EndpointInboxHeaderState {
    receipts_enabled: bool,
    seen_watermark: u64,
    bus_head: u64,
    unread_msg_rows: u64,
    pending_post_rows: u64,
}

impl EndpointInboxHeaderState {
    #[must_use]
    pub const fn new(receipts_enabled: bool, initial_seen: u64) -> Self {
        Self {
            receipts_enabled,
            seen_watermark: initial_seen,
            bus_head: 0,
            unread_msg_rows: 0,
            pending_post_rows: 0,
        }
    }

    /// Exact `<n>` in `OK <n> hold= ...` (`Lines` framing counts BOTH `msg` and `post` rows!).
    #[must_use]
    pub const fn header_line_count(&self) -> u64 {
        self.unread_msg_rows.saturating_add(self.pending_post_rows)
    }

    #[must_use]
    pub const fn seen_watermark(&self) -> u64 {
        self.seen_watermark
    }

    pub fn set_counts(&mut self, unread_msgs: u64, pending_posts: u64, bus_head: u64) {
        self.unread_msg_rows = unread_msgs;
        self.pending_post_rows = pending_posts;
        if bus_head > self.bus_head {
            self.bus_head = bus_head;
        }
    }

    /// Drain or `--peek` the inbox up to `max_msg_id`; returns `(header_n, new_seen_watermark)`.
    pub fn read_inbox(&mut self, max_msg_id: u64, is_peek: bool) -> (u64, u64) {
        let n = self.header_line_count();
        if !is_peek {
            self.seen_watermark = seen_watermark_advance_b135(self.seen_watermark, max_msg_id);
        }
        (n, self.seen_watermark)
    }

    /// Execute `inbox seen <msg_id> [verdict]`; returns `Some((re_offset, verdict))` when an `ack` is owed!
    #[allow(clippy::manual_map)]
    pub fn mark_seen_with_verdict(
        &mut self,
        msg_id: u64,
        msg_bus_offset: u64,
        is_ask_or_task: bool,
        verdict: Option<SeenVerdictWord>,
    ) -> Option<(u64, SeenVerdictWord)> {
        self.seen_watermark = seen_watermark_advance_b135(self.seen_watermark, msg_id);
        if self.unread_msg_rows > 0 {
            self.unread_msg_rows = self.unread_msg_rows.saturating_sub(1);
        }
        if seen_emits_sender_ack_b135(
            self.receipts_enabled,
            verdict.is_some(),
            is_ask_or_task,
            false,
        ) {
            match verdict {
                Some(v) => Some((msg_bus_offset, v)),
                None => None,
            }
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn header_counts_msg_plus_post_rows_and_deliver_truncates_at_64k_minus_1() {
        let mut s = EndpointInboxHeaderState::new(true, 40);
        s.set_counts(2, 1, 90_340);
        // §9.1 example: 2 `msg` rows + 1 `post` row -> `OK 3`, NOT `OK 2`!
        let (hdr_n, seen_peek) = s.read_inbox(42, true);
        assert_eq!(hdr_n, 3);
        assert_eq!(seen_peek, 40);

        // `inbox seen 42 handled` on a `task` advances `seen` to 42 and emits `ack`!
        assert_eq!(
            s.mark_seen_with_verdict(42, 90_340, true, Some(SeenVerdictWord::Handled)),
            Some((90_340, SeenVerdictWord::Handled))
        );
        assert_eq!(s.seen_watermark(), 42);
        // On a `note` (`is_ask_or_task == false`), no `ack` is published:
        assert_eq!(
            s.mark_seen_with_verdict(43, 90_350, false, Some(SeenVerdictWord::Handled)),
            None
        );

        // 100 KiB post -> `true_len = 102_400`, `stored_deliver_len = 65_535`, `preview = 512`, `more = true`!
        let sz = compute_delivered_sizing(102_400);
        assert_eq!(sz.true_len, 102_400);
        assert_eq!(sz.stored_deliver_len, DELIVER_BODY_MAX);
        assert_eq!(sz.inline_preview_len, INLINE_PREVIEW_MAX);
        assert!(sz.more_flag);
    }
}
