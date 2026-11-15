// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Endpoint dual-bound `outbox` (`128` rows AND `4 MiB`), `Bytes`-framed peek, & idempotent
//! `outbox sent` retirement (`docs/DESIGN-aterm-fabric.md` §11.2 deviations 1–4, 8, 9 lines 3560–3600;
//! `Astream.Host.TlaDualBoundOutboxPeekRetire`).
//!
//! Protects outbound delivery without ever silently dropping a post told `OK`:
//! - `post` refuses `Scope::Edge` (`RefusedEdgeScope`), and refuses at the door with `ERR outbox full`
//!   when either `queued_rows >= 128` OR `queued_bytes + body_len > 4 MiB` (`4_194_304` B), NEVER
//!   evicting an accepted outbound message!
//! - When `wants_wait && !bridge_attached`, the post IS queued in the outbox (listed in `inbox`),
//!   and immediately answers `ERR fabric absent id=<id>` rather than hanging to timeout (§11.2 dev 9)!
//! - `outbox` (`BridgeOnly`) is a `Bytes`-framed PEEK that moves no watermark and drops nothing, so a
//!   bridge killed mid-publish re-peeks and republishes under the same `(producer_id, producer_seq)`.
//! - `outbox sent <sid> <id> off=<n|->` (`BridgeOnly`) retires the retained body and wakes `--wait`
//!   (`off=-` wakes `ERR undeliverable`), idempotently (`OK` on duplicate retire, no second event!).

#[cfg(clean_islands)]
#[path = "dual_bound_outbox_peek_retire_island.rs"]
mod dual_bound_outbox_peek_retire_island;
#[cfg(clean_islands)]
pub use dual_bound_outbox_peek_retire_island::{
    outbox_bytes_clamp_b136, outbox_post_id_advance_b136,
};

/// Maximum queued un-retired outbound posts (`128` rows).
pub const OUTBOX_MAX_ROWS: u64 = 128;

/// Maximum retained outbound bytes across queued posts (`4 MiB`).
pub const OUTBOX_MAX_BYTES: u64 = 4_194_304;

/// Maximum single outbound `post` payload (`256 KiB`).
pub const SINGLE_POST_MAX_BYTES: u64 = 262_144;

#[cfg(not(clean_islands))]
/// Clamp retained outbox bytes to `bytes_cap` (`OUTBOX_MAX_BYTES`).
#[must_use]
pub const fn outbox_bytes_clamp_b136(cand_bytes: u64, bytes_cap: u64) -> u64 {
    if cand_bytes < bytes_cap {
        cand_bytes
    } else {
        bytes_cap
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance allocated outbound post ID.
#[must_use]
pub const fn outbox_post_id_advance_b136(cur_id: u64, cand_id: u64) -> u64 {
    if cur_id < cand_id {
        cand_id
    } else {
        cur_id
    }
}

contract_fn! {
    /// True iff `!is_edge_scope && body_len <= single_max && queued_rows < max_rows && next_bytes <= max_bytes`.
    #[must_use]
    pub const fn outbox_post_admissible_b136(
        is_edge_scope: bool,
        body_len: u64,
        single_max: u64,
        queued_rows: u64,
        max_rows: u64,
        next_bytes: u64,
        max_bytes: u64,
    ) -> bool
    clauses [ensures result == (!is_edge_scope && body_len <= single_max && queued_rows < max_rows && next_bytes <= max_bytes)]
    {
        !is_edge_scope
            && body_len <= single_max
            && queued_rows < max_rows
            && next_bytes <= max_bytes
    }
}

/// Endpoint response to an outbound `post` request.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum OutboxEnqueueVerdict {
    /// Queued; if `park_caller == true`, caller waits for `outbox sent`!
    Queued { post_id: u64, park_caller: bool },
    /// Queued in outbox, but `post --wait` with no attached bridge answers `ERR fabric absent id=<n>` at once!
    QueuedErrFabricAbsent { post_id: u64 },
    /// Refused: `Scope::Edge` cannot speak as session S (§11.2 line 3351).
    RefusedEdgeScope,
    /// Refused: `body_len > 256 KiB`.
    RefusedBodyTooLarge,
    /// Refused at door: `ERR outbox full` (never evicts an already-accepted post!).
    RefusedOutboxFull,
}

/// Outcome of `outbox sent <sid> <id> off=<n|->` (`BridgeOnly`).
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum OutboxRetireVerdict {
    /// Landed at `bus_offset`: body freed, parked `--wait` released with `OK <id> off=<n>`.
    LandedAtOffset(u64),
    /// Retired `off=-`: body freed, parked `--wait` woken with `ERR undeliverable`.
    RetiredUndeliverable,
    /// Already retired earlier: idempotent `OK` with zero duplicate events!
    IdempotentNoop,
}

/// Endpoint dual-bound outbox queue state machine.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct DualBoundOutboxQueue {
    max_rows: u64,
    max_bytes: u64,
    queued_rows: u64,
    queued_bytes: u64,
    next_post_id: u64,
    highest_retired_id: u64,
}

impl DualBoundOutboxQueue {
    #[must_use]
    pub const fn new(max_rows: u64, max_bytes: u64) -> Self {
        let r_cap = if max_rows == 0 {
            OUTBOX_MAX_ROWS
        } else {
            max_rows
        };
        let b_cap = if max_bytes == 0 {
            OUTBOX_MAX_BYTES
        } else {
            max_bytes
        };
        Self {
            max_rows: r_cap,
            max_bytes: b_cap,
            queued_rows: 0,
            queued_bytes: 0,
            next_post_id: 0,
            highest_retired_id: 0,
        }
    }

    #[must_use]
    pub const fn queued_rows(&self) -> u64 {
        self.queued_rows
    }

    #[must_use]
    pub const fn queued_bytes(&self) -> u64 {
        outbox_bytes_clamp_b136(self.queued_bytes, self.max_bytes)
    }

    /// `BridgeOnly` `outbox` peek: returns `(queued_rows, queued_bytes)` without moving any watermark!
    #[must_use]
    pub const fn peek_outbox(&self) -> (u64, u64) {
        (self.queued_rows, self.queued_bytes())
    }

    /// Attempt to enqueue an outbound `post`.
    pub fn enqueue_post(
        &mut self,
        is_edge_scope: bool,
        body_len: u64,
        wants_wait: bool,
        bridge_attached: bool,
    ) -> OutboxEnqueueVerdict {
        if is_edge_scope {
            return OutboxEnqueueVerdict::RefusedEdgeScope;
        }
        if body_len > SINGLE_POST_MAX_BYTES {
            return OutboxEnqueueVerdict::RefusedBodyTooLarge;
        }
        let next_bytes = self.queued_bytes.saturating_add(body_len);
        if !outbox_post_admissible_b136(
            false,
            body_len,
            SINGLE_POST_MAX_BYTES,
            self.queued_rows,
            self.max_rows,
            next_bytes,
            self.max_bytes,
        ) {
            return OutboxEnqueueVerdict::RefusedOutboxFull;
        }
        let id =
            outbox_post_id_advance_b136(self.next_post_id, self.next_post_id.saturating_add(1));
        self.next_post_id = id;
        self.queued_rows = self.queued_rows.saturating_add(1);
        self.queued_bytes = outbox_bytes_clamp_b136(next_bytes, self.max_bytes);
        if wants_wait && !bridge_attached {
            OutboxEnqueueVerdict::QueuedErrFabricAbsent { post_id: id }
        } else {
            OutboxEnqueueVerdict::Queued {
                post_id: id,
                park_caller: wants_wait,
            }
        }
    }

    /// `BridgeOnly` `outbox sent <sid> <post_id> off=<bus_offset|None>`.
    pub fn retire_sent(
        &mut self,
        post_id: u64,
        retained_body_len: u64,
        bus_offset: Option<u64>,
    ) -> OutboxRetireVerdict {
        if post_id == 0 || post_id <= self.highest_retired_id || self.queued_rows == 0 {
            return OutboxRetireVerdict::IdempotentNoop;
        }
        self.highest_retired_id = outbox_post_id_advance_b136(self.highest_retired_id, post_id);
        self.queued_rows = self.queued_rows.saturating_sub(1);
        self.queued_bytes = self.queued_bytes.saturating_sub(retained_body_len);
        match bus_offset {
            Some(off) => OutboxRetireVerdict::LandedAtOffset(off),
            None => OutboxRetireVerdict::RetiredUndeliverable,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dual_bounds_peek_idempotent_retire_and_fabric_absent_wait_hold() {
        let mut q = DualBoundOutboxQueue::new(2, 1_024);
        assert_eq!(
            q.enqueue_post(true, 10, false, true),
            OutboxEnqueueVerdict::RefusedEdgeScope
        );
        // `post --wait` while bridge is absent queues post #1 and answers `ERR fabric absent id=1`!
        assert_eq!(
            q.enqueue_post(false, 600, true, false),
            OutboxEnqueueVerdict::QueuedErrFabricAbsent { post_id: 1 }
        );
        // Byte cap (`600 + 500 > 1_024`) refuses at door even though row count (`1 < 2`) has room!
        assert_eq!(
            q.enqueue_post(false, 500, false, true),
            OutboxEnqueueVerdict::RefusedOutboxFull
        );
        // `peek_outbox` leaves both rows and bytes intact across crashed bridge retries:
        assert_eq!(q.peek_outbox(), (1, 600));
        assert_eq!(q.peek_outbox(), (1, 600));
        // Retire `off=-` frees body bytes; duplicate retire is `IdempotentNoop`!
        assert_eq!(
            q.retire_sent(1, 600, None),
            OutboxRetireVerdict::RetiredUndeliverable
        );
        assert_eq!(
            q.retire_sent(1, 600, None),
            OutboxRetireVerdict::IdempotentNoop
        );
        assert_eq!(q.peek_outbox(), (0, 0));
    }
}
