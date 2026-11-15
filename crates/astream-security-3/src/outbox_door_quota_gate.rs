// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Endpoint outbound `outbox` / `outbox sent` dual-quota door gate (`128` rows AND `4 MiB`)
//! (`docs/DESIGN-aterm-fabric.md` §11.2 deviations 1–5, §15 line 4035;
//! `Astream.Broker.TlaOutboxDoorQuotaGate`).
//!
//! Enforces `aterm`'s outbound plane invariants:
//! - `post` refuses AT THE DOOR (never drops queued items!) whenever adding the row would exceed
//!   either `MAX_OUTBOX_ROWS` (`128`) or `MAX_OUTBOX_BYTES` (`4 MiB`),
//! - `outbox` peeks queued rows without advancing `acked_outbox_id`, and ONLY `Scope::Bridge` may
//!   invoke `outbox` or `outbox sent`,
//! - `outbox sent <sid> <id> off=<n|->` monotonically advances `acked_outbox_id` and releases the
//!   completed row's count and byte budget.

#[cfg(clean_islands)]
#[path = "outbox_door_quota_gate_island.rs"]
mod outbox_door_quota_gate_island;
#[cfg(clean_islands)]
pub use outbox_door_quota_gate_island::{
    outbox_acked_id_advance_b125, outbox_bytes_clamp_b125, outbox_rows_clamp_b125,
};

#[cfg(not(clean_islands))]
/// Clamp queued outbox row count to `max_rows` (`128`).
#[must_use]
pub const fn outbox_rows_clamp_b125(cand_rows: u64, max_rows: u64) -> u64 {
    if cand_rows < max_rows {
        cand_rows
    } else {
        max_rows
    }
}

#[cfg(not(clean_islands))]
/// Clamp queued outbox byte total to `max_bytes` (`4 MiB`).
#[must_use]
pub const fn outbox_bytes_clamp_b125(cand_bytes: u64, max_bytes: u64) -> u64 {
    if cand_bytes < max_bytes {
        cand_bytes
    } else {
        max_bytes
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `acked_outbox_id`.
#[must_use]
pub const fn outbox_acked_id_advance_b125(cur_id: u64, cand_id: u64) -> u64 {
    if cur_id < cand_id {
        cand_id
    } else {
        cur_id
    }
}

contract_fn! {
    /// True iff `next_rows <= max_rows && next_bytes <= max_bytes` (admissible at the outbox door).
    #[must_use]
    pub const fn outbox_door_fits_b125(
        next_rows: u64,
        max_rows: u64,
        next_bytes: u64,
        max_bytes: u64,
    ) -> bool
    clauses [ensures result == (next_rows <= max_rows && next_bytes <= max_bytes)]
    {
        next_rows <= max_rows && next_bytes <= max_bytes
    }
}

pub const DEFAULT_MAX_OUTBOX_ROWS: u64 = 128;
pub const DEFAULT_MAX_OUTBOX_BYTES: u64 = 4 * 1024 * 1024;

/// Caller scope on `aterm`'s control socket (`Scope::Bridge` vs regular session/edge caller).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OutboxCallerScope {
    BridgeOnly,
    SessionOrOwner,
}

/// Outcome of a `post` enqueue or `outbox` / `outbox sent` control call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OutboxDoorOutcome {
    Enqueued {
        outbox_id: u64,
        queued_rows: u64,
        queued_bytes: u64,
    },
    RefusedDoorRowLimit {
        queued_rows: u64,
        max_rows: u64,
    },
    RefusedDoorByteLimit {
        queued_bytes: u64,
        attempted_bytes: u64,
        max_bytes: u64,
    },
    RefusedBridgeOnlyScope,
    Peeked {
        queued_rows: u64,
        queued_bytes: u64,
        acked_outbox_id: u64,
    },
    MarkedSent {
        acked_outbox_id: u64,
        queued_rows: u64,
        queued_bytes: u64,
    },
}

/// Dual-quota (`rows <= max_rows`, `bytes <= max_bytes`) outbound door gate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OutboxDoorQuotaGate {
    max_rows: u64,
    max_bytes: u64,
    queued_rows: u64,
    queued_bytes: u64,
    next_outbox_id: u64,
    acked_outbox_id: u64,
}

impl OutboxDoorQuotaGate {
    #[must_use]
    pub const fn new(max_rows: u64, max_bytes: u64) -> Self {
        Self {
            max_rows,
            max_bytes,
            queued_rows: 0,
            queued_bytes: 0,
            next_outbox_id: 0,
            acked_outbox_id: 0,
        }
    }

    /// Enqueue an outbound `post` of `payload_bytes`, refusing at the door if either quota overflows.
    pub fn try_enqueue_post(&mut self, payload_bytes: u64) -> OutboxDoorOutcome {
        let Some(cand_rows) = self.queued_rows.checked_add(1) else {
            return OutboxDoorOutcome::RefusedDoorRowLimit {
                queued_rows: self.queued_rows,
                max_rows: self.max_rows,
            };
        };
        if cand_rows > self.max_rows {
            return OutboxDoorOutcome::RefusedDoorRowLimit {
                queued_rows: self.queued_rows,
                max_rows: self.max_rows,
            };
        }
        let Some(cand_bytes) = self.queued_bytes.checked_add(payload_bytes) else {
            return OutboxDoorOutcome::RefusedDoorByteLimit {
                queued_bytes: self.queued_bytes,
                attempted_bytes: payload_bytes,
                max_bytes: self.max_bytes,
            };
        };
        if !outbox_door_fits_b125(cand_rows, self.max_rows, cand_bytes, self.max_bytes) {
            return OutboxDoorOutcome::RefusedDoorByteLimit {
                queued_bytes: self.queued_bytes,
                attempted_bytes: payload_bytes,
                max_bytes: self.max_bytes,
            };
        }
        self.queued_rows = outbox_rows_clamp_b125(cand_rows, self.max_rows);
        self.queued_bytes = outbox_bytes_clamp_b125(cand_bytes, self.max_bytes);
        self.next_outbox_id = self.next_outbox_id.saturating_add(1);
        OutboxDoorOutcome::Enqueued {
            outbox_id: self.next_outbox_id,
            queued_rows: self.queued_rows,
            queued_bytes: self.queued_bytes,
        }
    }

    /// `outbox` peek (`BridgeOnly`): reads queue metrics without advancing `acked_outbox_id`.
    #[must_use]
    pub const fn peek_outbox(&self, scope: OutboxCallerScope) -> OutboxDoorOutcome {
        if !matches!(scope, OutboxCallerScope::BridgeOnly) {
            return OutboxDoorOutcome::RefusedBridgeOnlyScope;
        }
        OutboxDoorOutcome::Peeked {
            queued_rows: self.queued_rows,
            queued_bytes: self.queued_bytes,
            acked_outbox_id: self.acked_outbox_id,
        }
    }

    /// `outbox sent <sid> <id> off=<n|->` (`BridgeOnly`): acknowledges `outbox_id` and frees budget.
    pub fn mark_sent(
        &mut self,
        scope: OutboxCallerScope,
        outbox_id: u64,
        released_bytes: u64,
    ) -> OutboxDoorOutcome {
        if !matches!(scope, OutboxCallerScope::BridgeOnly) {
            return OutboxDoorOutcome::RefusedBridgeOnlyScope;
        }
        if outbox_id > self.acked_outbox_id && outbox_id <= self.next_outbox_id {
            self.acked_outbox_id = outbox_acked_id_advance_b125(self.acked_outbox_id, outbox_id);
            self.queued_rows = self.queued_rows.saturating_sub(1);
            self.queued_bytes = self.queued_bytes.saturating_sub(released_bytes);
        }
        OutboxDoorOutcome::MarkedSent {
            acked_outbox_id: self.acked_outbox_id,
            queued_rows: self.queued_rows,
            queued_bytes: self.queued_bytes,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_at_the_door_on_rows_or_bytes_and_enforces_bridge_only_peek_and_sent() {
        let mut gate = OutboxDoorQuotaGate::new(2, 1_000);

        assert_eq!(
            gate.try_enqueue_post(600),
            OutboxDoorOutcome::Enqueued {
                outbox_id: 1,
                queued_rows: 1,
                queued_bytes: 600,
            }
        );
        // Exceeds 1_000-byte door limit -> refused without dropping row 1!
        assert_eq!(
            gate.try_enqueue_post(500),
            OutboxDoorOutcome::RefusedDoorByteLimit {
                queued_bytes: 600,
                attempted_bytes: 500,
                max_bytes: 1_000,
            }
        );
        assert_eq!(
            gate.try_enqueue_post(300),
            OutboxDoorOutcome::Enqueued {
                outbox_id: 2,
                queued_rows: 2,
                queued_bytes: 900,
            }
        );
        // Exceeds 2-row door limit!
        assert_eq!(
            gate.try_enqueue_post(10),
            OutboxDoorOutcome::RefusedDoorRowLimit {
                queued_rows: 2,
                max_rows: 2,
            }
        );

        // Non-bridge scope refused; bridge peek leaves acked_outbox_id untouched.
        assert_eq!(
            gate.peek_outbox(OutboxCallerScope::SessionOrOwner),
            OutboxDoorOutcome::RefusedBridgeOnlyScope
        );
        assert_eq!(
            gate.peek_outbox(OutboxCallerScope::BridgeOnly),
            OutboxDoorOutcome::Peeked {
                queued_rows: 2,
                queued_bytes: 900,
                acked_outbox_id: 0,
            }
        );

        // Bridge `outbox sent` releases row 1's 600 bytes so a new post succeeds.
        assert_eq!(
            gate.mark_sent(OutboxCallerScope::BridgeOnly, 1, 600),
            OutboxDoorOutcome::MarkedSent {
                acked_outbox_id: 1,
                queued_rows: 1,
                queued_bytes: 300,
            }
        );
        assert_eq!(
            gate.try_enqueue_post(500),
            OutboxDoorOutcome::Enqueued {
                outbox_id: 3,
                queued_rows: 2,
                queued_bytes: 800,
            }
        );
    }
}
