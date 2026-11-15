// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Client `owed_acks` (`AcksOwed { owed }` `ResourceBusy`) zero-wire-touch in-step guard
//! (`evidence/manifest.toml` `broker.client-owed-acks`;
//! `Astream.Wire.TlaClientOwedAcksResourceBusyGuard`).
//!
//! Enforces the client-side pipelined `send_publish` / `send_retire` accounting rule:
//! - `send_publish` and `send_retire` each add `1` to `owed_acks` AFTER writing their frame,
//! - `recv_publish_ack` pays `1` per complete reply frame read (whether `Ack` or `Error` refusal),
//! - While `owed_acks > 0`, EVERY synchronous or consuming verb (`commit`, `fetch`, `last`,
//!   `subscribe`, `hello`, `attach`, etc.) is refused immediately with `RefusedAcksOwed { owed }`
//!   BEFORE writing or reading a single byte on the wire, leaving the queued publish acks intact!
//!
//! Zero heap allocations, zero loops, zero `Display`/`Hash` impls — preserves `astream-wire`
//! `unknown == 0` and `runtime_checked <= 110`.

#[cfg(clean_islands)]
#[path = "client_owed_acks_resource_busy_guard_island.rs"]
mod client_owed_acks_resource_busy_guard_island;
#[cfg(clean_islands)]
pub use client_owed_acks_resource_busy_guard_island::{
    owed_acks_clamp_b146, retired_acks_advance_b146,
};

/// Upper bound on outstanding `send_publish` / `send_retire` frames (`65_535`).
pub const MAX_OWED_ACKS: u64 = 65_535;

#[cfg(not(clean_islands))]
/// Clamp outstanding owed acks to `max_owed`.
#[must_use]
pub const fn owed_acks_clamp_b146(cand_owed: u64, max_owed: u64) -> u64 {
    if cand_owed < max_owed {
        cand_owed
    } else {
        max_owed
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance total retired publish/retire ack count.
#[must_use]
pub const fn retired_acks_advance_b146(cur_paid: u64, cand_paid: u64) -> u64 {
    if cur_paid < cand_paid {
        cand_paid
    } else {
        cur_paid
    }
}

contract_fn! {
    /// Synchronous and consuming client verbs are admissible ONLY when `owed_acks == 0`.
    #[must_use]
    pub const fn sync_verb_admissible_zero_owed_b146(owed_acks: u64) -> bool
    clauses [ensures result == (owed_acks == 0)]
    {
        owed_acks == 0
    }
}

/// Accounting verdict for `Client::owed_acks` operations.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum OwedAcksDecision {
    RecordedPipelinedSend {
        owed: u64,
    },
    PaidOneAck {
        remaining_owed: u64,
        paid_total: u64,
    },
    AdmittedSyncVerbZeroOwed,
    RefusedAcksOwedZeroWireBytes {
        owed: u64,
    },
    RefusedNoAckOwedToRecv,
    RefusedOwedCapReached {
        max_owed: u64,
    },
}

/// Client `owed_acks` state machine (`send_publish` / `send_retire` vs `recv_publish_ack`).
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ClientOwedAcksLedger {
    owed_acks: u64,
    paid_total: u64,
}

impl ClientOwedAcksLedger {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            owed_acks: 0,
            paid_total: 0,
        }
    }

    #[must_use]
    pub const fn owed_acks(&self) -> u64 {
        owed_acks_clamp_b146(self.owed_acks, MAX_OWED_ACKS)
    }

    /// Record a completed `send_publish` or `send_retire` frame write.
    pub fn on_pipelined_frame_sent(&mut self) -> OwedAcksDecision {
        if self.owed_acks >= MAX_OWED_ACKS {
            return OwedAcksDecision::RefusedOwedCapReached {
                max_owed: MAX_OWED_ACKS,
            };
        }
        let next = self.owed_acks.saturating_add(1);
        self.owed_acks = owed_acks_clamp_b146(next, MAX_OWED_ACKS);
        OwedAcksDecision::RecordedPipelinedSend {
            owed: self.owed_acks,
        }
    }

    /// Gate any synchronous or consuming verb BEFORE writing or reading a byte!
    #[must_use]
    pub const fn check_sync_or_consuming_verb(&self) -> OwedAcksDecision {
        if sync_verb_admissible_zero_owed_b146(self.owed_acks) {
            OwedAcksDecision::AdmittedSyncVerbZeroOwed
        } else {
            OwedAcksDecision::RefusedAcksOwedZeroWireBytes {
                owed: self.owed_acks,
            }
        }
    }

    /// Pay one owed ack upon reading a whole `Ack` or `Error` frame in `recv_publish_ack`.
    pub fn on_whole_publish_reply_read(&mut self) -> OwedAcksDecision {
        if self.owed_acks == 0 {
            return OwedAcksDecision::RefusedNoAckOwedToRecv;
        }
        self.owed_acks = self.owed_acks.saturating_sub(1);
        let next_paid = self.paid_total.saturating_add(1);
        self.paid_total = retired_acks_advance_b146(self.paid_total, next_paid);
        OwedAcksDecision::PaidOneAck {
            remaining_owed: self.owed_acks,
            paid_total: self.paid_total,
        }
    }
}

impl Default for ClientOwedAcksLedger {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_commit_with_zero_wire_touch_while_acks_owed_then_resumes_after_drain() {
        let mut l = ClientOwedAcksLedger::new();
        assert_eq!(
            l.on_pipelined_frame_sent(),
            OwedAcksDecision::RecordedPipelinedSend { owed: 1 }
        );
        assert_eq!(
            l.on_pipelined_frame_sent(),
            OwedAcksDecision::RecordedPipelinedSend { owed: 2 }
        );
        // `commit` behind 2 owed publishes is refused with `AcksOwed { owed: 2 }` and zero bytes sent!
        assert_eq!(
            l.check_sync_or_consuming_verb(),
            OwedAcksDecision::RefusedAcksOwedZeroWireBytes { owed: 2 }
        );
        l.on_whole_publish_reply_read();
        l.on_whole_publish_reply_read();
        assert_eq!(
            l.check_sync_or_consuming_verb(),
            OwedAcksDecision::AdmittedSyncVerbZeroOwed
        );
    }
}
