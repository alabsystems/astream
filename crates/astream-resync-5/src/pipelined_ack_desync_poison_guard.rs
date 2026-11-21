// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pipelined `Ack` desync poisoning & bounded peer `Fetch`/`Last` row cap
//! (`Astream.Wire.TlaPipelinedAckDesyncPoisonGuard`).
//!
//! Prevents both client-protocol hazards:
//! 1. If `publish_pipelined` aborts mid-batch with unread in-flight acks (`unread_inflight_acks > 0`),
//!    the request/reply stream is irreversibly marked `desynced` so a subsequent `publish` NEVER
//!    consumes an earlier record's stale `Ack(offset)` as its own!
//! 2. `fetch` and `last` enforce `MAX_PEER_RESPONSE_ROWS` (`65_536`) before buffering rows from an
//!    untrusted or misbehaving peer.
//!
//! Zero heap allocations, zero loops, zero `Display`/`Hash` impls — preserves `astream-wire`
//! `unknown == 0` and `runtime_checked <= 110`.

#[cfg(clean_islands)]
#[path = "pipelined_ack_desync_poison_guard_island.rs"]
mod pipelined_ack_desync_poison_guard_island;
#[cfg(clean_islands)]
pub use pipelined_ack_desync_poison_guard_island::{
    peer_row_batch_clamp_b141, pipelined_inflight_clamp_b141,
};

/// Maximum pipelined publish frames in flight on a single client connection (`4_096`).
pub const MAX_PIPELINED_INFLIGHT: u64 = 4_096;
/// Maximum `Fetch`/`Last` response rows buffered from a peer in one reply (`65_536`).
pub const MAX_PEER_RESPONSE_ROWS: u64 = 65_536;

#[cfg(not(clean_islands))]
/// Clamp in-flight pipelined publish count to `max_inflight`.
#[must_use]
pub const fn pipelined_inflight_clamp_b141(cand_inflight: u64, max_inflight: u64) -> u64 {
    if cand_inflight < max_inflight {
        cand_inflight
    } else {
        max_inflight
    }
}

#[cfg(not(clean_islands))]
/// Clamp peer-supplied `Fetch`/`Last` row count to `max_rows`.
#[must_use]
pub const fn peer_row_batch_clamp_b141(cand_rows: u64, max_rows: u64) -> u64 {
    if cand_rows < max_rows {
        cand_rows
    } else {
        max_rows
    }
}

contract_fn! {
    /// True iff a synchronous request may safely begin on the wire (`!desynced && unread_inflight_acks == 0`).
    #[must_use]
    pub const fn pipelined_channel_synchronized_b141(
        desynced: bool,
        unread_inflight_acks: u64,
    ) -> bool
    clauses [ensures result == (!desynced && unread_inflight_acks == 0)]
    {
        !desynced && unread_inflight_acks == 0
    }
}

/// Verdict for client request/response framing synchronization.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum PipelinedSyncVerdict {
    AdmittedBatch { inflight_acks: u64 },
    DrainedAllAcksSynchronized,
    AdmittedPeerRow { buffered_rows: u64 },
    RefusedDesyncedUnreadAcks,
    RefusedInflightBatchTooLarge { requested: u64 },
    RefusedPeerRowCapExceeded { buffered_rows: u64 },
}

/// Client-side pipelined `Ack` synchronization and response-row bound tracker.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct PipelinedChannelGuard {
    unread_inflight_acks: u64,
    buffered_peer_rows: u64,
    desynced: bool,
}

impl PipelinedChannelGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            unread_inflight_acks: 0,
            buffered_peer_rows: 0,
            desynced: false,
        }
    }

    #[must_use]
    pub const fn is_synchronized(&self) -> bool {
        pipelined_channel_synchronized_b141(self.desynced, self.unread_inflight_acks)
    }

    /// Begin a `publish` or `publish_pipelined` batch of `batch_len` frames (`>= 1`).
    pub fn begin_publish_batch(&mut self, batch_len: u64) -> PipelinedSyncVerdict {
        if !pipelined_channel_synchronized_b141(self.desynced, self.unread_inflight_acks) {
            self.desynced = true;
            return PipelinedSyncVerdict::RefusedDesyncedUnreadAcks;
        }
        if batch_len == 0 || batch_len > MAX_PIPELINED_INFLIGHT {
            return PipelinedSyncVerdict::RefusedInflightBatchTooLarge {
                requested: batch_len,
            };
        }
        self.unread_inflight_acks =
            pipelined_inflight_clamp_b141(batch_len, MAX_PIPELINED_INFLIGHT);
        PipelinedSyncVerdict::AdmittedBatch {
            inflight_acks: self.unread_inflight_acks,
        }
    }

    /// Record completion of `acks_read` out of `unread_inflight_acks`; if `acks_read < unread`,
    /// latch `desynced = true` so subsequent calls never read stale acks!
    pub fn finish_ack_drain(&mut self, acks_read: u64) -> PipelinedSyncVerdict {
        if self.desynced {
            return PipelinedSyncVerdict::RefusedDesyncedUnreadAcks;
        }
        if acks_read < self.unread_inflight_acks {
            self.unread_inflight_acks = self.unread_inflight_acks.saturating_sub(acks_read);
            self.desynced = true;
            PipelinedSyncVerdict::RefusedDesyncedUnreadAcks
        } else {
            self.unread_inflight_acks = 0;
            PipelinedSyncVerdict::DrainedAllAcksSynchronized
        }
    }

    pub const fn reset_peer_rows(&mut self) {
        self.buffered_peer_rows = 0;
    }

    /// Account one incoming `Deliver` row during a `Fetch` or `Last` query before `CaughtUp`.
    pub fn on_peer_query_row(&mut self) -> PipelinedSyncVerdict {
        if self.desynced {
            return PipelinedSyncVerdict::RefusedDesyncedUnreadAcks;
        }
        if self.buffered_peer_rows >= MAX_PEER_RESPONSE_ROWS {
            self.desynced = true;
            return PipelinedSyncVerdict::RefusedPeerRowCapExceeded {
                buffered_rows: self.buffered_peer_rows,
            };
        }
        let next = self.buffered_peer_rows.saturating_add(1);
        self.buffered_peer_rows = peer_row_batch_clamp_b141(next, MAX_PEER_RESPONSE_ROWS);
        PipelinedSyncVerdict::AdmittedPeerRow {
            buffered_rows: self.buffered_peer_rows,
        }
    }
}

impl Default for PipelinedChannelGuard {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interrupted_pipelined_batch_poisons_channel_against_stale_ack_aliasing() {
        let mut g = PipelinedChannelGuard::new();
        assert_eq!(
            g.begin_publish_batch(4),
            PipelinedSyncVerdict::AdmittedBatch { inflight_acks: 4 }
        );
        // Only 2 of 4 acks read before timeout -> channel latches `desynced`!
        assert_eq!(
            g.finish_ack_drain(2),
            PipelinedSyncVerdict::RefusedDesyncedUnreadAcks
        );
        assert!(!g.is_synchronized());
        // Next `publish` refuses instead of reading ack #3's stale offset!
        assert_eq!(
            g.begin_publish_batch(1),
            PipelinedSyncVerdict::RefusedDesyncedUnreadAcks
        );
    }
}
