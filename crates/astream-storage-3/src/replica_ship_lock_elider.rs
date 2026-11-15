// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Out-of-lock `Replicated` follower shipping coordinator
//! (`Astream.Broker.TlaReplicaShipLockElider`).
//!
//! Decouples `Mutex<BrokerLog>` acquisition from synchronous follower TCP I/O:
//! 1. Under the short `BrokerLog` critical section, the leader stages `[prev_hw, staged_hw)`
//!    into an immutable byte slice and drops the mutex.
//! 2. Outside the mutex, follower shipping advances `quorum_acked_hw <= staged_hw`, so a
//!    stalled follower (`REPLICA_IO_TIMEOUT`) never blocks `Fast`/`Ordered` appends or
//!    `Fetch`/`Last` reads on `BrokerLog`.

#[cfg(clean_islands)]
#[path = "replica_ship_lock_elider_island.rs"]
mod replica_ship_lock_elider_island;
#[cfg(clean_islands)]
pub use replica_ship_lock_elider_island::{replica_quorum_clamp, replica_staged_advance};

#[cfg(not(clean_islands))]
/// Monotonically advance the leader's staged replication high-water mark.
#[must_use]
pub const fn replica_staged_advance(cur_staged: u64, cand_staged: u64) -> u64 {
    if cur_staged < cand_staged {
        cand_staged
    } else {
        cur_staged
    }
}

#[cfg(not(clean_islands))]
/// Clamp follower quorum-acknowledged watermark to `<= staged_hw`.
#[must_use]
pub const fn replica_quorum_clamp(cand_quorum: u64, staged_hw: u64) -> u64 {
    if cand_quorum < staged_hw {
        cand_quorum
    } else {
        staged_hw
    }
}

contract_fn! {
    /// True iff all staged records up to `target_offset` have reached follower quorum.
    #[must_use]
    pub const fn replica_offset_quorum_durable(target_offset: u64, quorum_acked_hw: u64) -> bool
    clauses [ensures result == (target_offset < quorum_acked_hw)]
    {
        target_offset < quorum_acked_hw
    }
}

/// Ticket returned when a batch is staged under `BrokerLog` before dropping the lock.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StagedShipTicket {
    pub batch_first_offset: u64,
    pub batch_end_offset: u64,
}

/// Out-of-lock follower shipping watermark tracker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReplicaShipLockElider {
    staged_hw: u64,
    quorum_acked_hw: u64,
    in_flight_shippers: u64,
    max_shippers: u64,
}

impl ReplicaShipLockElider {
    #[must_use]
    pub const fn new(base_offset: u64, max_shippers: u64) -> Self {
        let cap = if max_shippers == 0 { 8 } else { max_shippers };
        Self {
            staged_hw: base_offset,
            quorum_acked_hw: base_offset,
            in_flight_shippers: 0,
            max_shippers: cap,
        }
    }

    #[must_use]
    pub const fn staged_hw(&self) -> u64 {
        self.staged_hw
    }

    #[must_use]
    pub const fn quorum_acked_hw(&self) -> u64 {
        self.quorum_acked_hw
    }

    /// Stage `count` newly appended records under the short lock and return a shipping ticket.
    pub fn stage_batch(&mut self, count: u64) -> Option<StagedShipTicket> {
        if count == 0 || self.in_flight_shippers >= self.max_shippers {
            return None;
        }
        let first = self.staged_hw;
        let cand_end = first.saturating_add(count);
        self.staged_hw = replica_staged_advance(self.staged_hw, cand_end);
        self.quorum_acked_hw = replica_quorum_clamp(self.quorum_acked_hw, self.staged_hw);
        self.in_flight_shippers = self.in_flight_shippers.saturating_add(1);
        Some(StagedShipTicket {
            batch_first_offset: first,
            batch_end_offset: self.staged_hw,
        })
    }

    /// Record out-of-lock follower quorum ack up to `follower_hw`.
    pub fn complete_ship(&mut self, follower_hw: u64) -> u64 {
        self.in_flight_shippers = self.in_flight_shippers.saturating_sub(1);
        let monotonic_ack = replica_staged_advance(self.quorum_acked_hw, follower_hw);
        self.quorum_acked_hw = replica_quorum_clamp(monotonic_ack, self.staged_hw);
        self.quorum_acked_hw
    }

    /// True iff `offset` is durably acknowledged by the follower quorum.
    #[must_use]
    pub const fn is_durable(&self, offset: u64) -> bool {
        replica_offset_quorum_durable(offset, self.quorum_acked_hw)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stages_under_short_lock_and_clamps_quorum_ack_to_staged_hw() {
        let mut elider = ReplicaShipLockElider::new(10, 4);
        let t1 = elider.stage_batch(5).unwrap();
        assert_eq!(t1.batch_first_offset, 10);
        assert_eq!(t1.batch_end_offset, 15);
        assert!(!elider.is_durable(14));

        // Follower reporting bogus hw > staged_hw (e.g. 99) is clamped to staged_hw (15):
        assert_eq!(elider.complete_ship(99), 15);
        assert!(elider.is_durable(14));
        assert!(!elider.is_durable(15));
    }
}
