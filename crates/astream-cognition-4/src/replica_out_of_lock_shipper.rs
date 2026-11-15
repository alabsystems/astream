// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Out-of-lock `Replicated` tier follower shipping coordinator
//! (`Astream.Broker.TlaReplicaOutOfLockShipper`).
//!
//! Decouples follower replication I/O from `Mutex<BrokerLog>`: producers advance `local_append_hw`
//! under a brief lock, while the replication worker snapshots `[durable_quorum_hw..local_append_hw]`
//! outside the lock, bounds in-flight bytes to `max_inflight_bytes`, and advances
//! `durable_quorum_hw <= local_append_hw` monotonically on follower ACKs or trips a circuit breaker
//! on `REPLICA_IO_TIMEOUT` without stalling local non-replicated lanes.

#[cfg(clean_islands)]
#[path = "replica_out_of_lock_shipper_island.rs"]
mod replica_out_of_lock_shipper_island;
#[cfg(clean_islands)]
pub use replica_out_of_lock_shipper_island::{
    replica_inflight_clamp_b115, replica_quorum_hw_advance_b115,
};

#[cfg(not(clean_islands))]
/// Clamp in-flight follower shipping byte budget to `max_inflight`.
#[must_use]
pub const fn replica_inflight_clamp_b115(cand_bytes: u64, max_inflight: u64) -> u64 {
    if cand_bytes < max_inflight {
        cand_bytes
    } else {
        max_inflight
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `durable_quorum_hw`.
#[must_use]
pub const fn replica_quorum_hw_advance_b115(cur_quorum_hw: u64, cand_quorum_hw: u64) -> u64 {
    if cur_quorum_hw < cand_quorum_hw {
        cand_quorum_hw
    } else {
        cur_quorum_hw
    }
}

contract_fn! {
    /// True iff `ack_hw` does not exceed `local_append_hw`.
    #[must_use]
    pub const fn replica_ack_within_local_hw_b115(ack_hw: u64, local_append_hw: u64) -> bool
    clauses [ensures result == (ack_hw <= local_append_hw)]
    {
        ack_hw <= local_append_hw
    }
}

/// Out-of-lock shipping slice planned for a follower round-trip.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReplicaShipPlan {
    CaughtUp {
        quorum_hw: u64,
    },
    ShipBatch {
        start_offset: u64,
        end_offset: u64,
        batch_bytes: u64,
    },
    CircuitOpenDegraded {
        consecutive_timeouts: u32,
    },
}

/// Coordinator tracking `local_append_hw`, `durable_quorum_hw`, and follower circuit health.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReplicaOutOfLockShipper {
    local_append_hw: u64,
    durable_quorum_hw: u64,
    inflight_bytes: u64,
    max_inflight_bytes: u64,
    consecutive_timeouts: u32,
    max_timeouts_before_open: u32,
}

impl ReplicaOutOfLockShipper {
    #[must_use]
    pub const fn new(max_inflight_bytes: u64, max_timeouts_before_open: u32) -> Self {
        let cap = if max_inflight_bytes == 0 {
            1024 * 1024
        } else {
            max_inflight_bytes
        };
        let tcap = if max_timeouts_before_open == 0 {
            3
        } else {
            max_timeouts_before_open
        };
        Self {
            local_append_hw: 0,
            durable_quorum_hw: 0,
            inflight_bytes: 0,
            max_inflight_bytes: cap,
            consecutive_timeouts: 0,
            max_timeouts_before_open: tcap,
        }
    }

    #[must_use]
    pub const fn durable_quorum_hw(&self) -> u64 {
        self.durable_quorum_hw
    }

    #[must_use]
    pub const fn local_append_hw(&self) -> u64 {
        self.local_append_hw
    }

    /// Record a new local WAL append high-water mark (under brief lock).
    pub fn observe_local_append(&mut self, new_local_hw: u64) {
        self.local_append_hw = replica_quorum_hw_advance_b115(self.local_append_hw, new_local_hw);
    }

    /// Plan an out-of-lock follower shipping batch of `proposed_bytes`.
    pub fn plan_ship_batch(&mut self, proposed_bytes: u64) -> ReplicaShipPlan {
        if self.consecutive_timeouts >= self.max_timeouts_before_open {
            return ReplicaShipPlan::CircuitOpenDegraded {
                consecutive_timeouts: self.consecutive_timeouts,
            };
        }
        if self.durable_quorum_hw >= self.local_append_hw {
            return ReplicaShipPlan::CaughtUp {
                quorum_hw: self.durable_quorum_hw,
            };
        }
        let clamped = replica_inflight_clamp_b115(proposed_bytes, self.max_inflight_bytes);
        self.inflight_bytes = clamped;
        ReplicaShipPlan::ShipBatch {
            start_offset: self.durable_quorum_hw,
            end_offset: self.local_append_hw,
            batch_bytes: clamped,
        }
    }

    /// Commit a follower ACK up to `ack_hw` (must be `<= local_append_hw`).
    pub fn record_follower_ack(&mut self, ack_hw: u64) -> bool {
        if !replica_ack_within_local_hw_b115(ack_hw, self.local_append_hw) {
            return false;
        }
        self.durable_quorum_hw = replica_quorum_hw_advance_b115(self.durable_quorum_hw, ack_hw);
        self.inflight_bytes = 0;
        self.consecutive_timeouts = 0;
        true
    }

    /// Record a `REPLICA_IO_TIMEOUT` without holding `Mutex<BrokerLog>`.
    pub fn record_io_timeout(&mut self) {
        self.inflight_bytes = 0;
        self.consecutive_timeouts = self.consecutive_timeouts.saturating_add(1);
    }

    /// Reset circuit breaker after a background follower health probe succeeds.
    pub fn record_probe_recovered(&mut self) {
        self.consecutive_timeouts = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ships_out_of_lock_and_trips_circuit_on_repeated_timeouts() {
        let mut s = ReplicaOutOfLockShipper::new(65_536, 2);
        s.observe_local_append(50);
        assert_eq!(
            s.plan_ship_batch(100_000),
            ReplicaShipPlan::ShipBatch {
                start_offset: 0,
                end_offset: 50,
                batch_bytes: 65_536,
            }
        );
        assert!(s.record_follower_ack(50));
        assert_eq!(
            s.plan_ship_batch(4096),
            ReplicaShipPlan::CaughtUp { quorum_hw: 50 }
        );

        s.observe_local_append(75);
        s.record_io_timeout();
        s.record_io_timeout();
        assert_eq!(
            s.plan_ship_batch(4096),
            ReplicaShipPlan::CircuitOpenDegraded {
                consecutive_timeouts: 2
            }
        );
        s.record_probe_recovered();
        assert!(matches!(
            s.plan_ship_batch(4096),
            ReplicaShipPlan::ShipBatch { .. }
        ));
    }
}
