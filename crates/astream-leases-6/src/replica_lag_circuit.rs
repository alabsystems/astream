// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Follower shipping timeout & lag circuit breaker (`Astream.Broker.TlaReplicaLagCircuit`).
//!
//! Prevents a single partitioned or slow `Replicated`-tier follower from stalling synchronous
//! leader commits repeatedly for `REPLICA_IO_TIMEOUT`: once consecutive shipping timeouts reach
//! `max_timeouts` or lag exceeds `max_sync_lag`, the follower transitions cleanly into
//! `ReplicaCircuitPhase::DemotedCatchup` until an async catch-up probe confirms recovery within
//! [`replica_within_lag_budget`].

#[cfg(clean_islands)]
#[path = "replica_lag_circuit_island.rs"]
mod replica_lag_circuit_island;
#[cfg(clean_islands)]
pub use replica_lag_circuit_island::{replica_confirmed_advance, replica_timeout_clamp};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn replica_timeout_clamp(cand_timeouts: u64, max_timeouts: u64) -> u64 {
    if cand_timeouts < max_timeouts {
        cand_timeouts
    } else {
        max_timeouts
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn replica_confirmed_advance(cur_confirmed: u64, cand_confirmed: u64) -> u64 {
    if cur_confirmed < cand_confirmed {
        cand_confirmed
    } else {
        cur_confirmed
    }
}

contract_fn! {
    /// Verified check that follower lag sits within the synchronous shipping budget
    /// (`lag_records <= max_sync_lag`), linked via `clean-kernel-defeq` to
    /// `replica_within_lag_budget_isl`.
    #[must_use]
    pub const fn replica_within_lag_budget(lag_records: u64, max_sync_lag: u64) -> bool
    clauses [ensures result == (lag_records <= max_sync_lag)]
    {
        lag_records <= max_sync_lag
    }
}

/// Circuit state for one `Replicated`-tier follower link.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReplicaCircuitPhase {
    /// Follower participates in synchronous commit shipping.
    SyncActive,
    /// Follower timed out once and is probed with bounded budget.
    HalfOpenProbe,
    /// Follower is demoted to background catch-up outside the leader's synchronous commit path.
    DemotedCatchup,
}

/// Per-follower lag and timeout circuit breaker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReplicaLagCircuit {
    confirmed_offset: u64,
    consecutive_timeouts: u64,
    max_timeouts: u64,
    max_sync_lag: u64,
    phase: ReplicaCircuitPhase,
}

impl ReplicaLagCircuit {
    /// Create a circuit breaker in `SyncActive` with `max_timeouts >= 1` and `max_sync_lag`.
    #[must_use]
    pub const fn new(max_timeouts: u64, max_sync_lag: u64) -> Self {
        let cap_to = if max_timeouts == 0 { 1 } else { max_timeouts };
        Self {
            confirmed_offset: 0,
            consecutive_timeouts: 0,
            max_timeouts: cap_to,
            max_sync_lag,
            phase: ReplicaCircuitPhase::SyncActive,
        }
    }

    #[must_use]
    pub const fn confirmed_offset(&self) -> u64 {
        self.confirmed_offset
    }

    #[must_use]
    pub const fn consecutive_timeouts(&self) -> u64 {
        self.consecutive_timeouts
    }

    #[must_use]
    pub const fn phase(&self) -> ReplicaCircuitPhase {
        self.phase
    }

    /// Whether the leader should include this follower on the synchronous commit path at `leader_head`.
    #[must_use]
    pub const fn eligible_for_sync(&self, leader_head: u64) -> bool {
        let lag = leader_head.saturating_sub(self.confirmed_offset);
        !matches!(self.phase, ReplicaCircuitPhase::DemotedCatchup)
            && replica_within_lag_budget(lag, self.max_sync_lag)
    }

    /// Record a shipping timeout at `leader_head` and return the updated circuit phase.
    pub fn record_timeout(&mut self, leader_head: u64) -> ReplicaCircuitPhase {
        let next = self.consecutive_timeouts.saturating_add(1);
        self.consecutive_timeouts = replica_timeout_clamp(next, self.max_timeouts);
        let lag = leader_head.saturating_sub(self.confirmed_offset);
        if self.consecutive_timeouts >= self.max_timeouts
            || !replica_within_lag_budget(lag, self.max_sync_lag)
        {
            self.phase = ReplicaCircuitPhase::DemotedCatchup;
        } else {
            self.phase = ReplicaCircuitPhase::HalfOpenProbe;
        }
        self.phase
    }

    /// Record a confirmed follower offset ack at `leader_head`, re-admitting to `SyncActive` once
    /// lag sits within `max_sync_lag`.
    pub fn record_ack(&mut self, acked_offset: u64, leader_head: u64) -> ReplicaCircuitPhase {
        let capped_ack = if acked_offset < leader_head {
            acked_offset
        } else {
            leader_head
        };
        self.confirmed_offset = replica_confirmed_advance(self.confirmed_offset, capped_ack);
        self.consecutive_timeouts = 0;
        let lag = leader_head.saturating_sub(self.confirmed_offset);
        if replica_within_lag_budget(lag, self.max_sync_lag) {
            self.phase = ReplicaCircuitPhase::SyncActive;
        } else {
            self.phase = ReplicaCircuitPhase::DemotedCatchup;
        }
        self.phase
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn demotes_slow_follower_and_readmits_after_catchup() {
        let mut c = ReplicaLagCircuit::new(2, 64);
        assert!(c.eligible_for_sync(20));

        assert_eq!(c.record_timeout(20), ReplicaCircuitPhase::HalfOpenProbe);
        assert_eq!(c.consecutive_timeouts(), 1);
        assert!(c.eligible_for_sync(20));

        // Second timeout trips DemotedCatchup so leader writes stop blocking on REPLICA_IO_TIMEOUT.
        assert_eq!(c.record_timeout(20), ReplicaCircuitPhase::DemotedCatchup);
        assert_eq!(c.consecutive_timeouts(), 2);
        assert!(!c.eligible_for_sync(20));

        // Partial catch-up still > 64 behind stays DemotedCatchup, but resets timeout streak.
        assert_eq!(c.record_ack(10, 100), ReplicaCircuitPhase::DemotedCatchup);
        assert_eq!(c.confirmed_offset(), 10);
        assert_eq!(c.consecutive_timeouts(), 0);

        // Catch-up within 64 records re-admits follower to SyncActive!
        assert_eq!(c.record_ack(80, 100), ReplicaCircuitPhase::SyncActive);
        assert!(c.eligible_for_sync(100));
    }
}
