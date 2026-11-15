// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Autonomous background quorum lease-heartbeat failover daemon
//! (`docs/ROADMAP.md` §"Replicated tier follow-ons";
//! `Astream.Broker.TlaAutonomousQuorumLeaseDaemon`).
//!
//! Coordinates split-brain-free autonomous failover across a replicated broker cluster:
//! - A leader renews its bounded lease `[round_start_ms, round_start_ms + lease_duration_ms]` ONLY
//!   when at least `quorum_size` replicas acknowledge the heartbeat round, and steps down before
//!   `round_start_ms + lease_duration_ms` if quorum is lost,
//! - Followers withhold votes and refuse election until `last_leader_lease_expiry_ms + drift_guard_ms`
//!   has strictly elapsed, guaranteeing disjoint write leases across bounded clock skew,
//! - Every promoted leader advances `leader_term` monotonically.

#[cfg(clean_islands)]
#[path = "autonomous_quorum_lease_daemon_island.rs"]
mod autonomous_quorum_lease_daemon_island;
#[cfg(clean_islands)]
pub use autonomous_quorum_lease_daemon_island::{
    quorum_lease_duration_clamp_b126, quorum_term_advance_b126,
};

#[cfg(not(clean_islands))]
/// Clamp a leader heartbeat lease duration to `max_lease_ms`.
#[must_use]
pub const fn quorum_lease_duration_clamp_b126(cand_ms: u64, max_lease_ms: u64) -> u64 {
    if cand_ms < max_lease_ms {
        cand_ms
    } else {
        max_lease_ms
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the cluster failover term epoch.
#[must_use]
pub const fn quorum_term_advance_b126(cur_term: u64, cand_term: u64) -> u64 {
    if cur_term < cand_term {
        cand_term
    } else {
        cur_term
    }
}

contract_fn! {
    /// True iff `now_ms >= guarded_expiry_ms && votes >= quorum_needed` (safe to promote a new leader).
    #[must_use]
    pub const fn quorum_failover_ready_b126(
        now_ms: u64,
        guarded_expiry_ms: u64,
        votes: u64,
        quorum_needed: u64,
    ) -> bool
    clauses [ensures result == (now_ms >= guarded_expiry_ms && votes >= quorum_needed)]
    {
        now_ms >= guarded_expiry_ms && votes >= quorum_needed
    }
}

/// Role of a node under the autonomous lease-heartbeat failover daemon.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LeaseDaemonRole {
    Follower,
    Leader { lease_until_ms: u64 },
}

/// Daemon tick outcome on a heartbeat or election evaluation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LeaseDaemonAction {
    LeaderLeaseRenewed { term: u64, lease_until_ms: u64 },
    LeaderSteppedDownQuorumLost { term: u64 },
    ElectionBlockedLeaseActive { guarded_expiry_ms: u64 },
    ElectionInsufficientVotes { votes: u64, quorum_needed: u64 },
    PromotedNewLeader { new_term: u64, lease_until_ms: u64 },
}

/// Stateful autonomous quorum lease-heartbeat failover daemon.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AutonomousQuorumLeaseDaemon {
    role: LeaseDaemonRole,
    current_term: u64,
    quorum_needed: u64,
    lease_duration_ms: u64,
    max_lease_ms: u64,
    drift_guard_ms: u64,
    observed_lease_expiry_ms: u64,
}

impl AutonomousQuorumLeaseDaemon {
    #[must_use]
    pub const fn new_follower(
        initial_term: u64,
        quorum_needed: u64,
        lease_duration_ms: u64,
        max_lease_ms: u64,
        drift_guard_ms: u64,
    ) -> Self {
        let clamped_lease = quorum_lease_duration_clamp_b126(lease_duration_ms, max_lease_ms);
        Self {
            role: LeaseDaemonRole::Follower,
            current_term: initial_term,
            quorum_needed: if quorum_needed == 0 { 1 } else { quorum_needed },
            lease_duration_ms: clamped_lease,
            max_lease_ms,
            drift_guard_ms,
            observed_lease_expiry_ms: 0,
        }
    }

    #[must_use]
    pub const fn role(&self) -> LeaseDaemonRole {
        self.role
    }

    #[must_use]
    pub const fn current_term(&self) -> u64 {
        self.current_term
    }

    /// Follower observes a valid heartbeat from a leader at `leader_term` expiring at `expiry_ms`.
    pub fn on_leader_heartbeat(&mut self, leader_term: u64, expiry_ms: u64) {
        if leader_term >= self.current_term {
            self.current_term = quorum_term_advance_b126(self.current_term, leader_term);
            self.role = LeaseDaemonRole::Follower;
            if expiry_ms > self.observed_lease_expiry_ms {
                self.observed_lease_expiry_ms = expiry_ms;
            }
        }
    }

    /// Leader evaluates a heartbeat round begun at `round_start_ms` with `quorum_acks` responses.
    pub fn tick_leader_heartbeat(
        &mut self,
        round_start_ms: u64,
        now_ms: u64,
        quorum_acks: u64,
    ) -> LeaseDaemonAction {
        let LeaseDaemonRole::Leader { lease_until_ms } = self.role else {
            return LeaseDaemonAction::LeaderSteppedDownQuorumLost {
                term: self.current_term,
            };
        };
        if now_ms >= lease_until_ms || quorum_acks < self.quorum_needed {
            self.role = LeaseDaemonRole::Follower;
            return LeaseDaemonAction::LeaderSteppedDownQuorumLost {
                term: self.current_term,
            };
        }
        let dur = quorum_lease_duration_clamp_b126(self.lease_duration_ms, self.max_lease_ms);
        let renewed_until = round_start_ms.saturating_add(dur);
        let next_until = if renewed_until > lease_until_ms {
            renewed_until
        } else {
            lease_until_ms
        };
        self.role = LeaseDaemonRole::Leader {
            lease_until_ms: next_until,
        };
        self.observed_lease_expiry_ms = next_until;
        LeaseDaemonAction::LeaderLeaseRenewed {
            term: self.current_term,
            lease_until_ms: next_until,
        }
    }

    /// Follower attempts autonomous quorum failover at `now_ms` with `votes` pre-vote/vote grants.
    pub fn try_autonomous_failover(&mut self, now_ms: u64, votes: u64) -> LeaseDaemonAction {
        let guarded_expiry = self
            .observed_lease_expiry_ms
            .saturating_add(self.drift_guard_ms);
        if now_ms < guarded_expiry {
            return LeaseDaemonAction::ElectionBlockedLeaseActive {
                guarded_expiry_ms: guarded_expiry,
            };
        }
        if !quorum_failover_ready_b126(now_ms, guarded_expiry, votes, self.quorum_needed) {
            return LeaseDaemonAction::ElectionInsufficientVotes {
                votes,
                quorum_needed: self.quorum_needed,
            };
        }
        self.current_term =
            quorum_term_advance_b126(self.current_term, self.current_term.saturating_add(1));
        let dur = quorum_lease_duration_clamp_b126(self.lease_duration_ms, self.max_lease_ms);
        let lease_until_ms = now_ms.saturating_add(dur);
        self.role = LeaseDaemonRole::Leader { lease_until_ms };
        self.observed_lease_expiry_ms = lease_until_ms;
        LeaseDaemonAction::PromotedNewLeader {
            new_term: self.current_term,
            lease_until_ms,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_failover_during_lease_plus_drift_guard_then_promotes_and_steps_down_on_partition() {
        let mut daemon = AutonomousQuorumLeaseDaemon::new_follower(4, 2, 500, 1_000, 50);
        daemon.on_leader_heartbeat(4, 2_000);

        // At t=2_030, lease (2_000) + drift_guard (50) = 2_050 has NOT elapsed -> blocked!
        assert_eq!(
            daemon.try_autonomous_failover(2_030, 3),
            LeaseDaemonAction::ElectionBlockedLeaseActive {
                guarded_expiry_ms: 2_050
            }
        );

        // At t=2_050 with only 1 vote (< quorum 2) -> refused.
        assert_eq!(
            daemon.try_autonomous_failover(2_050, 1),
            LeaseDaemonAction::ElectionInsufficientVotes {
                votes: 1,
                quorum_needed: 2,
            }
        );

        // At t=2_050 with 2 quorum votes -> promoted to term 5 with lease [2_050, 2_550]!
        assert_eq!(
            daemon.try_autonomous_failover(2_050, 2),
            LeaseDaemonAction::PromotedNewLeader {
                new_term: 5,
                lease_until_ms: 2_550,
            }
        );
        assert_eq!(
            daemon.tick_leader_heartbeat(2_200, 2_220, 2),
            LeaseDaemonAction::LeaderLeaseRenewed {
                term: 5,
                lease_until_ms: 2_700,
            }
        );

        // Partition drops quorum_acks to 1 -> steps down immediately!
        assert_eq!(
            daemon.tick_leader_heartbeat(2_400, 2_450, 1),
            LeaseDaemonAction::LeaderSteppedDownQuorumLost { term: 5 }
        );
        assert_eq!(daemon.role(), LeaseDaemonRole::Follower);
    }
}
