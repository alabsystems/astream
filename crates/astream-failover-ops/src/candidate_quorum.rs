// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Raft / Viewstamped-Replication log-completeness majority-quorum ballot box
//! (`DESIGN-aterm-fabric.md` §15, `Astream.Failover.TlaCandidateQuorum`).
//!
//! Ensures zero acked-record loss during autonomous failover:
//! - A voter in `epoch` grants at most one vote, and ONLY if the candidate's log position
//!   `(cand_last_epoch, cand_head_offset)` is at least as up-to-date as the voter's own!
//! - Majority quorum requires `(cluster_size / 2) + 1` distinct voters (`cand_has_quorum`).

use std::collections::BTreeSet;

#[cfg(clean_islands)]
#[path = "candidate_quorum_island.rs"]
mod candidate_quorum_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cand_votes_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cand_epoch_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use candidate_quorum_island::{cand_epoch_advance, cand_votes_clamp};

/// Maximum voting replicas in one replicated broker group.
pub const MAX_CLUSTER_VOTERS: u64 = 31;

contract_fn! {
    /// Verified majority threshold check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `cand_has_quorum_isl`.
    #[must_use]
    pub const fn cand_has_quorum(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Checks whether candidate log `(c_epoch, c_head)` is at least as up-to-date as voter `(v_epoch, v_head)`.
#[must_use]
pub const fn candidate_log_up_to_date(
    cand_last_epoch: u64,
    cand_head_offset: u64,
    voter_last_epoch: u64,
    voter_head_offset: u64,
) -> bool {
    if cand_last_epoch != voter_last_epoch {
        cand_last_epoch > voter_last_epoch
    } else {
        cand_head_offset >= voter_head_offset
    }
}

/// Majority ballot box for a single failover candidate.
#[derive(Debug, Clone)]
pub struct CandidateQuorumBallot {
    cluster_size: u64,
    epoch: u64,
    candidate_id: u64,
    cand_last_epoch: u64,
    cand_head_offset: u64,
    granted_voters: BTreeSet<u64>,
}

impl CandidateQuorumBallot {
    #[must_use]
    pub fn new(
        cluster_size: u64,
        epoch: u64,
        candidate_id: u64,
        cand_last_epoch: u64,
        cand_head_offset: u64,
    ) -> Self {
        let clamped_size = cand_votes_clamp(cluster_size, MAX_CLUSTER_VOTERS);
        let eff_size = if clamped_size == 0 { 1 } else { clamped_size };
        let mut granted_voters = BTreeSet::new();
        granted_voters.insert(candidate_id); // candidate votes for itself
        Self {
            cluster_size: eff_size,
            epoch: cand_epoch_advance(0, epoch),
            candidate_id,
            cand_last_epoch,
            cand_head_offset,
            granted_voters,
        }
    }

    #[must_use]
    pub const fn required_majority(&self) -> u64 {
        (self.cluster_size / 2).saturating_add(1)
    }

    #[must_use]
    pub fn has_won_election(&self) -> bool {
        let tally = cand_votes_clamp(self.granted_voters.len() as u64, self.cluster_size);
        cand_has_quorum(tally, self.required_majority())
    }

    /// Evaluates and records a peer replica's vote iff `voter_epoch <= self.epoch` and
    /// `candidate_log_up_to_date` holds.
    pub fn record_peer_response(
        &mut self,
        voter_id: u64,
        voter_epoch: u64,
        voter_last_epoch: u64,
        voter_head_offset: u64,
        already_voted_in_epoch: bool,
    ) -> bool {
        if voter_id == self.candidate_id || already_voted_in_epoch || voter_epoch > self.epoch {
            return false;
        }
        if !candidate_log_up_to_date(
            self.cand_last_epoch,
            self.cand_head_offset,
            voter_last_epoch,
            voter_head_offset,
        ) {
            return false;
        }
        self.granted_voters.insert(voter_id);
        self.has_won_election()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn five_node_election_requires_three_up_to_date_votes_and_rejects_lagging_candidate() {
        let mut ballot = CandidateQuorumBallot::new(5, 4, 10, 3, 500);
        assert_eq!(ballot.required_majority(), 3);
        assert!(!ballot.has_won_election()); // 1/5 self-vote

        // Peer 11 has higher head (505) in epoch 3 -> refuses vote!
        assert!(!ballot.record_peer_response(11, 4, 3, 505, false));
        // Peer 12 has (3, 500) -> grants vote (2/5)
        assert!(!ballot.record_peer_response(12, 3, 3, 500, false));
        // Duplicate vote from 12 changes nothing
        assert!(!ballot.record_peer_response(12, 4, 3, 500, false));
        // Peer 13 has (2, 999) -> older last_epoch 2 < 3 -> grants vote (3/5 -> WINS!)
        assert!(ballot.record_peer_response(13, 3, 2, 999, false));
        assert!(ballot.has_won_election());
    }
}
