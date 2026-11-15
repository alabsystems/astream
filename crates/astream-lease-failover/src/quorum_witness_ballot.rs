// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Split-brain-proof quorum witness ballot counter (`Astream.LeaseFail.TlaQuorumWitnessBallot`)
//! requiring `floor(N/2) + 1` distinct witness votes in a strictly higher election term.

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
#[path = "quorum_witness_ballot_island.rs"]
mod quorum_witness_ballot_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lhf_votes_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lhf_term_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use quorum_witness_ballot_island::{lhf_term_advance, lhf_votes_clamp};

/// Maximum cluster voting members (`31`).
pub const MAX_CLUSTER_VOTERS: u64 = 31;

contract_fn! {
    /// Verified strict quorum majority (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `lhf_has_majority_isl`.
    #[must_use]
    pub const fn lhf_has_majority(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct QuorumBallot {
    cluster_size: u64,
    invalid_cluster: bool,
    term: u64,
    voter_mask: u32,
}

impl QuorumBallot {
    #[must_use]
    pub const fn new(cluster_size: u64) -> Self {
        let sz = lhf_votes_clamp(cluster_size, MAX_CLUSTER_VOTERS);
        Self {
            cluster_size: if sz == 0 { 1 } else { sz },
            invalid_cluster: cluster_size == 0 || cluster_size > MAX_CLUSTER_VOTERS,
            term: 0,
            voter_mask: 0,
        }
    }

    pub fn begin_term(&mut self, next_term: u64) -> bool {
        if self.invalid_cluster || next_term <= self.term {
            return false;
        }
        self.term = lhf_term_advance(self.term, next_term);
        self.voter_mask = 0;
        true
    }

    pub fn record_vote(&mut self, voter_idx: u8, term: u64) -> bool {
        if self.invalid_cluster
            || self.term == 0
            || term != self.term
            || u64::from(voter_idx) >= self.cluster_size
        {
            return false;
        }
        self.voter_mask |= 1u32 << (voter_idx & 31);
        let votes = u64::from(self.voter_mask.count_ones());
        let majority = (self.cluster_size >> 1).saturating_add(1);
        lhf_has_majority(votes, majority)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deduplicates_voter_ids_and_requires_strict_majority() {
        let mut b = QuorumBallot::new(3);
        assert!(b.begin_term(1));
        assert!(!b.record_vote(0, 1));
        assert!(!b.record_vote(0, 1));
        assert!(b.record_vote(2, 1));
    }
}
