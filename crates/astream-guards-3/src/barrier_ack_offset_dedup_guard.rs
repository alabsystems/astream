// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Acknowledged-broadcast `Last` barrier offset-test & dedup-answer counter guard
//! (`evidence/manifest.toml` `broker.barrier-count-by-last`;
//! `Astream.Broker.TlaBarrierAckOffsetDedupGuard`).
//!
//! Enforces the broadcast barrier counting law over `/f/<F>/pub/*/*/ack/<B>`:
//! - A barrier named by `PublishAck` offset `B` (`barrier_offset`) admits ONLY `Last` rows
//!   whose log `row_offset >= barrier_offset` (strictly rejecting pre-published stale rows
//!   with `row_offset < B` that happen to name `/ack/<B>`),
//! - Re-sent acks dedup to their original offset (`row_offset <= prev_seen_max_offset` when
//!   already counted), and total counted answers never exceed `expected_members`!

#[cfg(clean_islands)]
#[path = "barrier_ack_offset_dedup_guard_island.rs"]
mod barrier_ack_offset_dedup_guard_island;
#[cfg(clean_islands)]
pub use barrier_ack_offset_dedup_guard_island::{
    barrier_count_clamp_b149, barrier_max_offset_advance_b149,
};

/// Upper bound on tracked barrier participants per `Last` page (`4_096`).
pub const MAX_BARRIER_MEMBERS: u64 = 4_096;

#[cfg(not(clean_islands))]
/// Clamp counted barrier answers to `expected_members`.
#[must_use]
pub const fn barrier_count_clamp_b149(cand_count: u64, expected_members: u64) -> u64 {
    if cand_count < expected_members {
        cand_count
    } else {
        expected_members
    }
}

#[cfg(not(clean_islands))]
/// Advance highest verified barrier answer offset monotonically.
#[must_use]
pub const fn barrier_max_offset_advance_b149(cur_max_off: u64, cand_off: u64) -> u64 {
    if cur_max_off < cand_off {
        cand_off
    } else {
        cur_max_off
    }
}

contract_fn! {
    /// True iff `row_offset >= barrier_offset` and `re_matches_barrier`.
    #[must_use]
    pub const fn barrier_row_postdates_broadcast_b149(
        row_offset: u64,
        barrier_offset: u64,
        re_matches_barrier: bool,
    ) -> bool
    clauses [ensures result == (re_matches_barrier && row_offset >= barrier_offset)]
    {
        re_matches_barrier && row_offset >= barrier_offset
    }
}

/// Decision when evaluating a `Last` row on `/f/<F>/pub/<node>/<sid>/ack/<B>`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BarrierRowDecision {
    CountedAnswer {
        answered_count: u64,
        quorum_complete: bool,
    },
    IgnoredPreBroadcastRow {
        row_offset: u64,
        barrier_offset: u64,
    },
    IgnoredMismatchedReField,
    IgnoredDuplicateResend {
        deduped_offset: u64,
    },
}

/// Counts post-broadcast (`offset >= B`) unique member answers for barrier `B`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BroadcastBarrierCounter {
    barrier_offset: u64,
    expected_members: u64,
    answered_count: u64,
    max_answer_offset: u64,
}

impl BroadcastBarrierCounter {
    #[must_use]
    pub const fn new(barrier_offset: u64, expected_members: u64) -> Self {
        let cap = barrier_count_clamp_b149(expected_members, MAX_BARRIER_MEMBERS);
        Self {
            barrier_offset,
            expected_members: cap,
            answered_count: 0,
            max_answer_offset: barrier_offset,
        }
    }

    #[must_use]
    pub const fn answered_count(&self) -> u64 {
        barrier_count_clamp_b149(self.answered_count, self.expected_members)
    }

    /// Inspect one `Last` row at `row_offset`.
    pub fn observe_last_row(
        &mut self,
        row_offset: u64,
        re_matches_barrier: bool,
        already_seen_offset: bool,
    ) -> BarrierRowDecision {
        if !re_matches_barrier {
            return BarrierRowDecision::IgnoredMismatchedReField;
        }
        if !barrier_row_postdates_broadcast_b149(
            row_offset,
            self.barrier_offset,
            re_matches_barrier,
        ) {
            return BarrierRowDecision::IgnoredPreBroadcastRow {
                row_offset,
                barrier_offset: self.barrier_offset,
            };
        }
        if already_seen_offset {
            return BarrierRowDecision::IgnoredDuplicateResend {
                deduped_offset: row_offset,
            };
        }
        let next = self.answered_count.saturating_add(1);
        self.answered_count = barrier_count_clamp_b149(next, self.expected_members);
        self.max_answer_offset =
            barrier_max_offset_advance_b149(self.max_answer_offset, row_offset);
        BarrierRowDecision::CountedAnswer {
            answered_count: self.answered_count,
            quorum_complete: self.answered_count == self.expected_members,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn excludes_pre_broadcast_row_below_b_and_dedups_resent_ack_offsets() {
        let mut c = BroadcastBarrierCounter::new(10, 4);
        // Member 0 pre-published `/ack/10` at offset 9 (< B=10) -> MUST be excluded!
        assert_eq!(
            c.observe_last_row(9, true, false),
            BarrierRowDecision::IgnoredPreBroadcastRow {
                row_offset: 9,
                barrier_offset: 10,
            }
        );
        // Four members answer at offsets 11, 12, 13, 14 (one resent deduped to 12):
        assert_eq!(
            c.observe_last_row(11, true, false),
            BarrierRowDecision::CountedAnswer {
                answered_count: 1,
                quorum_complete: false,
            }
        );
        assert_eq!(
            c.observe_last_row(12, true, false),
            BarrierRowDecision::CountedAnswer {
                answered_count: 2,
                quorum_complete: false,
            }
        );
        assert_eq!(
            c.observe_last_row(12, true, true),
            BarrierRowDecision::IgnoredDuplicateResend { deduped_offset: 12 }
        );
        c.observe_last_row(13, true, false);
        assert_eq!(
            c.observe_last_row(14, true, false),
            BarrierRowDecision::CountedAnswer {
                answered_count: 4,
                quorum_complete: true,
            }
        );
    }
}
