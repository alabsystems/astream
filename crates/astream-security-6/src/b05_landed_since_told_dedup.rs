// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Sim item B05 `Bridge::landed_since` + `fetch_told_kept` post-cut replay dedup planner
//! (`docs/DESIGN-aterm-fabric.md` §3 lines 664–678; `Astream.Broker.TlaB05LandedSinceToldDedup`).
//!
//! When compaction drops dedup keys below the cut, republishing an in-flight entry or pinned
//! retry without checking `FetchTold` from `min(journaled_head, continues_at)` risks writing a
//! duplicate copy if retention still holds the unread mail below `oldest`! Furthermore, any
//! record offset already claimed by another sequence's replay/retry MUST be skipped so an
//! identical-body earlier post never suppresses a subsequent post.

#[cfg(clean_islands)]
#[path = "b05_landed_since_told_dedup_island.rs"]
mod b05_landed_since_told_dedup_island;
#[cfg(clean_islands)]
pub use b05_landed_since_told_dedup_island::{
    b05_claimed_cursor_advance_b131, b05_read_start_clamp_b131,
};

/// Fixed ring of claimed post offsets (`32` slots, zero heap allocation).
pub const MAX_CLAIMED_POST_SLOTS: usize = 32;

#[cfg(not(clean_islands))]
/// Clamp read-back start offset to `continues_at` (`min(journal_head, continues_at)`).
#[must_use]
pub const fn b05_read_start_clamp_b131(journal_head: u64, continues_at: u64) -> u64 {
    if journal_head < continues_at {
        journal_head
    } else {
        continues_at
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance highest claimed bus offset settled across replays/retries.
#[must_use]
pub const fn b05_claimed_cursor_advance_b131(cur_claimed: u64, cand_claimed: u64) -> u64 {
    if cur_claimed < cand_claimed {
        cand_claimed
    } else {
        cur_claimed
    }
}

contract_fn! {
    /// True iff `read_start < retained_oldest` (ordinary `Fetch` refuses `retained-from=`, so `FetchTold` is required!).
    #[must_use]
    pub const fn b05_needs_told_fallback_b131(read_start: u64, retained_oldest: u64) -> bool
    clauses [ensures result == (read_start < retained_oldest)]
    {
        read_start < retained_oldest
    }
}

/// Strategy selected to verify whether a post already landed before republishing.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum B05ReadbackPlan {
    /// Log does not continue the attempt's generation: safe to republish directly.
    DisjointLogRepublishNow,
    /// Read from `start_offset` with ordinary `Fetch` (`start_offset >= retained_oldest`).
    FetchOrdinary { start_offset: u64 },
    /// Read from `start_offset` on a dedicated `REQUEST_TOLD_FETCH` connection so held mail below `retained_oldest` is seen!
    FetchToldBelowOldest { start_offset: u64 },
}

/// Pure stack B05 post-cut read-back planner and per-sequence offset claim table.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy)]
pub struct B05LandedSinceLedger {
    claimed_offsets: [Option<(u64, u64)>; MAX_CLAIMED_POST_SLOTS], // (seq, bus_offset)
    write_idx: usize,
    claimed_hwm: u64,
}

impl Default for B05LandedSinceLedger {
    fn default() -> Self {
        Self::new()
    }
}

impl B05LandedSinceLedger {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            claimed_offsets: [None; MAX_CLAIMED_POST_SLOTS],
            write_idx: 0,
            claimed_hwm: 0,
        }
    }

    #[must_use]
    pub const fn claimed_hwm(&self) -> u64 {
        self.claimed_hwm
    }

    /// Plan the read-back scan for an attempt journaled at `journal_head` against `(continues_at, retained_oldest)`.
    #[must_use]
    pub fn plan_readback(
        &self,
        journal_head: u64,
        continues_at: Option<u64>,
        retained_oldest: u64,
    ) -> B05ReadbackPlan {
        let Some(cont_cap) = continues_at else {
            return B05ReadbackPlan::DisjointLogRepublishNow;
        };
        let start_offset = b05_read_start_clamp_b131(journal_head, cont_cap);
        if b05_needs_told_fallback_b131(start_offset, retained_oldest) {
            B05ReadbackPlan::FetchToldBelowOldest { start_offset }
        } else {
            B05ReadbackPlan::FetchOrdinary { start_offset }
        }
    }

    /// Record that `seq` settled at `bus_offset`.
    pub fn record_claim(&mut self, seq: u64, bus_offset: u64) {
        let idx = self.write_idx & (MAX_CLAIMED_POST_SLOTS - 1);
        if let Some(slot) = self.claimed_offsets.get_mut(idx) {
            *slot = Some((seq, bus_offset));
        }
        self.write_idx = self.write_idx.wrapping_add(1) & (MAX_CLAIMED_POST_SLOTS - 1);
        self.claimed_hwm = b05_claimed_cursor_advance_b131(self.claimed_hwm, bus_offset);
    }

    /// Return `true` iff `candidate_offset` with matching body is unclaimed by any OTHER sequence (so `for_seq` can adopt it).
    #[must_use]
    pub fn can_adopt_matching_record(&self, for_seq: u64, candidate_offset: u64) -> bool {
        let mut rest = self.claimed_offsets.as_slice();
        while let &[entry, ref tail @ ..] = rest {
            if let Some((claimed_seq, claimed_off)) = entry {
                if claimed_off == candidate_offset && claimed_seq != for_seq {
                    return false;
                }
            }
            rest = tail;
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn switches_to_fetch_told_below_oldest_clamps_to_continues_and_skips_other_seq_claims() {
        let mut ledger = B05LandedSinceLedger::new();
        assert_eq!(
            ledger.plan_readback(40, Some(32), 50),
            B05ReadbackPlan::FetchToldBelowOldest { start_offset: 32 }
        );
        assert_eq!(
            ledger.plan_readback(60, Some(80), 50),
            B05ReadbackPlan::FetchOrdinary { start_offset: 60 }
        );
        assert_eq!(
            ledger.plan_readback(40, None, 50),
            B05ReadbackPlan::DisjointLogRepublishNow
        );

        // Seq 1 settled at bus offset 44; seq 2 with identical words MUST NOT adopt offset 44!
        ledger.record_claim(1, 44);
        assert!(!ledger.can_adopt_matching_record(2, 44));
        assert!(ledger.can_adopt_matching_record(1, 44));
        assert!(ledger.can_adopt_matching_record(2, 45));
    }
}
