// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Divergent-tail truncation calculator (`BrokerLog::truncate_replica_to`,
//! `Astream.LeaseFail.TlaDivergentTailTrunc`) computing safe common-ancestor truncation points
//! without ever cutting below the committed quorum durable watermark.

#[cfg(clean_islands)]
#[path = "divergent_tail_trunc_island.rs"]
mod divergent_tail_trunc_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lhf_tail_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lhf_common_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use divergent_tail_trunc_island::{lhf_common_advance, lhf_tail_clamp};

/// Maximum uncommitted divergent tail span (`1_000_000` records).
pub const MAX_DIVERGENT_RECORDS: u64 = 1_000_000;

contract_fn! {
    /// Verified truncation above quorum watermark (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `lhf_prefix_aligned_isl`.
    #[must_use]
    pub const fn lhf_prefix_aligned(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct DivergentTailPlanner {
    quorum_committed: u64,
}

impl DivergentTailPlanner {
    #[must_use]
    pub const fn new(quorum_committed: u64) -> Self {
        Self { quorum_committed }
    }

    pub fn advance_quorum(&mut self, committed: u64) {
        self.quorum_committed = lhf_common_advance(self.quorum_committed, committed);
    }

    /// Returns bytes/records to drop `Some(drop_count)` if `common_offset >= quorum_committed`.
    #[must_use]
    pub const fn plan_truncate(&self, local_head: u64, common_offset: u64) -> Option<u64> {
        if !lhf_prefix_aligned(common_offset, self.quorum_committed) || common_offset > local_head {
            return None;
        }
        let raw_drop = local_head.saturating_sub(common_offset);
        let clamped = lhf_tail_clamp(raw_drop, MAX_DIVERGENT_RECORDS);
        if clamped != raw_drop {
            return None;
        }
        Some(clamped)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_truncation_below_quorum_committed_offset() {
        let mut p = DivergentTailPlanner::new(500);
        p.advance_quorum(520);
        assert_eq!(p.plan_truncate(550, 510), None);
        assert_eq!(p.plan_truncate(550, 525), Some(25));
    }
}
