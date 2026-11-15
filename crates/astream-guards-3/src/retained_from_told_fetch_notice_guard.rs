// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `retained-from=<off>` refusal vs `fetch_told` pre-page `Gap` notice guard
//! (`evidence/manifest.toml` `broker.retention-rules`;
//! `Astream.Broker.TlaRetainedFromToldFetchNoticeGuard`).
//!
//! Enforces the R4 / A9 `Fetch` vs `fetch_told` (`REQUEST_TOLD_FETCH`) contract:
//! - Head query (`max_records == 0`) NEVER refuses on `from < filter_oldest`; it answers `Mark`
//!   carrying `oldest = filter_oldest`,
//! - Plain `Fetch` (`told_fetch == false`) with `from < filter_oldest` and no complete coverage
//!   refuses `ERR_RECORD_REFUSED` (`retained-from=<filter_oldest>`) instead of clamping silently,
//! - Told `Fetch` (`told_fetch == true`) with `from < filter_oldest`:
//!   * If `held_records_below_oldest > 0` OR `bounded_scan_exhausted_below_oldest`, emits
//!     `Response::Gap { from, to: filter_oldest }` AHEAD of the page (never after!) and reads on,
//!   * If `held_records_below_oldest == 0` AND `!bounded_scan_exhausted_below_oldest` (even if
//!     the page holds records `>= filter_oldest`), STILL refuses `retained-from=<filter_oldest>`!

#[cfg(clean_islands)]
#[path = "retained_from_told_fetch_notice_guard_island.rs"]
mod retained_from_told_fetch_notice_guard_island;
#[cfg(clean_islands)]
pub use retained_from_told_fetch_notice_guard_island::{
    filter_oldest_advance_b150, gap_from_clamp_b150,
};

#[cfg(not(clean_islands))]
/// Clamp reported gap start so `gap_from <= filter_oldest`.
#[must_use]
pub const fn gap_from_clamp_b150(req_from: u64, filter_oldest: u64) -> u64 {
    if req_from < filter_oldest {
        req_from
    } else {
        filter_oldest
    }
}

#[cfg(not(clean_islands))]
/// Advance filter's `oldest` complete offset monotonically across retention cuts.
#[must_use]
pub const fn filter_oldest_advance_b150(cur_oldest: u64, cand_oldest: u64) -> u64 {
    if cur_oldest < cand_oldest {
        cand_oldest
    } else {
        cur_oldest
    }
}

contract_fn! {
    /// True iff a told fetch (`from < filter_oldest`) holds surviving records or scan budget ran out below `oldest`.
    #[must_use]
    pub const fn told_fetch_reads_on_below_oldest_b150(
        told_fetch: bool,
        held_below_oldest: u64,
        scan_exhausted_below_oldest: bool,
    ) -> bool
    clauses [ensures result == (told_fetch && (held_below_oldest > 0 || scan_exhausted_below_oldest))]
    {
        told_fetch && (held_below_oldest > 0 || scan_exhausted_below_oldest)
    }
}

/// Wire reply plan for `Fetch` / `fetch_told` against a retained log.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RetainedFetchDecision {
    HeadQueryMarkOnly {
        oldest_trailer: u64,
    },
    CompleteRangePageNoGap {
        from: u64,
        oldest_trailer: u64,
    },
    EmitGapAheadOfPageAndReadOn {
        gap_from: u64,
        gap_to: u64,
        held_below_oldest: u64,
    },
    RefusedRetainedFrom {
        retained_from: u64,
    },
}

/// Evaluates `Fetch` / `fetch_told` wire behavior against monotonic `filter_oldest`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RetainedFetchPlanner {
    filter_oldest: u64,
}

impl RetainedFetchPlanner {
    #[must_use]
    pub const fn new(initial_oldest: u64) -> Self {
        Self {
            filter_oldest: initial_oldest,
        }
    }

    pub fn advance_filter_oldest(&mut self, cand_oldest: u64) -> u64 {
        self.filter_oldest = filter_oldest_advance_b150(self.filter_oldest, cand_oldest);
        self.filter_oldest
    }

    #[must_use]
    pub const fn plan_fetch(
        &self,
        req_from: u64,
        max_records: u64,
        told_fetch: bool,
        held_below_oldest: u64,
        scan_exhausted_below_oldest: bool,
    ) -> RetainedFetchDecision {
        if max_records == 0 {
            return RetainedFetchDecision::HeadQueryMarkOnly {
                oldest_trailer: self.filter_oldest,
            };
        }
        if req_from >= self.filter_oldest {
            return RetainedFetchDecision::CompleteRangePageNoGap {
                from: req_from,
                oldest_trailer: self.filter_oldest,
            };
        }
        if told_fetch_reads_on_below_oldest_b150(
            told_fetch,
            held_below_oldest,
            scan_exhausted_below_oldest,
        ) {
            let gf = gap_from_clamp_b150(req_from, self.filter_oldest);
            RetainedFetchDecision::EmitGapAheadOfPageAndReadOn {
                gap_from: gf,
                gap_to: self.filter_oldest,
                held_below_oldest,
            }
        } else {
            RetainedFetchDecision::RefusedRetainedFrom {
                retained_from: self.filter_oldest,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_head_query_exemption_plain_refusal_and_told_fetch_held_or_scan_exhausted_rules() {
        let mut p = RetainedFetchPlanner::new(151);
        // Head query (max_records=0) at from=0 never refuses:
        assert_eq!(
            p.plan_fetch(0, 0, false, 0, false),
            RetainedFetchDecision::HeadQueryMarkOnly {
                oldest_trailer: 151,
            }
        );
        // Plain fetch from 5 (< 151) refuses `retained-from=151`:
        assert_eq!(
            p.plan_fetch(5, 64, false, 2, false),
            RetainedFetchDecision::RefusedRetainedFrom { retained_from: 151 }
        );
        // Told fetch holding 0 records below 151 (and scan not exhausted) STILL refuses!
        assert_eq!(
            p.plan_fetch(5, 64, true, 0, false),
            RetainedFetchDecision::RefusedRetainedFrom { retained_from: 151 }
        );
        // Told fetch holding unread mail below 151 emits Gap(5..151) AHEAD of page and reads on!
        assert_eq!(
            p.plan_fetch(5, 64, true, 2, false),
            RetainedFetchDecision::EmitGapAheadOfPageAndReadOn {
                gap_from: 5,
                gap_to: 151,
                held_below_oldest: 2,
            }
        );
        assert_eq!(p.advance_filter_oldest(200), 200);
    }
}
