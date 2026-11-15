// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `TAG_LAST` (`0x09`) bounded index scan (`LAST_PAGE_MAX = 4_096`, `LAST_SCAN_MAX = 65_536`)
//! & `Mark.resume` cursor completeness gate (`docs/DESIGN-aterm-fabric.md` §11.1 lines 2856–2869,
//! 2935–2948; `Astream.Broker.TlaLastScanResumeCursorGate`).
//!
//! Enforces the two non-obvious pagination invariants of `Last`:
//! - A page shorter than `max` — EVEN AN EMPTY PAGE (`delivered == 0`) — is NOT the end of the
//!   scan when `visited == LAST_SCAN_MAX` (`65_536`) and entries remain in range; ONLY an empty
//!   `Mark.resume` (`has_resume == false`) signals completion, while a truncated `Mark` frame
//!   missing the trailing `resume` length prefix is refused as malformed!
//! - Every emitted non-empty `resume` subject MUST match the caller's filter (`resume_matches_filter`)
//!   so a guarded connection never leaks an unauthorized subject name via `Mark.resume`, and
//!   strictly advances `after_rank` (`after_rank < resume_rank`) on every page!

#[cfg(clean_islands)]
#[path = "last_scan_resume_cursor_gate_island.rs"]
mod last_scan_resume_cursor_gate_island;
#[cfg(clean_islands)]
pub use last_scan_resume_cursor_gate_island::{
    last_page_clamp_b135, last_resume_rank_advance_b135,
};

/// Maximum `Delivery` rows emitted per `Last` page (`4_096`).
pub const LAST_PAGE_MAX: u64 = 4_096;

/// Maximum `BTreeMap` entries visited (matched OR unmatched) per `Last` page (`65_536`).
pub const LAST_SCAN_MAX: u64 = 65_536;

#[cfg(not(clean_islands))]
/// Clamp caller-requested `max` to `LAST_PAGE_MAX` (`page_cap`).
#[must_use]
pub const fn last_page_clamp_b135(req_max: u64, page_cap: u64) -> u64 {
    if req_max < page_cap {
        req_max
    } else {
        page_cap
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance lexicographic `after` cursor rank across `Last` pages.
#[must_use]
pub const fn last_resume_rank_advance_b135(cur_rank: u64, cand_rank: u64) -> u64 {
    if cur_rank < cand_rank {
        cand_rank
    } else {
        cur_rank
    }
}

contract_fn! {
    /// True iff `has_resume_field && (!has_nonempty_resume || (resume_matches_filter && after_rank < resume_rank))`.
    #[must_use]
    pub const fn last_mark_well_formed_b135(
        has_resume_field: bool,
        has_nonempty_resume: bool,
        resume_matches_filter: bool,
        after_rank: u64,
        resume_rank: u64,
    ) -> bool
    clauses [ensures result == (has_resume_field && (!has_nonempty_resume || (resume_matches_filter && after_rank < resume_rank)))]
    {
        has_resume_field
            && (!has_nonempty_resume || (resume_matches_filter && after_rank < resume_rank))
    }
}

/// Client-side pagination step verdict after decoding a `Last` page + `Mark`.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum LastPageStepVerdict {
    /// `Mark.resume == ""` (`None`): scan reached the end of the filter's range!
    ScanComplete { delivered_rows: u64 },
    /// Non-empty `Mark.resume`: issue another `Last { after = resume }` (even if `delivered_rows == 0`!).
    ContinueFromCursor {
        delivered_rows: u64,
        next_after_rank: u64,
    },
    /// Truncated `Mark` (missing `resume` field), non-progressing cursor, or filter-leaking `resume`!
    RefusedMalformedMark,
}

/// Client/broker `Last` cursor state machine.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct LastScanCursorMachine {
    page_cap: u64,
    scan_cap: u64,
    after_rank: u64,
    completed: bool,
    total_delivered: u64,
}

impl LastScanCursorMachine {
    #[must_use]
    pub const fn new(initial_after_rank: u64) -> Self {
        Self {
            page_cap: LAST_PAGE_MAX,
            scan_cap: LAST_SCAN_MAX,
            after_rank: initial_after_rank,
            completed: false,
            total_delivered: 0,
        }
    }

    #[must_use]
    pub const fn effective_page_max(&self, req_max: u64) -> u64 {
        last_page_clamp_b135(req_max, self.page_cap)
    }

    #[must_use]
    pub const fn after_rank(&self) -> u64 {
        self.after_rank
    }

    #[must_use]
    pub const fn is_completed(&self) -> bool {
        self.completed
    }

    /// Validate and apply one `Last` response page (`has_resume_field == false` means truncated v2 `Mark`!).
    pub fn apply_page(
        &mut self,
        req_max: u64,
        delivered_rows: u64,
        visited_entries: u64,
        has_resume_field: bool,
        resume_rank: Option<u64>,
        resume_matches_filter: bool,
    ) -> LastPageStepVerdict {
        let clamped_max = self.effective_page_max(req_max);
        if delivered_rows > clamped_max || visited_entries > self.scan_cap {
            return LastPageStepVerdict::RefusedMalformedMark;
        }
        let (has_nonempty, r_rank) = match resume_rank {
            Some(r) => (true, r),
            None => (false, self.after_rank),
        };
        if !last_mark_well_formed_b135(
            has_resume_field,
            has_nonempty,
            resume_matches_filter,
            self.after_rank,
            r_rank,
        ) {
            return LastPageStepVerdict::RefusedMalformedMark;
        }
        self.total_delivered = self.total_delivered.saturating_add(delivered_rows);
        if has_nonempty {
            let next_rank = last_resume_rank_advance_b135(self.after_rank, r_rank);
            self.after_rank = next_rank;
            LastPageStepVerdict::ContinueFromCursor {
                delivered_rows,
                next_after_rank: next_rank,
            }
        } else {
            self.completed = true;
            LastPageStepVerdict::ScanComplete { delivered_rows }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_page_cut_at_last_scan_max_continues_and_truncated_mark_refuses() {
        let mut m = LastScanCursorMachine::new(0);
        // 65_536 unmatched entries visited -> 0 delivered, non-empty filter-matching synthetic resume cursor:
        assert_eq!(
            m.apply_page(4_096, 0, LAST_SCAN_MAX, true, Some(500), true),
            LastPageStepVerdict::ContinueFromCursor {
                delivered_rows: 0,
                next_after_rank: 500
            }
        );
        assert!(!m.is_completed());
        // Truncated 16-byte `Mark` missing `resume` string is refused as malformed (NOT EndOfRange!):
        assert_eq!(
            m.apply_page(4_096, 1, 10, false, None, false),
            LastPageStepVerdict::RefusedMalformedMark
        );
        // Non-advancing cursor (`500 <= 500`) or filter-mismatching `resume` is refused:
        assert_eq!(
            m.apply_page(4_096, 1, 10, true, Some(500), true),
            LastPageStepVerdict::RefusedMalformedMark
        );
        assert_eq!(
            m.apply_page(4_096, 1, 10, true, Some(600), false),
            LastPageStepVerdict::RefusedMalformedMark
        );
        // Final page with empty `resume` (`None`) marks scan complete:
        assert_eq!(
            m.apply_page(4_096, 3, 42, true, None, true),
            LastPageStepVerdict::ScanComplete { delivered_rows: 3 }
        );
        assert!(m.is_completed());
    }
}
