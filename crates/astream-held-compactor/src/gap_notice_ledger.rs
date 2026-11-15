// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! R4 addendum A9 `Response::Gap` (`tag 0x87`) range & count ledger reporting exact evicted record
//! counts when `[cursor .. oldest)` is covered by the in-memory ledger and `None` (`records=unknown`,
//! never a guess) across prefix cuts, restarts, or spill floors (`Astream.HeldComp.TlaGapNoticeLedger`).

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
#[path = "gap_notice_ledger_island.rs"]
mod gap_notice_ledger_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn hc_led_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn hc_told_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use gap_notice_ledger_island::{hc_led_clamp, hc_told_advance};

/// Maximum evicted records tracked in memory per class (`65_536`).
pub const MAX_GAP_LEDGER_ENTRIES: u64 = 65_536;

contract_fn! {
    /// Verified ledger coverage (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `hc_count_exact_isl`.
    #[must_use]
    pub const fn hc_count_exact(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GapNotice {
    pub from: u64,
    pub to: u64,
    pub exact_records: Option<u64>,
}

#[derive(Debug, Clone)]
pub struct GapLedgerState {
    spill_floor: u64,
    told_up_to: u64,
}

impl GapLedgerState {
    #[must_use]
    pub const fn new(spill_floor: u64) -> Self {
        Self {
            spill_floor,
            told_up_to: 0,
        }
    }

    pub fn plan_gap(
        &mut self,
        cursor: u64,
        filter_oldest: u64,
        ledger_counted_in_range: u64,
        restarted_or_unplanned: bool,
    ) -> Option<GapNotice> {
        if cursor >= filter_oldest || self.told_up_to >= filter_oldest {
            return None;
        }
        let span = filter_oldest.saturating_sub(cursor);
        let clamped_cnt = hc_led_clamp(ledger_counted_in_range, MAX_GAP_LEDGER_ENTRIES);
        let exact = if !restarted_or_unplanned
            && clamped_cnt == ledger_counted_in_range
            && ledger_counted_in_range <= span
            && hc_count_exact(cursor, self.spill_floor)
        {
            Some(clamped_cnt)
        } else {
            None
        };
        self.told_up_to = hc_told_advance(self.told_up_to, filter_oldest);
        Some(GapNotice {
            from: cursor,
            to: filter_oldest,
            exact_records: exact,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reports_exact_count_above_spill_floor_and_unknown_after_restart_or_spill() {
        let mut l = GapLedgerState::new(10);
        let g1 = l.plan_gap(12, 20, 3, false).expect("gap");
        assert_eq!(g1.exact_records, Some(3));
        let g2 = l.plan_gap(5, 25, 3, false).expect("spill gap");
        assert_eq!(g2.exact_records, None);
    }
}
