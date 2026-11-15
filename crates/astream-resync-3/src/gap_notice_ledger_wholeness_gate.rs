// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `TAG_GAP` (`0x87`) retention drop ledger wholeness & `owed_range` advancement gate
//! (`docs/REQUIREMENTS-fabric-operations-2026-09-14.md` R4 Addendum A9 lines 195–267;
//! `Astream.Broker.TlaGapNoticeLedgerWholenessGate`).
//!
//! Enforces the exact `Gap { from, to, known, records }` soundness rules of Addendum A9:
//! - A count (`known = true, records = N`) is emitted ONLY when `ledger_whole_from <= cursor` AND
//!   `all_classes_countable_hold` AND `max_class_since <= cursor`; otherwise `known = false`!
//! - A look that tells nothing (`known && newly_dropped == 0`, or `!known` on an already-uncounted
//!   range) leaves `told_up_to` UNMOVED so a later uncounted spill inside the range is still told!
//! - A range previously told WITH a count (`told_was_counted == true`) is told AGAIN with `known = false`
//!   if a subsequent give-up inside `[cursor, filter_oldest)` makes the ledger uncountable!
//! - For `fetch_told` below `filter_oldest`, a bounded scan (`FETCH_SCAN_MAX = 65_536`) that stops
//!   below `filter_oldest` with `0` matched records answers as HOLDING (empty page told, `next` moves)
//!   rather than falsely refusing `ERR retained-from=<filter_oldest>`!

#[cfg(clean_islands)]
#[path = "gap_notice_ledger_wholeness_gate_island.rs"]
mod gap_notice_ledger_wholeness_gate_island;
#[cfg(clean_islands)]
pub use gap_notice_ledger_wholeness_gate_island::{
    gap_ledger_entries_clamp_b138, gap_told_floor_advance_b138,
};

/// Bounded in-memory retention drop ledger entry cap (`65_536` entries).
pub const GAP_LEDGER_MAX_ENTRIES: u64 = 65_536;

/// Bounded `Fetch` scan step limit (`65_536` records).
pub const FETCH_SCAN_MAX_RECORDS: u64 = 65_536;

#[cfg(not(clean_islands))]
/// Clamp in-memory drop-ledger entry count to `ledger_cap` (`65_536`).
#[must_use]
pub const fn gap_ledger_entries_clamp_b138(cand_entries: u64, ledger_cap: u64) -> u64 {
    if cand_entries < ledger_cap {
        cand_entries
    } else {
        ledger_cap
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `told_up_to` watermark ONLY when a notice actually fires.
#[must_use]
pub const fn gap_told_floor_advance_b138(cur_told: u64, cand_told: u64) -> u64 {
    if cur_told < cand_told {
        cand_told
    } else {
        cur_told
    }
}

contract_fn! {
    /// True iff `all_classes_countable_hold && ledger_whole_from <= cursor && max_class_since <= cursor`.
    #[must_use]
    pub const fn gap_count_is_known_b138(
        all_classes_countable_hold: bool,
        ledger_whole_from: u64,
        max_class_since: u64,
        cursor: u64,
    ) -> bool
    clauses [ensures result == (all_classes_countable_hold && ledger_whole_from <= cursor && max_class_since <= cursor)]
    {
        all_classes_countable_hold && ledger_whole_from <= cursor && max_class_since <= cursor
    }
}

/// Outbound `TAG_GAP` (`0x87`) decision before delivering or paging from `cursor < filter_oldest`.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum GapNoticeDecision {
    /// Cursor is at or above `filter_oldest`, or nothing new to tell right now (`told_up_to` stays put!).
    NoNoticeNeeded,
    /// Emit `Gap { from, to, known: true, records }` ahead of records!
    EmitCountedGap { from: u64, to: u64, records: u64 },
    /// Emit `Gap { from, to, known: false, records: 0 }` (range alone, never a guess!).
    EmitUncountedRangeGap { from: u64, to: u64 },
}

/// `fetch_told` below-`oldest` page classification (Addendum A9 lines 245–265).
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum FetchToldBelowOldestVerdict {
    /// Filter holds records (or scan hit `FETCH_SCAN_MAX` below `oldest`): return page + `next`!
    DeliverHeldPage { next_offset: u64 },
    /// Scan reached `>= filter_oldest` with `0` held matches in `[from, filter_oldest)`: answer `ERR retained-from=<oldest>`!
    RefuseRetainedFrom { oldest: u64 },
}

/// Classify a `fetch_told` scan starting at `from < filter_oldest`.
#[must_use]
pub const fn classify_fetch_told_scan(
    from: u64,
    filter_oldest: u64,
    matched_below_oldest: u64,
    scan_next_offset: u64,
) -> FetchToldBelowOldestVerdict {
    if from >= filter_oldest || matched_below_oldest > 0 || scan_next_offset < filter_oldest {
        // Note A9 line 263: when `scan_next_offset < filter_oldest` even with 0 matches,
        // the bounded scan ran out before reaching `oldest` and MUST answer as holding!
        FetchToldBelowOldestVerdict::DeliverHeldPage {
            next_offset: scan_next_offset,
        }
    } else {
        FetchToldBelowOldestVerdict::RefuseRetainedFrom {
            oldest: filter_oldest,
        }
    }
}

/// Per-tail `Gap` notice wholeness & `told_up_to` state machine.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct TailGapNoticeGate {
    ledger_cap: u64,
    ledger_entries: u64,
    told_up_to: u64,
    told_was_counted: bool,
    told_records_sum: u64,
}

impl TailGapNoticeGate {
    #[must_use]
    pub const fn new(initial_cursor: u64) -> Self {
        Self {
            ledger_cap: GAP_LEDGER_MAX_ENTRIES,
            ledger_entries: 0,
            told_up_to: initial_cursor,
            told_was_counted: true,
            told_records_sum: 0,
        }
    }

    #[must_use]
    pub const fn ledger_entries(&self) -> u64 {
        gap_ledger_entries_clamp_b138(self.ledger_entries, self.ledger_cap)
    }

    #[must_use]
    pub const fn told_up_to(&self) -> u64 {
        self.told_up_to
    }

    pub fn set_ledger_entries(&mut self, entries: u64) {
        self.ledger_entries = gap_ledger_entries_clamp_b138(entries, self.ledger_cap);
    }

    /// Evaluate whether a tail at `cursor` against `filter_oldest` owes a `Gap` frame right now.
    pub fn evaluate_tail_gap(
        &mut self,
        cursor: u64,
        filter_oldest: u64,
        all_classes_countable_hold: bool,
        ledger_whole_from: u64,
        max_class_since: u64,
        total_dropped_in_range: u64,
    ) -> GapNoticeDecision {
        if cursor >= filter_oldest {
            return GapNoticeDecision::NoNoticeNeeded;
        }
        let known = gap_count_is_known_b138(
            all_classes_countable_hold,
            ledger_whole_from,
            max_class_since,
            cursor,
        );
        if known {
            let newly_dropped = total_dropped_in_range.saturating_sub(self.told_records_sum);
            if newly_dropped == 0 {
                // A9 line 218: a look that counted 0 leaves `told_up_to` unmoved!
                return GapNoticeDecision::NoNoticeNeeded;
            }
            self.told_up_to = gap_told_floor_advance_b138(self.told_up_to, filter_oldest);
            self.told_was_counted = true;
            self.told_records_sum = total_dropped_in_range;
            GapNoticeDecision::EmitCountedGap {
                from: cursor,
                to: filter_oldest,
                records: newly_dropped,
            }
        } else {
            if filter_oldest <= self.told_up_to && !self.told_was_counted {
                // Range already told with `known = false`: covers every later give-up inside it!
                return GapNoticeDecision::NoNoticeNeeded;
            }
            // Either `filter_oldest > told_up_to` OR range was previously counted and lost wholeness!
            self.told_up_to = gap_told_floor_advance_b138(self.told_up_to, filter_oldest);
            self.told_was_counted = false;
            GapNoticeDecision::EmitUncountedRangeGap {
                from: cursor,
                to: filter_oldest,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_count_spill_leaves_range_owed_and_lost_wholeness_re_tells_uncounted_range() {
        let mut g = TailGapNoticeGate::new(10);
        // Spill widens `filter_oldest` to 50 with 0 dropped records of this filter -> tells nothing & keeps `told_up_to == 10`!
        assert_eq!(
            g.evaluate_tail_gap(10, 50, true, 0, 0, 0),
            GapNoticeDecision::NoNoticeNeeded
        );
        assert_eq!(g.told_up_to(), 10);
        // Later 3 records in `[10, 50)` are dropped -> counted notice `[10, 50), records = 3`:
        assert_eq!(
            g.evaluate_tail_gap(10, 50, true, 0, 0, 3),
            GapNoticeDecision::EmitCountedGap {
                from: 10,
                to: 50,
                records: 3
            }
        );
        // Ledger overflows (`ledger_whole_from = 25 > 10`) inside `[10, 50)` -> re-told once as uncounted range!
        assert_eq!(
            g.evaluate_tail_gap(10, 50, true, 25, 0, 3),
            GapNoticeDecision::EmitUncountedRangeGap { from: 10, to: 50 }
        );
        // Subsequent poll on same `[10, 50)` uncounted range is silent:
        assert_eq!(
            g.evaluate_tail_gap(10, 50, true, 25, 0, 4),
            GapNoticeDecision::NoNoticeNeeded
        );
        // `fetch_told` scan running out at 65_546 < oldest 100_000 with 0 matches answers as holding!
        assert_eq!(
            classify_fetch_told_scan(10, 100_000, 0, 65_546),
            FetchToldBelowOldestVerdict::DeliverHeldPage {
                next_offset: 65_546
            }
        );
        assert_eq!(
            classify_fetch_told_scan(65_546, 100_000, 0, 100_000),
            FetchToldBelowOldestVerdict::RefuseRetainedFrom { oldest: 100_000 }
        );
    }
}
