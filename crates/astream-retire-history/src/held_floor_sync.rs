// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `<log>.held` per-class spill floor and counted `Gap` range ledger (`R4 addendum A9`,
//! `broker.retention-rules`, `Astream.Retire.TlaHeldFloorSync`).

use std::collections::VecDeque;

#[cfg(clean_islands)]
#[path = "held_floor_sync_island.rs"]
mod held_floor_sync_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn held_ledger_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn held_floor_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use held_floor_sync_island::{held_floor_advance, held_ledger_clamp};

/// Maximum evicted-record offsets retained in the exact gap-count ledger.
pub const MAX_HELD_LEDGER_RANGES: u64 = 128;

contract_fn! {
    /// Verified floor comparison (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `held_gap_needed_isl`.
    #[must_use]
    pub const fn held_gap_needed(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Gap notice emitted to a `Subscribe` or `Fetch` reader below `oldest`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GapNoticeRange {
    pub from: u64,
    pub to: u64,
    /// `Some(n)` when the ledger remained whole across `[from..to)`, `None` (`unknown`) past spill!
    pub lost_records: Option<u64>,
}

/// Bounded spill-floor and evicted-offset ledger matching `broker.retention-rules` (`A9`).
#[derive(Debug, Clone)]
pub struct HeldSpillLedger {
    cap: u64,
    oldest_floor: u64,
    counted_from: u64,
    evicted_offsets: VecDeque<u64>,
}

impl Default for HeldSpillLedger {
    fn default() -> Self {
        Self::new()
    }
}

impl HeldSpillLedger {
    #[must_use]
    pub const fn new() -> Self {
        Self::with_capacity(MAX_HELD_LEDGER_RANGES)
    }

    #[must_use]
    pub const fn with_capacity(cap: u64) -> Self {
        let c = held_ledger_clamp(cap, MAX_HELD_LEDGER_RANGES);
        Self {
            cap: if c == 0 { 1 } else { c },
            oldest_floor: 0,
            counted_from: 0,
            evicted_offsets: VecDeque::new(),
        }
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.evicted_offsets.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.evicted_offsets.is_empty()
    }

    /// Records a rule-planned give-up of `offset`, raising `oldest_floor` to at least `offset + 1`.
    pub fn record_give_up(&mut self, offset: u64) {
        let next_floor = offset.saturating_add(1);
        self.oldest_floor = held_floor_advance(self.oldest_floor, next_floor);
        if offset < self.counted_from {
            return;
        }
        for &existing in &self.evicted_offsets {
            if existing == offset {
                return;
            }
        }
        if (self.evicted_offsets.len() as u64) >= self.cap {
            if let Some(spilled) = self.evicted_offsets.pop_front() {
                self.counted_from =
                    held_floor_advance(self.counted_from, spilled.saturating_add(1));
            }
        }
        self.evicted_offsets.push_back(offset);
    }

    /// Raises `counted_from` and `oldest_floor` on an unplanned cut / restart so counts below
    /// `cut_offset` report `None` (`unknown`) instead of guessing!
    pub fn record_unplanned_spill(&mut self, cut_offset: u64) {
        self.oldest_floor = held_floor_advance(self.oldest_floor, cut_offset);
        self.counted_from = held_floor_advance(self.counted_from, cut_offset);
        while let Some(&front) = self.evicted_offsets.front() {
            if front < cut_offset {
                self.evicted_offsets.pop_front();
            } else {
                break;
            }
        }
    }

    /// Computes a `GapNoticeRange` if `reader_cursor < oldest_floor`.
    #[must_use]
    pub fn gap_for_cursor(&self, reader_cursor: u64) -> Option<GapNoticeRange> {
        if held_gap_needed(reader_cursor, self.oldest_floor) {
            return None;
        }
        let lost_records = if held_gap_needed(reader_cursor, self.counted_from) {
            let mut n = 0u64;
            for &off in &self.evicted_offsets {
                if off >= reader_cursor && off < self.oldest_floor {
                    n = n.saturating_add(1);
                }
            }
            Some(n)
        } else {
            None
        };
        Some(GapNoticeRange {
            from: reader_cursor,
            to: self.oldest_floor,
            lost_records,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn spill_ledger_counts_exact_losses_above_counted_from_and_reports_unknown_after_spill() {
        let mut ledger = HeldSpillLedger::with_capacity(2);
        ledger.record_give_up(3);
        ledger.record_give_up(7);
        assert_eq!(
            ledger.gap_for_cursor(0),
            Some(GapNoticeRange {
                from: 0,
                to: 8,
                lost_records: Some(2)
            })
        );
        // Third give-up spills offset 3 -> counted_from moves to 4, so cursor 0 is now `None` (unknown),
        // while cursor 5 still gets exact count `Some(2)` (offsets 7 and 9)!
        ledger.record_give_up(9);
        assert_eq!(
            ledger.gap_for_cursor(0),
            Some(GapNoticeRange {
                from: 0,
                to: 10,
                lost_records: None
            })
        );
        assert_eq!(
            ledger.gap_for_cursor(5),
            Some(GapNoticeRange {
                from: 5,
                to: 10,
                lost_records: Some(2)
            })
        );
    }
}
