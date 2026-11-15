// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bounded replay cursor stepping across Held + Retained bus records strictly below a `Cut`
//! ceiling (`cursor < cut_exclusive`) in deterministic page batches (`Astream.LinkCut.TlaReplaySliceCursor`).

#[cfg(clean_islands)]
#[path = "replay_slice_cursor_island.rs"]
mod replay_slice_cursor_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lc_page_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lc_cursor_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use replay_slice_cursor_island::{lc_cursor_advance, lc_page_clamp};

/// Maximum records fetched per replay slice step (`512`).
pub const MAX_REPLAY_PAGE: u64 = 512;

contract_fn! {
    /// Verified replay remaining-records check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `lc_below_cut_ceiling_isl`.
    #[must_use]
    pub const fn lc_below_cut_ceiling(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct ReplaySliceCursor {
    next_offset: u64,
    cut_exclusive: u64,
    page_limit: u64,
}

impl ReplaySliceCursor {
    #[must_use]
    pub const fn new(start_offset: u64, cut_exclusive: u64, page_limit: u64) -> Self {
        let lim = lc_page_clamp(page_limit, MAX_REPLAY_PAGE);
        Self {
            next_offset: start_offset,
            cut_exclusive,
            page_limit: if lim == 0 { 1 } else { lim },
        }
    }

    pub fn next_fetch_budget(&mut self, delivered_last_step: u64) -> u64 {
        let cand = self.next_offset.saturating_add(delivered_last_step);
        self.next_offset = lc_cursor_advance(self.next_offset, cand);
        let need_exclusive = self.next_offset.saturating_add(1);
        if !lc_below_cut_ceiling(self.cut_exclusive, need_exclusive) {
            return 0;
        }
        let rem = self.cut_exclusive.saturating_sub(self.next_offset);
        if rem < self.page_limit {
            rem
        } else {
            self.page_limit
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn drains_exact_remaining_records_up_to_cut_and_stops_at_ceiling() {
        let mut c = ReplaySliceCursor::new(0, 150, 64);
        assert_eq!(c.next_fetch_budget(0), 64);
        assert_eq!(c.next_fetch_budget(64), 64);
        assert_eq!(c.next_fetch_budget(64), 22);
        assert_eq!(c.next_fetch_budget(22), 0);
    }
}
