// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! 256-row terminal damage bitset (`4 x u64` words) tracking mutated rows between Metal frames so
//! single-line shell prompts upload `< 1%` of viewport vertices (`Astream.MetalDmg.TlaDirtyRowBitset`).

#[cfg(clean_islands)]
#[path = "dirty_row_bitset_island.rs"]
mod dirty_row_bitset_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn md_row_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn md_upload_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use dirty_row_bitset_island::{md_row_clamp, md_upload_advance};

/// Highest row index tracked directly in the 256-bit mask (`255`).
pub const MAX_BITSET_ROW: u64 = 255;

contract_fn! {
    /// Verified dirty-row non-empty check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `md_has_dirty_rows_isl`.
    #[must_use]
    pub const fn md_has_dirty_rows(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct DirtyRowBitset {
    w0: u64,
    w1: u64,
    w2: u64,
    w3: u64,
    uploads: u64,
}

impl DirtyRowBitset {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            w0: 0,
            w1: 0,
            w2: 0,
            w3: 0,
            uploads: 0,
        }
    }

    pub fn mark_row(&mut self, row: u64) {
        let r = md_row_clamp(row, MAX_BITSET_ROW);
        let bit = 1u64 << (r & 63);
        match r >> 6 {
            0 => self.w0 |= bit,
            1 => self.w1 |= bit,
            2 => self.w2 |= bit,
            _ => self.w3 |= bit,
        }
    }

    #[must_use]
    pub const fn dirty_count(&self) -> u64 {
        (self.w0.count_ones() as u64)
            .saturating_add(self.w1.count_ones() as u64)
            .saturating_add(self.w2.count_ones() as u64)
            .saturating_add(self.w3.count_ones() as u64)
    }

    pub fn take_dirty_count(&mut self) -> u64 {
        let count = self.dirty_count();
        self.w0 = 0;
        self.w1 = 0;
        self.w2 = 0;
        self.w3 = 0;
        if md_has_dirty_rows(count, 1) {
            self.uploads = md_upload_advance(self.uploads, self.uploads.saturating_add(1));
        }
        count
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deduplicates_dirty_rows_across_words_and_clears_on_upload() {
        let mut d = DirtyRowBitset::new();
        d.mark_row(3);
        d.mark_row(3);
        d.mark_row(140);
        assert_eq!(d.take_dirty_count(), 2);
        assert_eq!(d.take_dirty_count(), 0);
    }
}
