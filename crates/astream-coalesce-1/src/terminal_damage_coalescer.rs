// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Inline-bitset terminal dirty-row damage tracker & contiguous span coalescer.
//!
//! Tracks row-level visual damage across up to [`MAX_DAMAGE_ROWS`] (`512`) rows in a
//! fixed `[u64; 8]` stack bitset (zero heap allocation while painting, zero closures,
//! `0 mandated`) and coalesces adjacent dirty rows separated by `<= max_gap_rows` clean
//! rows into minimal `(start_row, end_row_exclusive)` spans — or upgrades to a full
//! keyframe sync when dirty coverage reaches `keyframe_pct`.
//! Backed by Clean TLA+ island `Astream.Term.TlaDirtyRowCoalescer`.

#![allow(clippy::assign_op_pattern)]

#[cfg(clean_islands)]
#[path = "terminal_damage_coalescer_island.rs"]
mod terminal_damage_coalescer_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn damage_rows_clamp(proposed_rows: u64, max_rows: u64) -> u64 {
    if proposed_rows < max_rows {
        proposed_rows
    } else {
        max_rows
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn damage_dirty_clamp(dirty_rows: u64, total_rows: u64) -> u64 {
    if dirty_rows < total_rows {
        dirty_rows
    } else {
        total_rows
    }
}
#[cfg(clean_islands)]
pub use terminal_damage_coalescer_island::{damage_dirty_clamp, damage_rows_clamp};

contract_fn! {
    /// Kernel-certified bounds check that `row` lies strictly within `total_rows`
    /// (`row < total_rows`), linked via `clean-kernel-defeq` to `damage_row_in_bounds_isl`.
    #[must_use]
    pub const fn damage_row_in_bounds(row: u64, total_rows: u64) -> bool
    clauses [ensures result == (row < total_rows)]
    {
        row < total_rows
    }
}

/// Maximum terminal rows tracked inline (`8 * 64 = 512`, matching `screen::MAX_DIM`).
pub const MAX_DAMAGE_ROWS: u16 = 512;
const BITSET_WORDS: usize = 8;

/// Half-open dirty row span `[start_row, end_row)` ready for delta wire transmission.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DirtyRowSpan {
    /// Inclusive first dirty row (`< end_row`).
    pub start_row: u16,
    /// Exclusive end row (`<= total_rows`).
    pub end_row: u16,
}

/// Flush plan computed by [`ScreenDamageTracker::drain_plan`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DamageFlushPlan {
    /// Zero rows changed since last flush.
    Clean,
    /// Coalesced delta spans covering all modified rows.
    DeltaSpans(Vec<DirtyRowSpan>),
    /// Full-screen keyframe warranted (resize, altscreen switch, or dirty ratio `>= keyframe_pct`).
    FullKeyframe { total_rows: u16 },
}

/// Zero-allocation `[u64; 8]` dirty-row damage accumulator for `astream_term::Screen`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ScreenDamageTracker {
    bits: [u64; BITSET_WORDS],
    dirty_rows: u16,
    total_rows: u16,
    force_keyframe: bool,
}

impl ScreenDamageTracker {
    /// Construct a clean [`ScreenDamageTracker`] for `rows` (`1..=MAX_DAMAGE_ROWS`).
    #[must_use]
    pub const fn new(rows: u16) -> Self {
        let non_zero = if rows == 0 { 1 } else { rows };
        let clamped = damage_rows_clamp(non_zero as u64, MAX_DAMAGE_ROWS as u64) as u16;
        Self {
            bits: [0u64; BITSET_WORDS],
            dirty_rows: 0,
            total_rows: clamped,
            force_keyframe: false,
        }
    }

    /// Configured terminal row count (`1..=MAX_DAMAGE_ROWS`).
    #[must_use]
    pub const fn total_rows(&self) -> u16 {
        self.total_rows
    }

    /// Number of distinct dirty rows currently marked (`<= total_rows`).
    #[must_use]
    pub const fn dirty_rows(&self) -> u16 {
        self.dirty_rows
    }

    /// Test whether `row` is currently marked dirty.
    #[must_use]
    pub fn is_row_dirty(&self, row: u16) -> bool {
        if !damage_row_in_bounds(row as u64, self.total_rows as u64) {
            return false;
        }
        let word = (row as usize) / 64;
        let bit = ((row as u32) % 64) & 63;
        match self.bits.get(word) {
            Some(&w) => (w & (1u64 << bit)) != 0,
            None => false,
        }
    }

    /// Mark a single `row` dirty if in bounds (`row < total_rows`).
    pub fn mark_row(&mut self, row: u16) {
        if !damage_row_in_bounds(row as u64, self.total_rows as u64) {
            return;
        }
        let word = (row as usize) / 64;
        let bit = ((row as u32) % 64) & 63;
        let Some(slot) = self.bits.get_mut(word) else {
            return;
        };
        let mask = 1u64 << bit;
        if (*slot & mask) == 0 {
            *slot = *slot | mask;
            self.dirty_rows = damage_dirty_clamp(
                (self.dirty_rows as u64).saturating_add(1),
                self.total_rows as u64,
            ) as u16;
        }
    }

    /// Mark inclusive range `start_row..=end_row_inclusive` dirty (e.g. scroll region).
    pub fn mark_range_inclusive(&mut self, start_row: u16, end_row_inclusive: u16) {
        if start_row > end_row_inclusive {
            return;
        }
        let mut r = start_row;
        while r <= end_row_inclusive && damage_row_in_bounds(r as u64, self.total_rows as u64) {
            self.mark_row(r);
            let Some(next) = r.checked_add(1) else {
                break;
            };
            r = next;
        }
    }

    /// Resize the tracked grid to `new_rows` and latch `FullKeyframe` for the next flush.
    pub fn on_resize_or_altscreen(&mut self, new_rows: u16) {
        let non_zero = if new_rows == 0 { 1 } else { new_rows };
        self.total_rows = damage_rows_clamp(non_zero as u64, MAX_DAMAGE_ROWS as u64) as u16;
        self.bits = [0u64; BITSET_WORDS];
        self.dirty_rows = self.total_rows;
        let mut r = 0u16;
        while r < self.total_rows {
            let word = (r as usize) / 64;
            let bit = ((r as u32) % 64) & 63;
            if let Some(slot) = self.bits.get_mut(word) {
                *slot = *slot | (1u64 << bit);
            }
            r = r.saturating_add(1);
        }
        self.force_keyframe = true;
    }

    /// Drain all accumulated damage into a [`DamageFlushPlan`], coalescing dirty rows
    /// separated by `<= max_gap_rows` clean rows and upgrading to `FullKeyframe` when
    /// `(dirty_rows * 100) >= (total_rows * keyframe_pct)`.
    pub fn drain_plan(&mut self, max_gap_rows: u16, keyframe_pct: u8) -> DamageFlushPlan {
        if self.dirty_rows == 0 && !self.force_keyframe {
            return DamageFlushPlan::Clean;
        }
        let pct = (if keyframe_pct < 100 {
            keyframe_pct
        } else {
            100
        }) as u64;
        let promote_keyframe = self.force_keyframe
            || ((self.dirty_rows as u64).saturating_mul(100)
                >= (self.total_rows as u64).saturating_mul(pct)
                && pct > 0);

        let rows = self.total_rows;
        let mut spans = Vec::new();
        if !promote_keyframe {
            let mut r = 0u16;
            while r < rows {
                if !self.is_row_dirty(r) {
                    r = r.saturating_add(1);
                    continue;
                }
                let start = r;
                let mut end = r.saturating_add(1);
                loop {
                    // Look ahead up to `max_gap_rows + 1` rows for another dirty row to coalesce.
                    let mut probe = end;
                    let raw_lim = end.saturating_add(max_gap_rows);
                    let row_last = rows.saturating_sub(1);
                    let limit = if raw_lim < row_last {
                        raw_lim
                    } else {
                        row_last
                    };
                    let mut found_next = None;
                    while probe <= limit && probe < rows {
                        if self.is_row_dirty(probe) {
                            found_next = Some(probe);
                            break;
                        }
                        probe = probe.saturating_add(1);
                    }
                    match found_next {
                        Some(hit) => {
                            end = hit.saturating_add(1);
                        }
                        None => break,
                    }
                }
                spans.push(DirtyRowSpan {
                    start_row: start,
                    end_row: end,
                });
                r = end;
            }
        }

        self.bits = [0u64; BITSET_WORDS];
        self.dirty_rows = 0;
        self.force_keyframe = false;

        if promote_keyframe {
            DamageFlushPlan::FullKeyframe { total_rows: rows }
        } else {
            DamageFlushPlan::DeltaSpans(spans)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn coalesces_nearby_dirty_rows_and_upgrades_heavy_damage_to_keyframe() {
        let mut dt = ScreenDamageTracker::new(24);
        assert_eq!(dt.drain_plan(1, 75), DamageFlushPlan::Clean);

        // Rows 2, 3, and 5 (gap of 1 clean row at 4) + isolated row 20 -> 2 spans: [2, 6) and [20, 21)!
        dt.mark_row(2);
        dt.mark_row(3);
        dt.mark_row(5);
        dt.mark_row(20);
        assert_eq!(dt.dirty_rows(), 4);
        assert_eq!(
            dt.drain_plan(1, 75),
            DamageFlushPlan::DeltaSpans(vec![
                DirtyRowSpan {
                    start_row: 2,
                    end_row: 6
                },
                DirtyRowSpan {
                    start_row: 20,
                    end_row: 21
                },
            ])
        );
        assert_eq!(dt.dirty_rows(), 0);

        // Marking 18 of 24 rows (75%) triggers `FullKeyframe`!
        dt.mark_range_inclusive(0, 17);
        assert_eq!(
            dt.drain_plan(1, 75),
            DamageFlushPlan::FullKeyframe { total_rows: 24 }
        );
    }
}
