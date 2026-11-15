// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Segmented WAL rotation & binary-searchable base-offset index (`Astream.Engine.TlaSegmentedWalCursor`).
//!
//! Tracks sealed immutable WAL segments `(base_offset, record_count, byte_len)` alongside the
//! active mutable tail segment so long-running `aterm` session journals bound hot RAM and roll
//! cleanly at `(max_records_per_segment, max_bytes_per_segment)`.

#[cfg(clean_islands)]
#[path = "segmented_wal_cursor_island.rs"]
mod segmented_wal_cursor_island;
#[cfg(clean_islands)]
pub use segmented_wal_cursor_island::{seg_base_advance, seg_records_clamp};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn seg_base_advance(cur_base: u64, cand_base: u64) -> u64 {
    if cur_base < cand_base {
        cand_base
    } else {
        cur_base
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn seg_records_clamp(cand_recs: u64, max_recs: u64) -> u64 {
    if cand_recs < max_recs {
        cand_recs
    } else {
        max_recs
    }
}

contract_fn! {
    /// Verified check whether `offset` sits at or above `seg_base`, linked via
    /// `clean-kernel-defeq` to `seg_offset_in_window_isl`.
    #[must_use]
    pub const fn seg_offset_in_window(seg_base: u64, offset: u64) -> bool
    clauses [ensures result == (seg_base <= offset)]
    {
        seg_base <= offset
    }
}

/// Sealed immutable segment descriptor.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SealedWalSegment {
    pub segment_index: u64,
    pub base_offset: u64,
    pub record_count: u64,
    pub byte_len: u64,
}

/// Segmented WAL rotation planner and segment-lookup cursor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SegmentedWalCursor {
    max_records_per_seg: u64,
    max_bytes_per_seg: u64,
    active_segment_index: u64,
    active_base: u64,
    active_records: u64,
    active_bytes: u64,
    sealed: Vec<SealedWalSegment>,
}

impl SegmentedWalCursor {
    #[must_use]
    pub const fn new(max_records_per_seg: u64, max_bytes_per_seg: u64) -> Self {
        let cap_r = if max_records_per_seg == 0 {
            4_096
        } else {
            max_records_per_seg
        };
        let cap_b = if max_bytes_per_seg == 0 {
            16 * 1024 * 1024
        } else {
            max_bytes_per_seg
        };
        Self {
            max_records_per_seg: cap_r,
            max_bytes_per_seg: cap_b,
            active_segment_index: 0,
            active_base: 0,
            active_records: 0,
            active_bytes: 0,
            sealed: Vec::new(),
        }
    }

    #[must_use]
    pub const fn active_base(&self) -> u64 {
        self.active_base
    }

    #[must_use]
    pub const fn active_records(&self) -> u64 {
        self.active_records
    }

    #[must_use]
    pub fn sealed_segments(&self) -> &[SealedWalSegment] {
        &self.sealed
    }

    /// Record an append of `frame_bytes` at the tail, rotating to a fresh segment beforehand if
    /// the active segment has reached `max_records_per_seg` or would exceed `max_bytes_per_seg`.
    pub fn observe_append(&mut self, frame_bytes: u64) -> Option<SealedWalSegment> {
        let mut rolled = None;
        let would_overflow_bytes = self.active_records > 0
            && self.active_bytes.saturating_add(frame_bytes) > self.max_bytes_per_seg;
        if self.active_records >= self.max_records_per_seg || would_overflow_bytes {
            let sealed_seg = SealedWalSegment {
                segment_index: self.active_segment_index,
                base_offset: self.active_base,
                record_count: self.active_records,
                byte_len: self.active_bytes,
            };
            self.sealed.push(sealed_seg);
            let next_base = self.active_base.saturating_add(self.active_records);
            self.active_base = seg_base_advance(self.active_base, next_base);
            self.active_segment_index = self.active_segment_index.saturating_add(1);
            self.active_records = 0;
            self.active_bytes = 0;
            rolled = Some(sealed_seg);
        }
        let next_recs = self.active_records.saturating_add(1);
        self.active_records = seg_records_clamp(next_recs, self.max_records_per_seg);
        self.active_bytes = self.active_bytes.saturating_add(frame_bytes);
        rolled
    }

    /// Locate the segment index owning `offset` (`None` if `offset` exceeds the current head).
    #[must_use]
    pub fn locate_segment(&self, offset: u64) -> Option<u64> {
        let head = self.active_base.saturating_add(self.active_records);
        if offset >= head {
            return None;
        }
        if seg_offset_in_window(self.active_base, offset) {
            return Some(self.active_segment_index);
        }
        let mut rest = self.sealed.as_slice();
        while let &[seg, ref tail @ ..] = rest {
            let seg_end = seg.base_offset.saturating_add(seg.record_count);
            if seg_offset_in_window(seg.base_offset, offset) && offset < seg_end {
                return Some(seg.segment_index);
            }
            rest = tail;
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rolls_segments_monotonically_and_locates_historical_offsets() {
        let mut cur = SegmentedWalCursor::new(3, 1_024);
        assert_eq!(cur.observe_append(200), None);
        assert_eq!(cur.observe_append(200), None);
        assert_eq!(cur.observe_append(200), None);
        // 4th append rolls segment 0 (base=0, count=3) and opens segment 1 at base=3.
        let rolled = cur.observe_append(200).expect("rolled segment 0");
        assert_eq!(rolled.segment_index, 0);
        assert_eq!(rolled.base_offset, 0);
        assert_eq!(rolled.record_count, 3);
        assert_eq!(cur.active_base(), 3);
        assert_eq!(cur.active_records(), 1);

        assert_eq!(cur.locate_segment(0), Some(0));
        assert_eq!(cur.locate_segment(2), Some(0));
        assert_eq!(cur.locate_segment(3), Some(1));
        assert_eq!(cur.locate_segment(4), None);
    }
}
