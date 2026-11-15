// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Segmented broker log seal & RAM-resident payload eviction fence
//! (`Astream.Broker.TlaBrokerSegmentSealFence`).
//!
//! Bounds the in-RAM hot segment byte footprint during multi-day `aterm` fleet
//! runs by maintaining the 3-watermark invariant
//! `evicted_before <= sealed_before <= hw_offset` and bounding active hot bytes
//! to `<= max_segment_bytes`.

#[cfg(clean_islands)]
#[path = "broker_segment_seal_fence_island.rs"]
mod broker_segment_seal_fence_island;
#[cfg(clean_islands)]
pub use broker_segment_seal_fence_island::{
    seg_hot_bytes_clamp, seg_hw_advance, seg_watermark_clamp,
};

#[cfg(not(clean_islands))]
/// Monotonically advance high-water offset.
#[must_use]
pub const fn seg_hw_advance(cur_hw: u64, cand_hw: u64) -> u64 {
    if cur_hw < cand_hw {
        cand_hw
    } else {
        cur_hw
    }
}

#[cfg(not(clean_islands))]
/// Clamp a lower watermark (`evicted_before` or `sealed_before`) to `ceiling`.
#[must_use]
pub const fn seg_watermark_clamp(cand_mark: u64, ceiling: u64) -> u64 {
    if cand_mark < ceiling {
        cand_mark
    } else {
        ceiling
    }
}

#[cfg(not(clean_islands))]
/// Clamp hot in-RAM segment byte tally to `max_seg_bytes`.
#[must_use]
pub const fn seg_hot_bytes_clamp(cand_bytes: u64, max_seg_bytes: u64) -> u64 {
    if cand_bytes < max_seg_bytes {
        cand_bytes
    } else {
        max_seg_bytes
    }
}

/// Action returned when appending a record to the active segment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SegmentAppendDecision {
    AppendedHot {
        hw_offset: u64,
        hot_bytes: u64,
    },
    RollAndSealSegment {
        sealed_before: u64,
        hw_offset: u64,
        hot_bytes: u64,
    },
}

/// Pure stack 3-watermark segment roll & RAM-eviction fence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BrokerSegmentSealFence {
    max_segment_bytes: u64,
    evicted_before: u64,
    sealed_before: u64,
    hw_offset: u64,
    hot_bytes: u64,
}

impl BrokerSegmentSealFence {
    #[must_use]
    pub const fn new(base_offset: u64, max_segment_bytes: u64) -> Self {
        let cap = if max_segment_bytes == 0 {
            4096
        } else {
            max_segment_bytes
        };
        Self {
            max_segment_bytes: cap,
            evicted_before: base_offset,
            sealed_before: base_offset,
            hw_offset: base_offset,
            hot_bytes: 0,
        }
    }

    #[must_use]
    pub const fn evicted_before(&self) -> u64 {
        self.evicted_before
    }

    #[must_use]
    pub const fn sealed_before(&self) -> u64 {
        self.sealed_before
    }

    #[must_use]
    pub const fn hw_offset(&self) -> u64 {
        self.hw_offset
    }

    #[must_use]
    pub const fn hot_bytes(&self) -> u64 {
        self.hot_bytes
    }

    /// Record an append of `record_bytes` and roll the hot segment if `max_segment_bytes` would overflow.
    pub fn record_append(&mut self, record_bytes: u64) -> SegmentAppendDecision {
        let next_hw = self.hw_offset.saturating_add(1);
        let would_use = self.hot_bytes.saturating_add(record_bytes);
        if self.hot_bytes > 0 && would_use > self.max_segment_bytes {
            // Seal everything up to current `hw_offset` before placing new record in fresh segment:
            let next_sealed = seg_hw_advance(self.sealed_before, self.hw_offset);
            self.sealed_before = seg_watermark_clamp(next_sealed, next_hw);
            self.evicted_before = seg_watermark_clamp(self.evicted_before, self.sealed_before);
            self.hw_offset = seg_hw_advance(self.hw_offset, next_hw);
            self.hot_bytes = seg_hot_bytes_clamp(record_bytes, self.max_segment_bytes);
            SegmentAppendDecision::RollAndSealSegment {
                sealed_before: self.sealed_before,
                hw_offset: self.hw_offset,
                hot_bytes: self.hot_bytes,
            }
        } else {
            self.hw_offset = seg_hw_advance(self.hw_offset, next_hw);
            self.hot_bytes = seg_hot_bytes_clamp(would_use, self.max_segment_bytes);
            SegmentAppendDecision::AppendedHot {
                hw_offset: self.hw_offset,
                hot_bytes: self.hot_bytes,
            }
        }
    }

    /// Evict sealed cold-segment bytes from RAM up to `candidate_evict_before` (clamped to `sealed_before`).
    pub fn evict_sealed_ram(&mut self, candidate_evict_before: u64) -> u64 {
        let next_evict = seg_hw_advance(self.evicted_before, candidate_evict_before);
        self.evicted_before = seg_watermark_clamp(next_evict, self.sealed_before);
        self.evicted_before
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preserves_three_watermark_order_across_roll_and_ram_eviction() {
        let mut fence = BrokerSegmentSealFence::new(100, 1024);
        assert_eq!(
            fence.record_append(600),
            SegmentAppendDecision::AppendedHot {
                hw_offset: 101,
                hot_bytes: 600,
            }
        );
        // Second 600B append overflows 1024B -> seals [100..101) and starts fresh segment:
        assert_eq!(
            fence.record_append(600),
            SegmentAppendDecision::RollAndSealSegment {
                sealed_before: 101,
                hw_offset: 102,
                hot_bytes: 600,
            }
        );
        // Evicting past sealed_before (e.g. 999) clamps safely at `sealed_before == 101`!
        assert_eq!(fence.evict_sealed_ram(999), 101);
        assert!(fence.evicted_before() <= fence.sealed_before());
        assert!(fence.sealed_before() <= fence.hw_offset());
    }
}
