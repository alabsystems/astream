// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! CRC-indexed hot/cold scrollback chunk tiering with active-selection pin protection
//! (`Astream.Restore.TlaScrollbackTier`).

use astream_wire::crc32_ieee;
use std::collections::VecDeque;

#[cfg(clean_islands)]
#[path = "scrollback_tier_island.rs"]
mod scrollback_tier_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sb_hot_chunks_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sb_evicted_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use scrollback_tier_island::{sb_evicted_advance, sb_hot_chunks_clamp};

/// Maximum hot uncompressed scrollback chunks kept in RAM per tab.
pub const MAX_HOT_SCROLLBACK_CHUNKS: u64 = 256;

contract_fn! {
    /// Verified pin guard (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sb_pinned_safe_isl`.
    #[must_use]
    pub const fn sb_pinned_safe(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScrollbackChunkMeta {
    pub chunk_id: u64,
    pub byte_len: u32,
    pub crc32: u32,
}

/// Hot-RAM to disk-spilled scrollback tier manager that never evicts a user's active selection!
#[derive(Debug, Clone)]
pub struct ScrollbackTierLedger {
    max_hot: u64,
    evicted_watermark: u64,
    pinned_from_chunk: Option<u64>,
    hot: VecDeque<(ScrollbackChunkMeta, Vec<u8>)>,
}

#[inline(never)]
fn crc32_sum(bytes: &[u8]) -> u32 {
    crc32_ieee(bytes)
}

impl ScrollbackTierLedger {
    #[must_use]
    pub const fn new(max_hot: u64) -> Self {
        let c = sb_hot_chunks_clamp(max_hot, MAX_HOT_SCROLLBACK_CHUNKS);
        Self {
            max_hot: if c == 0 { 1 } else { c },
            evicted_watermark: 0,
            pinned_from_chunk: None,
            hot: VecDeque::new(),
        }
    }

    pub fn set_selection_pin(&mut self, from_chunk: Option<u64>) {
        self.pinned_from_chunk = from_chunk;
    }

    /// Pushes a hot chunk (`chunk_id`) and returns any oldest unpinned chunk spilled to cold disk.
    pub fn push_hot_chunk(
        &mut self,
        chunk_id: u64,
        bytes: Vec<u8>,
    ) -> Option<(ScrollbackChunkMeta, Vec<u8>)> {
        let meta = ScrollbackChunkMeta {
            chunk_id,
            byte_len: bytes.len() as u32,
            crc32: crc32_sum(&bytes),
        };
        let mut spilled = None;
        if (self.hot.len() as u64) >= self.max_hot {
            let hard_cap_hit = (self.hot.len() as u64) >= MAX_HOT_SCROLLBACK_CHUNKS;
            let can_evict = match (self.hot.front(), self.pinned_from_chunk) {
                (Some((front_m, _)), Some(pin_id)) => {
                    hard_cap_hit || !sb_pinned_safe(front_m.chunk_id, pin_id)
                }
                (Some(_), None) => true,
                (None, _) => false,
            };
            if can_evict {
                if let Some((ev_m, ev_b)) = self.hot.pop_front() {
                    self.evicted_watermark =
                        sb_evicted_advance(self.evicted_watermark, ev_m.chunk_id.saturating_add(1));
                    spilled = Some((ev_m, ev_b));
                }
            }
        }
        self.hot.push_back((meta, bytes));
        spilled
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scrollback_tier_spills_oldest_unpinned_chunk_and_protects_pinned_selection() {
        let mut sb = ScrollbackTierLedger::new(2);
        assert!(sb.push_hot_chunk(1, b"row-1".to_vec()).is_none());
        assert!(sb.push_hot_chunk(2, b"row-2".to_vec()).is_none());
        let (m, _) = sb.push_hot_chunk(3, b"row-3".to_vec()).unwrap();
        assert_eq!(m.chunk_id, 1);

        // Pin chunk 2 -> pushing chunk 4 must NOT evict chunk 2!
        sb.set_selection_pin(Some(2));
        assert!(sb.push_hot_chunk(4, b"row-4".to_vec()).is_none());
    }
}
