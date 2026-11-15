// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Metal GPU glyph-atlas tile eviction LRU (`<= 4,096` rasterized glyph slots) keeping printable
//! ASCII resident while evicting cold off-screen CJK/emoji tiles (`Astream.Grapheme.TlaAtlasGlyphLru`).

use std::collections::VecDeque;

#[cfg(clean_islands)]
#[path = "atlas_glyph_lru_island.rs"]
mod atlas_glyph_lru_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn gr_tiles_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn gr_evict_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use atlas_glyph_lru_island::{gr_evict_advance, gr_tiles_clamp};

/// Maximum glyph tiles in one 2D Metal texture page (`4,096`).
pub const MAX_GLYPH_ATLAS_TILES: u64 = 4_096;

contract_fn! {
    /// Verified atlas capacity headroom (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `gr_atlas_has_room_isl`.
    #[must_use]
    pub const fn gr_atlas_has_room(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Tracks rasterized `glyph_hash -> tile_id` residency with bounded LRU eviction.
#[derive(Debug, Clone)]
pub struct GlyphAtlasCache {
    capacity: usize,
    lru: VecDeque<u64>,
    evictions: u64,
}

impl GlyphAtlasCache {
    #[must_use]
    pub const fn new(capacity: u64) -> Self {
        let c = if capacity == 0 { 1 } else { capacity };
        Self {
            capacity: gr_tiles_clamp(c, MAX_GLYPH_ATLAS_TILES) as usize,
            lru: VecDeque::new(),
            evictions: 0,
        }
    }

    /// Touches or inserts `glyph_key`, returning `Some(evicted_key)` when the atlas was full.
    pub fn touch(&mut self, glyph_key: u64) -> Option<u64> {
        let mut found = false;
        for k in core::mem::take(&mut self.lru) {
            if k == glyph_key {
                found = true;
            } else {
                self.lru.push_back(k);
            }
        }
        if found {
            self.lru.push_back(glyph_key);
            return None;
        }
        let mut evicted = None;
        if !gr_atlas_has_room(
            self.capacity as u64,
            (self.lru.len() as u64).saturating_add(1),
        ) {
            evicted = self.lru.pop_front();
            if evicted.is_some() {
                self.evictions = gr_evict_advance(self.evictions, self.evictions.saturating_add(1));
            }
        }
        self.lru.push_back(glyph_key);
        evicted
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn glyph_atlas_lru_promotes_hits_and_evicts_least_recently_used_tile() {
        let mut c = GlyphAtlasCache::new(2);
        assert_eq!(c.touch(0x41), None);
        assert_eq!(c.touch(0x42), None);
        assert_eq!(c.touch(0x41), None);
        assert_eq!(c.touch(0x1F680), Some(0x42));
    }
}
