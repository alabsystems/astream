// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bounded terminal scrollback page-ring allocator evicting oldest cold pages strictly within each
//! `aterm` tab's RAM budget (`Astream.ScrollTier.TlaPageRingAllocator`).

#[cfg(clean_islands)]
#[path = "page_ring_allocator_island.rs"]
mod page_ring_allocator_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sb_pages_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sb_evict_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use page_ring_allocator_island::{sb_evict_advance, sb_pages_clamp};

/// Maximum scrollback pages per tab (`16_384` x 4 KiB = 64 MiB).
pub const MAX_SCROLLBACK_PAGES: u64 = 16_384;

contract_fn! {
    /// Verified page-ring bound (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sb_within_ram_cap_isl`.
    #[must_use]
    pub const fn sb_within_ram_cap(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct ScrollbackPageRing {
    cap_pages: u64,
    live_pages: u64,
    evicted_pages: u64,
}

impl ScrollbackPageRing {
    #[must_use]
    pub const fn new(cap_pages: u64) -> Self {
        let cap = sb_pages_clamp(cap_pages, MAX_SCROLLBACK_PAGES);
        Self {
            cap_pages: if cap == 0 { 1 } else { cap },
            live_pages: 0,
            evicted_pages: 0,
        }
    }

    pub fn push_page(&mut self) -> bool {
        let next = self.live_pages.saturating_add(1);
        if sb_within_ram_cap(self.cap_pages, next) {
            self.live_pages = next;
            false
        } else {
            self.evicted_pages =
                sb_evict_advance(self.evicted_pages, self.evicted_pages.saturating_add(1));
            true
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn evicts_oldest_page_once_ring_reaches_page_cap() {
        let mut r = ScrollbackPageRing::new(2);
        assert!(!r.push_page());
        assert!(!r.push_page());
        assert!(r.push_page());
        assert_eq!(r.live_pages, 2);
    }
}
