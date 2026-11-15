// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Three-slot CPU->GPU `MTLBuffer` ring allocator ensuring the CPU never overwrites a vertex
//! buffer while `MTLCommandBuffer` completion handlers still hold it in flight
//! (`Astream.MetalDmg.TlaTripleBufferRing`).

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "triple_buffer_ring_island.rs"]
mod triple_buffer_ring_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn md_inflight_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn md_acquire_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use triple_buffer_ring_island::{md_acquire_advance, md_inflight_clamp};

/// Triple-buffering slot count (`3`).
pub const TRIPLE_RING_SLOTS: u64 = 3;

contract_fn! {
    /// Verified free-slot availability (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `md_slot_free_isl`.
    #[must_use]
    pub const fn md_slot_free(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct TripleBufferRing {
    in_flight: u64,
    next_slot: u64,
    acquires: u64,
}

impl TripleBufferRing {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            in_flight: 0,
            next_slot: 0,
            acquires: 0,
        }
    }

    pub fn try_acquire(&mut self) -> Option<u64> {
        let next_if = self.in_flight.saturating_add(1);
        if !md_slot_free(TRIPLE_RING_SLOTS, next_if) {
            return None;
        }
        self.in_flight = md_inflight_clamp(next_if, TRIPLE_RING_SLOTS);
        let slot = self.next_slot;
        let cand_slot = slot.saturating_add(1);
        self.next_slot = if cand_slot >= TRIPLE_RING_SLOTS {
            0
        } else {
            cand_slot
        };
        self.acquires = md_acquire_advance(self.acquires, self.acquires.saturating_add(1));
        Some(slot)
    }

    pub fn complete_gpu_frame(&mut self) {
        self.in_flight = self.in_flight.saturating_sub(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn allows_three_frames_in_flight_and_blocks_fourth_until_gpu_completion() {
        let mut r = TripleBufferRing::new();
        assert_eq!(r.try_acquire(), Some(0));
        assert_eq!(r.try_acquire(), Some(1));
        assert_eq!(r.try_acquire(), Some(2));
        assert_eq!(r.try_acquire(), None);
        r.complete_gpu_frame();
        assert_eq!(r.try_acquire(), Some(0));
    }
}
