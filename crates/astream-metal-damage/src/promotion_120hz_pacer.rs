// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Apple Silicon ProMotion adaptive frame pacer stepping cleanly between `120Hz` (`8_333 us` on
//! active input/output), `60Hz` (`16_666 us`), and `0Hz` idle sleep (`Astream.MetalDmg.TlaPromotion120hzPacer`).

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
#[path = "promotion_120hz_pacer_island.rs"]
mod promotion_120hz_pacer_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn md_hz_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn md_tick_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use promotion_120hz_pacer_island::{md_hz_clamp, md_tick_advance};

/// Maximum frame interval (`33_333 us` = 30Hz floor when active).
pub const MAX_ACTIVE_FRAME_US: u64 = 33_333;

contract_fn! {
    /// Verified vsync deadline check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `md_frame_due_isl`.
    #[must_use]
    pub const fn md_frame_due(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct ProMotionPacer {
    last_present_us: u64,
    frames_presented: u64,
}

impl Default for ProMotionPacer {
    fn default() -> Self {
        Self::new()
    }
}

impl ProMotionPacer {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            last_present_us: 0,
            frames_presented: 0,
        }
    }

    pub fn poll_vsync(&mut self, now_us: u64, has_damage: bool, interactive_burst: bool) -> bool {
        if !has_damage {
            return false;
        }
        let period_us = md_hz_clamp(
            if interactive_burst { 8_333 } else { 16_666 },
            MAX_ACTIVE_FRAME_US,
        );
        let due_us = if self.frames_presented == 0 {
            0
        } else {
            self.last_present_us.saturating_add(period_us)
        };
        if md_frame_due(now_us, due_us) {
            self.last_present_us = now_us;
            self.frames_presented = md_tick_advance(
                self.frames_presented,
                self.frames_presented.saturating_add(1),
            );
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sleeps_at_zero_hz_without_damage_and_paces_120hz_during_input_burst() {
        let mut p = ProMotionPacer::new();
        assert!(!p.poll_vsync(10_000, false, true));
        assert!(p.poll_vsync(10_000, true, true));
        assert!(!p.poll_vsync(15_000, true, true));
        assert!(p.poll_vsync(18_500, true, true));
    }
}
