// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Deterministic `aterm harness agy pick` pool rotator selecting the primary model pool when above
//! reserve and rotating cleanly to healthy peer pools when low or spent (`Astream.AgyQuota.TlaModelPickRotator`).

#[cfg(clean_islands)]
#[path = "model_pick_rotator_island.rs"]
mod model_pick_rotator_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn aq_pool_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn aq_rot_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use model_pick_rotator_island::{aq_pool_clamp, aq_rot_advance};

/// Maximum pool slot index (`0 = Gemini`, `1 = Claude`, `2 = Gpt`).
pub const MAX_POOL_SLOT: u64 = 2;

contract_fn! {
    /// Verified pool health gate (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `aq_pick_healthy_isl`.
    #[must_use]
    pub const fn aq_pick_healthy(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct ModelPickRouter {
    gemini_bps: u64,
    claude_bps: u64,
    gpt_bps: u64,
    rotations_emitted: u64,
}

impl ModelPickRouter {
    #[must_use]
    pub const fn new(gemini_bps: u64, claude_bps: u64, gpt_bps: u64) -> Self {
        Self {
            gemini_bps: aq_pool_clamp(gemini_bps, 10_000),
            claude_bps: aq_pool_clamp(claude_bps, 10_000),
            gpt_bps: aq_pool_clamp(gpt_bps, 10_000),
            rotations_emitted: 0,
        }
    }

    #[must_use]
    const fn bps_for(&self, slot: u64) -> u64 {
        match slot {
            0 => self.gemini_bps,
            1 => self.claude_bps,
            _ => self.gpt_bps,
        }
    }

    pub fn pick_pool_slot(&mut self, preferred_slot: u64, min_reserve_bps: u64) -> Option<u64> {
        let pref = aq_pool_clamp(preferred_slot, MAX_POOL_SLOT);
        if aq_pick_healthy(self.bps_for(pref), min_reserve_bps) {
            return Some(pref);
        }
        let mut step = 1u64;
        while step <= MAX_POOL_SLOT {
            let cand = pref.saturating_add(step) % 3;
            if aq_pick_healthy(self.bps_for(cand), min_reserve_bps) {
                self.rotations_emitted = aq_rot_advance(
                    self.rotations_emitted,
                    self.rotations_emitted.saturating_add(1),
                );
                return Some(cand);
            }
            step = step.saturating_add(1);
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn spent_preferred_pool_rotates_deterministically_to_next_healthy_pool() {
        let mut r = ModelPickRouter::new(200, 4_500, 8_000);
        assert_eq!(r.pick_pool_slot(0, 1_000), Some(1));
        assert_eq!(r.pick_pool_slot(2, 1_000), Some(2));
    }
}
