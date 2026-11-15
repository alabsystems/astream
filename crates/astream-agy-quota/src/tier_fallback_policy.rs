// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Reasoning-tier floor guard ensuring `aterm harness agy pick` never silently downgrades a deep
//! verification or architecture task below its minimum model capability tier (`Astream.AgyQuota.TlaTierFallbackPolicy`).

#[cfg(clean_islands)]
#[path = "tier_fallback_policy_island.rs"]
mod tier_fallback_policy_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn aq_tier_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn aq_fb_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use tier_fallback_policy_island::{aq_fb_advance, aq_tier_clamp};

/// Highest capability tier (`0 = flash_lite`, `1 = flash`, `2 = standard`, `3 = pro`).
pub const MAX_MODEL_TIER: u64 = 3;

contract_fn! {
    /// Verified tier-floor predicate (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `aq_tier_preserved_isl`.
    #[must_use]
    pub const fn aq_tier_preserved(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct TierFallbackGuard {
    checks_run: u64,
}

impl TierFallbackGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self { checks_run: 0 }
    }

    pub fn validate_candidate_tier(&mut self, candidate_tier: u64, required_floor: u64) -> bool {
        self.checks_run = aq_fb_advance(self.checks_run, self.checks_run.saturating_add(1));
        if required_floor > MAX_MODEL_TIER {
            return false;
        }
        let cand = aq_tier_clamp(candidate_tier, MAX_MODEL_TIER);
        let floor = aq_tier_clamp(required_floor, MAX_MODEL_TIER);
        aq_tier_preserved(cand, floor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_flash_fallback_when_pro_tier_is_required() {
        let mut g = TierFallbackGuard::new();
        assert!(g.validate_candidate_tier(3, 3));
        assert!(!g.validate_candidate_tier(1, 3));
    }
}
