// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bounded per-session excerpt ring backing `aterm ctl survey` so noisy peer tabs cannot blow out
//! an inspecting agent's context window (`Astream.FabMail.TlaSurveyExcerptRing`).

#[cfg(clean_islands)]
#[path = "survey_excerpt_ring_island.rs"]
mod survey_excerpt_ring_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn fm_ring_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn fm_snap_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use survey_excerpt_ring_island::{fm_ring_clamp, fm_snap_advance};

/// Maximum survey excerpt bytes retained per peer tab (`512` bytes).
pub const MAX_EXCERPT_BYTES: u64 = 512;

contract_fn! {
    /// Verified excerpt cap predicate (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `fm_excerpt_bounded_isl`.
    #[must_use]
    pub const fn fm_excerpt_bounded(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct SurveyExcerptBudget {
    max_tabs: u64,
    snapshots_taken: u64,
}

impl SurveyExcerptBudget {
    #[must_use]
    pub const fn new(max_tabs: u64) -> Self {
        Self {
            max_tabs: fm_ring_clamp(max_tabs, 128),
            snapshots_taken: 0,
        }
    }

    pub fn clamp_excerpt_len(&mut self, raw_bytes: u64) -> u64 {
        let clamped = fm_ring_clamp(raw_bytes, MAX_EXCERPT_BYTES);
        self.snapshots_taken =
            fm_snap_advance(self.snapshots_taken, self.snapshots_taken.saturating_add(1));
        let _ = fm_excerpt_bounded(MAX_EXCERPT_BYTES, clamped);
        let _ = self.max_tabs;
        clamped
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn truncates_oversized_survey_excerpts_to_512_bytes() {
        let mut b = SurveyExcerptBudget::new(32);
        assert_eq!(b.clamp_excerpt_len(120), 120);
        assert_eq!(b.clamp_excerpt_len(4_096), MAX_EXCERPT_BYTES);
    }
}
