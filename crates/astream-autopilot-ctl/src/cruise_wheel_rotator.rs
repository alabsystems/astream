// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Six-spoke `autopilot=cruise` continuation prompt rotator (`aterm` primer: `widest_check` ->
//! `hostile_review` -> `out_of_scope` -> `measure_vs_main` -> `next_open_issue` ->
//! `land_session_diff`, then cycling back to the first; `Astream.Autopilot.TlaCruiseWheelRotator`).

#[cfg(clean_islands)]
#[path = "cruise_wheel_rotator_island.rs"]
mod cruise_wheel_rotator_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ap_spoke_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ap_cycle_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use cruise_wheel_rotator_island::{ap_cycle_advance, ap_spoke_clamp};

/// Exact number of continuation spokes in `aterm`'s `autopilot=cruise` wheel (`0..=5`).
pub const MAX_CRUISE_SPOKE_INDEX: u64 = 5;

contract_fn! {
    /// Verified spoke bound (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ap_wheel_valid_isl`.
    #[must_use]
    pub const fn ap_wheel_valid(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CruiseSpoke {
    WidestCheck,
    HostileReview,
    OutOfScopeFollowup,
    MeasureAgainstMain,
    NextOpenIssue,
    LandSessionDiffOnly,
}

impl CruiseSpoke {
    #[must_use]
    pub const fn from_index(idx: u64) -> Self {
        match idx {
            0 => Self::WidestCheck,
            1 => Self::HostileReview,
            2 => Self::OutOfScopeFollowup,
            3 => Self::MeasureAgainstMain,
            4 => Self::NextOpenIssue,
            _ => Self::LandSessionDiffOnly,
        }
    }
}

/// Rotates deterministically through the 6 `cruise` continuation prompts.
#[derive(Debug, Clone, Default)]
pub struct CruiseWheelState {
    next_idx: u64,
    completed_rotations: u64,
}

impl CruiseWheelState {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            next_idx: 0,
            completed_rotations: 0,
        }
    }

    pub fn take_next_spoke(&mut self) -> CruiseSpoke {
        let idx = ap_spoke_clamp(self.next_idx, MAX_CRUISE_SPOKE_INDEX);
        let _ = ap_wheel_valid(MAX_CRUISE_SPOKE_INDEX, idx);
        let spoke = CruiseSpoke::from_index(idx);
        if idx >= MAX_CRUISE_SPOKE_INDEX {
            self.next_idx = 0;
            self.completed_rotations = ap_cycle_advance(
                self.completed_rotations,
                self.completed_rotations.saturating_add(1),
            );
        } else {
            self.next_idx = idx.saturating_add(1);
        }
        spoke
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cruise_wheel_cycles_through_all_six_spokes_and_wraps_to_widest_check() {
        let mut w = CruiseWheelState::new();
        assert_eq!(w.take_next_spoke(), CruiseSpoke::WidestCheck);
        assert_eq!(w.take_next_spoke(), CruiseSpoke::HostileReview);
        assert_eq!(w.take_next_spoke(), CruiseSpoke::OutOfScopeFollowup);
        assert_eq!(w.take_next_spoke(), CruiseSpoke::MeasureAgainstMain);
        assert_eq!(w.take_next_spoke(), CruiseSpoke::NextOpenIssue);
        assert_eq!(w.take_next_spoke(), CruiseSpoke::LandSessionDiffOnly);
        assert_eq!(w.take_next_spoke(), CruiseSpoke::WidestCheck);
    }
}
