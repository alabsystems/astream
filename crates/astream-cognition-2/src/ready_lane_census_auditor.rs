// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! 21-target READY verification census & monotonic 80%-floor ratchet auditor
//! (`Astream.Evidence.TlaReadyLaneCensusAuditor`).
//!
//! Milestone Island #400 across `astream`: models the `scripts/verify-ready.sh` non-regression
//! gate over all 21 workspace targets (`proved >= floor`, `failed == 0`, `contract_panics == 0`,
//! `coverage_complete`, `wall_backstop == 0`) and computes strictly non-decreasing `int(proved * 0.80)`
//! floor ratchets without ever lowering an existing floor.

#[cfg(clean_islands)]
#[path = "ready_lane_census_auditor_island.rs"]
mod ready_lane_census_auditor_island;
#[cfg(clean_islands)]
pub use ready_lane_census_auditor_island::{
    census_targets_clamp_b112, ratcheted_floor_advance_b112,
};

#[cfg(not(clean_islands))]
/// Clamp audited READY target count to `max_targets` (`21`).
#[must_use]
pub const fn census_targets_clamp_b112(cand_targets: u64, max_targets: u64) -> u64 {
    if cand_targets < max_targets {
        cand_targets
    } else {
        max_targets
    }
}

#[cfg(not(clean_islands))]
/// Monotonically ratchet a target's proved floor (`never lower a floor to go green`).
#[must_use]
pub const fn ratcheted_floor_advance_b112(cur_floor: u64, cand_floor: u64) -> u64 {
    if cur_floor < cand_floor {
        cand_floor
    } else {
        cur_floor
    }
}

contract_fn! {
    /// True iff a target's verified counts meet `verify-ready.sh`'s zero-refutation & floor bar.
    #[must_use]
    pub const fn ready_target_green_b112(
        proved: u64,
        floor: u64,
        failed: u64,
        panics: u64,
        wall_backstop: u64,
    ) -> bool
    clauses [ensures result == (floor <= proved && failed == 0 && panics == 0 && wall_backstop == 0)]
    {
        floor <= proved && failed == 0 && panics == 0 && wall_backstop == 0
    }
}

/// Number of workspace library + binary targets in `scripts/verify-ready.sh`.
pub const READY_WORKSPACE_TARGETS: u64 = 21;

/// Per-target census evaluation & floor-ratchet proposal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TargetCensusVerdict {
    Green {
        new_ratcheted_floor: u64,
        checked_targets: u64,
    },
    Regressed {
        proved: u64,
        floor: u64,
        failed: u64,
    },
}

/// Stateful census auditor for the 21 `verify-ready.sh` targets.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReadyLaneCensusAuditor {
    max_targets: u64,
    checked_targets: u64,
    regressed_targets: u64,
    total_proved: u64,
}

impl Default for ReadyLaneCensusAuditor {
    fn default() -> Self {
        Self::new()
    }
}

impl ReadyLaneCensusAuditor {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            max_targets: READY_WORKSPACE_TARGETS,
            checked_targets: 0,
            regressed_targets: 0,
            total_proved: 0,
        }
    }

    #[must_use]
    pub const fn checked_targets(&self) -> u64 {
        self.checked_targets
    }

    #[must_use]
    pub const fn regressed_targets(&self) -> u64 {
        self.regressed_targets
    }

    #[must_use]
    pub const fn total_proved(&self) -> u64 {
        self.total_proved
    }

    /// Audit one READY target and compute its ratcheted floor `max(cur_floor, (proved * 4) / 5)`.
    pub fn record_target(
        &mut self,
        proved: u64,
        cur_floor: u64,
        failed: u64,
        panics: u64,
        wall_backstop: u64,
        coverage_complete: bool,
    ) -> TargetCensusVerdict {
        let cand_t = self.checked_targets.saturating_add(1);
        self.checked_targets = census_targets_clamp_b112(cand_t, self.max_targets);
        self.total_proved = self.total_proved.saturating_add(proved);

        if !coverage_complete
            || !ready_target_green_b112(proved, cur_floor, failed, panics, wall_backstop)
        {
            self.regressed_targets = self.regressed_targets.saturating_add(1);
            return TargetCensusVerdict::Regressed {
                proved,
                floor: cur_floor,
                failed,
            };
        }
        let eighty_pct = proved.saturating_mul(4) / 5;
        let next_floor = ratcheted_floor_advance_b112(cur_floor, eighty_pct);
        TargetCensusVerdict::Green {
            new_ratcheted_floor: next_floor,
            checked_targets: self.checked_targets,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ratchets_floor_upward_at_eighty_percent_and_never_lowers() {
        let mut aud = ReadyLaneCensusAuditor::new();
        // astream-wire: 751 proved vs 348 floor -> ratchets to 600:
        assert_eq!(
            aud.record_target(751, 348, 0, 0, 0, true),
            TargetCensusVerdict::Green {
                new_ratcheted_floor: 600,
                checked_targets: 1,
            }
        );
        // astream-digest: 725 proved (80% = 580) vs 596 floor -> preserves 596!
        assert_eq!(
            aud.record_target(725, 596, 0, 0, 0, true),
            TargetCensusVerdict::Green {
                new_ratcheted_floor: 596,
                checked_targets: 2,
            }
        );
        assert_eq!(aud.regressed_targets(), 0);
    }
}
