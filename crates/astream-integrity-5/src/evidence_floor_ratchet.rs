// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Monotone 80%-proved floor ratchet evaluator for `scripts/verify-ready.sh` targets.
//!
//! Each target in `scripts/verify-ready.sh` pins a non-decreasing `proved` floor computed as
//! `max(current_floor, (proved * 4) / 5)` once verification reports `total > 0`,
//! `failed == 0`, `contract_panics == 0`, and `coverage_complete == true`.
//!
//! Clean specification: `evidence_floor_ratchet_island.rs` (`Astream.Evidence.TlaProvedFloorRatchet`).

#[cfg(clean_islands)]
#[path = "evidence_floor_ratchet_island.rs"]
mod evidence_floor_ratchet_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ratchet_floor_clamp(cand_floor: u64, proved_count: u64) -> u64 {
    if cand_floor < proved_count {
        cand_floor
    } else {
        proved_count
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ratchet_floor_advance(cur_floor: u64, cand_floor: u64) -> u64 {
    if cur_floor < cand_floor {
        cand_floor
    } else {
        cur_floor
    }
}
#[cfg(clean_islands)]
pub use evidence_floor_ratchet_island::{ratchet_floor_advance, ratchet_floor_clamp};

contract_fn! {
    /// Kernel-certified check that `floor_val <= proved_val`, linked via
    /// `clean-kernel-defeq` to `ratchet_floor_within_proved_isl`.
    #[must_use]
    pub const fn ratchet_floor_within_proved(floor_val: u64, proved_val: u64) -> bool
    clauses [ensures result == (floor_val <= proved_val)]
    {
        floor_val <= proved_val
    }
}

/// Summary counts extracted from a target's `report.json`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReadyReportCounts {
    pub total: u64,
    pub proved: u64,
    pub failed: u64,
    pub contract_panics: u64,
    pub mandated: u64,
    pub timed_out: u64,
    pub coverage_complete: bool,
}

/// Verdict produced when evaluating `ReadyReportCounts` against `current_floor` and `max_mandated`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FloorRatchetVerdict {
    /// Target passed all gates and keeps or raises its floor monotonically (`next_floor >= current_floor`).
    Passed {
        previous_floor: u64,
        next_floor: u64,
        raised: bool,
    },
    /// Vacuous run (`total == 0`).
    VacuousReport,
    /// One or more refuted obligations (`failed > 0`).
    RefutedObligations { failed: u64 },
    /// One or more contract panics (`contract_panics > 0`).
    ContractPanics { panics: u64 },
    /// Timed-out obligations (`timed_out > 0`).
    TimedOutObligations { timed_out: u64 },
    /// Incomplete unit coverage (`coverage_complete == false`).
    IncompleteCoverage,
    /// Mandated count exceeded crate policy (`mandated > max_mandated`).
    MandatedExceeded { mandated: u64, max_mandated: u64 },
    /// Proved obligations fell below `current_floor`.
    BelowFloor { proved: u64, floor: u64 },
}

/// Evaluate `counts` against `current_floor` and `max_mandated`, computing the monotone
/// 80% ratcheted floor when all verification gates hold.
#[must_use]
pub fn evaluate_floor_ratchet(
    current_floor: u64,
    max_mandated: u64,
    counts: ReadyReportCounts,
) -> FloorRatchetVerdict {
    if counts.total == 0 {
        return FloorRatchetVerdict::VacuousReport;
    }
    if counts.failed > 0 {
        return FloorRatchetVerdict::RefutedObligations {
            failed: counts.failed,
        };
    }
    if counts.contract_panics > 0 {
        return FloorRatchetVerdict::ContractPanics {
            panics: counts.contract_panics,
        };
    }
    if counts.timed_out > 0 {
        return FloorRatchetVerdict::TimedOutObligations {
            timed_out: counts.timed_out,
        };
    }
    if !counts.coverage_complete {
        return FloorRatchetVerdict::IncompleteCoverage;
    }
    if counts.mandated > max_mandated {
        return FloorRatchetVerdict::MandatedExceeded {
            mandated: counts.mandated,
            max_mandated,
        };
    }
    if counts.proved < current_floor {
        return FloorRatchetVerdict::BelowFloor {
            proved: counts.proved,
            floor: current_floor,
        };
    }

    let eighty_pct = counts.proved.saturating_mul(4) / 5;
    let clamped_cand = ratchet_floor_clamp(eighty_pct, counts.proved);
    let _ = ratchet_floor_within_proved(clamped_cand, counts.proved);
    let next_floor = ratchet_floor_advance(current_floor, clamped_cand);

    FloorRatchetVerdict::Passed {
        previous_floor: current_floor,
        next_floor,
        raised: next_floor > current_floor,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn raises_floor_to_eighty_percent_and_never_lowers_or_ignores_failures() {
        let kafka_counts = ReadyReportCounts {
            total: 1902,
            proved: 1420,
            failed: 0,
            contract_panics: 0,
            mandated: 0,
            timed_out: 0,
            coverage_complete: true,
        };
        let v_raise = evaluate_floor_ratchet(1124, 0, kafka_counts);
        assert_eq!(
            v_raise,
            FloorRatchetVerdict::Passed {
                previous_floor: 1124,
                next_floor: 1136,
                raised: true,
            }
        );

        // When 80% is below an existing higher floor (`288`), floor stays at `288`.
        let bin_counts = ReadyReportCounts {
            total: 641,
            proved: 332,
            failed: 0,
            contract_panics: 0,
            mandated: 0,
            timed_out: 0,
            coverage_complete: true,
        };
        let v_keep = evaluate_floor_ratchet(288, 0, bin_counts);
        assert_eq!(
            v_keep,
            FloorRatchetVerdict::Passed {
                previous_floor: 288,
                next_floor: 288,
                raised: false,
            }
        );

        // Mandated violation on a 0-mandated crate is rejected.
        let bad_mandated = ReadyReportCounts {
            mandated: 1,
            ..kafka_counts
        };
        assert_eq!(
            evaluate_floor_ratchet(1124, 0, bad_mandated),
            FloorRatchetVerdict::MandatedExceeded {
                mandated: 1,
                max_mandated: 0,
            }
        );
    }
}
