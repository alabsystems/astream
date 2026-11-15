// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Proof-Floor Ratchet & Reproducible Readiness Gate Auditor (`Astream.Evidence.TlaFloorRatchet`).
//!
//! Codifies the workspace readiness contract enforced by `scripts/verify-ready.sh` and
//! `publish/README.md`:
//! - Every verified crate carries a monotone proof floor (`floor_ratchet_advance(prev, cand)`
//!   guarantees `prev <= floor` — floors never regress!).
//! - Recommended ratcheted floors follow `max(current_floor, (proved * 4) / 5)` (`80%` rule),
//!   clamped by `floor_target_clamp` so a recommended floor never exceeds `proved`.
//! - Readiness requires `proved >= floor`, `failed <= allowed_failed`, `mandated <= allowed_mandated`,
//!   `runtime_checked <= allowed_runtime_checked`, `contract_panics == 0`, `wall_backstop == 0`,
//!   `coverage_complete == true`, and `reproducible == true`.

#[cfg(clean_islands)]
#[path = "ratchet_audit_island.rs"]
mod ratchet_audit_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn floor_ratchet_advance(prev_floor: u64, cand_floor: u64) -> u64 {
    if prev_floor < cand_floor {
        cand_floor
    } else {
        prev_floor
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn floor_target_clamp(target: u64, proved: u64) -> u64 {
    if target < proved {
        target
    } else {
        proved
    }
}
#[cfg(clean_islands)]
pub use ratchet_audit_island::{floor_ratchet_advance, floor_target_clamp};

contract_fn! {
    /// Verified check whether `proved` meets or exceeds `floor` (`floor <= proved`),
    /// linked via `clean-kernel-defeq` to `floor_meets_bar_isl`.
    #[must_use]
    pub const fn floor_meets_bar(proved: u64, floor: u64) -> bool
    clauses [ensures result == (floor <= proved)]
    {
        floor <= proved
    }
}

/// Summary metrics extracted from a `targo trust check` target report.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TargetProofMetrics {
    pub proved: u64,
    pub failed: u64,
    pub mandated: u64,
    pub runtime_checked: u64,
    pub contract_panics: u64,
    pub wall_backstop: u64,
    pub coverage_complete: bool,
    pub reproducible: bool,
}

/// Declared policy bounds for a single target in `verify-ready`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TargetGatePolicy {
    pub current_floor: u64,
    pub allowed_failed: u64,
    pub allowed_mandated: u64,
    pub allowed_runtime_checked: u64,
}

/// Failure reason when a target report fails [`audit_target_readiness`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReadinessFailure {
    CoverageIncomplete,
    NotReproducible { wall_backstop: u64 },
    ContractPanic { count: u64 },
    FailedExceeded { actual: u64, allowed: u64 },
    MandatedExceeded { actual: u64, allowed: u64 },
    RuntimeCheckedExceeded { actual: u64, allowed: u64 },
    BelowFloor { proved: u64, floor: u64 },
}

/// Result of auditing a target's Trust report and computing its 80%-rule ratcheted floor.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReadinessAuditOutcome {
    /// `Ok(())` when every readiness condition holds, or the first blocking failure.
    pub status: Result<(), ReadinessFailure>,
    /// Monotone ratcheted floor `max(current_floor, min(proved, (proved * 4) / 5))`.
    pub recommended_floor: u64,
}

/// Compute the monotone 80%-rule ratcheted proof floor (`>= current_floor`).
#[must_use]
pub fn compute_ratchet_floor(current_floor: u64, proved: u64) -> u64 {
    let four_fifths = match proved.checked_mul(4) {
        Some(prod) => prod / 5,
        None => (proved / 5).saturating_mul(4),
    };
    let bounded_rec = floor_target_clamp(four_fifths, proved);
    floor_ratchet_advance(current_floor, bounded_rec)
}

/// Evaluate `metrics` against `policy` and compute the monotone ratcheted floor.
#[must_use]
pub fn audit_target_readiness(
    metrics: TargetProofMetrics,
    policy: TargetGatePolicy,
) -> ReadinessAuditOutcome {
    let recommended_floor = compute_ratchet_floor(policy.current_floor, metrics.proved);

    if !metrics.coverage_complete {
        return ReadinessAuditOutcome {
            status: Err(ReadinessFailure::CoverageIncomplete),
            recommended_floor,
        };
    }
    if !metrics.reproducible || metrics.wall_backstop > 0 {
        return ReadinessAuditOutcome {
            status: Err(ReadinessFailure::NotReproducible {
                wall_backstop: metrics.wall_backstop,
            }),
            recommended_floor,
        };
    }
    if metrics.contract_panics > 0 {
        return ReadinessAuditOutcome {
            status: Err(ReadinessFailure::ContractPanic {
                count: metrics.contract_panics,
            }),
            recommended_floor,
        };
    }
    if metrics.failed > policy.allowed_failed {
        return ReadinessAuditOutcome {
            status: Err(ReadinessFailure::FailedExceeded {
                actual: metrics.failed,
                allowed: policy.allowed_failed,
            }),
            recommended_floor,
        };
    }
    if metrics.mandated > policy.allowed_mandated {
        return ReadinessAuditOutcome {
            status: Err(ReadinessFailure::MandatedExceeded {
                actual: metrics.mandated,
                allowed: policy.allowed_mandated,
            }),
            recommended_floor,
        };
    }
    if metrics.runtime_checked > policy.allowed_runtime_checked {
        return ReadinessAuditOutcome {
            status: Err(ReadinessFailure::RuntimeCheckedExceeded {
                actual: metrics.runtime_checked,
                allowed: policy.allowed_runtime_checked,
            }),
            recommended_floor,
        };
    }
    if !floor_meets_bar(metrics.proved, policy.current_floor) {
        return ReadinessAuditOutcome {
            status: Err(ReadinessFailure::BelowFloor {
                proved: metrics.proved,
                floor: policy.current_floor,
            }),
            recommended_floor,
        };
    }

    ReadinessAuditOutcome {
        status: Ok(()),
        recommended_floor,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clean_twins_match_invariants() {
        assert_eq!(floor_ratchet_advance(439, 461), 461);
        assert_eq!(floor_ratchet_advance(461, 400), 461);
        assert_eq!(floor_target_clamp(800, 1000), 800);
        assert_eq!(floor_target_clamp(1200, 1000), 1000);
        assert!(floor_meets_bar(500, 500));
        assert!(!floor_meets_bar(499, 500));
    }

    #[test]
    fn audits_strict_zero_gap_crate_and_ratchets_floor_monotonically() {
        let policy = TargetGatePolicy {
            current_floor: 1124,
            allowed_failed: 0,
            allowed_mandated: 0,
            allowed_runtime_checked: u64::MAX,
        };
        let good = TargetProofMetrics {
            proved: 1422,
            failed: 0,
            mandated: 0,
            runtime_checked: 12,
            contract_panics: 0,
            wall_backstop: 0,
            coverage_complete: true,
            reproducible: true,
        };
        let out = audit_target_readiness(good, policy);
        assert_eq!(out.status, Ok(()));
        // int(1422 * 4 / 5) = 1137 > 1124!
        assert_eq!(out.recommended_floor, 1137);

        let backstop_hit = TargetProofMetrics {
            wall_backstop: 6,
            reproducible: false,
            ..good
        };
        assert_eq!(
            audit_target_readiness(backstop_hit, policy).status,
            Err(ReadinessFailure::NotReproducible { wall_backstop: 6 })
        );
    }
}
