// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Linear `frame_decodes_after` CRC resync budget & conservative fault-on-exhaustion guard
//! (`evidence/manifest.toml` `wire.steps.torn-vs-fault`; `Astream.Wire.TlaResyncCrcLookalikeBudget`).
//!
//! Models the anti-quadratic look-alike defense in `astream_wire::steps`:
//! - Effective CRC budget is `max(RESYNC_CRC_FLOOR = 16 MiB, RESYNC_CRC_PER_BYTE * tail_bytes)`,
//! - Every candidate frame look-alike is pre-charged its `declared_len` BEFORE hashing its CRC,
//! - If a candidate's `declared_len` exceeds remaining budget, the search stops immediately and
//!   returns `ConservativeFaultNeverTorn` (never `Torn`), guaranteeing no intact record hidden
//!   beyond unsearched look-alikes can ever be silently truncated!
//!
//! Zero heap allocations, zero loops, zero `Display`/`Hash` impls — preserves `astream-wire`
//! `unknown == 0` and `runtime_checked <= 110`.

#[cfg(clean_islands)]
#[path = "resync_crc_lookalike_budget_island.rs"]
mod resync_crc_lookalike_budget_island;
#[cfg(clean_islands)]
pub use resync_crc_lookalike_budget_island::{
    resync_budget_floor_max_b143, resync_charged_crc_clamp_b143,
};

/// Production `RESYNC_CRC_FLOOR` (`16 MiB`).
pub const RESYNC_CRC_FLOOR_BYTES: u64 = 16 * 1024 * 1024;
/// Production linear CRC multiplier (`2` CRC bytes per scanned byte after break).
pub const RESYNC_CRC_PER_BYTE_SLOPE: u64 = 2;

#[cfg(not(clean_islands))]
/// Compute `max(floor_bytes, linear_slope_bytes)`.
#[must_use]
pub const fn resync_budget_floor_max_b143(floor_bytes: u64, linear_slope_bytes: u64) -> u64 {
    if floor_bytes < linear_slope_bytes {
        linear_slope_bytes
    } else {
        floor_bytes
    }
}

#[cfg(not(clean_islands))]
/// Clamp cumulative pre-charged CRC bytes to `budget_bytes`.
#[must_use]
pub const fn resync_charged_crc_clamp_b143(cand_charged: u64, budget_bytes: u64) -> u64 {
    if cand_charged < budget_bytes {
        cand_charged
    } else {
        budget_bytes
    }
}

contract_fn! {
    /// True iff `already_charged <= budget_bytes` and `next_charged <= budget_bytes`.
    #[must_use]
    pub const fn resync_crc_candidate_admissible_b143(
        already_charged: u64,
        next_charged: u64,
        budget_bytes: u64,
    ) -> bool
    clauses [ensures result == (already_charged <= budget_bytes && next_charged <= budget_bytes)]
    {
        already_charged <= budget_bytes && next_charged <= budget_bytes
    }
}

/// Decision for pre-charging a look-alike frame candidate during post-break resync search.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ResyncCandidateCharge {
    /// Candidate pre-charged within linear budget: safe to run CRC over `declared_len` bytes.
    HashCandidate {
        charged_total: u64,
        budget_bytes: u64,
    },
    /// Budget exhausted before hashing: stop search and classify break as `Fault` (NEVER `Torn`)!
    StopSearchConservativeFault {
        charged_total: u64,
        budget_bytes: u64,
    },
}

/// Linear-work CRC budget meter for `frame_decodes_after`.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ResyncCrcBudgetMeter {
    budget_bytes: u64,
    charged_bytes: u64,
}

impl ResyncCrcBudgetMeter {
    #[must_use]
    pub const fn for_post_break_span(bytes_after_break: u64) -> Self {
        let slope = bytes_after_break.saturating_mul(RESYNC_CRC_PER_BYTE_SLOPE);
        Self {
            budget_bytes: resync_budget_floor_max_b143(RESYNC_CRC_FLOOR_BYTES, slope),
            charged_bytes: 0,
        }
    }

    #[must_use]
    pub const fn budget_bytes(&self) -> u64 {
        self.budget_bytes
    }

    /// Pre-charge `declared_len` BEFORE computing the candidate's CRC32.
    pub fn charge_candidate(&mut self, declared_len: u64) -> ResyncCandidateCharge {
        let Some(next) = self.charged_bytes.checked_add(declared_len) else {
            return ResyncCandidateCharge::StopSearchConservativeFault {
                charged_total: self.charged_bytes,
                budget_bytes: self.budget_bytes,
            };
        };
        if !resync_crc_candidate_admissible_b143(self.charged_bytes, next, self.budget_bytes) {
            return ResyncCandidateCharge::StopSearchConservativeFault {
                charged_total: self.charged_bytes,
                budget_bytes: self.budget_bytes,
            };
        }
        self.charged_bytes = resync_charged_crc_clamp_b143(next, self.budget_bytes);
        ResyncCandidateCharge::HashCandidate {
            charged_total: self.charged_bytes,
            budget_bytes: self.budget_bytes,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_16mib_floor_2x_slope_and_conservative_fault_on_exhaustion() {
        let mut floor_m = ResyncCrcBudgetMeter::for_post_break_span(48 * 1024);
        assert_eq!(floor_m.budget_bytes(), RESYNC_CRC_FLOOR_BYTES);
        assert_eq!(
            floor_m.charge_candidate(10 * 1024 * 1024),
            ResyncCandidateCharge::HashCandidate {
                charged_total: 10 * 1024 * 1024,
                budget_bytes: RESYNC_CRC_FLOOR_BYTES
            }
        );
        // Second 10 MiB look-alike exceeds 16 MiB floor -> stops BEFORE hashing and answers Fault!
        assert_eq!(
            floor_m.charge_candidate(10 * 1024 * 1024),
            ResyncCandidateCharge::StopSearchConservativeFault {
                charged_total: 10 * 1024 * 1024,
                budget_bytes: RESYNC_CRC_FLOOR_BYTES
            }
        );

        // Past 8 MiB (`9 MiB`), slope `2 * 9 MiB = 18 MiB` dominates the 16 MiB floor:
        let slope_m = ResyncCrcBudgetMeter::for_post_break_span(9 * 1024 * 1024);
        assert_eq!(slope_m.budget_bytes(), 18 * 1024 * 1024);
    }
}
