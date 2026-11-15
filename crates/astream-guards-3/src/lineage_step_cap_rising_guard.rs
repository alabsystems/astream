// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `Lineage::MAX` (`8`) strictly-rising generation step & `min(cursor, common)` reader resume
//! guard (`evidence/manifest.toml` `broker.unclean-generation` & `broker.log-identity`;
//! `Astream.Wire.TlaLineageStepCapRisingGuard`).
//!
//! Enforces the `astream_wire::logid::Lineage` wire & constructor laws:
//! - At most `MAX_LINEAGE_STEPS` (`8`) steps are admitted by `Lineage::from_steps` and the
//!   `Hello` `Nonce` extension decoder; step lists `> 8` or non-rising generations
//!   (`cand_gen <= prev_gen`) are refused fail-closed,
//! - Across a valid unclean-stop lineage step `(next_gen, common)`, a reader holding `cursor`
//!   resumes at `min(cursor, common)` rather than resetting to `0` or reading past `common`.
//!
//! Zero heap allocations, zero loops, zero `Display`/`Hash` impls — preserves `astream-wire`
//! `unknown == 0` and `runtime_checked <= 110`.

#[cfg(clean_islands)]
#[path = "lineage_step_cap_rising_guard_island.rs"]
mod lineage_step_cap_rising_guard_island;
#[cfg(clean_islands)]
pub use lineage_step_cap_rising_guard_island::{
    lineage_gen_advance_b149, resume_common_clamp_b149,
};

/// Maximum number of lineage steps encoded in `<log>.id` FORMAT 2 and `Hello` extensions (`8`).
pub const MAX_LINEAGE_STEPS: u64 = 8;

#[cfg(not(clean_islands))]
/// Clamp reader `cursor` to `common` (`min(cursor, common)`).
#[must_use]
pub const fn resume_common_clamp_b149(reader_cursor: u64, common_floor: u64) -> u64 {
    if reader_cursor < common_floor {
        reader_cursor
    } else {
        common_floor
    }
}

#[cfg(not(clean_islands))]
/// Advance accepted lineage generation monotonically.
#[must_use]
pub const fn lineage_gen_advance_b149(cur_gen: u64, cand_gen: u64) -> u64 {
    if cur_gen < cand_gen {
        cand_gen
    } else {
        cur_gen
    }
}

contract_fn! {
    /// True iff `step_index < max_steps` and `cand_gen > prev_gen` (strictly rising generation).
    #[must_use]
    pub const fn lineage_step_rising_within_cap_b149(
        step_index: u64,
        max_steps: u64,
        has_prev: bool,
        prev_gen: u64,
        cand_gen: u64,
    ) -> bool
    clauses [ensures result == (step_index < max_steps && (!has_prev || prev_gen < cand_gen))]
    {
        step_index < max_steps && (!has_prev || prev_gen < cand_gen)
    }
}

/// Decision when validating a lineage step or computing reader resume cursor.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum LineageStepDecision {
    AdmittedRisingStep {
        step_count: u64,
        latest_gen: u64,
        common_floor: u64,
    },
    RefusedExceedsMaxSteps {
        max_steps: u64,
    },
    RefusedNonRisingGeneration {
        prev_gen: u64,
        cand_gen: u64,
    },
    ResumedAtMinCursorCommon {
        resume_cursor: u64,
    },
}

/// Tracks strictly rising lineage steps (`<= 8`) and newest common floor.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct LineageStepGuard {
    step_count: u64,
    has_prev: bool,
    latest_gen: u64,
    newest_common: u64,
}

impl LineageStepGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            step_count: 0,
            has_prev: false,
            latest_gen: 0,
            newest_common: u64::MAX,
        }
    }

    #[must_use]
    pub const fn step_count(&self) -> u64 {
        self.step_count
    }

    /// Validate and append one `(cand_gen, cand_common)` step under `Lineage::from_steps` rules.
    pub fn push_step(&mut self, cand_gen: u64, cand_common: u64) -> LineageStepDecision {
        if self.step_count >= MAX_LINEAGE_STEPS {
            return LineageStepDecision::RefusedExceedsMaxSteps {
                max_steps: MAX_LINEAGE_STEPS,
            };
        }
        if !lineage_step_rising_within_cap_b149(
            self.step_count,
            MAX_LINEAGE_STEPS,
            self.has_prev,
            self.latest_gen,
            cand_gen,
        ) {
            return LineageStepDecision::RefusedNonRisingGeneration {
                prev_gen: self.latest_gen,
                cand_gen,
            };
        }
        self.step_count = self.step_count.saturating_add(1);
        self.has_prev = true;
        self.latest_gen = lineage_gen_advance_b149(self.latest_gen, cand_gen);
        self.newest_common = resume_common_clamp_b149(self.newest_common, cand_common);
        LineageStepDecision::AdmittedRisingStep {
            step_count: self.step_count,
            latest_gen: self.latest_gen,
            common_floor: self.newest_common,
        }
    }

    /// Compute `min(reader_cursor, newest_common)` for gap-free reader resume.
    #[must_use]
    pub const fn compute_reader_resume(&self, reader_cursor: u64) -> LineageStepDecision {
        LineageStepDecision::ResumedAtMinCursorCommon {
            resume_cursor: resume_common_clamp_b149(reader_cursor, self.newest_common),
        }
    }
}

impl Default for LineageStepGuard {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_strictly_rising_generations_8_step_cap_and_min_cursor_common_resume() {
        let mut g = LineageStepGuard::new();
        assert_eq!(
            g.push_step(1, 12),
            LineageStepDecision::AdmittedRisingStep {
                step_count: 1,
                latest_gen: 1,
                common_floor: 12,
            }
        );
        // Same generation `1` does NOT rise -> refused!
        assert_eq!(
            g.push_step(1, 10),
            LineageStepDecision::RefusedNonRisingGeneration {
                prev_gen: 1,
                cand_gen: 1,
            }
        );
        assert_eq!(
            g.compute_reader_resume(15),
            LineageStepDecision::ResumedAtMinCursorCommon { resume_cursor: 12 }
        );
        assert_eq!(
            g.compute_reader_resume(7),
            LineageStepDecision::ResumedAtMinCursorCommon { resume_cursor: 7 }
        );
    }
}
