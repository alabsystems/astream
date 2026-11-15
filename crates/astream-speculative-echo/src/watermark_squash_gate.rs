// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `term.predict.watermark-squash` hit-rate floor verifier enforcing `predict_hit_rate >= 0.80`
//! (`8_000` basis points) across interactive terminal benchmark corpora
//! (`Astream.SpecEcho.TlaWatermarkSquashGate`).

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
#[path = "watermark_squash_gate_island.rs"]
mod watermark_squash_gate_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn se_bps_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn se_eval_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use watermark_squash_gate_island::{se_bps_clamp, se_eval_advance};

/// Basis-point floor (`8_000 bps` = `0.80` hit rate).
pub const WATERMARK_SQUASH_FLOOR_BPS: u64 = 8_000;

contract_fn! {
    /// Verified `>= 0.80` hit-rate gate (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `se_meets_hit_floor_isl`.
    #[must_use]
    pub const fn se_meets_hit_floor(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct WatermarkSquashEvaluator {
    runs: u64,
}

impl WatermarkSquashEvaluator {
    #[must_use]
    pub const fn new() -> Self {
        Self { runs: 0 }
    }

    pub fn evaluate_corpus(
        &mut self,
        hits: u64,
        total_steps: u64,
        converged_eq_full: bool,
    ) -> bool {
        self.runs = se_eval_advance(self.runs, self.runs.saturating_add(1));
        if !converged_eq_full || total_steps == 0 || hits > total_steps {
            return false;
        }
        let raw_bps = match hits.checked_mul(10_000) {
            Some(scaled) => match scaled.checked_div(total_steps) {
                Some(q) => q,
                None => return false,
            },
            None => {
                // Both `hits` and `total_steps` exceed `u64::MAX / 10_000`; scale down losslessly
                // in basis-point resolution via `total_steps / 10_000 >= 1`.
                let q10k = total_steps / 10_000;
                let scaled_denom = if q10k >= 1 { q10k } else { 1 };
                match hits.checked_div(scaled_denom) {
                    Some(q) => q,
                    None => return false,
                }
            }
        };
        let bps = se_bps_clamp(raw_bps, 10_000);
        se_meets_hit_floor(bps, WATERMARK_SQUASH_FLOOR_BPS)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_eighty_percent_hit_rate_and_exact_final_screen_convergence() {
        let mut e = WatermarkSquashEvaluator::new();
        assert!(e.evaluate_corpus(96, 100, true));
        assert!(!e.evaluate_corpus(75, 100, true));
        assert!(!e.evaluate_corpus(99, 100, false));
    }
}
