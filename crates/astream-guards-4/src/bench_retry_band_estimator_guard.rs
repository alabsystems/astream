// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Nearest-band `BENCH_ATTEMPTS = 3` estimator & single-shot `test` claim guard
//! (`evidence/manifest.toml` `evidence.bench-retry-is-an-estimator`;
//! `Astream.Evidence.TlaBenchRetryBandEstimatorGuard`).
//!
//! Enforces the `astream-evidence` retry & sample-selection laws:
//! - A `test` or `selftest` claim (`is_bench == false`) executes AT MOST ONCE (`attempts <= 1`),
//!   never retrying a transient failure,
//! - A `bench` claim (`is_bench == true`) executes up to `BENCH_ATTEMPTS = 3` times, stopping
//!   immediately when a sample lands in `[min_floor, max_ceiling]` (`distance_to_band == 0`),
//!   retaining the sample with MINIMAL `distance_to_band` across misses, and failing closed
//!   if a sample prints no metric!

#[cfg(clean_islands)]
#[path = "bench_retry_band_estimator_guard_island.rs"]
mod bench_retry_band_estimator_guard_island;
#[cfg(clean_islands)]
pub use bench_retry_band_estimator_guard_island::{
    bench_attempts_advance_b151, nearest_band_dist_clamp_b151,
};

/// Maximum attempts for a `bench` claim (`3`).
pub const BENCH_MAX_ATTEMPTS: u64 = 3;

#[cfg(not(clean_islands))]
/// Monotonically tighten `best_distance` to the target band (`min(best_dist, cand_dist)`).
#[must_use]
pub const fn nearest_band_dist_clamp_b151(cand_dist: u64, best_dist: u64) -> u64 {
    if cand_dist < best_dist {
        cand_dist
    } else {
        best_dist
    }
}

#[cfg(not(clean_islands))]
/// Advance executed attempt counter monotonically.
#[must_use]
pub const fn bench_attempts_advance_b151(cur_attempts: u64, cand_attempts: u64) -> u64 {
    if cur_attempts < cand_attempts {
        cand_attempts
    } else {
        cur_attempts
    }
}

contract_fn! {
    /// True iff `is_bench`, `best_dist > 0` (not yet in band), and `attempts < max_attempts`.
    #[must_use]
    pub const fn bench_retry_permitted_b151(
        is_bench: bool,
        best_dist: u64,
        attempts: u64,
        max_attempts: u64,
    ) -> bool
    clauses [ensures result == (is_bench && best_dist > 0 && attempts < max_attempts)]
    {
        is_bench && best_dist > 0 && attempts < max_attempts
    }
}

/// Verdict after each claim sample execution.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BenchEstimatorDecision {
    PassedInBand {
        attempts: u64,
        selected_sample: u64,
    },
    RetryBenchSample {
        attempts: u64,
        nearest_sample: u64,
        nearest_dist: u64,
    },
    FailedOutOfBandExhausted {
        attempts: u64,
        nearest_sample: u64,
        nearest_dist: u64,
    },
    FailedTestClaimSingleShot,
    FailedMissingBenchMetric,
}

/// Tracks best-of-`BENCH_MAX_ATTEMPTS` nearest-band sample selection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BenchBandEstimator {
    is_bench: bool,
    min_floor: u64,
    max_ceiling: u64,
    attempts: u64,
    best_sample: u64,
    best_dist: u64,
}

impl BenchBandEstimator {
    #[must_use]
    pub const fn new(is_bench: bool, min_floor: u64, max_ceiling: u64) -> Self {
        Self {
            is_bench,
            min_floor,
            max_ceiling,
            attempts: 0,
            best_sample: 0,
            best_dist: u64::MAX,
        }
    }

    const fn band_distance(&self, sample: u64) -> u64 {
        if sample < self.min_floor {
            self.min_floor - sample
        } else {
            sample.saturating_sub(self.max_ceiling)
        }
    }

    /// Record a `test` claim run (`passed`: exit 0). Never retries!
    pub fn record_test_run(&mut self, passed: bool) -> BenchEstimatorDecision {
        let next = self.attempts.saturating_add(1);
        self.attempts = bench_attempts_advance_b151(self.attempts, next);
        if passed {
            BenchEstimatorDecision::PassedInBand {
                attempts: self.attempts,
                selected_sample: 0,
            }
        } else {
            BenchEstimatorDecision::FailedTestClaimSingleShot
        }
    }

    /// Record a `bench` claim sample (`None` if command printed no `METRIC` line).
    pub fn record_bench_sample(&mut self, sample: Option<u64>) -> BenchEstimatorDecision {
        let next = self.attempts.saturating_add(1);
        self.attempts = bench_attempts_advance_b151(self.attempts, next);
        let Some(val) = sample else {
            return BenchEstimatorDecision::FailedMissingBenchMetric;
        };
        let dist = self.band_distance(val);
        if dist <= self.best_dist {
            self.best_dist = nearest_band_dist_clamp_b151(dist, self.best_dist);
            self.best_sample = val;
        }
        if self.best_dist == 0 {
            BenchEstimatorDecision::PassedInBand {
                attempts: self.attempts,
                selected_sample: self.best_sample,
            }
        } else if bench_retry_permitted_b151(
            self.is_bench,
            self.best_dist,
            self.attempts,
            BENCH_MAX_ATTEMPTS,
        ) {
            BenchEstimatorDecision::RetryBenchSample {
                attempts: self.attempts,
                nearest_sample: self.best_sample,
                nearest_dist: self.best_dist,
            }
        } else {
            BenchEstimatorDecision::FailedOutOfBandExhausted {
                attempts: self.attempts,
                nearest_sample: self.best_sample,
                nearest_dist: self.best_dist,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keeps_nearest_sample_to_two_sided_band_and_never_retries_test_claims() {
        let mut test_est = BenchBandEstimator::new(false, 0, 0);
        assert_eq!(
            test_est.record_test_run(false),
            BenchEstimatorDecision::FailedTestClaimSingleShot
        );

        // Two-sided band [100, 200]: overshoot 250 (dist 50), undershoot 80 (dist 20), then 60 (dist 40)
        // -> reports nearest sample 80 (dist 20) after 3 attempts!
        let mut bench_est = BenchBandEstimator::new(true, 100, 200);
        assert_eq!(
            bench_est.record_bench_sample(Some(250)),
            BenchEstimatorDecision::RetryBenchSample {
                attempts: 1,
                nearest_sample: 250,
                nearest_dist: 50,
            }
        );
        assert_eq!(
            bench_est.record_bench_sample(Some(80)),
            BenchEstimatorDecision::RetryBenchSample {
                attempts: 2,
                nearest_sample: 80,
                nearest_dist: 20,
            }
        );
        assert_eq!(
            bench_est.record_bench_sample(Some(60)),
            BenchEstimatorDecision::FailedOutOfBandExhausted {
                attempts: 3,
                nearest_sample: 80,
                nearest_dist: 20,
            }
        );
    }
}
