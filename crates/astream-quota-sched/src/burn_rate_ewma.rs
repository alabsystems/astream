// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Integer EWMA quota burn-rate forecaster comparing time-to-exhaustion (`tte_ms`) against
//! next pool reset (`Astream.Quota.TlaBurnRateEwma`).

#[cfg(clean_islands)]
#[path = "burn_rate_ewma_island.rs"]
mod burn_rate_ewma_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn burn_rate_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn burn_sample_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use burn_rate_ewma_island::{burn_rate_clamp, burn_sample_advance};

/// Maximum tracked burn rate (`1_000_000` units/minute).
pub const MAX_BURN_UNITS_PER_MIN: u64 = 1_000_000;

contract_fn! {
    /// Verified sustainability check (`threshold <= observed`, i.e. `ms_to_reset <= tte_ms`),
    /// linked via `clean-kernel-defeq` to `burn_outlasts_reset_isl`.
    #[must_use]
    pub const fn burn_outlasts_reset(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// EWMA burn-rate estimator (`ewma = (3 * ewma + sample) / 4`).
#[derive(Debug, Clone, Default)]
pub struct BurnRateForecaster {
    ewma_per_min: u64,
    samples: u64,
}

impl BurnRateForecaster {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            ewma_per_min: 0,
            samples: 0,
        }
    }

    pub fn observe_minute_burn(&mut self, units_per_min: u64) -> u64 {
        let s = burn_rate_clamp(units_per_min, MAX_BURN_UNITS_PER_MIN);
        self.ewma_per_min = if self.samples == 0 {
            s
        } else {
            (self.ewma_per_min.saturating_mul(3).saturating_add(s)) >> 2
        };
        self.samples = burn_sample_advance(self.samples, self.samples.saturating_add(1));
        self.ewma_per_min
    }

    /// Returns `true` iff `remaining_units` at `ewma_per_min` outlasts `minutes_to_reset`.
    #[must_use]
    pub const fn sustainable_until_reset(
        &self,
        remaining_units: u64,
        minutes_to_reset: u64,
    ) -> bool {
        if remaining_units == 0 && minutes_to_reset > 0 {
            return false;
        }
        if self.ewma_per_min == 0 {
            return true;
        }
        let tte_min = remaining_units / self.ewma_per_min;
        burn_outlasts_reset(tte_min, minutes_to_reset)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ewma_burn_forecaster_flags_premature_exhaustion_before_window_reset() {
        let mut b = BurnRateForecaster::new();
        assert_eq!(b.observe_minute_burn(100), 100);
        assert!(b.sustainable_until_reset(6_000, 50));
        assert!(!b.sustainable_until_reset(3_000, 50));
    }
}
