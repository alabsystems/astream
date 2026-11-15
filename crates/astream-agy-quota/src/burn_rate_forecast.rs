// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Depletion-horizon forecaster estimating remaining minutes of `autopilot=cruise` execution at the
//! observed credit burn rate before a 5-hour window hits reserve (`Astream.AgyQuota.TlaBurnRateForecast`).

#[cfg(clean_islands)]
#[path = "burn_rate_forecast_island.rs"]
mod burn_rate_forecast_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn aq_rate_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn aq_sample_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use burn_rate_forecast_island::{aq_rate_clamp, aq_sample_advance};

/// Maximum burn-rate bound (`1_000_000` credits/minute).
pub const MAX_BURN_PER_MIN: u64 = 1_000_000;

contract_fn! {
    /// Verified runway safety check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `aq_runway_safe_isl`.
    #[must_use]
    pub const fn aq_runway_safe(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct BurnRateForecaster {
    samples: u64,
}

impl BurnRateForecaster {
    #[must_use]
    pub const fn new() -> Self {
        Self { samples: 0 }
    }

    pub fn runway_exceeds_minutes(
        &mut self,
        usable_credits: u64,
        credits_per_min: u64,
        min_minutes_needed: u64,
    ) -> bool {
        self.samples = aq_sample_advance(self.samples, self.samples.saturating_add(1));
        let rate = aq_rate_clamp(credits_per_min, MAX_BURN_PER_MIN);
        if rate == 0 {
            return true;
        }
        let required_credits = rate.saturating_mul(min_minutes_needed);
        aq_runway_safe(usable_credits, required_credits)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flags_insufficient_runway_before_window_exhaustion() {
        let mut f = BurnRateForecaster::new();
        assert!(f.runway_exceeds_minutes(6_000, 100, 45));
        assert!(!f.runway_exceeds_minutes(3_000, 100, 45));
    }
}
