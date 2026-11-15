// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! OIDC workload JWT `iat`/`nbf`/`exp` clock-skew evaluator (`docs/ROADMAP.md` §1) enforcing bounded
//! clock skew and monotonic `iat` freshness per workload subject (`Astream.ExtAuth.TlaOidcClaimsWindow`).

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
#[path = "oidc_claims_window_island.rs"]
mod oidc_claims_window_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ext_skew_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ext_iat_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use oidc_claims_window_island::{ext_iat_advance, ext_skew_clamp};

/// Maximum OIDC clock-skew tolerance (`30_000` ms).
pub const MAX_OIDC_SKEW_MS: u64 = 30_000;

contract_fn! {
    /// Verified OIDC claim time bound (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ext_token_valid_isl`.
    #[must_use]
    pub const fn ext_token_valid(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct OidcClaimsValidator {
    skew_ms: u64,
    latest_iat_ms: u64,
}

impl OidcClaimsValidator {
    #[must_use]
    pub const fn new(skew_ms: u64) -> Self {
        Self {
            skew_ms: ext_skew_clamp(skew_ms, MAX_OIDC_SKEW_MS),
            latest_iat_ms: 0,
        }
    }

    pub fn validate(&mut self, iat_ms: u64, nbf_ms: u64, exp_ms: u64, now_ms: u64) -> bool {
        if iat_ms == 0 || iat_ms > exp_ms {
            return false;
        }
        let Some(min_exp) = nbf_ms.checked_add(1) else {
            return false;
        };
        if !ext_token_valid(exp_ms, min_exp) {
            return false;
        }
        let adj_now = now_ms.saturating_add(self.skew_ms);
        if !ext_token_valid(adj_now, nbf_ms) || !ext_token_valid(adj_now, iat_ms) {
            return false;
        }
        if !ext_token_valid(exp_ms.saturating_add(self.skew_ms), now_ms) {
            return false;
        }
        if !ext_token_valid(iat_ms, self.latest_iat_ms) {
            return false;
        }
        self.latest_iat_ms = ext_iat_advance(self.latest_iat_ms, iat_ms);
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn validates_nbf_exp_with_bounded_skew_and_monotonic_iat() {
        let mut v = OidcClaimsValidator::new(5_000);
        assert!(v.validate(10_000, 10_000, 70_000, 8_000));
        assert!(!v.validate(9_000, 9_000, 70_000, 12_000));
        assert!(!v.validate(15_000, 15_000, 20_000, 30_000));
    }
}
