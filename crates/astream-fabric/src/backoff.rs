// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Adaptive WAN reconnect backoff and RFC 6298 RTT/RTO timeout estimation.
//!
//! When dozens of `aterm` agents or `FederationRunner` links traverse high-RTT
//! WAN / Internet paths (`docs/DESIGN-aterm-fabric.md` §15), fixed reconnect
//! sleeps either stampede `MAX_CONNS` on recovery or stall far longer than needed,
//! and static socket timeouts misclassify normal WAN latency spikes as dead peers.
//!
//! This module provides two deterministic, allocation-free primitives backed by
//! the `Astream.Broker.TlaAdaptiveBackoff` Clean island:
//! - [`AdaptiveBackoff`]: AWS-style decorrelated-jitter exponential backoff driven
//!   by a caller-seeded SplitMix64 stream (so replay and tests are 100% deterministic),
//!   provably bounded by `max_ms` and monotone in `attempt`.
//! - [`RttEstimator`]: integer RFC 6298 smoothed RTT (`srtt_us`) + mean deviation
//!   (`rttvar_us`) + clamped retransmission/probe timeout (`rto_ms`).

#[cfg(clean_islands)]
#[path = "backoff_island.rs"]
mod backoff_island;
#[cfg(clean_islands)]
pub use backoff_island::{backoff_attempt_advance, backoff_delay_clamp};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn backoff_delay_clamp(proposed_ms: u64, max_ms: u64) -> u64 {
    if proposed_ms < max_ms {
        proposed_ms
    } else {
        max_ms
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn backoff_attempt_advance(cur_attempt: u64, next_attempt: u64) -> u64 {
    if cur_attempt < next_attempt {
        next_attempt
    } else {
        cur_attempt
    }
}

/// Default minimum reconnect delay (`25 ms`).
pub const DEFAULT_BASE_BACKOFF_MS: u64 = 25;

/// Default maximum reconnect ceiling (`30_000 ms`).
pub const DEFAULT_MAX_BACKOFF_MS: u64 = 30_000;

/// Default minimum RTO floor (`100 ms`).
pub const DEFAULT_MIN_RTO_MS: u64 = 100;

/// Default maximum RTO ceiling (`60_000 ms`).
pub const DEFAULT_MAX_RTO_MS: u64 = 60_000;

/// Clamp a proposed backoff or timeout delay (in milliseconds) to `max_ms`.
#[inline]
#[must_use]
pub const fn clamp_backoff_delay_ms(proposed_ms: u64, max_ms: u64) -> u64 {
    backoff_delay_clamp(proposed_ms, max_ms)
}

/// Advance the retry attempt counter monotonically.
#[inline]
#[must_use]
pub const fn advance_backoff_attempt(cur_attempt: u64, next_attempt: u64) -> u64 {
    backoff_attempt_advance(cur_attempt, next_attempt)
}

contract_fn! {
    /// Contracted check that a computed backoff or RTO delay never exceeds `max_ms`.
    #[must_use]
    pub const fn backoff_delay_in_range(delay_ms: u64, max_ms: u64) -> bool
    clauses [ensures result == (delay_ms <= max_ms)]
    {
        delay_ms <= max_ms
    }
}

#[inline]
fn splitmix64_next(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// Deterministic decorrelated-jitter backoff schedule (`sleep = min(max_ms, rand(base_ms..=prev*3))`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdaptiveBackoff {
    base_ms: u64,
    max_ms: u64,
    attempt: u64,
    prev_delay_ms: u64,
    rng_state: u64,
}

impl AdaptiveBackoff {
    /// Construct a schedule seeded by `seed` (e.g. principal hash ^ link index).
    pub fn new(base_ms: u64, max_ms: u64, seed: u64) -> Self {
        let clamped_base = clamp_backoff_delay_ms(base_ms, max_ms);
        Self {
            base_ms: clamped_base,
            max_ms,
            attempt: 0,
            prev_delay_ms: clamped_base,
            rng_state: seed ^ 0xD1B5_4A32_D192_ED03,
        }
    }

    /// Construct with `DEFAULT_BASE_BACKOFF_MS` (`25 ms`) and `DEFAULT_MAX_BACKOFF_MS` (`30 s`).
    pub fn with_defaults(seed: u64) -> Self {
        Self::new(DEFAULT_BASE_BACKOFF_MS, DEFAULT_MAX_BACKOFF_MS, seed)
    }

    pub fn attempt(&self) -> u64 {
        self.attempt
    }

    pub fn max_ms(&self) -> u64 {
        self.max_ms
    }

    pub fn last_delay_ms(&self) -> u64 {
        self.prev_delay_ms
    }

    /// Compute the next decorrelated-jitter delay in `[base_ms, max_ms]` and
    /// advance `attempt` monotonically.
    pub fn next_delay_ms(&mut self) -> u64 {
        let proposed_attempt = self.attempt.saturating_add(1);
        self.attempt = advance_backoff_attempt(self.attempt, proposed_attempt);

        let upper_unclamped = self.prev_delay_ms.saturating_mul(3).max(self.base_ms);
        let upper = clamp_backoff_delay_ms(upper_unclamped, self.max_ms);
        let span = upper.saturating_sub(self.base_ms);
        let jitter = if span == 0 {
            0
        } else {
            let r = splitmix64_next(&mut self.rng_state);
            if span == u64::MAX {
                r
            } else {
                r % (span + 1)
            }
        };
        let raw_delay = self.base_ms.saturating_add(jitter);
        let delay = clamp_backoff_delay_ms(raw_delay, self.max_ms);
        let _ = backoff_delay_in_range(delay, self.max_ms);
        self.prev_delay_ms = delay;
        delay
    }

    /// Reset backoff state after a healthy session handshake/heartbeat.
    pub fn reset(&mut self) {
        self.attempt = 0;
        self.prev_delay_ms = self.base_ms;
    }
}

/// Integer RFC 6298 RTT and adaptive probe/read timeout (`RTO`) estimator.
///
/// Tracks smoothed RTT (`srtt_us`) and RTT variation (`rttvar_us`) in microseconds:
/// - First sample `R`: `srtt = R`, `rttvar = R / 2`
/// - Subsequent sample `R`:
///   `rttvar = (3 * rttvar + |srtt - R|) / 4`,
///   `srtt   = (7 * srtt + R) / 8`
/// - `RTO = clamp(srtt + max(1_000 us, 4 * rttvar), min_rto_ms..=max_rto_ms)`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RttEstimator {
    srtt_us: u64,
    rttvar_us: u64,
    samples: u64,
    min_rto_ms: u64,
    max_rto_ms: u64,
}

impl RttEstimator {
    pub fn new(min_rto_ms: u64, max_rto_ms: u64) -> Self {
        let floor = clamp_backoff_delay_ms(min_rto_ms, max_rto_ms);
        Self {
            srtt_us: 0,
            rttvar_us: 0,
            samples: 0,
            min_rto_ms: floor,
            max_rto_ms,
        }
    }

    pub fn with_defaults() -> Self {
        Self::new(DEFAULT_MIN_RTO_MS, DEFAULT_MAX_RTO_MS)
    }

    pub fn samples(&self) -> u64 {
        self.samples
    }

    pub fn srtt_us(&self) -> u64 {
        self.srtt_us
    }

    pub fn rttvar_us(&self) -> u64 {
        self.rttvar_us
    }

    /// Record a measured round-trip sample in microseconds (`Hello`/`Nonce` or heartbeat RTT).
    pub fn observe_rtt_us(&mut self, sample_us: u64) {
        let r = sample_us.max(1);
        if self.samples == 0 {
            self.srtt_us = r;
            self.rttvar_us = (r / 2).max(1);
        } else {
            let diff = self.srtt_us.abs_diff(r);
            self.rttvar_us = self.rttvar_us.saturating_mul(3).saturating_add(diff) / 4;
            self.srtt_us = self.srtt_us.saturating_mul(7).saturating_add(r) / 8;
        }
        let next_s = self.samples.saturating_add(1);
        self.samples = advance_backoff_attempt(self.samples, next_s);
    }

    /// Compute the current adaptive timeout (`RTO`) in milliseconds, clamped to
    /// `[min_rto_ms, max_rto_ms]`. Before the first sample arrives, returns
    /// `clamp(1_000, min_rto_ms..=max_rto_ms)`.
    pub fn rto_ms(&self) -> u64 {
        let raw_ms = if self.samples == 0 {
            1_000u64
        } else {
            let k_var_us = self.rttvar_us.saturating_mul(4).max(1_000);
            let total_us = self.srtt_us.saturating_add(k_var_us);
            total_us.saturating_add(999) / 1_000
        };
        let floored = raw_ms.max(self.min_rto_ms);
        let rto = clamp_backoff_delay_ms(floored, self.max_rto_ms);
        let _ = backoff_delay_in_range(rto, self.max_rto_ms);
        rto
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decorrelated_jitter_stays_bounded_deterministic_and_spreads_peers() {
        let mut a1 = AdaptiveBackoff::new(20, 5_000, 0x1111);
        let mut a2 = AdaptiveBackoff::new(20, 5_000, 0x1111);
        let mut b = AdaptiveBackoff::new(20, 5_000, 0x2222);

        let mut seq_a = Vec::new();
        let mut seq_b = Vec::new();
        for step in 1..=32u64 {
            let d1 = a1.next_delay_ms();
            let d2 = a2.next_delay_ms();
            let db = b.next_delay_ms();
            assert_eq!(d1, d2, "same seed must replay identically");
            assert_eq!(a1.attempt(), step);
            assert!((20..=5_000).contains(&d1));
            assert!((20..=5_000).contains(&db));
            assert!(backoff_delay_in_range(d1, 5_000));
            seq_a.push(d1);
            seq_b.push(db);
        }
        assert_ne!(seq_a, seq_b, "distinct peer seeds must desynchronize");
        a1.reset();
        assert_eq!(a1.attempt(), 0);
        assert_eq!(a1.last_delay_ms(), 20);
    }

    #[test]
    fn rtt_estimator_scales_rto_across_lan_and_wan_samples() {
        let mut lan = RttEstimator::new(50, 10_000);
        for _ in 0..8 {
            lan.observe_rtt_us(800); // 0.8 ms LAN
        }
        assert_eq!(lan.rto_ms(), 50, "LAN RTT clamps cleanly to min_rto_ms");

        let mut wan = RttEstimator::new(50, 10_000);
        wan.observe_rtt_us(180_000); // 180 ms transcontinental link
        wan.observe_rtt_us(220_000); // 220 ms jitter
        let rto = wan.rto_ms();
        assert!((250..=10_000).contains(&rto), "unexpected WAN RTO {rto}ms");
        assert!(backoff_delay_in_range(rto, 10_000));
    }
}
