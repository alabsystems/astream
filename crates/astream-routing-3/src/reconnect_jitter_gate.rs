// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pure stack decorrelated-jitter WAN reconnect gate (`Astream.Wire.TlaReconnectJitterGate`).
//!
//! Prevents synchronized reconnect storms against `asb`'s `MAX_CONNS` ceiling
//! after a WAN/VPN blip: uses deterministic SplitMix64 mixing over `(session_seed, attempt)`
//! with **zero heap allocations** and **zero external RNG dependencies**.

#[cfg(clean_islands)]
#[path = "reconnect_jitter_gate_island.rs"]
mod reconnect_jitter_gate_island;
#[cfg(clean_islands)]
pub use reconnect_jitter_gate_island::{reconnect_attempt_advance, reconnect_delay_clamp};

/// Default base reconnect delay (`50 ms`).
pub const DEFAULT_BASE_DELAY_MS: u64 = 50;

/// Default cap on reconnect backoff (`10_000 ms = 10 s`).
pub const DEFAULT_MAX_DELAY_MS: u64 = 10_000;

#[cfg(not(clean_islands))]
/// Monotonically advance the consecutive reconnect attempt counter within an outage epoch.
#[must_use]
pub const fn reconnect_attempt_advance(cur_attempt: u64, cand_attempt: u64) -> u64 {
    if cur_attempt < cand_attempt {
        cand_attempt
    } else {
        cur_attempt
    }
}

#[cfg(not(clean_islands))]
/// Clamp computed reconnect delay to `max_delay_ms`.
#[must_use]
pub const fn reconnect_delay_clamp(cand_delay_ms: u64, max_delay_ms: u64) -> u64 {
    if cand_delay_ms < max_delay_ms {
        cand_delay_ms
    } else {
        max_delay_ms
    }
}

contract_fn! {
    /// True iff `now_ms` has reached `next_allowed_ms`.
    #[must_use]
    pub const fn reconnect_ready(next_allowed_ms: u64, now_ms: u64) -> bool
    clauses [ensures result == (next_allowed_ms <= now_ms)]
    {
        next_allowed_ms <= now_ms
    }
}

const fn splitmix64(seed: u64) -> u64 {
    let z0 = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let z1 = (z0 ^ (z0 >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    let z2 = (z1 ^ (z1 >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z2 ^ (z2 >> 31)
}

/// Pure stack per-session reconnect backoff gate.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ReconnectJitterGate {
    session_seed: u64,
    attempt: u64,
    last_delay_ms: u64,
    next_allowed_ms: u64,
    base_delay_ms: u64,
    max_delay_ms: u64,
}

impl ReconnectJitterGate {
    #[must_use]
    pub const fn new(session_seed: u64, base_delay_ms: u64, max_delay_ms: u64) -> Self {
        let base = if base_delay_ms == 0 {
            DEFAULT_BASE_DELAY_MS
        } else {
            base_delay_ms
        };
        let max_d = if max_delay_ms < base {
            base
        } else {
            max_delay_ms
        };
        Self {
            session_seed,
            attempt: 0,
            last_delay_ms: 0,
            next_allowed_ms: 0,
            base_delay_ms: base,
            max_delay_ms: max_d,
        }
    }

    #[must_use]
    pub const fn attempt(&self) -> u64 {
        self.attempt
    }

    #[must_use]
    pub const fn last_delay_ms(&self) -> u64 {
        self.last_delay_ms
    }

    #[must_use]
    pub const fn next_allowed_ms(&self) -> u64 {
        self.next_allowed_ms
    }

    #[must_use]
    pub const fn can_dial_now(&self, now_ms: u64) -> bool {
        reconnect_ready(self.next_allowed_ms, now_ms)
    }

    /// Schedule the next decorrelated-jitter retry after a failed dial at `now_ms`.
    pub fn record_failure(&mut self, now_ms: u64) -> u64 {
        let cand_att = self.attempt.saturating_add(1);
        self.attempt = reconnect_attempt_advance(self.attempt, cand_att);

        let shift = if self.attempt <= 16 {
            self.attempt.saturating_sub(1) as u32
        } else {
            16
        };
        let exp_cap = self.base_delay_ms.saturating_mul(1u64 << (shift & 63));
        let bounded_cap = reconnect_delay_clamp(exp_cap, self.max_delay_ms);

        // Spread deterministically in [bounded_cap / 2, bounded_cap] using low 10 bits of SplitMix64
        let rnd = splitmix64(self.session_seed ^ self.attempt) & 0x3ff;
        let half = bounded_cap >> 1;
        let jitter_span = bounded_cap.saturating_sub(half);
        let jitter = jitter_span.saturating_mul(rnd) >> 10;
        let raw_delay = half.saturating_add(jitter);
        let final_delay = reconnect_delay_clamp(raw_delay, self.max_delay_ms);

        self.last_delay_ms = final_delay;
        self.next_allowed_ms = now_ms.saturating_add(final_delay);
        final_delay
    }

    /// Reset backoff state upon a healthy `Attached` session handshake.
    pub fn record_connected(&mut self) {
        self.attempt = 0;
        self.last_delay_ms = 0;
        self.next_allowed_ms = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decorrelates_peer_sessions_and_respects_max_delay() {
        let mut g1 = ReconnectJitterGate::new(0x1111, 100, 2_000);
        let mut g2 = ReconnectJitterGate::new(0x2222, 100, 2_000);

        let mut diverged = false;
        let mut t = 1_000u64;
        for _ in 0..8 {
            let d1 = g1.record_failure(t);
            let d2 = g2.record_failure(t);
            assert!(d1 <= 2_000);
            assert!(d2 <= 2_000);
            if d1 != d2 {
                diverged = true;
            }
            assert!(!g1.can_dial_now(t + d1.saturating_sub(1)));
            assert!(g1.can_dial_now(t + d1));
            t += 2_000;
        }
        assert!(diverged);

        g1.record_connected();
        assert_eq!(g1.attempt(), 0);
        assert!(g1.can_dial_now(0));
    }
}
