// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Deterministic FNV-1a-seeded exponential retry backoff with thundering-herd spread
//! (`astream_wire::fnv1a_64`, `Astream.Quota.TlaCooldownJitter`).

use astream_wire::fnv1a_64;

#[cfg(clean_islands)]
#[path = "cooldown_jitter_island.rs"]
mod cooldown_jitter_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn jitter_delay_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn jitter_attempt_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use cooldown_jitter_island::{jitter_attempt_advance, jitter_delay_clamp};

/// Maximum backoff delay (`60` seconds).
pub const MAX_JITTER_BACKOFF_MS: u64 = 60_000;

contract_fn! {
    /// Verified retry readiness (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `jitter_ready_at_isl`.
    #[must_use]
    pub const fn jitter_ready_at(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Deterministic, replay-safe backoff schedule seeded by `(session_id, attempt)`.
#[derive(Debug, Clone)]
pub struct CooldownJitterPlanner {
    base_ms: u64,
    attempt: u64,
    ready_at_ms: u64,
}

impl CooldownJitterPlanner {
    #[must_use]
    pub const fn new(base_ms: u64) -> Self {
        Self {
            base_ms: if base_ms == 0 { 250 } else { base_ms },
            attempt: 0,
            ready_at_ms: 0,
        }
    }

    #[allow(clippy::manual_unwrap_or, clippy::manual_unwrap_or_default)]
    pub fn schedule_retry(&mut self, session_id: &str, now_ms: u64) -> u64 {
        let next_att = self.attempt.saturating_add(1);
        self.attempt = jitter_attempt_advance(self.attempt, next_att);
        let raw_shift = (self.attempt.saturating_sub(1)) as u32;
        let shift = (if raw_shift < 10 { raw_shift } else { 10 }) & 63;
        let exp = self.base_ms.saturating_mul(1u64 << (shift & 63));
        let capped = jitter_delay_clamp(exp, MAX_JITTER_BACKOFF_MS);
        let mut seed = Vec::new();
        seed.extend_from_slice(session_id.as_bytes());
        seed.extend_from_slice(&self.attempt.to_le_bytes());
        let quarter = capped >> 2;
        let spread = if quarter == 0 { 1 } else { quarter };
        let jitter = match fnv1a_64(&seed).checked_rem(spread) {
            Some(r) => r,
            None => 0,
        };
        let total = jitter_delay_clamp(capped.saturating_add(jitter), MAX_JITTER_BACKOFF_MS);
        self.ready_at_ms = now_ms.saturating_add(total);
        self.ready_at_ms
    }

    #[must_use]
    pub const fn is_ready(&self, now_ms: u64) -> bool {
        jitter_ready_at(now_ms, self.ready_at_ms)
    }

    pub fn reset(&mut self) {
        self.attempt = 0;
        self.ready_at_ms = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fnv1a_jitter_spreads_peer_sessions_deterministically_without_rng_seam() {
        let mut a = CooldownJitterPlanner::new(500);
        let mut b = CooldownJitterPlanner::new(500);
        let ra = a.schedule_retry("@s-tab-1", 10_000);
        let rb = b.schedule_retry("@s-tab-2", 10_000);
        assert!(ra >= 10_500 && rb >= 10_500);
        assert_ne!(ra, rb);
        assert!(!a.is_ready(ra - 1));
        assert!(a.is_ready(ra));
    }
}
