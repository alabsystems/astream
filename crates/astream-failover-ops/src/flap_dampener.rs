// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! BGP-style exponential half-life failover flap dampener (`ROADMAP.md` line 106,
//! `Astream.Failover.TlaFlapDampener`).

#[cfg(clean_islands)]
#[path = "flap_dampener_island.rs"]
mod flap_dampener_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn flap_penalty_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn flap_ready_at_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use flap_dampener_island::{flap_penalty_clamp, flap_ready_at_advance};

/// Hard cap on accumulated flap penalty score.
pub const MAX_FLAP_PENALTY_SCORE: u64 = 1024;
/// Penalty added per observed leader transition.
pub const FLAP_PENALTY_PER_EVENT: u64 = 250;

contract_fn! {
    /// Verified cooldown check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `flap_cooled_down_isl`.
    #[must_use]
    pub const fn flap_cooled_down(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Dampener state suppressing rapid oscillating elections.
#[derive(Debug, Clone)]
pub struct FailoverFlapDampener {
    half_life_ms: u64,
    suppress_threshold: u64,
    penalty: u64,
    last_decay_ms: u64,
    ready_at_ms: u64,
    initialized: bool,
}

impl Default for FailoverFlapDampener {
    fn default() -> Self {
        Self::new()
    }
}

impl FailoverFlapDampener {
    #[must_use]
    pub const fn new() -> Self {
        Self::with_params(5_000, 500)
    }

    #[must_use]
    pub const fn with_params(half_life_ms: u64, suppress_threshold: u64) -> Self {
        Self {
            half_life_ms: if half_life_ms == 0 { 1 } else { half_life_ms },
            suppress_threshold: flap_penalty_clamp(suppress_threshold, MAX_FLAP_PENALTY_SCORE),
            penalty: 0,
            last_decay_ms: 0,
            ready_at_ms: 0,
            initialized: false,
        }
    }

    fn decay_to(&mut self, now_ms: u64) {
        if !self.initialized || now_ms <= self.last_decay_ms {
            return;
        }
        let elapsed = now_ms.saturating_sub(self.last_decay_ms);
        let Some(halvings) = elapsed.checked_div(self.half_life_ms) else {
            return;
        };
        if halvings > 0 {
            self.penalty = if halvings >= 63 {
                0
            } else {
                self.penalty >> ((halvings as u32) & 63)
            };
            self.last_decay_ms = self
                .last_decay_ms
                .saturating_add(halvings.saturating_mul(self.half_life_ms));
        }
    }

    /// Records a failover event at `now_ms`, advancing `ready_at_ms` when `penalty >= suppress_threshold`.
    pub fn record_flap(&mut self, now_ms: u64) -> u64 {
        if !self.initialized {
            self.last_decay_ms = now_ms;
            self.initialized = true;
        } else {
            self.decay_to(now_ms);
        }
        let bumped = self.penalty.saturating_add(FLAP_PENALTY_PER_EVENT);
        self.penalty = flap_penalty_clamp(bumped, MAX_FLAP_PENALTY_SCORE);
        if self.penalty >= self.suppress_threshold {
            let cooldown = now_ms.saturating_add(self.half_life_ms);
            self.ready_at_ms = flap_ready_at_advance(self.ready_at_ms, cooldown);
        }
        self.penalty
    }

    /// Returns `true` iff autonomous failover is allowed at `now_ms`.
    pub fn may_initiate_failover(&mut self, now_ms: u64) -> bool {
        self.decay_to(now_ms);
        self.penalty < self.suppress_threshold && flap_cooled_down(now_ms, self.ready_at_ms)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rapid_flaps_suppress_until_half_life_decays_penalty() {
        let mut d = FailoverFlapDampener::with_params(1_000, 500);
        assert!(d.may_initiate_failover(100));
        assert_eq!(d.record_flap(100), 250);
        assert!(d.may_initiate_failover(200));
        // Second immediate flap reaches 500 >= suppress_threshold!
        assert_eq!(d.record_flap(200), 500);
        assert!(!d.may_initiate_failover(500));
        // After 1_000 ms half-life (at 1_200 ms), penalty halves to 250 < 500 and cooldown expires!
        assert!(d.may_initiate_failover(1_200));
    }
}
