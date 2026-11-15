// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm harness agy` & `aterm harness agy pick` dual-window model pool rotator
//! (`Astream.Agent.TlaAgyQuotaPoolRotator`).
//!
//! Models `aterm`'s separate Gemini vs Claude/GPT quota pools over both the weekly and 5-hour
//! windows (`0..=10_000` bps): computes each pool's bottleneck `min(weekly_bps, five_hour_bps)`
//! and rotates fan-out worker launches away from low or spent pools (`< reserve_floor_bps`)
//! before spawning workers.

#[cfg(clean_islands)]
#[path = "agy_quota_pool_rotator_island.rs"]
mod agy_quota_pool_rotator_island;
#[cfg(clean_islands)]
pub use agy_quota_pool_rotator_island::{agy_pool_bps_clamp_b119, agy_rotation_epoch_advance_b119};

#[cfg(not(clean_islands))]
/// Clamp remaining quota basis points to `max_bps` (`10_000`).
#[must_use]
pub const fn agy_pool_bps_clamp_b119(cand_bps: u64, max_bps: u64) -> u64 {
    if cand_bps < max_bps {
        cand_bps
    } else {
        max_bps
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `rotation_epoch`.
#[must_use]
pub const fn agy_rotation_epoch_advance_b119(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `effective_bps >= reserve_floor_bps`.
    #[must_use]
    pub const fn agy_pool_healthy_b119(effective_bps: u64, reserve_floor_bps: u64) -> bool
    clauses [ensures result == (reserve_floor_bps <= effective_bps)]
    {
        reserve_floor_bps <= effective_bps
    }
}

pub const MAX_QUOTA_BPS: u64 = 10_000;

/// Model pool families tracked by `aterm harness agy`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AgyModelPool {
    Gemini,
    Claude,
    Gpt,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct PoolGauge {
    weekly_bps: u64,
    five_hour_bps: u64,
}

impl PoolGauge {
    const FULL: Self = Self {
        weekly_bps: MAX_QUOTA_BPS,
        five_hour_bps: MAX_QUOTA_BPS,
    };

    #[must_use]
    const fn effective_bps(self) -> u64 {
        if self.weekly_bps < self.five_hour_bps {
            self.weekly_bps
        } else {
            self.five_hour_bps
        }
    }
}

/// Result of `aterm harness agy pick [<requested>]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AgyPickDecision {
    Selected {
        pool: AgyModelPool,
        rotated: bool,
        effective_bps: u64,
        rotation_epoch: u64,
    },
    AllPoolsBelowReserve {
        best_pool: AgyModelPool,
        effective_bps: u64,
    },
}

/// Dual-horizon quota tracker and fallback rotator for `aterm harness agy`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AgyQuotaPoolRotator {
    gemini: PoolGauge,
    claude: PoolGauge,
    gpt: PoolGauge,
    reserve_floor_bps: u64,
    rotation_epoch: u64,
}

impl Default for AgyQuotaPoolRotator {
    fn default() -> Self {
        Self::new(1_000)
    }
}

impl AgyQuotaPoolRotator {
    #[must_use]
    pub const fn new(raw_reserve_floor_bps: u64) -> Self {
        Self {
            gemini: PoolGauge::FULL,
            claude: PoolGauge::FULL,
            gpt: PoolGauge::FULL,
            reserve_floor_bps: agy_pool_bps_clamp_b119(raw_reserve_floor_bps, MAX_QUOTA_BPS),
            rotation_epoch: 0,
        }
    }

    pub fn update_pool(&mut self, pool: AgyModelPool, weekly_bps: u64, five_hour_bps: u64) {
        let g = PoolGauge {
            weekly_bps: agy_pool_bps_clamp_b119(weekly_bps, MAX_QUOTA_BPS),
            five_hour_bps: agy_pool_bps_clamp_b119(five_hour_bps, MAX_QUOTA_BPS),
        };
        match pool {
            AgyModelPool::Gemini => self.gemini = g,
            AgyModelPool::Claude => self.claude = g,
            AgyModelPool::Gpt => self.gpt = g,
        }
    }

    #[must_use]
    const fn gauge_for(&self, pool: AgyModelPool) -> PoolGauge {
        match pool {
            AgyModelPool::Gemini => self.gemini,
            AgyModelPool::Claude => self.claude,
            AgyModelPool::Gpt => self.gpt,
        }
    }

    /// Pick `requested` if healthy (`>= reserve_floor_bps`); otherwise rotate to the healthiest pool.
    pub fn pick(&mut self, requested: AgyModelPool) -> AgyPickDecision {
        let req_eff = self.gauge_for(requested).effective_bps();
        if agy_pool_healthy_b119(req_eff, self.reserve_floor_bps) {
            return AgyPickDecision::Selected {
                pool: requested,
                rotated: false,
                effective_bps: req_eff,
                rotation_epoch: self.rotation_epoch,
            };
        }
        let order = [
            AgyModelPool::Gemini,
            AgyModelPool::Claude,
            AgyModelPool::Gpt,
        ];
        let mut best_pool = requested;
        let mut best_eff = req_eff;
        let mut idx = 0usize;
        while let Some(&cand) = order.get(idx) {
            let eff = self.gauge_for(cand).effective_bps();
            if eff > best_eff {
                best_eff = eff;
                best_pool = cand;
            }
            idx = idx.saturating_add(1);
        }
        if agy_pool_healthy_b119(best_eff, self.reserve_floor_bps) {
            let next_ep = self.rotation_epoch.saturating_add(1);
            self.rotation_epoch = agy_rotation_epoch_advance_b119(self.rotation_epoch, next_ep);
            AgyPickDecision::Selected {
                pool: best_pool,
                rotated: best_pool != requested,
                effective_bps: best_eff,
                rotation_epoch: self.rotation_epoch,
            }
        } else {
            AgyPickDecision::AllPoolsBelowReserve {
                best_pool,
                effective_bps: best_eff,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rotates_from_five_hour_exhausted_claude_pool_to_healthy_gemini_pool() {
        let mut r = AgyQuotaPoolRotator::new(1_000);
        // Claude has 60% weekly left, but only 4% 5-hour left -> bottleneck 400 bps < 1000 floor!
        r.update_pool(AgyModelPool::Claude, 6_000, 400);
        r.update_pool(AgyModelPool::Gpt, 5_000, 500);
        r.update_pool(AgyModelPool::Gemini, 8_500, 7_200);

        assert_eq!(
            r.pick(AgyModelPool::Claude),
            AgyPickDecision::Selected {
                pool: AgyModelPool::Gemini,
                rotated: true,
                effective_bps: 7_200,
                rotation_epoch: 1,
            }
        );
    }
}
