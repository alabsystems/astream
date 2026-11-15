// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Multi-pool 5-hour & weekly quota rotator (`aterm harness agy pick` model selector).
//!
//! Under `aterm`, Gemini and Claude/GPT draw from independent 5-hour and weekly quota
//! pools (`aterm harness agy`). Before fanning out subagents or worker tabs, `QuotaPoolRotator`
//! computes each pool's bottleneck remaining headroom (`min(five_hour_bps, weekly_bps)` in
//! `0..=10_000` basis points), honors the requested pool when above `low_water_bps`, and
//! deterministically rotates onto the healthiest alternate pool when low or spent.
//!
//! Clean specification: `agy_quota_rotator_island.rs` (`Astream.Agent.TlaQuotaPoolRotator`).

#[cfg(clean_islands)]
#[path = "agy_quota_rotator_island.rs"]
mod agy_quota_rotator_island;

#[cfg(clean_islands)]
pub use agy_quota_rotator_island::{agy_rotator_bps_clamp, rotation_epoch_advance};

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn agy_rotator_bps_clamp(cand_bps: u64, max_bps: u64) -> u64 {
    if cand_bps < max_bps {
        cand_bps
    } else {
        max_bps
    }
}

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn rotation_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

/// Full quota pool capacity in basis points (`10_000` = `100.00%`).
pub const MAX_QUOTA_BPS: u64 = 10_000;
/// Default low-water rotation threshold (`1_000` bps = `10.00%` remaining).
pub const DEFAULT_LOW_WATER_BPS: u64 = 1_000;

contract_fn! {
    /// Kernel-certified check that `bps <= max_bps`, linked via
    /// `clean-kernel-defeq` to `quota_bps_within_max_isl`.
    #[must_use]
    pub const fn quota_bps_within_max(bps: u64, max_bps: u64) -> bool
    clauses [ensures result == (bps <= max_bps)]
    {
        bps <= max_bps
    }
}

fn clamp_bps(raw_bps: u64) -> u64 {
    let clamped = agy_rotator_bps_clamp(raw_bps, MAX_QUOTA_BPS);
    let _ = quota_bps_within_max(clamped, MAX_QUOTA_BPS);
    clamped
}

/// Independent quota pool families tracked by `aterm harness agy`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModelQuotaPool {
    Gemini,
    Claude,
    Gpt,
}

impl ModelQuotaPool {
    pub const ALL: [Self; 3] = [Self::Gemini, Self::Claude, Self::Gpt];
}

/// Snapshot of one model pool's 5-hour and weekly quota headroom in basis points.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PoolQuotaReading {
    pub five_hour_bps: u64,
    pub weekly_bps: u64,
}

impl PoolQuotaReading {
    /// Bottleneck remaining quota (`min(five_hour_bps, weekly_bps)`), clamped to `10_000`.
    #[must_use]
    pub fn effective_bps(self) -> u64 {
        let fh = clamp_bps(self.five_hour_bps);
        let wk = clamp_bps(self.weekly_bps);
        if fh < wk {
            fh
        } else {
            wk
        }
    }
}

/// Selection outcome returned by `QuotaPoolRotator::pick`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuotaPickDecision {
    /// Preferred pool had healthy headroom (`>= low_water_bps`).
    KeptPreferred {
        pool: ModelQuotaPool,
        effective_bps: u64,
    },
    /// Preferred pool was below `low_water_bps` and rotated to a healthier pool.
    Rotated {
        requested: ModelQuotaPool,
        chosen: ModelQuotaPool,
        chosen_bps: u64,
        rotation_epoch: u64,
    },
    /// Every pool is completely spent (`0` bps remaining across all pools).
    AllPoolsExhausted,
}

/// Deterministic multi-pool model quota tracker and rotator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuotaPoolRotator {
    gemini: PoolQuotaReading,
    claude: PoolQuotaReading,
    gpt: PoolQuotaReading,
    low_water_bps: u64,
    rotation_epoch: u64,
}

impl QuotaPoolRotator {
    /// Construct a rotator with all pools initially at 100% (`10_000` bps) and `low_water_bps`.
    #[must_use]
    pub fn new(low_water_bps: u64) -> Self {
        let full = PoolQuotaReading {
            five_hour_bps: MAX_QUOTA_BPS,
            weekly_bps: MAX_QUOTA_BPS,
        };
        Self {
            gemini: full,
            claude: full,
            gpt: full,
            low_water_bps: clamp_bps(low_water_bps),
            rotation_epoch: 0,
        }
    }

    /// Update the 5-hour and weekly remaining basis points for `pool`.
    pub fn update_pool(&mut self, pool: ModelQuotaPool, five_hour_bps: u64, weekly_bps: u64) {
        let reading = PoolQuotaReading {
            five_hour_bps: clamp_bps(five_hour_bps),
            weekly_bps: clamp_bps(weekly_bps),
        };
        match pool {
            ModelQuotaPool::Gemini => self.gemini = reading,
            ModelQuotaPool::Claude => self.claude = reading,
            ModelQuotaPool::Gpt => self.gpt = reading,
        }
    }

    #[must_use]
    pub const fn rotation_epoch(&self) -> u64 {
        self.rotation_epoch
    }

    #[must_use]
    pub fn effective_bps(&self, pool: ModelQuotaPool) -> u64 {
        match pool {
            ModelQuotaPool::Gemini => self.gemini.effective_bps(),
            ModelQuotaPool::Claude => self.claude.effective_bps(),
            ModelQuotaPool::Gpt => self.gpt.effective_bps(),
        }
    }

    /// Pick `preferred` if its bottleneck quota is `>= low_water_bps`; otherwise rotate to
    /// the pool with the highest positive remaining quota.
    pub fn pick(&mut self, preferred: ModelQuotaPool) -> QuotaPickDecision {
        let pref_bps = self.effective_bps(preferred);
        if pref_bps >= self.low_water_bps && pref_bps > 0 {
            return QuotaPickDecision::KeptPreferred {
                pool: preferred,
                effective_bps: pref_bps,
            };
        }

        let mut best_pool = preferred;
        let mut best_bps = pref_bps;
        let mut pools: &[ModelQuotaPool] = &ModelQuotaPool::ALL;
        while let &[cand_pool, ref rest @ ..] = pools {
            pools = rest;
            let cand_bps = self.effective_bps(cand_pool);
            if cand_bps > best_bps {
                best_bps = cand_bps;
                best_pool = cand_pool;
            }
        }

        if best_bps == 0 {
            return QuotaPickDecision::AllPoolsExhausted;
        }
        if best_pool == preferred {
            return QuotaPickDecision::KeptPreferred {
                pool: preferred,
                effective_bps: pref_bps,
            };
        }

        let next_epoch =
            rotation_epoch_advance(self.rotation_epoch, self.rotation_epoch.saturating_add(1));
        self.rotation_epoch = next_epoch;
        QuotaPickDecision::Rotated {
            requested: preferred,
            chosen: best_pool,
            chosen_bps: best_bps,
            rotation_epoch: next_epoch,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keeps_preferred_when_healthy_and_rotates_when_low_or_spent() {
        let mut rot = QuotaPoolRotator::new(DEFAULT_LOW_WATER_BPS);
        rot.update_pool(ModelQuotaPool::Claude, 4_500, 3_200);
        rot.update_pool(ModelQuotaPool::Gemini, 8_500, 9_000);
        rot.update_pool(ModelQuotaPool::Gpt, 2_000, 6_000);

        assert_eq!(
            rot.pick(ModelQuotaPool::Claude),
            QuotaPickDecision::KeptPreferred {
                pool: ModelQuotaPool::Claude,
                effective_bps: 3_200,
            }
        );

        // Claude 5-hour pool drops to 4% (400 bps < 1000 bps low-water) -> rotates to Gemini (8500 bps).
        rot.update_pool(ModelQuotaPool::Claude, 400, 3_200);
        assert_eq!(
            rot.pick(ModelQuotaPool::Claude),
            QuotaPickDecision::Rotated {
                requested: ModelQuotaPool::Claude,
                chosen: ModelQuotaPool::Gemini,
                chosen_bps: 8_500,
                rotation_epoch: 1,
            }
        );

        // Exhaust all pools -> AllPoolsExhausted.
        rot.update_pool(ModelQuotaPool::Claude, 0, 3_200);
        rot.update_pool(ModelQuotaPool::Gemini, 8_500, 0);
        rot.update_pool(ModelQuotaPool::Gpt, 0, 0);
        assert_eq!(
            rot.pick(ModelQuotaPool::Gemini),
            QuotaPickDecision::AllPoolsExhausted
        );
    }
}
