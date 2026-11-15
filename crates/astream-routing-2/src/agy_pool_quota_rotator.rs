// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Model-pool quota tracker & rotation selector (`Astream.Agent.TlaAgyPoolQuotaRotator`).
//!
//! Models `aterm harness agy` and `aterm harness agy pick [<model>]`:
//! tracks independent 5-hour and weekly quota basis points (`0..=10_000`) for
//! the `Gemini`, `Claude`, and `Gpt` model pools, rotating away from a low or
//! spent pool before fanning out worker sessions.

#[cfg(clean_islands)]
#[path = "agy_pool_quota_rotator_island.rs"]
mod agy_pool_quota_rotator_island;
#[cfg(clean_islands)]
pub use agy_pool_quota_rotator_island::{quota_bps_clamp_b87, quota_rot_epoch_advance};

/// Full quota in basis points (`100.00% = 10_000 bps`).
pub const MAX_QUOTA_BPS: u64 = 10_000;

/// Default low-quota rotation floor (`5.00% = 500 bps`).
pub const DEFAULT_LOW_FLOOR_BPS: u64 = 500;

#[cfg(not(clean_islands))]
/// Monotonically advance the pool-rotation epoch.
#[must_use]
pub const fn quota_rot_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

#[cfg(not(clean_islands))]
/// Clamp remaining quota basis points to `max_bps`.
#[must_use]
pub const fn quota_bps_clamp_b87(cand_bps: u64, max_bps: u64) -> u64 {
    if cand_bps < max_bps {
        cand_bps
    } else {
        max_bps
    }
}

contract_fn! {
    /// True iff `effective_bps` is strictly above `low_floor_bps`.
    #[must_use]
    pub const fn quota_pool_healthy_b87(low_floor_bps: u64, effective_bps: u64) -> bool
    clauses [ensures result == (low_floor_bps < effective_bps)]
    {
        low_floor_bps < effective_bps
    }
}

/// Independent quota pools managed by `aterm harness agy`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AgyModelPool {
    Gemini,
    Claude,
    Gpt,
}

/// Snapshot of one model pool's 5-hour and weekly remaining quota in basis points.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PoolQuotaSnapshot {
    pub five_hour_bps: u64,
    pub weekly_bps: u64,
}

impl PoolQuotaSnapshot {
    pub const FULL: Self = Self {
        five_hour_bps: MAX_QUOTA_BPS,
        weekly_bps: MAX_QUOTA_BPS,
    };

    #[must_use]
    pub const fn sanitized(five_hour_bps: u64, weekly_bps: u64) -> Self {
        Self {
            five_hour_bps: quota_bps_clamp_b87(five_hour_bps, MAX_QUOTA_BPS),
            weekly_bps: quota_bps_clamp_b87(weekly_bps, MAX_QUOTA_BPS),
        }
    }

    /// Bottleneck remaining quota (`min(five_hour_bps, weekly_bps)`).
    #[must_use]
    pub const fn effective_bps(self) -> u64 {
        if self.five_hour_bps < self.weekly_bps {
            self.five_hour_bps
        } else {
            self.weekly_bps
        }
    }
}

/// Deterministic `aterm harness agy pick` pool selector.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AgyPoolQuotaRotator {
    gemini: PoolQuotaSnapshot,
    claude: PoolQuotaSnapshot,
    gpt: PoolQuotaSnapshot,
    low_floor_bps: u64,
    rotation_epoch: u64,
}

impl Default for AgyPoolQuotaRotator {
    fn default() -> Self {
        Self::new(DEFAULT_LOW_FLOOR_BPS)
    }
}

impl AgyPoolQuotaRotator {
    #[must_use]
    pub const fn new(low_floor_bps: u64) -> Self {
        Self {
            gemini: PoolQuotaSnapshot::FULL,
            claude: PoolQuotaSnapshot::FULL,
            gpt: PoolQuotaSnapshot::FULL,
            low_floor_bps: quota_bps_clamp_b87(low_floor_bps, MAX_QUOTA_BPS),
            rotation_epoch: 0,
        }
    }

    #[must_use]
    pub const fn rotation_epoch(&self) -> u64 {
        self.rotation_epoch
    }

    #[must_use]
    pub const fn snapshot_for(&self, pool: AgyModelPool) -> PoolQuotaSnapshot {
        match pool {
            AgyModelPool::Gemini => self.gemini,
            AgyModelPool::Claude => self.claude,
            AgyModelPool::Gpt => self.gpt,
        }
    }

    /// Update a pool's 5-hour and weekly quota; advances `rotation_epoch` when it drops to/below floor.
    pub fn update_pool(&mut self, pool: AgyModelPool, five_hour_bps: u64, weekly_bps: u64) {
        let prev_healthy =
            quota_pool_healthy_b87(self.low_floor_bps, self.snapshot_for(pool).effective_bps());
        let snap = PoolQuotaSnapshot::sanitized(five_hour_bps, weekly_bps);
        match pool {
            AgyModelPool::Gemini => self.gemini = snap,
            AgyModelPool::Claude => self.claude = snap,
            AgyModelPool::Gpt => self.gpt = snap,
        }
        let now_healthy = quota_pool_healthy_b87(self.low_floor_bps, snap.effective_bps());
        if prev_healthy && !now_healthy {
            let cand = self.rotation_epoch.saturating_add(1);
            self.rotation_epoch = quota_rot_epoch_advance(self.rotation_epoch, cand);
        }
    }

    /// Pick `preferred` if above `low_floor_bps`; otherwise rotate to the highest-headroom healthy pool.
    #[must_use]
    pub const fn pick(&self, preferred: AgyModelPool) -> Option<AgyModelPool> {
        let pref_eff = self.snapshot_for(preferred).effective_bps();
        if quota_pool_healthy_b87(self.low_floor_bps, pref_eff) {
            return Some(preferred);
        }
        let candidates = [
            (AgyModelPool::Gemini, self.gemini.effective_bps()),
            (AgyModelPool::Claude, self.claude.effective_bps()),
            (AgyModelPool::Gpt, self.gpt.effective_bps()),
        ];
        let mut best: Option<(AgyModelPool, u64)> = None;
        let mut rest = candidates.as_slice();
        while let &[(pool, eff), ref tail @ ..] = rest {
            if quota_pool_healthy_b87(self.low_floor_bps, eff) {
                match best {
                    None => best = Some((pool, eff)),
                    Some((_, best_eff)) => {
                        if best_eff < eff {
                            best = Some((pool, eff));
                        }
                    }
                }
            }
            rest = tail;
        }
        match best {
            Some((pool, _)) => Some(pool),
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rotates_away_from_spent_five_hour_pool_to_highest_headroom() {
        let mut rot = AgyPoolQuotaRotator::new(500);
        assert_eq!(rot.pick(AgyModelPool::Claude), Some(AgyModelPool::Claude));
        assert_eq!(rot.rotation_epoch(), 0);

        // Claude 5-hour pool drops to 3.00% (300 bps <= 500 bps floor) even though weekly is 60%
        rot.update_pool(AgyModelPool::Claude, 300, 6_000);
        assert_eq!(rot.rotation_epoch(), 1);
        rot.update_pool(AgyModelPool::Gemini, 8_500, 9_000);
        rot.update_pool(AgyModelPool::Gpt, 7_000, 7_500);

        // Rotates Claude -> Gemini (8500 bps > 7000 bps)
        assert_eq!(rot.pick(AgyModelPool::Claude), Some(AgyModelPool::Gemini));

        // Exhaust all pools -> returns None instead of launching into a spent pool
        rot.update_pool(AgyModelPool::Gemini, 0, 9_000);
        rot.update_pool(AgyModelPool::Gpt, 500, 500);
        assert_eq!(rot.pick(AgyModelPool::Claude), None);
        assert_eq!(rot.rotation_epoch(), 3);
    }
}
