// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm harness agy` Model-Pool Quota Tracker & Low/Spent Pool Rotator.
//!
//! Under `agy`, `aterm harness agy` tracks each model pool's independent weekly and 5-hour
//! rolling quota remaining (Gemini apart from Claude and GPT), and `aterm harness agy pick`
//! rotates a requested model when its pool is spent or below the safety reserve floor so
//! fan-out workers do not stall mid-job on an exhausted 5-hour or weekly quota.
//!
//! Backed by Clean TLA+ Island `Astream.Agent.TlaAgyQuotaRotator`
//! (`agy_pool_rotator_island.rs`), proving `effectiveBps <= maxBps` and
//! `selectedIdx <= maxPoolIdx`.

#[cfg(clean_islands)]
#[path = "agy_pool_rotator_island.rs"]
mod island;
#[cfg(clean_islands)]
pub use island::{agy_pool_idx_clamp, agy_quota_min};

#[cfg(not(clean_islands))]
#[inline]
pub const fn agy_quota_min(weekly_bps: u64, five_hour_bps: u64) -> u64 {
    if weekly_bps < five_hour_bps {
        weekly_bps
    } else {
        five_hour_bps
    }
}

#[cfg(not(clean_islands))]
#[inline]
pub const fn agy_pool_idx_clamp(cand_idx: u64, max_idx: u64) -> u64 {
    if cand_idx < max_idx {
        cand_idx
    } else {
        max_idx
    }
}

contract_fn! {
    /// Kernel-certified check whether a model pool's effective quota (`min(weekly, 5h)` in
    /// basis points) meets or exceeds `reserve_floor_bps`.
    #[must_use]
    #[inline]
    pub const fn agy_pool_has_headroom(effective_bps: u64, reserve_floor_bps: u64) -> bool
    clauses [ensures result == (reserve_floor_bps <= effective_bps)]
    {
        reserve_floor_bps <= effective_bps
    }
}

/// 100.00% quota expressed in basis points (`10_000 bps`).
pub const MAX_QUOTA_BPS: u64 = 10_000;

/// Default low-pool rotation threshold: `5.00%` (`500 bps`).
pub const DEFAULT_RESERVE_FLOOR_BPS: u64 = 500;

/// Independent `agy` model quota pools (`Gemini` apart from `Claude` and `Gpt`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum AgyModelPool {
    Gemini = 0,
    Claude = 1,
    Gpt = 2,
}

pub const POOL_COUNT: usize = 3;
const MAX_POOL_IDX: u64 = (POOL_COUNT - 1) as u64;

impl AgyModelPool {
    #[inline]
    pub const fn from_index(idx: u64) -> Self {
        match idx {
            0 => Self::Gemini,
            1 => Self::Claude,
            _ => Self::Gpt,
        }
    }

    #[inline]
    pub const fn index(self) -> usize {
        match self {
            Self::Gemini => 0,
            Self::Claude => 1,
            Self::Gpt => 2,
        }
    }
}

/// Per-pool weekly and 5-hour quota snapshot in basis points (`0..=10_000`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PoolQuotaSnapshot {
    pub weekly_left_bps: u64,
    pub five_hour_left_bps: u64,
}

impl PoolQuotaSnapshot {
    pub const FULL: Self = Self {
        weekly_left_bps: MAX_QUOTA_BPS,
        five_hour_left_bps: MAX_QUOTA_BPS,
    };

    /// Certified effective quota (`min(weekly_left_bps, five_hour_left_bps) <= MAX_QUOTA_BPS`).
    #[inline]
    pub const fn effective_bps(self) -> u64 {
        let raw = agy_quota_min(self.weekly_left_bps, self.five_hour_left_bps);
        agy_quota_min(raw, MAX_QUOTA_BPS)
    }
}

/// Result of `AgyQuotaRotator::pick`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AgyPickResult {
    pub requested: AgyModelPool,
    pub selected: AgyModelPool,
    pub effective_bps: u64,
    pub rotated: bool,
    pub all_pools_low: bool,
}

/// Deterministic `aterm harness agy pick` pool selector certified by `TlaAgyPoolPickRotator`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AgyQuotaRotator {
    gemini: PoolQuotaSnapshot,
    claude: PoolQuotaSnapshot,
    gpt: PoolQuotaSnapshot,
    reserve_floor_bps: u64,
}

impl Default for AgyQuotaRotator {
    fn default() -> Self {
        Self::new(DEFAULT_RESERVE_FLOOR_BPS)
    }
}

impl AgyQuotaRotator {
    #[inline]
    pub const fn new(reserve_floor_bps: u64) -> Self {
        Self {
            gemini: PoolQuotaSnapshot::FULL,
            claude: PoolQuotaSnapshot::FULL,
            gpt: PoolQuotaSnapshot::FULL,
            reserve_floor_bps: agy_quota_min(reserve_floor_bps, MAX_QUOTA_BPS),
        }
    }

    #[must_use]
    #[inline]
    pub const fn reserve_floor_bps(&self) -> u64 {
        self.reserve_floor_bps
    }

    /// Updates `(weekly_left_bps, five_hour_left_bps)` for `pool`.
    #[inline]
    pub fn update_pool(
        &mut self,
        pool: AgyModelPool,
        weekly_left_bps: u64,
        five_hour_left_bps: u64,
    ) {
        let snap = PoolQuotaSnapshot {
            weekly_left_bps: agy_quota_min(weekly_left_bps, MAX_QUOTA_BPS),
            five_hour_left_bps: agy_quota_min(five_hour_left_bps, MAX_QUOTA_BPS),
        };
        match pool {
            AgyModelPool::Gemini => self.gemini = snap,
            AgyModelPool::Claude => self.claude = snap,
            AgyModelPool::Gpt => self.gpt = snap,
        }
    }

    #[inline]
    pub const fn snapshot(&self, pool: AgyModelPool) -> PoolQuotaSnapshot {
        match pool {
            AgyModelPool::Gemini => self.gemini,
            AgyModelPool::Claude => self.claude,
            AgyModelPool::Gpt => self.gpt,
        }
    }

    /// Evaluates `PickPool` (`Astream.Agent.TlaAgyPoolPickRotator`):
    /// - Keeps `preferred` if its `min(weekly, 5h)` quota meets `reserve_floor_bps`.
    /// - Otherwise rotates to the pool with the strictly highest effective headroom.
    pub fn pick(&self, preferred: AgyModelPool) -> AgyPickResult {
        let pref_idx = agy_pool_idx_clamp(preferred.index() as u64, MAX_POOL_IDX);
        let pref_snap = match pref_idx {
            0 => self.gemini,
            1 => self.claude,
            _ => self.gpt,
        };
        let pref_eff = pref_snap.effective_bps();

        if agy_pool_has_headroom(pref_eff, self.reserve_floor_bps) {
            return AgyPickResult {
                requested: preferred,
                selected: AgyModelPool::from_index(pref_idx),
                effective_bps: pref_eff,
                rotated: false,
                all_pools_low: false,
            };
        }

        // Preferred pool is low or spent -> pick pool with highest effective_bps!
        let mut best_idx = pref_idx;
        let mut best_eff = pref_eff;
        let candidates = [
            (0u64, self.gemini.effective_bps()),
            (1u64, self.claude.effective_bps()),
            (2u64, self.gpt.effective_bps()),
        ];
        let mut rest: &[(u64, u64)] = &candidates;
        while let &[(idx, eff), ref tail @ ..] = rest {
            if eff > best_eff {
                best_eff = eff;
                best_idx = agy_pool_idx_clamp(idx, MAX_POOL_IDX);
            }
            rest = tail;
        }

        let selected = AgyModelPool::from_index(best_idx);
        let all_pools_low = !agy_pool_has_headroom(best_eff, self.reserve_floor_bps);
        AgyPickResult {
            requested: preferred,
            selected,
            effective_bps: best_eff,
            rotated: selected != preferred,
            all_pools_low,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keeps_preferred_pool_when_both_weekly_and_five_hour_have_headroom() {
        let mut rot = AgyQuotaRotator::new(500); // 5% floor
        rot.update_pool(AgyModelPool::Claude, 4_000, 1_200);
        let pick = rot.pick(AgyModelPool::Claude);
        assert_eq!(pick.selected, AgyModelPool::Claude);
        assert_eq!(pick.effective_bps, 1_200);
        assert!(!pick.rotated);
        assert!(!pick.all_pools_low);
    }

    #[test]
    fn rotates_spent_five_hour_pool_to_healthiest_peer_pool() {
        let mut rot = AgyQuotaRotator::new(500); // 5% floor
                                                 // Claude has 60% weekly left, but 5-hour pool is down to 2% (200 bps < 500)!
        rot.update_pool(AgyModelPool::Claude, 6_000, 200);
        rot.update_pool(AgyModelPool::Gemini, 8_500, 7_200);
        rot.update_pool(AgyModelPool::Gpt, 5_000, 3_000);

        let pick = rot.pick(AgyModelPool::Claude);
        assert_eq!(pick.requested, AgyModelPool::Claude);
        assert_eq!(pick.selected, AgyModelPool::Gemini);
        assert_eq!(pick.effective_bps, 7_200);
        assert!(pick.rotated);
        assert!(!pick.all_pools_low);
    }
}
