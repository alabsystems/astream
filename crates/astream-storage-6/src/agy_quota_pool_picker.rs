// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm harness agy pick` multi-pool (Gemini vs Claude/GPT, 5h & weekly) quota picker
//! (`Astream.Agent.TlaAgyQuotaPoolPicker`).
//!
//! Models `aterm harness agy` quota rotation before fanning out `agy` subagents/workers:
//! tracks separate 5-hour and weekly remaining basis points (`0..=10_000`) for Gemini vs
//! Claude/GPT pools and deterministically rotates away from a low or spent pool.

#[cfg(clean_islands)]
#[path = "agy_quota_pool_picker_island.rs"]
mod agy_quota_pool_picker_island;
#[cfg(clean_islands)]
pub use agy_quota_pool_picker_island::{agy_pick_epoch_advance, agy_pool_rem_clamp};

#[cfg(not(clean_islands))]
/// Clamp remaining quota basis points to `max_bps` (`10_000`).
#[must_use]
pub const fn agy_pool_rem_clamp(cand_bps: u64, max_bps: u64) -> u64 {
    if cand_bps < max_bps {
        cand_bps
    } else {
        max_bps
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the `agy` pool-pick epoch.
#[must_use]
pub const fn agy_pick_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff both `five_hour_bps` and `weekly_bps` meet or exceed `floor_bps`.
    #[must_use]
    pub const fn agy_pool_above_floor(five_hour_bps: u64, weekly_bps: u64, floor_bps: u64) -> bool
    clauses [ensures result == (five_hour_bps >= floor_bps && weekly_bps >= floor_bps)]
    {
        five_hour_bps >= floor_bps && weekly_bps >= floor_bps
    }
}

/// Maximum basis points (`100.00%`).
pub const MAX_QUOTA_BPS: u64 = 10_000;

/// Disjoint `aterm harness agy` model quota pools.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AgyModelPool {
    Gemini,
    ClaudeAndGpt,
}

/// Outcome of `aterm harness agy pick`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AgyPickOutcome {
    SelectedPreferred { pool: AgyModelPool, pick_epoch: u64 },
    RotatedToHealthy { pool: AgyModelPool, pick_epoch: u64 },
    AllPoolsExhausted { pick_epoch: u64 },
}

/// Dual-pool (`Gemini` vs `ClaudeAndGpt`) 5h + weekly quota tracker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AgyQuotaPoolPicker {
    gemini_5h_bps: u64,
    gemini_weekly_bps: u64,
    claude_gpt_5h_bps: u64,
    claude_gpt_weekly_bps: u64,
    rotation_floor_bps: u64,
    pick_epoch: u64,
}

impl AgyQuotaPoolPicker {
    #[must_use]
    pub const fn new(rotation_floor_bps: u64) -> Self {
        let floor = if rotation_floor_bps == 0 {
            500
        } else if rotation_floor_bps > MAX_QUOTA_BPS {
            MAX_QUOTA_BPS
        } else {
            rotation_floor_bps
        };
        Self {
            gemini_5h_bps: MAX_QUOTA_BPS,
            gemini_weekly_bps: MAX_QUOTA_BPS,
            claude_gpt_5h_bps: MAX_QUOTA_BPS,
            claude_gpt_weekly_bps: MAX_QUOTA_BPS,
            rotation_floor_bps: floor,
            pick_epoch: 0,
        }
    }

    /// Update a pool's 5-hour and weekly remaining quota basis points (`0..=10_000`).
    pub fn update_pool_quota(&mut self, pool: AgyModelPool, five_hour_bps: u64, weekly_bps: u64) {
        let c5 = agy_pool_rem_clamp(five_hour_bps, MAX_QUOTA_BPS);
        let cw = agy_pool_rem_clamp(weekly_bps, MAX_QUOTA_BPS);
        match pool {
            AgyModelPool::Gemini => {
                self.gemini_5h_bps = c5;
                self.gemini_weekly_bps = cw;
            }
            AgyModelPool::ClaudeAndGpt => {
                self.claude_gpt_5h_bps = c5;
                self.claude_gpt_weekly_bps = cw;
            }
        }
    }

    #[must_use]
    fn pool_healthy(&self, pool: AgyModelPool) -> bool {
        match pool {
            AgyModelPool::Gemini => agy_pool_above_floor(
                self.gemini_5h_bps,
                self.gemini_weekly_bps,
                self.rotation_floor_bps,
            ),
            AgyModelPool::ClaudeAndGpt => agy_pool_above_floor(
                self.claude_gpt_5h_bps,
                self.claude_gpt_weekly_bps,
                self.rotation_floor_bps,
            ),
        }
    }

    /// Pick a model pool for a worker launch, rotating if `preferred` is low/spent.
    pub fn pick(&mut self, preferred: AgyModelPool) -> AgyPickOutcome {
        let next_ep = self.pick_epoch.saturating_add(1);
        self.pick_epoch = agy_pick_epoch_advance(self.pick_epoch, next_ep);
        if self.pool_healthy(preferred) {
            return AgyPickOutcome::SelectedPreferred {
                pool: preferred,
                pick_epoch: self.pick_epoch,
            };
        }
        let fallback = match preferred {
            AgyModelPool::Gemini => AgyModelPool::ClaudeAndGpt,
            AgyModelPool::ClaudeAndGpt => AgyModelPool::Gemini,
        };
        if self.pool_healthy(fallback) {
            AgyPickOutcome::RotatedToHealthy {
                pool: fallback,
                pick_epoch: self.pick_epoch,
            }
        } else {
            AgyPickOutcome::AllPoolsExhausted {
                pick_epoch: self.pick_epoch,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rotates_from_low_claude_gpt_pool_to_healthy_gemini_pool() {
        let mut picker = AgyQuotaPoolPicker::new(500);
        picker.update_pool_quota(AgyModelPool::ClaudeAndGpt, 200, 8_000);
        assert_eq!(
            picker.pick(AgyModelPool::ClaudeAndGpt),
            AgyPickOutcome::RotatedToHealthy {
                pool: AgyModelPool::Gemini,
                pick_epoch: 1,
            }
        );
    }
}
