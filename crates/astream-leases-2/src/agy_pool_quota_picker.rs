// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Multi-pool `aterm harness agy` / `aterm harness agy pick` quota headroom & fallback selector
//! (`Astream.Agent.TlaAgyPoolQuotaPicker`, Island #289).

#[cfg(clean_islands)]
#[path = "agy_pool_quota_picker_island.rs"]
mod agy_pool_quota_picker_island;
#[cfg(clean_islands)]
pub use agy_pool_quota_picker_island::{agy_picker_bp_clamp, agy_picker_headroom_bp};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn agy_picker_bp_clamp(quota_bp: u64, max_bp: u64) -> u64 {
    if quota_bp < max_bp {
        quota_bp
    } else {
        max_bp
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn agy_picker_headroom_bp(five_hour_bp: u64, weekly_bp: u64) -> u64 {
    if five_hour_bp < weekly_bp {
        five_hour_bp
    } else {
        weekly_bp
    }
}

/// Basis points representing 100.00% quota remaining (`10_000`).
pub const MAX_QUOTA_BP: u64 = 10_000;

/// Default low-pool rotation threshold in basis points (`500` = 5.00% remaining).
pub const DEFAULT_LOW_POOL_FLOOR_BP: u64 = 500;

contract_fn! {
    /// Verified check whether a model pool's effective headroom meets `low_floor_bp`
    /// (`low_floor_bp <= headroom_bp`), linked via `clean-kernel-defeq` to
    /// `agy_picker_healthy_isl`.
    #[must_use]
    pub const fn agy_picker_healthy(headroom_bp: u64, low_floor_bp: u64) -> bool
    clauses [ensures result == (low_floor_bp <= headroom_bp)]
    {
        low_floor_bp <= headroom_bp
    }
}

/// Separate quota pools tracked by `aterm harness agy`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AgyQuotaPool {
    /// Gemini model pool (tracked separately from Claude and GPT).
    Gemini,
    /// Shared Claude + GPT model pool.
    ClaudeAndGpt,
}

/// Snapshot of one `agy` pool's 5-hour and weekly remaining quota in basis points (`0..=10_000`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AgyPoolWindow {
    pub five_hour_bp: u64,
    pub weekly_bp: u64,
}

impl AgyPoolWindow {
    /// Clamp both windows into `0..=MAX_QUOTA_BP`.
    #[must_use]
    pub const fn new(five_hour_bp: u64, weekly_bp: u64) -> Self {
        Self {
            five_hour_bp: agy_picker_bp_clamp(five_hour_bp, MAX_QUOTA_BP),
            weekly_bp: agy_picker_bp_clamp(weekly_bp, MAX_QUOTA_BP),
        }
    }

    /// Bottleneck headroom (`min(five_hour_bp, weekly_bp)`), bounded by `MAX_QUOTA_BP`.
    #[must_use]
    pub const fn effective_headroom_bp(&self) -> u64 {
        let raw = agy_picker_headroom_bp(self.five_hour_bp, self.weekly_bp);
        agy_picker_bp_clamp(raw, MAX_QUOTA_BP)
    }
}

/// Outcome of [`AgyPoolQuotaPicker::pick`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AgyPickVerdict {
    /// Requested pool is healthy (`low_floor_bp <= headroom_bp`).
    KeptRequested {
        pool: AgyQuotaPool,
        headroom_bp: u64,
    },
    /// Requested pool was low/spent; rotated to a healthier pool.
    Rotated {
        from: AgyQuotaPool,
        to: AgyQuotaPool,
        headroom_bp: u64,
    },
    /// Requested pool is below `low_floor_bp`, peer is worse or spent, but requested still has
    /// `> 0` basis points left.
    DegradedKeep {
        pool: AgyQuotaPool,
        headroom_bp: u64,
    },
    /// Both pools are completely spent (`0 bp` remaining).
    AllPoolsExhausted,
}

/// Deterministic `aterm harness agy pick` pool selector.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AgyPoolQuotaPicker {
    gemini: AgyPoolWindow,
    claude_gpt: AgyPoolWindow,
    low_floor_bp: u64,
}

impl AgyPoolQuotaPicker {
    /// Construct a picker from live `gemini` and `claude_gpt` pool windows.
    #[must_use]
    pub const fn new(gemini: AgyPoolWindow, claude_gpt: AgyPoolWindow) -> Self {
        Self {
            gemini,
            claude_gpt,
            low_floor_bp: DEFAULT_LOW_POOL_FLOOR_BP,
        }
    }

    /// Set a custom low-pool rotation floor in basis points (`0..=MAX_QUOTA_BP`).
    #[must_use]
    pub const fn with_low_floor_bp(mut self, low_floor_bp: u64) -> Self {
        self.low_floor_bp = agy_picker_bp_clamp(low_floor_bp, MAX_QUOTA_BP);
        self
    }

    #[must_use]
    pub const fn low_floor_bp(&self) -> u64 {
        self.low_floor_bp
    }

    /// Effective headroom of `pool` in basis points.
    #[must_use]
    pub const fn headroom_bp(&self, pool: AgyQuotaPool) -> u64 {
        match pool {
            AgyQuotaPool::Gemini => self.gemini.effective_headroom_bp(),
            AgyQuotaPool::ClaudeAndGpt => self.claude_gpt.effective_headroom_bp(),
        }
    }

    /// Pick the pool that a launch of `requested` will run on.
    #[must_use]
    pub const fn pick(&self, requested: AgyQuotaPool) -> AgyPickVerdict {
        let alternate = match requested {
            AgyQuotaPool::Gemini => AgyQuotaPool::ClaudeAndGpt,
            AgyQuotaPool::ClaudeAndGpt => AgyQuotaPool::Gemini,
        };
        let req_bp = self.headroom_bp(requested);
        let alt_bp = self.headroom_bp(alternate);

        if agy_picker_healthy(req_bp, self.low_floor_bp) && req_bp > 0 {
            return AgyPickVerdict::KeptRequested {
                pool: requested,
                headroom_bp: req_bp,
            };
        }
        if alt_bp > req_bp && alt_bp > 0 {
            return AgyPickVerdict::Rotated {
                from: requested,
                to: alternate,
                headroom_bp: alt_bp,
            };
        }
        if req_bp > 0 {
            return AgyPickVerdict::DegradedKeep {
                pool: requested,
                headroom_bp: req_bp,
            };
        }
        AgyPickVerdict::AllPoolsExhausted
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keeps_healthy_pool_and_rotates_when_five_hour_or_weekly_is_low() {
        let rot = AgyPoolQuotaPicker::new(
            AgyPoolWindow::new(8_200, 7_500),
            AgyPoolWindow::new(200, 9_000),
        );
        assert_eq!(rot.low_floor_bp(), DEFAULT_LOW_POOL_FLOOR_BP);
        assert_eq!(
            rot.pick(AgyQuotaPool::Gemini),
            AgyPickVerdict::KeptRequested {
                pool: AgyQuotaPool::Gemini,
                headroom_bp: 7_500,
            }
        );
        assert_eq!(
            rot.pick(AgyQuotaPool::ClaudeAndGpt),
            AgyPickVerdict::Rotated {
                from: AgyQuotaPool::ClaudeAndGpt,
                to: AgyQuotaPool::Gemini,
                headroom_bp: 7_500,
            }
        );
    }

    #[test]
    fn fails_closed_when_all_pools_spent() {
        let rot =
            AgyPoolQuotaPicker::new(AgyPoolWindow::new(0, 5_000), AgyPoolWindow::new(4_000, 0));
        assert_eq!(
            rot.pick(AgyQuotaPool::Gemini),
            AgyPickVerdict::AllPoolsExhausted
        );
        assert_eq!(
            rot.pick(AgyQuotaPool::ClaudeAndGpt),
            AgyPickVerdict::AllPoolsExhausted
        );
    }
}
