//! AGY multi-pool quota tracker & deterministic low-pool failover (`aterm harness agy`,
//! `aterm harness agy pick`).

#[cfg(clean_islands)]
#[path = "agy_pool_failover_island.rs"]
mod agy_pool_failover_island;
#[cfg(clean_islands)]
pub use agy_pool_failover_island::{agy_failover_bps_clamp, agy_failover_effective_min};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn agy_failover_bps_clamp(bps: u64) -> u64 {
    if bps < 10_000 {
        bps
    } else {
        10_000
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn agy_failover_effective_min(weekly_bps: u64, five_hour_bps: u64) -> u64 {
    if weekly_bps < five_hour_bps {
        weekly_bps
    } else {
        five_hour_bps
    }
}

contract_fn! {
    #[must_use]
    pub const fn agy_failover_healthy(effective_bps: u64, reserve_floor_bps: u64) -> bool
    clauses [ensures result == (reserve_floor_bps <= effective_bps)]
    {
        reserve_floor_bps <= effective_bps
    }
}

pub const FULL_QUOTA_BPS: u64 = 10_000;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AgyPool {
    Gemini,
    ClaudeAndGpt,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AgyPoolQuota {
    pub weekly_remaining_bps: u64,
    pub five_hour_remaining_bps: u64,
}

impl AgyPoolQuota {
    #[must_use]
    pub const fn new(weekly_remaining_bps: u64, five_hour_remaining_bps: u64) -> Self {
        Self {
            weekly_remaining_bps: agy_failover_bps_clamp(weekly_remaining_bps),
            five_hour_remaining_bps: agy_failover_bps_clamp(five_hour_remaining_bps),
        }
    }

    #[must_use]
    pub const fn effective_bps(self) -> u64 {
        agy_failover_effective_min(self.weekly_remaining_bps, self.five_hour_remaining_bps)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AgyPickDecision {
    KeepRequested {
        pool: AgyPool,
        effective_bps: u64,
    },
    RotatedToHealthy {
        chosen: AgyPool,
        effective_bps: u64,
    },
    AllPoolsDepleted {
        best_pool: AgyPool,
        effective_bps: u64,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AgyPoolFailover {
    gemini: AgyPoolQuota,
    claude_gpt: AgyPoolQuota,
    reserve_floor_bps: u64,
}

impl AgyPoolFailover {
    #[must_use]
    pub const fn new(
        gemini: AgyPoolQuota,
        claude_gpt: AgyPoolQuota,
        reserve_floor_bps: u64,
    ) -> Self {
        Self {
            gemini,
            claude_gpt,
            reserve_floor_bps: agy_failover_bps_clamp(reserve_floor_bps),
        }
    }

    #[must_use]
    pub const fn gemini(&self) -> AgyPoolQuota {
        self.gemini
    }

    #[must_use]
    pub const fn claude_gpt(&self) -> AgyPoolQuota {
        self.claude_gpt
    }

    #[must_use]
    pub const fn reserve_floor_bps(&self) -> u64 {
        self.reserve_floor_bps
    }

    #[must_use]
    pub const fn pick(&self, requested: AgyPool) -> AgyPickDecision {
        let (req_eff, alt_pool, alt_eff) = match requested {
            AgyPool::Gemini => (
                self.gemini.effective_bps(),
                AgyPool::ClaudeAndGpt,
                self.claude_gpt.effective_bps(),
            ),
            AgyPool::ClaudeAndGpt => (
                self.claude_gpt.effective_bps(),
                AgyPool::Gemini,
                self.gemini.effective_bps(),
            ),
        };
        if agy_failover_healthy(req_eff, self.reserve_floor_bps) {
            AgyPickDecision::KeepRequested {
                pool: requested,
                effective_bps: req_eff,
            }
        } else if agy_failover_healthy(alt_eff, self.reserve_floor_bps) {
            AgyPickDecision::RotatedToHealthy {
                chosen: alt_pool,
                effective_bps: alt_eff,
            }
        } else if req_eff < alt_eff {
            AgyPickDecision::AllPoolsDepleted {
                best_pool: alt_pool,
                effective_bps: alt_eff,
            }
        } else {
            AgyPickDecision::AllPoolsDepleted {
                best_pool: requested,
                effective_bps: req_eff,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rotates_away_from_spent_5h_window_to_healthy_peer_pool() {
        let rot = AgyPoolFailover::new(
            AgyPoolQuota::new(8000, 400),
            AgyPoolQuota::new(6500, 5000),
            1000,
        );
        assert_eq!(rot.reserve_floor_bps(), 1000);
        assert_eq!(rot.gemini().effective_bps(), 400);
        assert_eq!(rot.claude_gpt().effective_bps(), 5000);
        assert_eq!(
            rot.pick(AgyPool::Gemini),
            AgyPickDecision::RotatedToHealthy {
                chosen: AgyPool::ClaudeAndGpt,
                effective_bps: 5000,
            }
        );
        assert_eq!(
            rot.pick(AgyPool::ClaudeAndGpt),
            AgyPickDecision::KeepRequested {
                pool: AgyPool::ClaudeAndGpt,
                effective_bps: 5000,
            }
        );
    }

    #[test]
    fn twin_grid_matches_clean_definitions() {
        let mut got_min = String::new();
        for a in [0u64, 1, 2] {
            for b in [0u64, 1, 2] {
                got_min.push_str(&agy_failover_effective_min(a, b).to_string());
            }
        }
        assert_eq!(got_min, "000011012");
        assert_eq!(agy_failover_bps_clamp(99_999), 10_000);
    }
}
