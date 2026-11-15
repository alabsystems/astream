// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Dual-horizon (5-hour & weekly) model-pool quota router and worker fan-out planner
//! (`Astream.Agent.TlaDualHorizonQuotaRouter`; `aterm harness agy` & `aterm harness agy pick`).
//!
//! Under `agy`, Gemini, Claude, and GPT draw from distinct model pools, each governed by
//! both a 5-hour rolling window and a 7-day weekly window. [`DualHorizonQuotaRouter`] evaluates
//! each pool's effective remaining quota in basis points (`0..=10_000`, i.e. `0.00%..=100.00%`)
//! as `min(five_hour_bps, weekly_bps)` via Clean-origin [`dual_quota_effective_min`] (after
//! clamping raw telemetry via [`dual_quota_bps_clamp`]), rotates low or spent pools to the
//! healthiest fallback pool in deterministic preference order, and sizes worker fan-out
//! budgets before spawning parallel tabs.

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "dual_horizon_quota_router_island.rs"]
mod dual_horizon_quota_router_island;
#[cfg(clean_islands)]
pub use dual_horizon_quota_router_island::{dual_quota_bps_clamp, dual_quota_effective_min};

/// Mirror of Clean's `dual_quota_bps_clamp` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn dual_quota_bps_clamp(raw_bps: u64, max_bps: u64) -> u64 {
    if raw_bps < max_bps {
        raw_bps
    } else {
        max_bps
    }
}

/// Mirror of Clean's `dual_quota_effective_min` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn dual_quota_effective_min(five_hour_bps: u64, weekly_bps: u64) -> u64 {
    if five_hour_bps < weekly_bps {
        five_hour_bps
    } else {
        weekly_bps
    }
}

contract_fn! {
    /// Kernel-certified check that a pool's effective quota meets or exceeds `floor_bps`
    /// (`floor_bps <= effective_bps`), linked via `clean-kernel-defeq` to
    /// `dual_quota_pool_viable_isl`.
    #[must_use]
    pub const fn dual_quota_pool_viable(effective_bps: u64, floor_bps: u64) -> bool
    clauses [ensures result == (floor_bps <= effective_bps)]
    {
        floor_bps <= effective_bps
    }
}

/// Full quota in basis points (`100.00% == 10_000 bps`).
pub const MAX_DUAL_QUOTA_BPS: u64 = 10_000;

/// Default low-quota rotation watermark (`10.00% == 1_000 bps`).
pub const DEFAULT_DUAL_ROTATE_FLOOR_BPS: u64 = 1_000;

/// Maximum parallel worker fan-out recommended from a single `agy` coordinator (`16`).
pub const MAX_DUAL_FANOUT_WORKERS: usize = 16;

/// Independent `agy` model quota pools (`aterm harness agy`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DualModelPool {
    /// Gemini model pool (tracked separately from Claude and GPT).
    Gemini,
    /// Claude model pool.
    Claude,
    /// GPT model pool.
    Gpt,
}

impl DualModelPool {
    /// Canonical pool order.
    pub const ALL: [Self; 3] = [Self::Gemini, Self::Claude, Self::Gpt];

    /// Canonical CLI pool identifier.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Gemini => "gemini",
            Self::Claude => "claude",
            Self::Gpt => "gpt",
        }
    }

    const fn index(self) -> usize {
        match self {
            Self::Gemini => 0,
            Self::Claude => 1,
            Self::Gpt => 2,
        }
    }
}

/// Clamped 5-hour and weekly quota snapshot for one [`DualModelPool`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DualPoolQuotaSnapshot {
    /// Remaining 5-hour rolling quota in basis points (`0..=10_000`).
    pub five_hour_bps: u64,
    /// Remaining weekly quota in basis points (`0..=10_000`).
    pub weekly_bps: u64,
    /// Bottleneck remaining quota `min(five_hour_bps, weekly_bps)` (`0..=10_000`).
    pub effective_bps: u64,
}

impl DualPoolQuotaSnapshot {
    /// Construct a clamped snapshot via Clean-origin [`dual_quota_bps_clamp`] and
    /// [`dual_quota_effective_min`].
    #[must_use]
    pub const fn new(raw_five_hour_bps: u64, raw_weekly_bps: u64) -> Self {
        let f = dual_quota_bps_clamp(raw_five_hour_bps, MAX_DUAL_QUOTA_BPS);
        let w = dual_quota_bps_clamp(raw_weekly_bps, MAX_DUAL_QUOTA_BPS);
        let eff = dual_quota_effective_min(f, w);
        Self {
            five_hour_bps: f,
            weekly_bps: w,
            effective_bps: eff,
        }
    }
}

/// Outcome of `DualHorizonQuotaRouter::pick` (`aterm harness agy pick [<model>]`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DualPoolPickDecision {
    /// Preferred pool is healthy (`effective_bps >= rotate_floor_bps`).
    SelectedPreferred {
        pool: DualModelPool,
        effective_bps: u64,
    },
    /// Preferred pool was low or spent; rotated to the highest-headroom viable pool.
    Rotated {
        requested: DualModelPool,
        chosen: DualModelPool,
        chosen_effective_bps: u64,
    },
    /// Every pool is below `rotate_floor_bps`, but `chosen` still has positive (> 0) quota.
    DegradedBestEffort {
        chosen: DualModelPool,
        chosen_effective_bps: u64,
    },
    /// Every pool has `0` remaining quota on either its 5-hour or weekly window.
    AllPoolsExhausted,
}

/// Deterministic multi-pool quota router and fan-out budget calculator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DualHorizonQuotaRouter {
    pools: [DualPoolQuotaSnapshot; 3],
    rotate_floor_bps: u64,
}

impl DualHorizonQuotaRouter {
    /// Create a router initialized at 100% quota across all 3 pools.
    #[must_use]
    pub const fn new(rotate_floor_bps: u64) -> Self {
        let full = DualPoolQuotaSnapshot::new(MAX_DUAL_QUOTA_BPS, MAX_DUAL_QUOTA_BPS);
        let floor = dual_quota_bps_clamp(rotate_floor_bps, MAX_DUAL_QUOTA_BPS);
        Self {
            pools: [full, full, full],
            rotate_floor_bps: if floor == 0 { 1 } else { floor },
        }
    }

    /// Configured rotation watermark in basis points.
    #[must_use]
    pub const fn rotate_floor_bps(&self) -> u64 {
        self.rotate_floor_bps
    }

    /// Update the 5-hour and weekly basis-point readings for `pool`.
    pub fn update_pool(
        &mut self,
        pool: DualModelPool,
        raw_five_hour_bps: u64,
        raw_weekly_bps: u64,
    ) {
        if let Some(slot) = self.pools.get_mut(pool.index()) {
            *slot = DualPoolQuotaSnapshot::new(raw_five_hour_bps, raw_weekly_bps);
        }
    }

    /// Read the current clamped snapshot for `pool` without slice indexing.
    #[must_use]
    pub const fn snapshot(&self, pool: DualModelPool) -> DualPoolQuotaSnapshot {
        let [gemini, claude, gpt] = self.pools;
        match pool {
            DualModelPool::Gemini => gemini,
            DualModelPool::Claude => claude,
            DualModelPool::Gpt => gpt,
        }
    }

    /// Pick the pool a launch should run when requesting `preferred`.
    #[must_use]
    pub const fn pick(&self, preferred: DualModelPool) -> DualPoolPickDecision {
        let pref_snap = self.snapshot(preferred);
        if dual_quota_pool_viable(pref_snap.effective_bps, self.rotate_floor_bps) {
            return DualPoolPickDecision::SelectedPreferred {
                pool: preferred,
                effective_bps: pref_snap.effective_bps,
            };
        }

        let mut best_viable: Option<(DualModelPool, u64)> = None;
        let mut best_nonzero: Option<(DualModelPool, u64)> = None;
        let mut rest: &[DualModelPool] = &DualModelPool::ALL;
        while let &[cand, ref tail @ ..] = rest {
            let eff = self.snapshot(cand).effective_bps;
            if dual_quota_pool_viable(eff, self.rotate_floor_bps) {
                let replace = match best_viable {
                    None => true,
                    Some((_, cur_eff)) => eff > cur_eff,
                };
                if replace {
                    best_viable = Some((cand, eff));
                }
            }
            if eff > 0 {
                let replace_nz = match best_nonzero {
                    None => true,
                    Some((_, cur_eff)) => eff > cur_eff,
                };
                if replace_nz {
                    best_nonzero = Some((cand, eff));
                }
            }
            rest = tail;
        }

        if let Some((chosen, eff)) = best_viable {
            return DualPoolPickDecision::Rotated {
                requested: preferred,
                chosen,
                chosen_effective_bps: eff,
            };
        }
        if let Some((chosen, eff)) = best_nonzero {
            return DualPoolPickDecision::DegradedBestEffort {
                chosen,
                chosen_effective_bps: eff,
            };
        }
        DualPoolPickDecision::AllPoolsExhausted
    }

    /// Compute the maximum safe worker fan-out count (`0..=MAX_DUAL_FANOUT_WORKERS`) given
    /// `per_worker_cost_bps` expected consumption per worker.
    #[must_use]
    pub const fn recommended_fanout(&self, pool: DualModelPool, per_worker_cost_bps: u64) -> usize {
        let snap = self.snapshot(pool);
        if !dual_quota_pool_viable(snap.effective_bps, self.rotate_floor_bps) {
            return 0;
        }
        let usable = snap.effective_bps.saturating_sub(self.rotate_floor_bps);
        let cost = if per_worker_cost_bps == 0 {
            1
        } else {
            per_worker_cost_bps
        };
        let raw_workers = match usable.checked_div(cost) {
            Some(v) => v as usize,
            None => 0,
        };
        if raw_workers == 0 {
            1
        } else if raw_workers > MAX_DUAL_FANOUT_WORKERS {
            MAX_DUAL_FANOUT_WORKERS
        } else {
            raw_workers
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn quota_router_rotates_spent_five_hour_pool_to_healthy_gemini_pool() {
        let mut router = DualHorizonQuotaRouter::new(DEFAULT_DUAL_ROTATE_FLOOR_BPS);
        assert_eq!(router.rotate_floor_bps(), DEFAULT_DUAL_ROTATE_FLOOR_BPS);
        router.update_pool(DualModelPool::Claude, 400, 8_000);
        router.update_pool(DualModelPool::Gemini, 7_500, 6_000);
        router.update_pool(DualModelPool::Gpt, 5_000, 5_500);

        assert_eq!(router.snapshot(DualModelPool::Claude).effective_bps, 400);
        assert_eq!(
            router.pick(DualModelPool::Claude),
            DualPoolPickDecision::Rotated {
                requested: DualModelPool::Claude,
                chosen: DualModelPool::Gemini,
                chosen_effective_bps: 6_000,
            }
        );
        assert_eq!(router.recommended_fanout(DualModelPool::Claude, 500), 0);
        assert_eq!(router.recommended_fanout(DualModelPool::Gemini, 1_000), 5);
    }

    #[test]
    fn quota_router_distinguishes_degraded_from_exhausted() {
        let mut router = DualHorizonQuotaRouter::new(1_000);
        router.update_pool(DualModelPool::Gemini, 0, 5_000);
        router.update_pool(DualModelPool::Claude, 300, 400);
        router.update_pool(DualModelPool::Gpt, 0, 0);

        assert_eq!(
            router.pick(DualModelPool::Gemini),
            DualPoolPickDecision::DegradedBestEffort {
                chosen: DualModelPool::Claude,
                chosen_effective_bps: 300,
            }
        );

        router.update_pool(DualModelPool::Claude, 300, 0);
        assert_eq!(
            router.pick(DualModelPool::Claude),
            DualPoolPickDecision::AllPoolsExhausted
        );
    }
}
