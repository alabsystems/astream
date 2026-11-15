// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Multi-provider model-pool quota tracker & deterministic rotation selector
//! (`aterm harness agy` & `aterm harness agy pick [<model>]`, `Astream.Agent.TlaQuotaPoolRouter`).
//!
//! Models separate weekly and 5-hour quota windows (`0..=10_000` basis points remaining)
//! per model pool (`Gemini` apart from `Claude` and `Gpt`), verifying health against a
//! configurable low-watermark floor (`quota_pool_healthy`) and deterministically rotating
//! launches from a low/spent pool onto the healthiest available fallback pool while
//! monotonically counting rotations via Clean-origin [`quota_rotation_advance`].

#[cfg(clean_islands)]
#[path = "quota_pool_island.rs"]
mod quota_pool_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn quota_bps_clamp(bps: u64, max_bps: u64) -> u64 {
    if bps < max_bps {
        bps
    } else {
        max_bps
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn quota_rotation_advance(prev_rot: u64, cand_rot: u64) -> u64 {
    if prev_rot < cand_rot {
        cand_rot
    } else {
        prev_rot
    }
}
#[cfg(clean_islands)]
pub use quota_pool_island::{quota_bps_clamp, quota_rotation_advance};

/// Full quota scale in basis points (`100.00% = 10_000 bps`).
pub const MAX_QUOTA_BPS: u64 = 10_000;

/// Default low-quota rotation threshold (`5.00% = 500 bps`).
pub const DEFAULT_LOW_WATERMARK_BPS: u64 = 500;

contract_fn! {
    /// Verified check that a model pool has at least `floor_bps` remaining in BOTH its
    /// weekly window and its 5-hour window, linked via `clean-kernel-defeq` to
    /// `quota_pool_healthy_isl`.
    #[must_use]
    pub const fn quota_pool_healthy(weekly_bps: u64, five_hour_bps: u64, floor_bps: u64) -> bool
    clauses [ensures result == (floor_bps <= weekly_bps && floor_bps <= five_hour_bps)]
    {
        floor_bps <= weekly_bps && floor_bps <= five_hour_bps
    }
}

/// Separate quota pools tracked by `aterm harness agy` (Gemini apart from Claude & GPT).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ModelPoolKind {
    /// Gemini quota pool (separate weekly & 5-hour window).
    Gemini,
    /// Claude quota pool.
    Claude,
    /// GPT quota pool.
    Gpt,
}

impl ModelPoolKind {
    /// Canonical default model identifier for each pool.
    #[must_use]
    pub const fn default_model(self) -> &'static str {
        match self {
            Self::Gemini => "gemini-pro",
            Self::Claude => "claude-opus",
            Self::Gpt => "gpt-codex",
        }
    }

    /// Classify a model name into its quota pool.
    #[must_use]
    pub fn from_model_name(model: &str) -> Self {
        if model.starts_with("gemini") || model.starts_with("flash") {
            Self::Gemini
        } else if model.starts_with("gpt")
            || model.starts_with("o3")
            || model.starts_with("o4")
            || model.starts_with("codex")
        {
            Self::Gpt
        } else {
            Self::Claude
        }
    }
}

/// Remaining quota snapshot for one [`ModelPoolKind`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PoolQuota {
    /// Pool identifier.
    pub pool: ModelPoolKind,
    /// Weekly quota left in basis points (`0..=MAX_QUOTA_BPS`).
    pub weekly_bps: u64,
    /// 5-hour rolling quota left in basis points (`0..=MAX_QUOTA_BPS`).
    pub five_hour_bps: u64,
}

impl PoolQuota {
    /// Construct a clamped quota snapshot.
    #[must_use]
    pub fn new(pool: ModelPoolKind, weekly_bps: u64, five_hour_bps: u64) -> Self {
        Self {
            pool,
            weekly_bps: quota_bps_clamp(weekly_bps, MAX_QUOTA_BPS),
            five_hour_bps: quota_bps_clamp(five_hour_bps, MAX_QUOTA_BPS),
        }
    }

    /// Bottleneck remaining quota (`min(weekly_bps, five_hour_bps)`).
    #[must_use]
    pub const fn effective_bps(self) -> u64 {
        if self.weekly_bps < self.five_hour_bps {
            self.weekly_bps
        } else {
            self.five_hour_bps
        }
    }

    /// Check whether both windows meet `floor_bps`.
    #[must_use]
    pub fn is_healthy(self, floor_bps: u64) -> bool {
        quota_pool_healthy(self.weekly_bps, self.five_hour_bps, floor_bps)
    }
}

/// Selection result from [`QuotaPoolRouter::pick`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PickedModel {
    /// Selected model name to launch.
    pub model: String,
    /// Pool backing `model`.
    pub pool: ModelPoolKind,
    /// `true` when the requested model's pool was below `low_watermark_bps` and rotated!
    pub rotated: bool,
    /// Effective bottleneck basis points remaining in the chosen pool.
    pub effective_bps: u64,
}

/// Deterministic `aterm harness agy pick` model-pool router.
#[derive(Debug, Clone)]
pub struct QuotaPoolRouter {
    low_watermark_bps: u64,
    rotations: u64,
    gemini: PoolQuota,
    claude: PoolQuota,
    gpt: PoolQuota,
}

impl QuotaPoolRouter {
    /// Create a router initialized at 100% (`10_000 bps`) across Gemini, Claude, and GPT.
    #[must_use]
    pub fn new(low_watermark_bps: u64) -> Self {
        let floor = quota_bps_clamp(low_watermark_bps, MAX_QUOTA_BPS);
        Self {
            low_watermark_bps: floor,
            rotations: 0,
            gemini: PoolQuota::new(ModelPoolKind::Gemini, MAX_QUOTA_BPS, MAX_QUOTA_BPS),
            claude: PoolQuota::new(ModelPoolKind::Claude, MAX_QUOTA_BPS, MAX_QUOTA_BPS),
            gpt: PoolQuota::new(ModelPoolKind::Gpt, MAX_QUOTA_BPS, MAX_QUOTA_BPS),
        }
    }

    /// Total pool rotations performed since router creation.
    #[must_use]
    pub const fn rotations(&self) -> u64 {
        self.rotations
    }

    /// Update the measured `(weekly_bps, five_hour_bps)` quota for `pool`.
    pub fn update_pool(&mut self, pool: ModelPoolKind, weekly_bps: u64, five_hour_bps: u64) {
        let snap = PoolQuota::new(pool, weekly_bps, five_hour_bps);
        match pool {
            ModelPoolKind::Gemini => self.gemini = snap,
            ModelPoolKind::Claude => self.claude = snap,
            ModelPoolKind::Gpt => self.gpt = snap,
        }
    }

    /// Inspect a pool's current quota snapshot.
    #[must_use]
    pub const fn quota(&self, pool: ModelPoolKind) -> PoolQuota {
        match pool {
            ModelPoolKind::Gemini => self.gemini,
            ModelPoolKind::Claude => self.claude,
            ModelPoolKind::Gpt => self.gpt,
        }
    }

    /// Pick the model a worker launch should run (`aterm harness agy pick [<model>]`):
    /// - If `requested_model`'s pool is healthy (`>= low_watermark_bps`), keeps `requested_model`.
    /// - Otherwise rotates to the pool with the highest `effective_bps` (preferring healthy
    ///   pools) and increments `rotations` monotonically!
    pub fn pick(&mut self, requested_model: Option<&str>) -> PickedModel {
        if let Some(req) = requested_model {
            let req_pool = ModelPoolKind::from_model_name(req);
            let q = self.quota(req_pool);
            if q.is_healthy(self.low_watermark_bps) {
                return PickedModel {
                    model: req.to_string(),
                    pool: req_pool,
                    rotated: false,
                    effective_bps: q.effective_bps(),
                };
            }
            let best = self.best_pool();
            if best.pool != req_pool {
                let cand = self.rotations.saturating_add(1);
                self.rotations = quota_rotation_advance(self.rotations, cand);
                return PickedModel {
                    model: best.pool.default_model().to_string(),
                    pool: best.pool,
                    rotated: true,
                    effective_bps: best.effective_bps(),
                };
            }
            return PickedModel {
                model: req.to_string(),
                pool: req_pool,
                rotated: false,
                effective_bps: q.effective_bps(),
            };
        }

        let best = self.best_pool();
        PickedModel {
            model: best.pool.default_model().to_string(),
            pool: best.pool,
            rotated: false,
            effective_bps: best.effective_bps(),
        }
    }

    fn pick_better(&self, best: PoolQuota, cand: PoolQuota) -> PoolQuota {
        let cand_ok = cand.is_healthy(self.low_watermark_bps);
        let best_ok = best.is_healthy(self.low_watermark_bps);
        let better = if cand_ok != best_ok {
            cand_ok
        } else {
            cand.effective_bps() > best.effective_bps()
        };
        if better {
            cand
        } else {
            best
        }
    }

    fn best_pool(&self) -> PoolQuota {
        let b1 = self.pick_better(self.gemini, self.claude);
        self.pick_better(b1, self.gpt)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keeps_healthy_requested_model_and_rotates_spent_five_hour_pool_onto_gemini() {
        let mut router = QuotaPoolRouter::new(DEFAULT_LOW_WATERMARK_BPS);
        router.update_pool(ModelPoolKind::Claude, 8_000, 200); // 5h window low (2% < 5%)!
        router.update_pool(ModelPoolKind::Gpt, 4_000, 3_500);
        router.update_pool(ModelPoolKind::Gemini, 9_500, 9_000);

        // Healthy GPT request stays on GPT.
        let p1 = router.pick(Some("gpt-codex"));
        assert!(!p1.rotated);
        assert_eq!(p1.model, "gpt-codex");
        assert_eq!(p1.pool, ModelPoolKind::Gpt);
        assert_eq!(router.rotations(), 0);

        // Low 5h Claude request rotates onto healthiest pool (Gemini, 9000 bps)!
        let p2 = router.pick(Some("claude-sonnet"));
        assert!(p2.rotated);
        assert_eq!(p2.pool, ModelPoolKind::Gemini);
        assert_eq!(p2.model, "gemini-pro");
        assert_eq!(p2.effective_bps, 9_000);
        assert_eq!(router.rotations(), 1);
    }
}
