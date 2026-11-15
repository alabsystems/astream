// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Deterministic low/spent pool rotator (`aterm harness agy pick [<model>]`,
//! `Astream.Quota.TlaModelRotator`).

#[cfg(clean_islands)]
#[path = "model_rotator_island.rs"]
mod model_rotator_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn rot_candidates_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn rot_switch_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use model_rotator_island::{rot_candidates_clamp, rot_switch_advance};

/// Maximum fallback candidates evaluated in one rotation chain.
pub const MAX_ROTATION_CANDIDATES: u64 = 16;

contract_fn! {
    /// Verified pool floor check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `rot_above_floor_isl`.
    #[must_use]
    pub const fn rot_above_floor(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PoolCandidate {
    pub model_id: String,
    pub left_5h_bps: u64,
    pub left_weekly_bps: u64,
}

impl PoolCandidate {
    #[must_use]
    pub const fn bottleneck_bps(&self) -> u64 {
        if self.left_5h_bps < self.left_weekly_bps {
            self.left_5h_bps
        } else {
            self.left_weekly_bps
        }
    }
}

/// Deterministic `agy pick` rotator selecting requested model when above `low_floor_bps`,
/// otherwise rotating to the highest-headroom healthy peer pool.
#[derive(Debug, Clone)]
pub struct ModelPoolRotator {
    low_floor_bps: u64,
    rotations_total: u64,
}

impl ModelPoolRotator {
    #[must_use]
    pub const fn new(low_floor_bps: u64) -> Self {
        Self {
            low_floor_bps,
            rotations_total: 0,
        }
    }

    #[must_use]
    pub const fn rotations_total(&self) -> u64 {
        self.rotations_total
    }

    pub fn pick_model(&mut self, requested: &str, pools: &[PoolCandidate]) -> Option<String> {
        let limit = rot_candidates_clamp(pools.len() as u64, MAX_ROTATION_CANDIDATES) as usize;
        let mut idx = 0usize;
        while idx < limit {
            if let Some(c) = pools.get(idx) {
                if c.model_id == requested
                    && rot_above_floor(c.bottleneck_bps(), self.low_floor_bps)
                {
                    return Some(c.model_id.clone());
                }
            }
            idx = idx.saturating_add(1);
        }
        let mut best: Option<&PoolCandidate> = None;
        let mut j = 0usize;
        while j < limit {
            if let Some(c) = pools.get(j) {
                if c.bottleneck_bps() > 0 {
                    match best {
                        None => best = Some(c),
                        Some(cur) if c.bottleneck_bps() > cur.bottleneck_bps() => best = Some(c),
                        _ => {}
                    }
                }
            }
            j = j.saturating_add(1);
        }
        if let Some(chosen) = best {
            if chosen.model_id != requested {
                self.rotations_total = rot_switch_advance(
                    self.rotations_total,
                    self.rotations_total.saturating_add(1),
                );
            }
            Some(chosen.model_id.clone())
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rotator_keeps_healthy_requested_model_and_rotates_low_pool_to_richest_peer() {
        let mut r = ModelPoolRotator::new(1_000);
        let pools = vec![
            PoolCandidate {
                model_id: "claude-opus".to_owned(),
                left_5h_bps: 400,
                left_weekly_bps: 8_000,
            },
            PoolCandidate {
                model_id: "gemini-pro".to_owned(),
                left_5h_bps: 9_200,
                left_weekly_bps: 9_000,
            },
            PoolCandidate {
                model_id: "gpt-5".to_owned(),
                left_5h_bps: 6_000,
                left_weekly_bps: 7_000,
            },
        ];
        // claude-opus 5h pool is at 4% (< 10% floor) -> rotates to gemini-pro (90%)!
        assert_eq!(
            r.pick_model("claude-opus", &pools).as_deref(),
            Some("gemini-pro")
        );
        assert_eq!(r.rotations_total(), 1);
        assert_eq!(r.pick_model("gpt-5", &pools).as_deref(), Some("gpt-5"));
        assert_eq!(r.rotations_total(), 1);
    }
}
