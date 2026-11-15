// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `/a/bind` & `/a/will` live-pin re-anchoring planner for `BrokerLog::retain_before`
//! (`Astream.Broker.TlaBindWillCompactionUnblocker`).
//!
//! Resolves the `ROADMAP.md` retention-compaction blocker: long-lived `aterm` session `/a/bind`
//! leases and `/a/will` registrations sit near offset `0` and pin the entire log against
//! `retain_before(horizon)`. When an active pin blocks `horizon` by more than `reanchor_span`,
//! this planner triggers a deterministic tail re-anchor to `log_hw` and advances `compacted_base`
//! monotonically up to `min(horizon, oldest_active_pin)`.

#[cfg(clean_islands)]
#[path = "bind_will_compaction_unblocker_island.rs"]
mod bind_will_compaction_unblocker_island;
#[cfg(clean_islands)]
pub use bind_will_compaction_unblocker_island::{
    retain_base_advance_b120, retain_pin_floor_clamp_b120,
};

#[cfg(not(clean_islands))]
/// Clamp `req_horizon` so compaction never advances past `oldest_pin`.
#[must_use]
pub const fn retain_pin_floor_clamp_b120(req_horizon: u64, oldest_pin: u64) -> u64 {
    if req_horizon < oldest_pin {
        req_horizon
    } else {
        oldest_pin
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `compacted_base`.
#[must_use]
pub const fn retain_base_advance_b120(cur_base: u64, cand_base: u64) -> u64 {
    if cur_base < cand_base {
        cand_base
    } else {
        cur_base
    }
}

contract_fn! {
    /// True iff `oldest_pin` is strictly below `req_horizon` (blocking full compaction).
    #[must_use]
    pub const fn pin_blocks_horizon_b120(oldest_pin: u64, req_horizon: u64) -> bool
    clauses [ensures result == (oldest_pin < req_horizon)]
    {
        oldest_pin < req_horizon
    }
}

/// Action planned for `BrokerLog::retain_before(req_horizon)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RetainUnblockPlan {
    /// Compact directly to `new_base` (no re-anchor required).
    CompactTo { new_base: u64 },
    /// Re-anchor live `/a/bind` + `/a/will` records below `req_horizon` at `reanchor_at_hw`,
    /// then compact up to `new_base_after_reanchor`.
    ReanchorAndCompact {
        reanchor_at_hw: u64,
        new_base_after_reanchor: u64,
    },
}

/// Planner tracking `/a/bind` and `/a/will` pin horizons across multi-day `aterm` runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BindWillCompactionUnblocker {
    compacted_base: u64,
    reanchor_threshold: u64,
    reanchor_count: u64,
}

impl Default for BindWillCompactionUnblocker {
    fn default() -> Self {
        Self::new(1_024)
    }
}

impl BindWillCompactionUnblocker {
    #[must_use]
    pub const fn new(reanchor_threshold: u64) -> Self {
        Self {
            compacted_base: 0,
            reanchor_threshold: if reanchor_threshold == 0 {
                1
            } else {
                reanchor_threshold
            },
            reanchor_count: 0,
        }
    }

    #[must_use]
    pub const fn compacted_base(&self) -> u64 {
        self.compacted_base
    }

    #[must_use]
    pub const fn reanchor_count(&self) -> u64 {
        self.reanchor_count
    }

    /// Plan compaction for `req_horizon` given `log_hw` and optional `(oldest_bind, oldest_will)`.
    pub fn plan_retain(
        &mut self,
        req_horizon: u64,
        log_hw: u64,
        oldest_bind: Option<u64>,
        oldest_will: Option<u64>,
    ) -> RetainUnblockPlan {
        let bounded_req = retain_pin_floor_clamp_b120(req_horizon, log_hw);
        let oldest_pin = match (oldest_bind, oldest_will) {
            (Some(b), Some(w)) => retain_pin_floor_clamp_b120(b, w),
            (Some(b), None) => b,
            (None, Some(w)) => w,
            (None, None) => log_hw,
        };
        if pin_blocks_horizon_b120(oldest_pin, bounded_req)
            && bounded_req.saturating_sub(oldest_pin) >= self.reanchor_threshold
        {
            self.reanchor_count = self.reanchor_count.saturating_add(1);
            let after_pin = retain_pin_floor_clamp_b120(bounded_req, log_hw);
            self.compacted_base = retain_base_advance_b120(self.compacted_base, after_pin);
            RetainUnblockPlan::ReanchorAndCompact {
                reanchor_at_hw: log_hw,
                new_base_after_reanchor: self.compacted_base,
            }
        } else {
            let safe_floor = retain_pin_floor_clamp_b120(bounded_req, oldest_pin);
            self.compacted_base = retain_base_advance_b120(self.compacted_base, safe_floor);
            RetainUnblockPlan::CompactTo {
                new_base: self.compacted_base,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reanchors_stale_bind_pin_when_gap_exceeds_threshold_and_never_regresses_base() {
        let mut u = BindWillCompactionUnblocker::new(500);
        // Pin at offset 10 with horizon 200 (< 500 threshold) -> clamps safely to 10:
        assert_eq!(
            u.plan_retain(200, 1_000, Some(10), Some(40)),
            RetainUnblockPlan::CompactTo { new_base: 10 }
        );
        // Horizon advances to 800 (`800 - 10 = 790 >= 500`) -> re-anchors to hw=1_000 and compacts to 800!
        assert_eq!(
            u.plan_retain(800, 1_000, Some(10), Some(40)),
            RetainUnblockPlan::ReanchorAndCompact {
                reanchor_at_hw: 1_000,
                new_base_after_reanchor: 800,
            }
        );
        assert_eq!(u.reanchor_count(), 1);
    }
}
