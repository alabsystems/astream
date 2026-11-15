// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pre-fanout worker admission gate verifying `aterm harness agy` headroom before spawning `N`
//! parallel subagents or `aterm ctl @self spawn` tabs (`Astream.AgyQuota.TlaFanoutAdmissionGate`).

#[cfg(clean_islands)]
#[path = "fanout_admission_gate_island.rs"]
mod fanout_admission_gate_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn aq_workers_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn aq_fanout_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use fanout_admission_gate_island::{aq_fanout_advance, aq_workers_clamp};

/// Hard ceiling on simultaneous `agy` fan-out workers per parent tab (`16`).
pub const MAX_FANOUT_WORKERS: u64 = 16;

contract_fn! {
    /// Verified fanout budget check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `aq_fanout_fits_isl`.
    #[must_use]
    pub const fn aq_fanout_fits(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct FanoutGate {
    batches_evaluated: u64,
}

impl FanoutGate {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            batches_evaluated: 0,
        }
    }

    pub fn admit_workers(
        &mut self,
        requested_workers: u64,
        per_worker_budget: u64,
        available_credits: u64,
    ) -> u64 {
        self.batches_evaluated = aq_fanout_advance(
            self.batches_evaluated,
            self.batches_evaluated.saturating_add(1),
        );
        let capped = aq_workers_clamp(requested_workers, MAX_FANOUT_WORKERS);
        let unit = if per_worker_budget == 0 {
            1
        } else {
            per_worker_budget
        };
        let mut admitted = capped;
        while admitted > 0 {
            let needed = admitted.saturating_mul(unit);
            if aq_fanout_fits(available_credits, needed) {
                return admitted;
            }
            admitted = admitted.saturating_sub(1);
        }
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scales_worker_count_down_to_fit_available_pool_credits() {
        let mut fg = FanoutGate::new();
        assert_eq!(fg.admit_workers(8, 500, 1_750), 3);
        assert_eq!(fg.admit_workers(4, 500, 200), 0);
    }
}
