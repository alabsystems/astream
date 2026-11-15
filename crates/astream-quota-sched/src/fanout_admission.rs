// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pre-spawn worker fanout admission gate ensuring parallel `aterm ctl @self spawn` waves fit
//! inside remaining 5-hour + weekly model-pool headroom (`Astream.Quota.TlaFanoutAdmission`).

#[cfg(clean_islands)]
#[path = "fanout_admission_island.rs"]
mod fanout_admission_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn fanout_workers_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn fanout_admitted_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use fanout_admission_island::{fanout_admitted_advance, fanout_workers_clamp};

/// Hard ceiling on parallel workers spawned in one fanout wave.
pub const MAX_FANOUT_WORKERS: u64 = 32;

contract_fn! {
    /// Verified budget check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `fanout_fits_pool_isl`.
    #[must_use]
    pub const fn fanout_fits_pool(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Computes safe worker count (`0..=requested_workers`) given estimated per-worker cost.
#[derive(Debug, Clone, Default)]
pub struct FanoutAdmissionController {
    admitted_total: u64,
}

impl FanoutAdmissionController {
    #[must_use]
    pub const fn new() -> Self {
        Self { admitted_total: 0 }
    }

    #[must_use]
    pub const fn admitted_total(&self) -> u64 {
        self.admitted_total
    }

    pub fn plan_wave(
        &mut self,
        requested_workers: u64,
        est_cost_per_worker_bps: u64,
        available_pool_bps: u64,
    ) -> u64 {
        let req = fanout_workers_clamp(requested_workers, MAX_FANOUT_WORKERS);
        if est_cost_per_worker_bps == 0 {
            self.admitted_total = fanout_admitted_advance(
                self.admitted_total,
                self.admitted_total.saturating_add(req),
            );
            return req;
        }
        let mut safe = 0u64;
        let mut n = 1u64;
        while n <= req {
            let need = n.saturating_mul(est_cost_per_worker_bps);
            if fanout_fits_pool(available_pool_bps, need) {
                safe = n;
                n = n.saturating_add(1);
            } else {
                break;
            }
        }
        self.admitted_total = fanout_admitted_advance(
            self.admitted_total,
            self.admitted_total.saturating_add(safe),
        );
        safe
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fanout_admission_scales_worker_wave_to_exact_pool_headroom() {
        let mut f = FanoutAdmissionController::new();
        assert_eq!(f.plan_wave(10, 1_500, 5_000), 3);
        assert_eq!(f.plan_wave(4, 2_000, 1_000), 0);
        assert_eq!(f.admitted_total(), 3);
    }
}
