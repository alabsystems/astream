// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Apple Silicon P-cluster + E-cluster millicore (`mc`, `1000 mc == 1 busy core`) aggregator for
//! `aterm ctl @self sys` (`Astream.SysTel.TlaClusterBusyCores`).

#[cfg(clean_islands)]
#[path = "cluster_busy_cores_island.rs"]
mod cluster_busy_cores_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sys_mc_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sys_sample_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use cluster_busy_cores_island::{sys_mc_clamp, sys_sample_advance};

/// Hard ceiling (`128` cores == `128_000` millicores).
pub const MAX_MACHINE_MILLICORES: u64 = 128_000;

contract_fn! {
    /// Verified saturation headroom (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sys_below_saturation_isl`.
    #[must_use]
    pub const fn sys_below_saturation(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Aggregates E-cluster and P-cluster busy millicores against physical core capacity.
#[derive(Debug, Clone)]
pub struct ClusterMillicoreMeter {
    capacity_mc: u64,
    samples: u64,
}

impl ClusterMillicoreMeter {
    #[must_use]
    pub const fn new(physical_cores: u64) -> Self {
        let raw_cap = physical_cores.saturating_mul(1_000);
        Self {
            capacity_mc: sys_mc_clamp(raw_cap, MAX_MACHINE_MILLICORES),
            samples: 0,
        }
    }

    /// Returns `(total_busy_mc, has_spare_core)` where `has_spare_core` requires `>= 1000 mc` idle.
    pub fn observe(&mut self, e_cluster_mc: u64, p_cluster_mc: u64) -> (u64, bool) {
        self.samples = sys_sample_advance(self.samples, self.samples.saturating_add(1));
        let total = sys_mc_clamp(e_cluster_mc.saturating_add(p_cluster_mc), self.capacity_mc);
        let needed_for_spare = total.saturating_add(1_000);
        (
            total,
            sys_below_saturation(self.capacity_mc, needed_for_spare),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn millicore_meter_sums_e_and_p_clusters_and_flags_full_core_saturation() {
        let mut m = ClusterMillicoreMeter::new(16);
        assert_eq!(m.observe(2_400, 8_100), (10_500, true));
        assert_eq!(m.observe(4_000, 11_500), (15_500, false));
    }
}
