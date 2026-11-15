// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Darwin QoS (`QOS_CLASS_BACKGROUND` / `PRIO_DARWIN_BG`) E-core clamping classifier for
//! `aterm ctl @self sys why` (`Astream.SysTel.TlaQosClampDiagnose`).

#[cfg(clean_islands)]
#[path = "qos_clamp_diagnose_island.rs"]
mod qos_clamp_diagnose_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sys_procs_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sys_diag_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use qos_clamp_diagnose_island::{sys_diag_advance, sys_procs_clamp};

/// Maximum processes inspected in one `sys why` snapshot.
pub const MAX_WHY_PROCS: u64 = 512;

contract_fn! {
    /// Verified P-core eligibility (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sys_unthrottled_isl`.
    #[must_use]
    pub const fn sys_unthrottled(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QosVerdict {
    UnthrottledPCores,
    ClampedToECoresBackground,
}

/// Diagnoses when a CPU-bound build/solver worker has been demoted onto Efficiency cores only.
#[derive(Debug, Clone, Default)]
pub struct DarwinQosDiagnoser {
    snapshots: u64,
}

impl DarwinQosDiagnoser {
    #[must_use]
    pub const fn new() -> Self {
        Self { snapshots: 0 }
    }

    /// `p_share_permille` is `p_cluster_mc * 1000 / total_mc` (`0..=1000`).
    pub fn classify(
        &mut self,
        total_busy_mc: u64,
        p_share_permille: u64,
        darwin_bg_flag: bool,
    ) -> QosVerdict {
        let _ = sys_procs_clamp(1, MAX_WHY_PROCS);
        self.snapshots = sys_diag_advance(self.snapshots, self.snapshots.saturating_add(1));
        if darwin_bg_flag || (total_busy_mc >= 800 && !sys_unthrottled(p_share_permille, 50)) {
            QosVerdict::ClampedToECoresBackground
        } else {
            QosVerdict::UnthrottledPCores
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn qos_diagnoser_identifies_ecore_clamped_background_workers() {
        let mut d = DarwinQosDiagnoser::new();
        assert_eq!(d.classify(3_500, 920, false), QosVerdict::UnthrottledPCores);
        assert_eq!(
            d.classify(1_900, 0, false),
            QosVerdict::ClampedToECoresBackground
        );
        assert_eq!(
            d.classify(200, 500, true),
            QosVerdict::ClampedToECoresBackground
        );
    }
}
