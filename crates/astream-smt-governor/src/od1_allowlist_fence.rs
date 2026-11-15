// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Strict `OD-1` `unproved_fail_closed` allowlist fence permitting ONLY the `16` pre-existing
//! upstream rows (`client.rs`: `3`, `astream-effects`: `7`, `astream-engine`: `6`) and `0` refuted
//! counterexamples anywhere (`Astream.SmtGov.TlaOd1AllowlistFence`).

#[cfg(clean_islands)]
#[path = "od1_allowlist_fence_island.rs"]
mod od1_allowlist_fence_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn smt_rows_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn smt_gate_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use od1_allowlist_fence_island::{smt_gate_advance, smt_rows_clamp};

/// Exact ceiling of pre-existing upstream `OD-1` rows across the entire workspace (`3 + 7 + 6 = 16`).
pub const MAX_ALLOWED_OD1_WORKSPACE_ROWS: u64 = 16;

contract_fn! {
    /// Verified zero genuine failures (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `smt_zero_refuted_isl`.
    #[must_use]
    pub const fn smt_zero_refuted(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

fn allowed_od1_for_target(target_label: &str) -> u64 {
    match target_label {
        "astream-broker" | "astream-broker-asb" => 3,
        "astream-effects" => 7,
        "astream-engine" => 6,
        _ => 0,
    }
}

/// Audits `failed` rows per READY target against the frozen `OD-1` allowlist.
#[derive(Debug, Clone, Default)]
pub struct Od1AllowlistAuditor {
    targets_checked: u64,
}

impl Od1AllowlistAuditor {
    #[must_use]
    pub const fn new() -> Self {
        Self { targets_checked: 0 }
    }

    pub fn verify_target(
        &mut self,
        target_label: &str,
        refuted_counterexamples: u64,
        unproved_od1_rows: u64,
    ) -> Result<(), &'static str> {
        let _ = smt_rows_clamp(unproved_od1_rows, MAX_ALLOWED_OD1_WORKSPACE_ROWS);
        self.targets_checked =
            smt_gate_advance(self.targets_checked, self.targets_checked.saturating_add(1));
        if !smt_zero_refuted(0, refuted_counterexamples) {
            return Err("refuted Level-0 SMT counterexample detected");
        }
        if unproved_od1_rows > allowed_od1_for_target(target_label) {
            return Err("unexpected unproved_fail_closed obligation outside frozen OD-1 allowlist");
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn od1_auditor_allows_frozen_upstream_rows_and_rejects_any_new_or_refuted_failure() {
        let mut a = Od1AllowlistAuditor::new();
        assert!(a.verify_target("astream-broker", 0, 3).is_ok());
        assert!(a.verify_target("astream-vt-ext", 0, 0).is_ok());
        assert!(a.verify_target("astream-vt-ext", 0, 1).is_err());
        assert!(a.verify_target("astream-broker", 1, 0).is_err());
    }
}
