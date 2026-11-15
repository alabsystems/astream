// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Custom rustup `trust` toolchain stale-symlink detector & `aterm pkg repair` planner
//! (`'rustc' is not installed for the custom toolchain 'trust'`, `Astream.Abrew.TlaToolchainLinkCheck`).

#[cfg(clean_islands)]
#[path = "toolchain_link_check_island.rs"]
mod toolchain_link_check_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pkg_links_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pkg_repair_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use toolchain_link_check_island::{pkg_links_clamp, pkg_repair_advance};

/// Required binaries in a healthy `trust` custom rustup toolchain (`rustc`, `cargo`, `rustdoc`, `clippy-driver`).
pub const REQUIRED_TRUST_LINKS: u64 = 4;

contract_fn! {
    /// Verified link health (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `pkg_link_healthy_isl`.
    #[must_use]
    pub const fn pkg_link_healthy(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ToolchainLinkDiagnosis {
    Healthy,
    RunAtermPkgRepair { reason: &'static str },
}

/// Diagnoses stale custom rustup `trust` symlinks from stderr or binary probe counts.
#[derive(Debug, Clone, Default)]
pub struct TrustToolchainDoctor {
    repairs_planned: u64,
}

impl TrustToolchainDoctor {
    #[must_use]
    pub const fn new() -> Self {
        Self { repairs_planned: 0 }
    }

    pub fn diagnose(
        &mut self,
        stderr_sample: &str,
        live_bin_targets: u64,
    ) -> ToolchainLinkDiagnosis {
        if stderr_sample.contains("'rustc' is not installed for the custom toolchain 'trust'") {
            self.repairs_planned =
                pkg_repair_advance(self.repairs_planned, self.repairs_planned.saturating_add(1));
            return ToolchainLinkDiagnosis::RunAtermPkgRepair {
                reason: "stale rustup custom toolchain link",
            };
        }
        let valid = pkg_links_clamp(live_bin_targets, REQUIRED_TRUST_LINKS);
        if !pkg_link_healthy(valid, REQUIRED_TRUST_LINKS) {
            self.repairs_planned =
                pkg_repair_advance(self.repairs_planned, self.repairs_planned.saturating_add(1));
            ToolchainLinkDiagnosis::RunAtermPkgRepair {
                reason: "missing store binary target under toolchains/trust",
            }
        } else {
            ToolchainLinkDiagnosis::Healthy
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn doctor_detects_exact_stale_trust_link_diagnostic_and_prescribes_pkg_repair() {
        let mut d = TrustToolchainDoctor::new();
        assert_eq!(d.diagnose("", 4), ToolchainLinkDiagnosis::Healthy);
        assert_eq!(
            d.diagnose(
                "error: 'rustc' is not installed for the custom toolchain 'trust'",
                4
            ),
            ToolchainLinkDiagnosis::RunAtermPkgRepair {
                reason: "stale rustup custom toolchain link"
            }
        );
    }
}
