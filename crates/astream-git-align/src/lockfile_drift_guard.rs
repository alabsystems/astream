// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Zero-third-party registry-package drift guard ensuring no workspace crate outside
//! `astream-aead` (and dev/gate `serde`/`toml`/`proptest` in `astream-evidence`) introduces new
//! `crates.io` dependencies (`README.md` lines 58–69, `Astream.GitAlign.TlaLockfileDriftGuard`).

#[cfg(clean_islands)]
#[path = "lockfile_drift_guard_island.rs"]
mod lockfile_drift_guard_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn git_pkgs_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn git_lock_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use lockfile_drift_guard_island::{git_lock_advance, git_pkgs_clamp};

/// Maximum locked packages audited in `Cargo.lock`.
pub const MAX_LOCKED_PACKAGES: u64 = 1_024;

contract_fn! {
    /// Verified zero-new-registry-pkg check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `git_lock_unchanged_isl`.
    #[must_use]
    pub const fn git_lock_unchanged(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Verifies that adding workspace path crates adds `0` external `registry+` packages to `Cargo.lock`.
#[derive(Debug, Clone)]
pub struct RegistryDependencyFreeze {
    baseline_registry_count: u64,
    checks: u64,
}

impl RegistryDependencyFreeze {
    #[must_use]
    pub const fn new(baseline_registry_count: u64) -> Self {
        Self {
            baseline_registry_count: git_pkgs_clamp(baseline_registry_count, MAX_LOCKED_PACKAGES),
            checks: 0,
        }
    }

    pub fn verify_registry_count(
        &mut self,
        current_registry_count: u64,
    ) -> Result<(), &'static str> {
        let cur = git_pkgs_clamp(current_registry_count, MAX_LOCKED_PACKAGES);
        self.checks = git_lock_advance(self.checks, self.checks.saturating_add(1));
        if !git_lock_unchanged(self.baseline_registry_count, cur) {
            return Err("Cargo.lock gained unexpected third-party crates.io dependencies");
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn registry_freeze_allows_path_crates_while_blocking_new_crates_io_packages() {
        let mut f = RegistryDependencyFreeze::new(48);
        assert!(f.verify_registry_count(48).is_ok());
        assert!(f.verify_registry_count(49).is_err());
    }
}
