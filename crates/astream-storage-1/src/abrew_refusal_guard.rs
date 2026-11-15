// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `atpkg-abrew` bypass-refusal & disabled-stub command gate
//! (`Astream.Host.TlaAbrewRefusalGuard`).
//!
//! Enforces `aterm`'s native `brew` compatibility invariants:
//! 1. `--real`, `--no-reroute`, and `ABREW_REAL` env bypasses ALWAYS refuse rather
//!    than invoking real Homebrew.
//! 2. When compatibility is disabled (`enabled == false`), the managed stub stays
//!    in place and refuses commands EXCEPT `on` and `status`.
//! 3. `bundle` allows bare `bundle` (native Brewfile) and `bundle status` /
//!    `bundle remove`, refusing legacy `bundle dump` / `bundle exec` sub-verbs.

#[cfg(clean_islands)]
#[path = "abrew_refusal_guard_island.rs"]
mod abrew_refusal_guard_island;
#[cfg(clean_islands)]
pub use abrew_refusal_guard_island::{abrew_audit_epoch_advance, abrew_refusals_clamp};

/// Hard upper bound on counted `abrew` refusals.
pub const MAX_ABREW_REFUSALS: u64 = 4_096;

#[cfg(not(clean_islands))]
/// Monotonically advance the `abrew` command-audit epoch.
#[must_use]
pub const fn abrew_audit_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

#[cfg(not(clean_islands))]
/// Clamp `abrew` refusal counter to `max_refusals`.
#[must_use]
pub const fn abrew_refusals_clamp(cand_refusals: u64, max_refusals: u64) -> u64 {
    if cand_refusals < max_refusals {
        cand_refusals
    } else {
        max_refusals
    }
}

contract_fn! {
    /// True iff zero bypass flags/env vars were supplied (`bypass_flags == 0`).
    #[must_use]
    pub const fn abrew_bypass_free(bypass_flags: u64, zero_expected: u64) -> bool
    clauses [ensures result == (bypass_flags == zero_expected)]
    {
        bypass_flags == zero_expected
    }
}

/// Refusal reasons emitted by the `abrew` compatibility stub.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbrewRefusal {
    RealHomebrewBypassForbidden,
    CompatibilityDisabledStub,
    UnsupportedBundleSubcommand,
    MissingSubcommand,
}

/// Authorized `abrew` dispatch action.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbrewDispatch {
    EnableCompat,
    DisableCompat,
    ReportStatus,
    NativeBundleInstall,
    LegacyBundleInspectOrRemove,
    NativePackageVerb,
}

/// Stateful `abrew` stub command gate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AbrewRefusalGuard {
    enabled: bool,
    audit_epoch: u64,
    refusals: u64,
}

impl Default for AbrewRefusalGuard {
    fn default() -> Self {
        Self::new(true)
    }
}

impl AbrewRefusalGuard {
    #[must_use]
    pub const fn new(enabled: bool) -> Self {
        Self {
            enabled,
            audit_epoch: 0,
            refusals: 0,
        }
    }

    #[must_use]
    pub const fn is_enabled(&self) -> bool {
        self.enabled
    }

    #[must_use]
    pub const fn audit_epoch(&self) -> u64 {
        self.audit_epoch
    }

    #[must_use]
    pub const fn refusals(&self) -> u64 {
        self.refusals
    }

    /// Evaluate `args` (excluding `argv[0]`) and `abrew_real_env_set`.
    pub fn evaluate(
        &mut self,
        args: &[&[u8]],
        abrew_real_env_set: bool,
    ) -> Result<AbrewDispatch, AbrewRefusal> {
        let cand_ep = self.audit_epoch.saturating_add(1);
        self.audit_epoch = abrew_audit_epoch_advance(self.audit_epoch, cand_ep);

        let mut bypass_hits = if abrew_real_env_set { 1u64 } else { 0u64 };
        let mut scan = args;
        while let &[a, ref tail @ ..] = scan {
            if a == b"--real" || a == b"--no-reroute" {
                bypass_hits = bypass_hits.saturating_add(1);
            }
            scan = tail;
        }
        if !abrew_bypass_free(bypass_hits, 0) {
            self.record_refusal();
            return Err(AbrewRefusal::RealHomebrewBypassForbidden);
        }

        let &[sub, ref rest @ ..] = args else {
            self.record_refusal();
            return Err(AbrewRefusal::MissingSubcommand);
        };

        if sub == b"on" {
            self.enabled = true;
            return Ok(AbrewDispatch::EnableCompat);
        }
        if sub == b"status" {
            return Ok(AbrewDispatch::ReportStatus);
        }
        if !self.enabled {
            self.record_refusal();
            return Err(AbrewRefusal::CompatibilityDisabledStub);
        }
        if sub == b"off" {
            self.enabled = false;
            return Ok(AbrewDispatch::DisableCompat);
        }
        if sub == b"bundle" {
            return match rest {
                [] => Ok(AbrewDispatch::NativeBundleInstall),
                [b"status", ..] | [b"remove", ..] => Ok(AbrewDispatch::LegacyBundleInspectOrRemove),
                _ => {
                    self.record_refusal();
                    Err(AbrewRefusal::UnsupportedBundleSubcommand)
                }
            };
        }
        Ok(AbrewDispatch::NativePackageVerb)
    }

    fn record_refusal(&mut self) {
        let cand = self.refusals.saturating_add(1);
        self.refusals = abrew_refusals_clamp(cand, MAX_ABREW_REFUSALS);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_real_bypass_and_retains_on_and_status_when_disabled() {
        let mut g = AbrewRefusalGuard::new(true);

        // --real, --no-reroute, and ABREW_REAL always refuse!
        assert_eq!(
            g.evaluate(&[b"--real", b"install", b"jq"], false),
            Err(AbrewRefusal::RealHomebrewBypassForbidden)
        );
        assert_eq!(
            g.evaluate(&[b"install", b"jq"], true),
            Err(AbrewRefusal::RealHomebrewBypassForbidden)
        );

        // Bare bundle and bundle status succeed; bundle exec refuses
        assert_eq!(
            g.evaluate(&[b"bundle"], false),
            Ok(AbrewDispatch::NativeBundleInstall)
        );
        assert_eq!(
            g.evaluate(&[b"bundle", b"status"], false),
            Ok(AbrewDispatch::LegacyBundleInspectOrRemove)
        );
        assert_eq!(
            g.evaluate(&[b"bundle", b"exec", b"sh"], false),
            Err(AbrewRefusal::UnsupportedBundleSubcommand)
        );

        // Disable compatibility: install refuses, status and on remain available!
        assert_eq!(
            g.evaluate(&[b"off"], false),
            Ok(AbrewDispatch::DisableCompat)
        );
        assert_eq!(
            g.evaluate(&[b"install", b"ripgrep"], false),
            Err(AbrewRefusal::CompatibilityDisabledStub)
        );
        assert_eq!(
            g.evaluate(&[b"status"], false),
            Ok(AbrewDispatch::ReportStatus)
        );
        assert_eq!(g.evaluate(&[b"on"], false), Ok(AbrewDispatch::EnableCompat));
        assert_eq!(
            g.evaluate(&[b"install", b"ripgrep"], false),
            Ok(AbrewDispatch::NativePackageVerb)
        );
    }
}
