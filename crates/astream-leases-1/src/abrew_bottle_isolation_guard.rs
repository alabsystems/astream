// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `atpkg-abrew` native brew compatibility & bypass-refusal guard
//! (`Astream.Host.TlaAbrewBottleIsolationGuard`, Island #281).

#![allow(
    clippy::assign_op_pattern,
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "abrew_bottle_isolation_guard_island.rs"]
mod abrew_bottle_isolation_guard_island;
#[cfg(clean_islands)]
pub use abrew_bottle_isolation_guard_island::{abrew_cask_kind_clamp, abrew_refusal_count_advance};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn abrew_cask_kind_clamp(kind_code: u64, max_kind: u64) -> u64 {
    if kind_code < max_kind {
        kind_code
    } else {
        max_kind
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn abrew_refusal_count_advance(prev: u64, next: u64) -> u64 {
    if prev < next {
        next
    } else {
        prev
    }
}

/// Bypass bit 0: `--real` passed on argv.
pub const BYPASS_FLAG_REAL: u64 = 1 << 0;
/// Bypass bit 1: `--no-reroute` passed on argv.
pub const BYPASS_FLAG_NO_REROUTE: u64 = 1 << 1;
/// Bypass bit 2: `ABREW_REAL` set in environment.
pub const BYPASS_ENV_ABREW_REAL: u64 = 1 << 2;

/// Maximum artifact kind code (`0 = Bottle`, `1 = TarCask`, `2 = ZipCask`, `3 = DmgCask`,
/// `4 = SingleFileCask`, `5 = UnsupportedPkgInstaller`).
pub const MAX_ABREW_ARTIFACT_KIND: u64 = 5;

contract_fn! {
    /// Verified check that zero Homebrew-bypass flags/env vars were supplied
    /// (`bypass_flags == 0`), linked via `clean-kernel-defeq` to `abrew_no_bypass_requested_isl`.
    #[must_use]
    pub const fn abrew_no_bypass_requested(bypass_flags: u64) -> bool
    clauses [ensures result == (bypass_flags == 0)]
    {
        bypass_flags == 0
    }
}

/// Supported and unsupported `abrew` artifact formats.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbrewArtifactKind {
    Bottle,
    TarCask,
    ZipCask,
    DmgCask,
    SingleFileCask,
    UnsupportedInstallerPkg,
}

impl AbrewArtifactKind {
    #[must_use]
    pub const fn code(self) -> u64 {
        match self {
            Self::Bottle => 0,
            Self::TarCask => 1,
            Self::ZipCask => 2,
            Self::DmgCask => 3,
            Self::SingleFileCask => 4,
            Self::UnsupportedInstallerPkg => 5,
        }
    }

    #[must_use]
    pub const fn is_supported(self) -> bool {
        abrew_cask_kind_clamp(self.code(), MAX_ABREW_ARTIFACT_KIND) < MAX_ABREW_ARTIFACT_KIND
    }
}

/// Decision produced by [`AbrewIsolationGuard::evaluate`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbrewDecision {
    /// Allowed administrative verb (`on` or `status`), available even when disabled.
    AllowAdminVerb,
    /// Allowed native install or native `bundle` inside `atpkg`'s isolated prefix.
    AllowIsolatedPrefixOp,
    /// Allowed read/cleanup of an owned legacy bundle (`bundle status` / `bundle remove`).
    AllowOwnedLegacyBundleOp,
    /// Refused `--real`, `--no-reroute`, or `ABREW_REAL` bypass attempt!
    RefuseRealHomebrewBypass { bypass_flags: u64 },
    /// Refused because `abrew` compatibility is currently disabled (managed stub retained).
    RefuseCompatDisabled,
    /// Refused unsupported cask/legacy operation (never falls back to real Homebrew).
    RefuseUnsupportedOperation,
}

/// Stateful `atpkg-abrew` isolation guard.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbrewIsolationGuard {
    compat_enabled: bool,
    refusal_count: u64,
}

impl Default for AbrewIsolationGuard {
    fn default() -> Self {
        Self::new(true)
    }
}

impl AbrewIsolationGuard {
    #[must_use]
    pub const fn new(compat_enabled: bool) -> Self {
        Self {
            compat_enabled,
            refusal_count: 0,
        }
    }

    #[must_use]
    pub const fn compat_enabled(&self) -> bool {
        self.compat_enabled
    }

    #[must_use]
    pub const fn refusal_count(&self) -> u64 {
        self.refusal_count
    }

    fn bump_refusal(&mut self) {
        self.refusal_count =
            abrew_refusal_count_advance(self.refusal_count, self.refusal_count.saturating_add(1));
    }

    /// Evaluate an `abrew` invocation (`args` after `brew`/`abrew`, `abrew_real_env` set).
    pub fn evaluate(
        &mut self,
        args: &[&str],
        abrew_real_env: bool,
        artifact_kind: Option<AbrewArtifactKind>,
    ) -> AbrewDecision {
        let mut bypass = if abrew_real_env {
            BYPASS_ENV_ABREW_REAL
        } else {
            0
        };
        let mut rest = args;
        while let [a, tail @ ..] = rest {
            if *a == "--real" {
                bypass = bypass | (BYPASS_FLAG_REAL);
            } else if *a == "--no-reroute" {
                bypass = bypass | (BYPASS_FLAG_NO_REROUTE);
            }
            rest = tail;
        }
        if !abrew_no_bypass_requested(bypass) {
            self.bump_refusal();
            return AbrewDecision::RefuseRealHomebrewBypass {
                bypass_flags: bypass,
            };
        }

        let first = match args.first() {
            Some(&s) => s,
            None => "status",
        };
        if first == "on" {
            self.compat_enabled = true;
            return AbrewDecision::AllowAdminVerb;
        }
        if first == "status" {
            return AbrewDecision::AllowAdminVerb;
        }
        if !self.compat_enabled {
            self.bump_refusal();
            return AbrewDecision::RefuseCompatDisabled;
        }
        if first == "off" {
            self.compat_enabled = false;
            return AbrewDecision::AllowAdminVerb;
        }

        if first == "bundle" {
            return match args.get(1) {
                None => AbrewDecision::AllowIsolatedPrefixOp,
                Some(&"status" | &"remove") if args.len() == 2 => {
                    AbrewDecision::AllowOwnedLegacyBundleOp
                }
                Some(_) => {
                    self.bump_refusal();
                    AbrewDecision::RefuseUnsupportedOperation
                }
            };
        }

        if first == "install" {
            let kind = match artifact_kind {
                Some(k) => k,
                None => AbrewArtifactKind::Bottle,
            };
            if kind.is_supported() {
                return AbrewDecision::AllowIsolatedPrefixOp;
            }
        }

        self.bump_refusal();
        AbrewDecision::RefuseUnsupportedOperation
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_real_bypass_and_keeps_on_and_status_when_disabled() {
        let mut g = AbrewIsolationGuard::new(true);
        assert!(g.compat_enabled());
        assert_eq!(
            g.evaluate(&["install", "--real", "jq"], false, None),
            AbrewDecision::RefuseRealHomebrewBypass {
                bypass_flags: BYPASS_FLAG_REAL
            }
        );
        assert_eq!(
            g.evaluate(&["install", "jq"], true, None),
            AbrewDecision::RefuseRealHomebrewBypass {
                bypass_flags: BYPASS_ENV_ABREW_REAL
            }
        );
        assert_eq!(
            g.evaluate(&["bundle"], false, None),
            AbrewDecision::AllowIsolatedPrefixOp
        );
        assert_eq!(
            g.evaluate(&["bundle", "status"], false, None),
            AbrewDecision::AllowOwnedLegacyBundleOp
        );
        assert_eq!(
            g.evaluate(&["bundle", "dump"], false, None),
            AbrewDecision::RefuseUnsupportedOperation
        );

        assert_eq!(
            g.evaluate(&["off"], false, None),
            AbrewDecision::AllowAdminVerb
        );
        assert!(!g.compat_enabled());
        assert_eq!(
            g.evaluate(
                &["install", "ripgrep"],
                false,
                Some(AbrewArtifactKind::Bottle)
            ),
            AbrewDecision::RefuseCompatDisabled
        );
        assert_eq!(
            g.evaluate(&["status"], false, None),
            AbrewDecision::AllowAdminVerb
        );
        assert_eq!(
            g.evaluate(&["on"], false, None),
            AbrewDecision::AllowAdminVerb
        );
        assert_eq!(
            g.evaluate(
                &["install", "ripgrep"],
                false,
                Some(AbrewArtifactKind::DmgCask)
            ),
            AbrewDecision::AllowIsolatedPrefixOp
        );
    }
}
