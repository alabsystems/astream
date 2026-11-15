// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Native `atpkg-abrew` compatibility router & real-Homebrew bypass refusal
//! (`Astream.Host.TlaAbrewCompatGuard`).
//!
//! Enforces the `aterm` `abrew` compatibility rules (`aterm help abrew`):
//! - `brew`, `abrew`, and `atpkg-abrew` never invoke or install real Homebrew.
//! - `--real`, `--no-reroute`, and non-empty `ABREW_REAL` are refused rather than bypassing
//!   `atpkg`'s managed prefix (`real_brew_invocations == 0`).
//! - When compatibility is disabled (`compat_enabled == false`), the managed stub stays in
//!   place and permits only `on` and `status`, refusing all package/bundle mutations.
//! - Bare `abrew bundle` installs a native `Brewfile`; `bundle status` and `bundle remove`
//!   only inspect or explicitly remove an owned legacy bundle.

#![allow(
    clippy::manual_unwrap_or,
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "abrew_compat_guard_island.rs"]
mod abrew_compat_guard_island;
#[cfg(clean_islands)]
pub use abrew_compat_guard_island::{abrew_refused_clamp, abrew_zero_real};

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn abrew_refused_clamp(refused: u64, total: u64) -> u64 {
    if refused < total {
        refused
    } else {
        total
    }
}

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn abrew_zero_real(_flag: u64) -> u64 {
    0
}

contract_fn! {
    /// Verified check that `ABREW_REAL` environment length is non-zero (`0 < abrew_real_len`),
    /// linked via `clean-kernel-defeq` to `abrew_has_bypass_env_isl`.
    #[must_use]
    pub const fn abrew_has_bypass_env(abrew_real_len: u64) -> bool
    clauses [ensures result == (0 < abrew_real_len)]
    {
        0 < abrew_real_len
    }
}

/// Classified `abrew` / `brew` routing outcome.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AbrewRouteDecision {
    /// Allowed administrative `on` or `status` verb (permitted even while compat is disabled).
    AllowAdminStatusOrEnable,
    /// Native `atpkg-abrew` bottle or supported cask (`tar`/`zip`/`DMG`/single-file) operation.
    AllowNativePrefixOp,
    /// Bare `abrew bundle`: install native `Brewfile` into `atpkg` prefix.
    AllowNativeBrewfileInstall,
    /// `abrew bundle status` or `abrew bundle remove`: inspect/remove owned legacy bundle only.
    AllowOwnedLegacyBundleOp {
        /// `true` when explicitly removing (`bundle remove`), `false` for `bundle status`.
        remove: bool,
    },
    /// Refused because caller attempted `--real`, `--no-reroute`, or `ABREW_REAL`.
    RefuseRealBrewBypass {
        /// Specific bypass flag or environment variable intercepted.
        trigger: &'static str,
    },
    /// Refused because `atpkg-abrew` compatibility is currently disabled (`only on/status`).
    RefuseCompatDisabled,
    /// Refused unsupported Homebrew subcommand or `bundle` flag.
    RefuseUnsupportedOperation,
}

/// Stateful `atpkg-abrew` compatibility guard.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbrewCompatGuard {
    compat_enabled: bool,
    real_brew_invocations: u64,
    refused_bypasses: u64,
    total_commands: u64,
}

impl AbrewCompatGuard {
    /// Construct a new guard with initial compatibility state `compat_enabled`.
    #[must_use]
    pub const fn new(compat_enabled: bool) -> Self {
        Self {
            compat_enabled,
            real_brew_invocations: 0,
            refused_bypasses: 0,
            total_commands: 0,
        }
    }

    /// Enable or disable native `abrew` compatibility (retaining stub).
    pub const fn set_compat_enabled(&mut self, enabled: bool) {
        self.compat_enabled = enabled;
    }

    /// Count of real Homebrew invocations (invariant: always `0`).
    #[must_use]
    pub const fn real_brew_invocations(&self) -> u64 {
        self.real_brew_invocations
    }

    /// Clamped count of refused `--real` / `--no-reroute` / `ABREW_REAL` bypasses (`<= total_commands`).
    #[must_use]
    pub const fn refused_bypasses(&self) -> u64 {
        self.refused_bypasses
    }

    /// Total `brew`/`abrew`/`atpkg-abrew` invocations evaluated.
    #[must_use]
    pub const fn total_commands(&self) -> u64 {
        self.total_commands
    }

    /// Route an `args` slice (excluding `argv[0]`) and optional `abrew_real_env` value.
    pub fn route(&mut self, args: &[&str], abrew_real_env: Option<&str>) -> AbrewRouteDecision {
        let next_total = self.total_commands.saturating_add(1);
        let env_len = match abrew_real_env {
            Some(v) => v.len() as u64,
            None => 0,
        };
        let mut flag_bypass: Option<&'static str> = None;
        let mut rest = args;
        while let &[a, ref tail @ ..] = rest {
            if a == "--real" || a.starts_with("--real=") {
                flag_bypass = Some("--real");
                break;
            }
            if a == "--no-reroute" || a.starts_with("--no-reroute=") {
                flag_bypass = Some("--no-reroute");
                break;
            }
            rest = tail;
        }

        if abrew_has_bypass_env(env_len) || flag_bypass.is_some() {
            let next_ref = self.refused_bypasses.saturating_add(1);
            self.real_brew_invocations = abrew_zero_real(next_ref);
            self.refused_bypasses = abrew_refused_clamp(next_ref, next_total);
            self.total_commands = next_total;
            let trigger = match flag_bypass {
                Some(f) => f,
                None => "ABREW_REAL",
            };
            return AbrewRouteDecision::RefuseRealBrewBypass { trigger };
        }

        self.real_brew_invocations = abrew_zero_real(self.refused_bypasses);
        self.refused_bypasses = abrew_refused_clamp(self.refused_bypasses, next_total);
        self.total_commands = next_total;

        let sub = match args.first() {
            Some(&s) => s,
            None => "status",
        };
        if sub == "on" || sub == "status" || sub == "--version" || sub == "help" || sub == "--help"
        {
            if sub == "on" {
                self.compat_enabled = true;
            }
            return AbrewRouteDecision::AllowAdminStatusOrEnable;
        }
        if !self.compat_enabled {
            return AbrewRouteDecision::RefuseCompatDisabled;
        }
        if sub == "off" {
            self.compat_enabled = false;
            return AbrewRouteDecision::AllowAdminStatusOrEnable;
        }
        if sub == "bundle" {
            return match args.get(1) {
                None => AbrewRouteDecision::AllowNativeBrewfileInstall,
                Some(&arg)
                    if args.len() == 2
                        && arg.len() > "--file=".len()
                        && arg.starts_with("--file=") =>
                {
                    AbrewRouteDecision::AllowNativeBrewfileInstall
                }
                Some(&"status") if args.len() == 2 => {
                    AbrewRouteDecision::AllowOwnedLegacyBundleOp { remove: false }
                }
                Some(&"remove") if args.len() == 2 => {
                    AbrewRouteDecision::AllowOwnedLegacyBundleOp { remove: true }
                }
                _ => AbrewRouteDecision::RefuseUnsupportedOperation,
            };
        }
        match sub {
            "install" | "uninstall" | "remove" | "list" | "info" | "search" | "upgrade" => {
                AbrewRouteDecision::AllowNativePrefixOp
            }
            _ => AbrewRouteDecision::RefuseUnsupportedOperation,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_real_bypass_flags_env_and_enforces_disabled_stub_and_bundle_rules() {
        let mut g = AbrewCompatGuard::new(true);

        assert_eq!(
            g.route(&["--real", "install", "jq"], None),
            AbrewRouteDecision::RefuseRealBrewBypass { trigger: "--real" }
        );
        assert_eq!(
            g.route(&["install", "jq"], Some("1")),
            AbrewRouteDecision::RefuseRealBrewBypass {
                trigger: "ABREW_REAL"
            }
        );
        assert_eq!(
            g.route(&["bundle"], None),
            AbrewRouteDecision::AllowNativeBrewfileInstall
        );
        assert_eq!(
            g.route(&["bundle", "status"], None),
            AbrewRouteDecision::AllowOwnedLegacyBundleOp { remove: false }
        );
        assert_eq!(
            g.route(&["bundle", "dump"], None),
            AbrewRouteDecision::RefuseUnsupportedOperation
        );

        // Disable compat: `install` refused, `status` and `on` still work!
        assert_eq!(
            g.route(&["off"], None),
            AbrewRouteDecision::AllowAdminStatusOrEnable
        );
        assert_eq!(
            g.route(&["install", "ripgrep"], None),
            AbrewRouteDecision::RefuseCompatDisabled
        );
        assert_eq!(
            g.route(&["status"], None),
            AbrewRouteDecision::AllowAdminStatusOrEnable
        );
        assert_eq!(g.real_brew_invocations(), 0);
        assert_eq!(g.refused_bypasses(), 2);
        assert_eq!(g.total_commands(), 8);
    }
}
