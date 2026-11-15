// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Fail-closed `abrew` compatibility guard refusing `--real`, `--no-reroute`, and `ABREW_REAL`
//! bypass attempts (`aterm` primer: never installs or invokes real Homebrew;
//! `Astream.Abrew.TlaRerouteRefusal`).

#[cfg(clean_islands)]
#[path = "reroute_refusal_island.rs"]
mod reroute_refusal_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pkg_args_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pkg_refused_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use reroute_refusal_island::{pkg_args_clamp, pkg_refused_advance};

/// Maximum argv tokens inspected per `brew` / `abrew` invocation.
pub const MAX_ABREW_ARGS: u64 = 256;

contract_fn! {
    /// Verified native-only check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `pkg_native_only_isl`.
    #[must_use]
    pub const fn pkg_native_only(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Enforces `atpkg-abrew`'s no-bypass and disabled-stub contract.
#[derive(Debug, Clone, Default)]
pub struct AbrewInvocationGuard {
    compat_enabled: bool,
    refusals: u64,
}

impl AbrewInvocationGuard {
    #[must_use]
    pub const fn new(compat_enabled: bool) -> Self {
        Self {
            compat_enabled,
            refusals: 0,
        }
    }

    pub fn validate(
        &mut self,
        args: &[&str],
        abrew_real_env_set: bool,
    ) -> Result<(), &'static str> {
        let max_args = pkg_args_clamp(MAX_ABREW_ARGS, MAX_ABREW_ARGS) as usize;
        if args.len() > max_args {
            self.refusals = pkg_refused_advance(self.refusals, self.refusals.saturating_add(1));
            return Err("abrew argument count exceeds MAX_ABREW_ARGS");
        }
        let lim = pkg_args_clamp(args.len() as u64, MAX_ABREW_ARGS) as usize;
        let env_flag = if abrew_real_env_set { 1u64 } else { 0u64 };
        if abrew_real_env_set || !pkg_native_only(0, env_flag) {
            self.refusals = pkg_refused_advance(self.refusals, self.refusals.saturating_add(1));
            return Err("ABREW_REAL refused: abrew never invokes real Homebrew");
        }
        let mut idx = 0usize;
        while idx < lim {
            let Some(&a) = args.get(idx) else {
                break;
            };
            if a == "--real"
                || a == "--no-reroute"
                || a.starts_with("--real=")
                || a.starts_with("--no-reroute=")
            {
                self.refusals = pkg_refused_advance(self.refusals, self.refusals.saturating_add(1));
                return Err("real Homebrew bypass flags (--real / --no-reroute) are refused");
            }
            idx = idx.saturating_add(1);
        }
        if !self.compat_enabled {
            let sub = match args.first() {
                Some(&s) => s,
                None => "",
            };
            if sub != "on" && sub != "status" {
                self.refusals = pkg_refused_advance(self.refusals, self.refusals.saturating_add(1));
                return Err(
                    "abrew compatibility disabled; only `on` and `status` remain available",
                );
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn abrew_guard_refuses_real_flags_abrew_real_env_and_disabled_commands() {
        let mut g = AbrewInvocationGuard::new(true);
        assert!(g.validate(&["install", "ripgrep"], false).is_ok());
        assert!(g.validate(&["--real", "install", "jq"], false).is_err());
        assert!(g.validate(&["install", "jq"], true).is_err());

        let mut off = AbrewInvocationGuard::new(false);
        assert!(off.validate(&["status"], false).is_ok());
        assert!(off.validate(&["install", "jq"], false).is_err());
    }
}
