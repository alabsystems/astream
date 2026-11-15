// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `atpkg-abrew` (`brew` compatibility) bypass-refusal and disabled-stub gate
//! (`aterm help abrew`; `Astream.Host.TlaAbrewRerouteRefusalGate`).
//!
//! Enforces `aterm`'s native `abrew` compatibility rules:
//! - `brew --real`, `brew --no-reroute`, and `ABREW_REAL` MUST refuse rather than bypass `abrew`
//!   or invoke real Homebrew,
//! - When `abrew` compatibility is disabled, the managed stub remains installed and refuses all
//!   commands EXCEPT `on` and `status`, which remain available.

#[cfg(clean_islands)]
#[path = "abrew_reroute_refusal_gate_island.rs"]
mod abrew_reroute_refusal_gate_island;
#[cfg(clean_islands)]
pub use abrew_reroute_refusal_gate_island::{abrew_cache_clamp_b123, abrew_epoch_advance_b123};

#[cfg(not(clean_islands))]
/// Clamp `abrew` prefix bottle cache bytes to `max_bytes`.
#[must_use]
pub const fn abrew_cache_clamp_b123(cand_bytes: u64, max_bytes: u64) -> u64 {
    if cand_bytes < max_bytes {
        cand_bytes
    } else {
        max_bytes
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `abrew` prefix install generation.
#[must_use]
pub const fn abrew_epoch_advance_b123(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff no real-Homebrew bypass flag or env var was requested (`bypass_mask == 0`).
    #[must_use]
    pub const fn abrew_bypass_absent_b123(bypass_mask: u64) -> bool
    clauses [ensures result == (bypass_mask == 0)]
    {
        bypass_mask == 0
    }
}

pub const BYPASS_FLAG_REAL: u64 = 1;
pub const BYPASS_FLAG_NO_REROUTE: u64 = 2;
pub const BYPASS_ENV_ABREW_REAL: u64 = 4;

/// Parsed `abrew` subcommand family.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbrewCommand {
    On,
    Off,
    Status,
    InstallBottleOrCask { bytes_needed: u64 },
    BundleNativeInstall { bytes_needed: u64 },
    BundleLegacyInspectOrRemove,
    UnsupportedOperation,
}

/// Gate verdict for an `abrew` (`brew`) invocation inside an `aterm` session.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbrewDecision {
    Admitted {
        install_epoch: u64,
        cache_bytes: u64,
    },
    RefusedRealHomebrewBypass {
        bypass_mask: u64,
    },
    RefusedCompatibilityDisabled,
    RefusedUnsupportedOperation,
}

/// Stateful `atpkg-abrew` command & bypass-refusal gate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AbrewRerouteRefusalGate {
    enabled: bool,
    cache_bytes: u64,
    max_cache_bytes: u64,
    install_epoch: u64,
}

impl AbrewRerouteRefusalGate {
    #[must_use]
    pub const fn new(enabled: bool, max_cache_bytes: u64) -> Self {
        Self {
            enabled,
            cache_bytes: 0,
            max_cache_bytes,
            install_epoch: 0,
        }
    }

    #[must_use]
    pub const fn is_enabled(&self) -> bool {
        self.enabled
    }

    /// Evaluate a `brew` / `abrew` invocation with `bypass_mask` (`--real`, `--no-reroute`, `ABREW_REAL`).
    pub fn evaluate(&mut self, bypass_mask: u64, cmd: AbrewCommand) -> AbrewDecision {
        // Bypass flags/env ALWAYS refuse, even for `status` or `on`.
        if !abrew_bypass_absent_b123(bypass_mask) {
            return AbrewDecision::RefusedRealHomebrewBypass { bypass_mask };
        }
        if !self.enabled {
            return match cmd {
                AbrewCommand::On => {
                    self.enabled = true;
                    AbrewDecision::Admitted {
                        install_epoch: self.install_epoch,
                        cache_bytes: self.cache_bytes,
                    }
                }
                AbrewCommand::Status => AbrewDecision::Admitted {
                    install_epoch: self.install_epoch,
                    cache_bytes: self.cache_bytes,
                },
                _ => AbrewDecision::RefusedCompatibilityDisabled,
            };
        }
        match cmd {
            AbrewCommand::On | AbrewCommand::Status | AbrewCommand::BundleLegacyInspectOrRemove => {
                AbrewDecision::Admitted {
                    install_epoch: self.install_epoch,
                    cache_bytes: self.cache_bytes,
                }
            }
            AbrewCommand::Off => {
                self.enabled = false;
                AbrewDecision::Admitted {
                    install_epoch: self.install_epoch,
                    cache_bytes: self.cache_bytes,
                }
            }
            AbrewCommand::InstallBottleOrCask { bytes_needed }
            | AbrewCommand::BundleNativeInstall { bytes_needed } => {
                self.cache_bytes = abrew_cache_clamp_b123(
                    self.cache_bytes.saturating_add(bytes_needed),
                    self.max_cache_bytes,
                );
                self.install_epoch = abrew_epoch_advance_b123(
                    self.install_epoch,
                    self.install_epoch.saturating_add(1),
                );
                AbrewDecision::Admitted {
                    install_epoch: self.install_epoch,
                    cache_bytes: self.cache_bytes,
                }
            }
            AbrewCommand::UnsupportedOperation => AbrewDecision::RefusedUnsupportedOperation,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_real_brew_bypass_and_keeps_only_on_and_status_when_disabled() {
        let mut gate = AbrewRerouteRefusalGate::new(true, 1_000_000);
        assert_eq!(
            gate.evaluate(BYPASS_FLAG_REAL, AbrewCommand::Status),
            AbrewDecision::RefusedRealHomebrewBypass {
                bypass_mask: BYPASS_FLAG_REAL
            }
        );
        assert_eq!(
            gate.evaluate(
                BYPASS_ENV_ABREW_REAL,
                AbrewCommand::InstallBottleOrCask { bytes_needed: 100 }
            ),
            AbrewDecision::RefusedRealHomebrewBypass {
                bypass_mask: BYPASS_ENV_ABREW_REAL
            }
        );

        // Disable compatibility -> refuses installs, keeps `status` and `on`.
        assert!(matches!(
            gate.evaluate(0, AbrewCommand::Off),
            AbrewDecision::Admitted { .. }
        ));
        assert_eq!(
            gate.evaluate(0, AbrewCommand::InstallBottleOrCask { bytes_needed: 100 }),
            AbrewDecision::RefusedCompatibilityDisabled
        );
        assert!(matches!(
            gate.evaluate(0, AbrewCommand::Status),
            AbrewDecision::Admitted { .. }
        ));
        assert!(matches!(
            gate.evaluate(0, AbrewCommand::On),
            AbrewDecision::Admitted { .. }
        ));
        assert_eq!(
            gate.evaluate(0, AbrewCommand::BundleNativeInstall { bytes_needed: 4096 }),
            AbrewDecision::Admitted {
                install_epoch: 1,
                cache_bytes: 4096
            }
        );
    }
}
