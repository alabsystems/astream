// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `atpkg-abrew` (`brew` compatibility) anti-bypass & disabled-state verb gate
//! (`Astream.Live.TlaAbrewRerouteRefusalFence`).
//!
//! Enforces `aterm help abrew` invariants:
//! - `brew --real`, `brew --no-reroute`, and `ABREW_REAL` are always refused fail-closed rather
//!   than bypassing `atpkg` into real Homebrew.
//! - When compatibility is disabled, managed stub retains control and refuses verbs except
//!   `on` and `status`.

#[cfg(clean_islands)]
#[path = "abrew_reroute_refusal_fence_island.rs"]
mod abrew_reroute_refusal_fence_island;
#[cfg(clean_islands)]
pub use abrew_reroute_refusal_fence_island::{abrew_epoch_advance_b111, abrew_refusal_clamp_b111};

#[cfg(not(clean_islands))]
/// Clamp `abrew` bypass/disabled refusal counter to `max_refusals`.
#[must_use]
pub const fn abrew_refusal_clamp_b111(cand_refusals: u64, max_refusals: u64) -> u64 {
    if cand_refusals < max_refusals {
        cand_refusals
    } else {
        max_refusals
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `abrew` command evaluation epoch.
#[must_use]
pub const fn abrew_epoch_advance_b111(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `refusals` remains strictly below `max_refusals`.
    #[must_use]
    pub const fn abrew_refusals_below_cap_b111(refusals: u64, max_refusals: u64) -> bool
    clauses [ensures result == (refusals < max_refusals)]
    {
        refusals < max_refusals
    }
}

/// Normalized `abrew` / `brew` subcommand class.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbrewSubcommand {
    On,
    Off,
    Status,
    InstallNativeBottleOrCask,
    BundleNativeBrewfile,
    BundleLegacyStatusOrRemove,
    UnsupportedHomebrewOp,
}

/// Evaluation verdict for an `abrew` / `brew` invocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbrewEvalVerdict {
    Allowed { epoch: u64, compat_enabled: bool },
    RefusedRealBypassAttempt { refusals: u64, epoch: u64 },
    RefusedCompatDisabled { refusals: u64, epoch: u64 },
    RefusedUnsupportedOperation { refusals: u64, epoch: u64 },
}

/// Policy fence for `atpkg-abrew` invocations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AbrewRerouteRefusalFence {
    compat_enabled: bool,
    refusals: u64,
    max_refusals: u64,
    epoch: u64,
}

impl AbrewRerouteRefusalFence {
    #[must_use]
    pub const fn new(compat_enabled: bool, max_refusals: u64) -> Self {
        let cap = if max_refusals == 0 {
            1024
        } else {
            max_refusals
        };
        Self {
            compat_enabled,
            refusals: 0,
            max_refusals: cap,
            epoch: 0,
        }
    }

    fn bump_refusal(&mut self) {
        if abrew_refusals_below_cap_b111(self.refusals, self.max_refusals) {
            let cand = self.refusals.saturating_add(1);
            self.refusals = abrew_refusal_clamp_b111(cand, self.max_refusals);
        }
    }

    /// Evaluate `cmd` given bypass indicators (`flag_real`, `flag_no_reroute`, `env_abrew_real`).
    pub fn evaluate(
        &mut self,
        cmd: AbrewSubcommand,
        flag_real: bool,
        flag_no_reroute: bool,
        env_abrew_real: bool,
    ) -> AbrewEvalVerdict {
        let next_ep = self.epoch.saturating_add(1);
        self.epoch = abrew_epoch_advance_b111(self.epoch, next_ep);

        if flag_real || flag_no_reroute || env_abrew_real {
            self.bump_refusal();
            return AbrewEvalVerdict::RefusedRealBypassAttempt {
                refusals: self.refusals,
                epoch: self.epoch,
            };
        }
        match cmd {
            AbrewSubcommand::On => {
                self.compat_enabled = true;
                AbrewEvalVerdict::Allowed {
                    epoch: self.epoch,
                    compat_enabled: true,
                }
            }
            AbrewSubcommand::Status => AbrewEvalVerdict::Allowed {
                epoch: self.epoch,
                compat_enabled: self.compat_enabled,
            },
            AbrewSubcommand::Off => {
                if !self.compat_enabled {
                    self.bump_refusal();
                    return AbrewEvalVerdict::RefusedCompatDisabled {
                        refusals: self.refusals,
                        epoch: self.epoch,
                    };
                }
                self.compat_enabled = false;
                AbrewEvalVerdict::Allowed {
                    epoch: self.epoch,
                    compat_enabled: false,
                }
            }
            AbrewSubcommand::UnsupportedHomebrewOp => {
                self.bump_refusal();
                AbrewEvalVerdict::RefusedUnsupportedOperation {
                    refusals: self.refusals,
                    epoch: self.epoch,
                }
            }
            AbrewSubcommand::InstallNativeBottleOrCask
            | AbrewSubcommand::BundleNativeBrewfile
            | AbrewSubcommand::BundleLegacyStatusOrRemove => {
                if !self.compat_enabled {
                    self.bump_refusal();
                    AbrewEvalVerdict::RefusedCompatDisabled {
                        refusals: self.refusals,
                        epoch: self.epoch,
                    }
                } else {
                    AbrewEvalVerdict::Allowed {
                        epoch: self.epoch,
                        compat_enabled: true,
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_real_bypass_and_keeps_on_status_when_disabled() {
        let mut f = AbrewRerouteRefusalFence::new(true, 16);
        assert_eq!(
            f.evaluate(
                AbrewSubcommand::InstallNativeBottleOrCask,
                true,
                false,
                false
            ),
            AbrewEvalVerdict::RefusedRealBypassAttempt {
                refusals: 1,
                epoch: 1,
            }
        );
        assert_eq!(
            f.evaluate(AbrewSubcommand::Off, false, false, false),
            AbrewEvalVerdict::Allowed {
                epoch: 2,
                compat_enabled: false,
            }
        );
        assert_eq!(
            f.evaluate(
                AbrewSubcommand::InstallNativeBottleOrCask,
                false,
                false,
                false
            ),
            AbrewEvalVerdict::RefusedCompatDisabled {
                refusals: 2,
                epoch: 3,
            }
        );
        assert_eq!(
            f.evaluate(AbrewSubcommand::Status, false, false, false),
            AbrewEvalVerdict::Allowed {
                epoch: 4,
                compat_enabled: false,
            }
        );
    }
}
