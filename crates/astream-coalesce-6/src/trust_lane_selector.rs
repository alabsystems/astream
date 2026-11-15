// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Trust toolchain lane selector & stale-link `aterm pkg repair` router
//! (`Astream.Host.TlaTrustLaneSelector`).
//!
//! Enforces the `aterm` Rust/Trust toolchain rules (`aterm help rust`):
//! - Wherever `$ATPKG_BIN` is set and Trust has a build for the host/target, `targo` is the
//!   default toolchain: `targo --unverified <cmd>` builds without proof claims,
//!   `targo trust <cmd>` formally verifies, and bare `targo <cmd>` is refused until a lane
//!   is named (`bare_allowed == 0`).
//! - When `aterm help rust` or `aterm pkg which targo` reports `unavailable on <target>` (or
//!   `$ATPKG_BIN` is unset), stock `cargo` is selected cleanly.
//! - When stderr reports `'rustc' is not installed for the custom toolchain 'trust'`, routes
//!   to bounded `aterm pkg repair` remediation (`repair_attempts <= max_repairs`).

#![allow(
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
#[path = "trust_lane_selector_island.rs"]
mod trust_lane_selector_island;
#[cfg(clean_islands)]
pub use trust_lane_selector_island::{trust_repair_clamp, trust_zero_bare};

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn trust_repair_clamp(attempts: u64, max_repairs: u64) -> u64 {
    if attempts < max_repairs {
        attempts
    } else {
        max_repairs
    }
}

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn trust_zero_bare(_flag: u64) -> u64 {
    0
}

contract_fn! {
    /// Verified check that bounded `aterm pkg repair` budget remains (`attempts < max_repairs`),
    /// linked via `clean-kernel-defeq` to `trust_repair_budget_remains_isl`.
    #[must_use]
    pub const fn trust_repair_budget_remains(attempts: u64, max_repairs: u64) -> bool
    clauses [ensures result == (attempts < max_repairs)]
    {
        attempts < max_repairs
    }
}

/// Requested compilation/verification intent for a Rust workspace command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TargoLaneIntent {
    /// Formal verification lane (`targo trust <cmd>`).
    TrustVerify,
    /// Unverified build/test lane (`targo --unverified <cmd>`).
    UnverifiedBuild,
    /// Caller omitted lane (`targo build` / `targo test`) — must be refused on `targo`.
    BareUnspecified,
}

/// Selected toolchain invocation or refusal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ToolchainSelection {
    /// Invoke `targo trust <subcommand>`.
    TargoTrust {
        /// Cargo/targo subcommand (`check`, `build`, `test`).
        subcommand: String,
    },
    /// Invoke `targo --unverified <subcommand>`.
    TargoUnverified {
        /// Cargo/targo subcommand (`build`, `test`, `clippy`, `doc`).
        subcommand: String,
    },
    /// Fall back to stock `cargo <subcommand>` because Trust has no build for `<target>`
    /// or `$ATPKG_BIN` is unset.
    StockCargoFallback {
        /// Cargo subcommand.
        subcommand: String,
    },
    /// Refuse bare `targo <subcommand>` until `trust` or `--unverified` is named.
    RefuseBareTargo {
        /// Subcommand that lacked an explicit lane.
        subcommand: String,
    },
}

/// Diagnosis of toolchain stderr for stale custom-toolchain links.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ToolchainRepairAction {
    /// Stderr is not a stale `'trust'` toolchain link error.
    NotStaleToolchainLink,
    /// Run `aterm pkg repair` once and retry (`attempt <= max_repairs`).
    RunAtermPkgRepair {
        /// 1-based repair attempt number.
        attempt: u64,
    },
    /// Stale link persisted past `max_repairs`; escalate instead of looping.
    RepairBudgetExhausted,
}

/// Stateful Trust toolchain lane selector and repair budget tracker.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustLaneSelector {
    atpkg_bin_present: bool,
    trust_target_available: bool,
    bare_allowed: u64,
    repair_attempts: u64,
    max_repairs: u64,
}

impl TrustLaneSelector {
    /// Create a selector for the measured environment (`$ATPKG_BIN` presence, target support,
    /// and bounded `aterm pkg repair` attempts).
    #[must_use]
    pub const fn new(
        atpkg_bin_present: bool,
        trust_target_available: bool,
        max_repairs: u64,
    ) -> Self {
        Self {
            atpkg_bin_present,
            trust_target_available,
            bare_allowed: 0,
            repair_attempts: 0,
            max_repairs,
        }
    }

    /// Parse `aterm pkg which targo` / `aterm help rust` probe output to detect
    /// `unavailable on <target>`.
    #[must_use]
    pub fn probe_says_target_available(probe_output: &str) -> bool {
        !contains_bytes(probe_output.as_bytes(), b"unavailable on ")
    }

    /// Count of permitted bare `targo` invocations (invariant: always `0`).
    #[must_use]
    pub const fn bare_allowed(&self) -> u64 {
        self.bare_allowed
    }

    /// Clamped count of `aterm pkg repair` runs (`<= max_repairs`).
    #[must_use]
    pub const fn repair_attempts(&self) -> u64 {
        self.repair_attempts
    }

    /// Select the concrete toolchain command for `(intent, subcommand)`.
    pub fn select(&mut self, intent: TargoLaneIntent, subcommand: &str) -> ToolchainSelection {
        self.bare_allowed = trust_zero_bare(self.repair_attempts);
        if !self.atpkg_bin_present || !self.trust_target_available {
            return ToolchainSelection::StockCargoFallback {
                subcommand: copy_str(subcommand),
            };
        }
        match intent {
            TargoLaneIntent::TrustVerify => ToolchainSelection::TargoTrust {
                subcommand: copy_str(subcommand),
            },
            TargoLaneIntent::UnverifiedBuild => ToolchainSelection::TargoUnverified {
                subcommand: copy_str(subcommand),
            },
            TargoLaneIntent::BareUnspecified => ToolchainSelection::RefuseBareTargo {
                subcommand: copy_str(subcommand),
            },
        }
    }

    /// Inspect `stderr` for `'rustc' is not installed for the custom toolchain 'trust'`
    /// and decide whether to run `aterm pkg repair`.
    pub fn diagnose_stderr(&mut self, stderr: &str) -> ToolchainRepairAction {
        let sb = stderr.as_bytes();
        let stale_link =
            contains_bytes(
                sb,
                b"'rustc' is not installed for the custom toolchain 'trust'",
            ) || contains_bytes(sb, b"is not installed for the custom toolchain 'trust'");
        if !stale_link {
            return ToolchainRepairAction::NotStaleToolchainLink;
        }
        if trust_repair_budget_remains(self.repair_attempts, self.max_repairs) {
            let raw_next = self.repair_attempts.saturating_add(1);
            self.bare_allowed = trust_zero_bare(raw_next);
            self.repair_attempts = trust_repair_clamp(raw_next, self.max_repairs);
            ToolchainRepairAction::RunAtermPkgRepair {
                attempt: self.repair_attempts,
            }
        } else {
            self.bare_allowed = trust_zero_bare(self.repair_attempts);
            self.repair_attempts = trust_repair_clamp(self.repair_attempts, self.max_repairs);
            ToolchainRepairAction::RepairBudgetExhausted
        }
    }
}

fn copy_str(src: &str) -> String {
    let mut out = String::new();
    out.push_str(src);
    out
}

fn contains_bytes(haystack: &[u8], needle: &[u8]) -> bool {
    if needle.is_empty() {
        return true;
    }
    if haystack.len() < needle.len() {
        return false;
    }
    let limit = haystack.len().saturating_sub(needle.len());
    let mut i = 0usize;
    while i <= limit {
        let end = i.saturating_add(needle.len());
        if let Some(sub) = haystack.get(i..end) {
            if sub == needle {
                return true;
            }
        }
        i = i.saturating_add(1);
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_bare_targo_falls_back_when_unavailable_and_bounds_pkg_repair() {
        let mut sel = TrustLaneSelector::new(true, true, 2);
        assert_eq!(
            sel.select(TargoLaneIntent::BareUnspecified, "build"),
            ToolchainSelection::RefuseBareTargo {
                subcommand: "build".to_string()
            }
        );
        assert_eq!(
            sel.select(TargoLaneIntent::TrustVerify, "check"),
            ToolchainSelection::TargoTrust {
                subcommand: "check".to_string()
            }
        );
        assert_eq!(sel.bare_allowed(), 0);

        // Stale link triggers `aterm pkg repair` up to max_repairs = 2, then exhausts cleanly.
        let err_msg = "error: 'rustc' is not installed for the custom toolchain 'trust'";
        assert_eq!(
            sel.diagnose_stderr(err_msg),
            ToolchainRepairAction::RunAtermPkgRepair { attempt: 1 }
        );
        assert_eq!(
            sel.diagnose_stderr(err_msg),
            ToolchainRepairAction::RunAtermPkgRepair { attempt: 2 }
        );
        assert_eq!(
            sel.diagnose_stderr(err_msg),
            ToolchainRepairAction::RepairBudgetExhausted
        );

        // Target unavailable -> stock cargo fallback!
        let avail = TrustLaneSelector::probe_says_target_available(
            "targo: unavailable on x86_64-pc-windows-msvc",
        );
        assert!(!avail);
        let mut cross = TrustLaneSelector::new(true, avail, 1);
        assert_eq!(
            cross.select(TargoLaneIntent::UnverifiedBuild, "check"),
            ToolchainSelection::StockCargoFallback {
                subcommand: "check".to_string()
            }
        );
    }
}
