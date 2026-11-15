// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `SIGHUP` revocation-file atomic reload & live principal subscription/will eviction guard
//! (`evidence/manifest.toml` `os.cordon` & `cap.expiry-enforced`;
//! `Astream.Cap.TlaSighupRevocationReloadGenerationGuard`).
//!
//! Enforces fail-closed `SIGHUP` revocation reloading (`Broker::load_revocation_file`,
//! `asb serve --revocation-file`):
//! - `sighup_generation` is incremented monotonically by the signal handler,
//! - When `signal_gen > applied_gen`, the broker parses and validates the new revocation file:
//!   * On valid parse (`reload_valid == true`, `entry_count <= MAX_REVOKED_PRINCIPALS`), swaps
//!     in the new table, advances `applied_gen`, and sweeps open subscriptions & pending wills,
//!   * On I/O or syntax error (`reload_valid == false`), RETAINS the active revocation set
//!     untouched so a torn or mistyped edit NEVER clears active revocations!

#[cfg(clean_islands)]
#[path = "sighup_revocation_reload_generation_guard_island.rs"]
mod sighup_revocation_reload_generation_guard_island;
#[cfg(clean_islands)]
pub use sighup_revocation_reload_generation_guard_island::{
    revocation_entries_clamp_b151, sighup_applied_gen_advance_b151,
};

/// Upper bound on tracked revoked principals per revocation list (`65_536`).
pub const MAX_REVOKED_PRINCIPALS: u64 = 65_536;

#[cfg(not(clean_islands))]
/// Clamp revocation list entry count to `MAX_REVOKED_PRINCIPALS`.
#[must_use]
pub const fn revocation_entries_clamp_b151(cand_entries: u64, max_entries: u64) -> u64 {
    if cand_entries < max_entries {
        cand_entries
    } else {
        max_entries
    }
}

#[cfg(not(clean_islands))]
/// Advance applied `SIGHUP` generation monotonically.
#[must_use]
pub const fn sighup_applied_gen_advance_b151(cur_gen: u64, cand_gen: u64) -> u64 {
    if cur_gen < cand_gen {
        cand_gen
    } else {
        cur_gen
    }
}

contract_fn! {
    /// True iff `signal_gen > applied_gen` (a new `SIGHUP` requires reloading the revocation file).
    #[must_use]
    pub const fn sighup_reload_due_b151(applied_gen: u64, signal_gen: u64) -> bool
    clauses [ensures result == (applied_gen < signal_gen)]
    {
        applied_gen < signal_gen
    }
}

/// Outcome of polling `sighup_generation` and reloading `--revocation-file`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SighupReloadDecision {
    UpToDateNoReload {
        applied_gen: u64,
        active_revoked_count: u64,
    },
    ReloadedAndSweepLivePrincipals {
        applied_gen: u64,
        active_revoked_count: u64,
    },
    FailedReloadRetainedActiveTable {
        failed_signal_gen: u64,
        retained_revoked_count: u64,
    },
}

/// Fail-closed `SIGHUP` revocation reload coordinator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SighupRevocationReloadGuard {
    applied_gen: u64,
    active_revoked_count: u64,
}

impl SighupRevocationReloadGuard {
    #[must_use]
    pub const fn new(initial_revoked_count: u64) -> Self {
        Self {
            applied_gen: 0,
            active_revoked_count: revocation_entries_clamp_b151(
                initial_revoked_count,
                MAX_REVOKED_PRINCIPALS,
            ),
        }
    }

    /// Reconcile `signal_gen` against `applied_gen` with the result of parsing `--revocation-file`.
    pub fn poll_and_apply_reload(
        &mut self,
        signal_gen: u64,
        parsed_revoked_count: Option<u64>,
    ) -> SighupReloadDecision {
        if !sighup_reload_due_b151(self.applied_gen, signal_gen) {
            return SighupReloadDecision::UpToDateNoReload {
                applied_gen: self.applied_gen,
                active_revoked_count: self.active_revoked_count,
            };
        }
        self.applied_gen = sighup_applied_gen_advance_b151(self.applied_gen, signal_gen);
        match parsed_revoked_count {
            Some(cnt) if cnt <= MAX_REVOKED_PRINCIPALS => {
                self.active_revoked_count =
                    revocation_entries_clamp_b151(cnt, MAX_REVOKED_PRINCIPALS);
                SighupReloadDecision::ReloadedAndSweepLivePrincipals {
                    applied_gen: self.applied_gen,
                    active_revoked_count: self.active_revoked_count,
                }
            }
            _ => SighupReloadDecision::FailedReloadRetainedActiveTable {
                failed_signal_gen: self.applied_gen,
                retained_revoked_count: self.active_revoked_count,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reloads_and_sweeps_on_sighup_while_retaining_active_revocations_on_failed_parse() {
        let mut g = SighupRevocationReloadGuard::new(3);
        assert_eq!(
            g.poll_and_apply_reload(0, None),
            SighupReloadDecision::UpToDateNoReload {
                applied_gen: 0,
                active_revoked_count: 3,
            }
        );
        // SIGHUP #1 with broken syntax -> keeps all 3 active revocations!
        assert_eq!(
            g.poll_and_apply_reload(1, None),
            SighupReloadDecision::FailedReloadRetainedActiveTable {
                failed_signal_gen: 1,
                retained_revoked_count: 3,
            }
        );
        // SIGHUP #2 with valid 5-entry revocation list -> swaps and sweeps live principals!
        assert_eq!(
            g.poll_and_apply_reload(2, Some(5)),
            SighupReloadDecision::ReloadedAndSweepLivePrincipals {
                applied_gen: 2,
                active_revoked_count: 5,
            }
        );
    }
}
