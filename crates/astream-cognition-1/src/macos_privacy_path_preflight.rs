// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! macOS TCC privacy-dialog preflight classifier (`Astream.Host.TlaMacosPrivacyPathPreflight`).
//!
//! Prevents unexpected blocking macOS TCC modal prompts (`aterm ctl privacy`):
//! - `WorkspaceOrSystemSafe` paths are always permitted.
//! - `ThreeFoldersOrVolume` (`~/Documents`, `~/Desktop`, `~/Downloads`, `/Volumes/*`) are permitted
//!   without a modal ONLY when `aterm_has_full_disk_access == true`.
//! - `SyncedOrOtherAppContainer` (`defaults` domains, `~/Library/Containers/*`, Music/Photos, iCloud)
//!   can raise a blocking modal EVEN WITH Full Disk Access, and are refused unless explicitly requested.

#[cfg(clean_islands)]
#[path = "macos_privacy_path_preflight_island.rs"]
mod macos_privacy_path_preflight_island;
#[cfg(clean_islands)]
pub use macos_privacy_path_preflight_island::{
    tcc_blocked_clamp_b109, tcc_preflight_epoch_advance_b109,
};

#[cfg(not(clean_islands))]
/// Clamp blocked TCC modal-hazard probe count to `max_blocked`.
#[must_use]
pub const fn tcc_blocked_clamp_b109(cand_blocked: u64, max_blocked: u64) -> u64 {
    if cand_blocked < max_blocked {
        cand_blocked
    } else {
        max_blocked
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the TCC preflight check epoch.
#[must_use]
pub const fn tcc_preflight_epoch_advance_b109(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `blocked_count` remains below the audit saturation cap `max_blocked`.
    #[must_use]
    pub const fn tcc_audit_below_cap_b109(blocked_count: u64, max_blocked: u64) -> bool
    clauses [ensures result == (blocked_count < max_blocked)]
    {
        blocked_count < max_blocked
    }
}

/// macOS TCC sensitivity tier of a target path or `defaults` domain.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MacosPathTier {
    WorkspaceOrSystemSafe,
    ThreeFoldersOrExternalVolume,
    SyncedFolderOrOtherAppData,
}

/// Preflight verdict before touching the filesystem or `defaults`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TccPreflightVerdict {
    PermittedNoModal { epoch: u64 },
    BlockedNeedsFullDiskAccess { epoch: u64 },
    BlockedModalHazardEvenWithFda { epoch: u64 },
}

/// macOS TCC modal-avoidance preflight gate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MacosPrivacyPathPreflight {
    aterm_has_fda: bool,
    blocked_count: u64,
    max_blocked_cap: u64,
    epoch: u64,
}

impl MacosPrivacyPathPreflight {
    #[must_use]
    pub const fn new(aterm_has_fda: bool, max_blocked_cap: u64) -> Self {
        let cap = if max_blocked_cap == 0 {
            1024
        } else {
            max_blocked_cap
        };
        Self {
            aterm_has_fda,
            blocked_count: 0,
            max_blocked_cap: cap,
            epoch: 0,
        }
    }

    #[must_use]
    pub const fn blocked_count(&self) -> u64 {
        self.blocked_count
    }

    /// Check whether probing `tier` (`explicit_operator_request == true` only when the person
    /// explicitly asked to inspect that exact path) can proceed without an unrequested TCC modal.
    pub fn check_probe(
        &mut self,
        tier: MacosPathTier,
        explicit_operator_request: bool,
    ) -> TccPreflightVerdict {
        let next_ep = self.epoch.saturating_add(1);
        self.epoch = tcc_preflight_epoch_advance_b109(self.epoch, next_ep);
        match tier {
            MacosPathTier::WorkspaceOrSystemSafe => {
                TccPreflightVerdict::PermittedNoModal { epoch: self.epoch }
            }
            MacosPathTier::ThreeFoldersOrExternalVolume => {
                if self.aterm_has_fda || explicit_operator_request {
                    TccPreflightVerdict::PermittedNoModal { epoch: self.epoch }
                } else {
                    if tcc_audit_below_cap_b109(self.blocked_count, self.max_blocked_cap) {
                        let cand = self.blocked_count.saturating_add(1);
                        self.blocked_count = tcc_blocked_clamp_b109(cand, self.max_blocked_cap);
                    }
                    TccPreflightVerdict::BlockedNeedsFullDiskAccess { epoch: self.epoch }
                }
            }
            MacosPathTier::SyncedFolderOrOtherAppData => {
                if explicit_operator_request {
                    TccPreflightVerdict::PermittedNoModal { epoch: self.epoch }
                } else {
                    if tcc_audit_below_cap_b109(self.blocked_count, self.max_blocked_cap) {
                        let cand = self.blocked_count.saturating_add(1);
                        self.blocked_count = tcc_blocked_clamp_b109(cand, self.max_blocked_cap);
                    }
                    TccPreflightVerdict::BlockedModalHazardEvenWithFda { epoch: self.epoch }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fda_permits_three_folders_but_still_blocks_unrequested_other_app_containers() {
        let mut gate = MacosPrivacyPathPreflight::new(true, 16);
        assert_eq!(
            gate.check_probe(MacosPathTier::ThreeFoldersOrExternalVolume, false),
            TccPreflightVerdict::PermittedNoModal { epoch: 1 }
        );
        assert_eq!(
            gate.check_probe(MacosPathTier::SyncedFolderOrOtherAppData, false),
            TccPreflightVerdict::BlockedModalHazardEvenWithFda { epoch: 2 }
        );
        assert_eq!(gate.blocked_count(), 1);
    }
}
