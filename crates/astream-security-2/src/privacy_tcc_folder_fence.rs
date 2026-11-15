// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! macOS TCC privacy dialog prevention fence (`aterm ctl privacy`;
//! `Astream.Host.TlaPrivacyTccFolderFence`).
//!
//! Models the exact macOS TCC consent surface documented in the `aterm` primer:
//! - Workspace paths are always safe,
//! - `~/Documents`, `~/Desktop`, `~/Downloads`, and `/Volumes/*` raise a blocking TCC dialog UNLESS
//!   `aterm` has Full Disk Access (`fda_granted == 1`),
//! - Other apps' containers (`~/Library/Containers/*`), `defaults` domains, Music/Photos libraries,
//!   and cloud-synced folders (`~/Library/CloudStorage/*`) CAN STILL raise blocking TCC dialogs even
//!   WITH Full Disk Access unless the operator explicitly requested that look!

#[cfg(clean_islands)]
#[path = "privacy_tcc_folder_fence_island.rs"]
mod privacy_tcc_folder_fence_island;
#[cfg(clean_islands)]
pub use privacy_tcc_folder_fence_island::{tcc_denials_advance_b123, tcc_path_len_clamp_b123};

#[cfg(not(clean_islands))]
/// Clamp inspected path length to `max_len`.
#[must_use]
pub const fn tcc_path_len_clamp_b123(cand_len: u64, max_len: u64) -> u64 {
    if cand_len < max_len {
        cand_len
    } else {
        max_len
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance blocked TCC dialog counter.
#[must_use]
pub const fn tcc_denials_advance_b123(cur_denials: u64, cand_denials: u64) -> u64 {
    if cur_denials < cand_denials {
        cand_denials
    } else {
        cur_denials
    }
}

contract_fn! {
    /// True iff Full Disk Access is granted (`fda_granted == 1`).
    #[must_use]
    pub const fn tcc_fda_covers_surface_b123(fda_granted: u64) -> bool
    clauses [ensures result == (fda_granted == 1)]
    {
        fda_granted == 1
    }
}

pub const MAX_TCC_INSPECTED_PATH_BYTES: u64 = 4096;

/// Classification of a macOS filesystem or preference target relative to TCC consent dialogs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TccSurfaceKind {
    WorkspaceSafe,
    FdaCoveredFolderOrVolume,
    AppContainerOrDefaultsOrMediaOrCloud,
}

/// Gate verdict before touching a path or `defaults` domain on macOS.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TccFenceDecision {
    Admit,
    BlockedWouldPromptPerson {
        surface: TccSurfaceKind,
        blocked_count: u64,
    },
}

/// Stateful macOS TCC dialog prevention fence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PrivacyTccFolderFence {
    fda_granted: u64,
    checked_path_len: u64,
    blocked_dialogs: u64,
}

impl PrivacyTccFolderFence {
    #[must_use]
    pub const fn new(full_disk_access_granted: bool) -> Self {
        Self {
            fda_granted: if full_disk_access_granted { 1 } else { 0 },
            checked_path_len: 0,
            blocked_dialogs: 0,
        }
    }

    #[must_use]
    pub const fn blocked_dialogs(&self) -> u64 {
        self.blocked_dialogs
    }

    /// Evaluate whether accessing `surface` (with `path_len_bytes`) is safe without raising an
    /// unsolicited TCC dialog on the operator's screen.
    pub fn evaluate_access(
        &mut self,
        surface: TccSurfaceKind,
        path_len_bytes: u64,
        operator_explicitly_requested: bool,
    ) -> TccFenceDecision {
        self.checked_path_len =
            tcc_path_len_clamp_b123(path_len_bytes, MAX_TCC_INSPECTED_PATH_BYTES);
        match surface {
            TccSurfaceKind::WorkspaceSafe => TccFenceDecision::Admit,
            TccSurfaceKind::FdaCoveredFolderOrVolume => {
                if tcc_fda_covers_surface_b123(self.fda_granted) || operator_explicitly_requested {
                    TccFenceDecision::Admit
                } else {
                    self.blocked_dialogs = tcc_denials_advance_b123(
                        self.blocked_dialogs,
                        self.blocked_dialogs.saturating_add(1),
                    );
                    TccFenceDecision::BlockedWouldPromptPerson {
                        surface,
                        blocked_count: self.blocked_dialogs,
                    }
                }
            }
            TccSurfaceKind::AppContainerOrDefaultsOrMediaOrCloud => {
                // Full Disk Access does NOT prevent TCC dialogs on other apps' containers,
                // `defaults` domains, Music/Photos, or cloud-synced folders!
                if operator_explicitly_requested {
                    TccFenceDecision::Admit
                } else {
                    self.blocked_dialogs = tcc_denials_advance_b123(
                        self.blocked_dialogs,
                        self.blocked_dialogs.saturating_add(1),
                    );
                    TccFenceDecision::BlockedWouldPromptPerson {
                        surface,
                        blocked_count: self.blocked_dialogs,
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
    fn fda_covers_three_folders_and_volumes_but_not_containers_or_cloud() {
        let mut with_fda = PrivacyTccFolderFence::new(true);
        assert_eq!(
            with_fda.evaluate_access(TccSurfaceKind::FdaCoveredFolderOrVolume, 32, false),
            TccFenceDecision::Admit
        );
        // Even WITH FDA, unsolicited look into another app's container or Music/Cloud is blocked!
        assert_eq!(
            with_fda.evaluate_access(
                TccSurfaceKind::AppContainerOrDefaultsOrMediaOrCloud,
                64,
                false
            ),
            TccFenceDecision::BlockedWouldPromptPerson {
                surface: TccSurfaceKind::AppContainerOrDefaultsOrMediaOrCloud,
                blocked_count: 1
            }
        );

        let mut without_fda = PrivacyTccFolderFence::new(false);
        assert_eq!(
            without_fda.evaluate_access(TccSurfaceKind::FdaCoveredFolderOrVolume, 32, false),
            TccFenceDecision::BlockedWouldPromptPerson {
                surface: TccSurfaceKind::FdaCoveredFolderOrVolume,
                blocked_count: 1
            }
        );
    }
}
