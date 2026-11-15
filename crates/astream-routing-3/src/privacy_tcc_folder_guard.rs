// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! macOS TCC modal-dialog hazard classifier (`Astream.Host.TlaPrivacyTccFolderGuard`).
//!
//! Enforces `aterm`'s macOS privacy-dialog prevention rule:
//! - Risk `0`: workspace / ordinary directories (never raises a TCC prompt).
//! - Risk `1`: `Documents`, `Desktop`, `Downloads`, `/Volumes/*` (prevented ONLY when
//!   `aterm` holds Full Disk Access; blocks on an OS dialog without FDA).
//! - Risk `2`: another app's container (`Library/Containers`, `Library/Group Containers`),
//!   cloud-synced `Library/Mobile Documents`, `Music`, or `Photos` library (can raise
//!   an OS modal dialog EVEN WITH Full Disk Access unless explicitly requested).

#[cfg(clean_islands)]
#[path = "privacy_tcc_folder_guard_island.rs"]
mod privacy_tcc_folder_guard_island;
#[cfg(clean_islands)]
pub use privacy_tcc_folder_guard_island::{tcc_audit_epoch_advance, tcc_refusals_clamp};

/// Hard upper bound on counted TCC guard refusals.
pub const MAX_TCC_REFUSALS: u64 = 4_096;

#[cfg(not(clean_islands))]
/// Monotonically advance the TCC path-audit epoch.
#[must_use]
pub const fn tcc_audit_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

#[cfg(not(clean_islands))]
/// Clamp TCC refusal counter to `max_refusals`.
#[must_use]
pub const fn tcc_refusals_clamp(cand_refusals: u64, max_refusals: u64) -> u64 {
    if cand_refusals < max_refusals {
        cand_refusals
    } else {
        max_refusals
    }
}

contract_fn! {
    /// True iff `risk_level <= max_allowed_risk`.
    #[must_use]
    pub const fn tcc_risk_permitted(risk_level: u64, max_allowed_risk: u64) -> bool
    clauses [ensures result == (risk_level <= max_allowed_risk)]
    {
        risk_level <= max_allowed_risk
    }
}

/// Classification of macOS TCC dialog risk for a candidate path.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TccPathClass {
    /// Ordinary path (`risk = 0`).
    Unrestricted,
    /// `Documents` / `Desktop` / `Downloads` / `/Volumes/*` (`risk = 1`, safe only under FDA).
    FdaProtectedFolder,
    /// App container / cloud sync / Music / Photos (`risk = 2`, prompts even with FDA).
    AppDataOrLibraryDialog,
}

impl TccPathClass {
    #[must_use]
    pub const fn risk_level(self) -> u64 {
        match self {
            Self::Unrestricted => 0,
            Self::FdaProtectedFolder => 1,
            Self::AppDataOrLibraryDialog => 2,
        }
    }
}

fn contains_subslice(haystack: &[u8], needle: &[u8]) -> bool {
    if needle.is_empty() {
        return true;
    }
    let mut scan = haystack;
    while scan.len() >= needle.len() {
        if scan.starts_with(needle) {
            return true;
        }
        let &[_, ref tail @ ..] = scan else {
            break;
        };
        scan = tail;
    }
    false
}

fn matches_dir_segment(path: &[u8], seg_slash: &[u8], seg_end: &[u8]) -> bool {
    contains_subslice(path, seg_slash) || path.ends_with(seg_end)
}

/// Classify `path` for unsolicited macOS TCC modal-dialog hazard.
#[must_use]
pub fn classify_macos_tcc_path(path: &[u8]) -> TccPathClass {
    if matches_dir_segment(path, b"/Library/Containers/", b"/Library/Containers")
        || matches_dir_segment(
            path,
            b"/Library/Group Containers/",
            b"/Library/Group Containers",
        )
        || matches_dir_segment(
            path,
            b"/Library/Mobile Documents/",
            b"/Library/Mobile Documents",
        )
        || matches_dir_segment(path, b"/Music/", b"/Music")
        || contains_subslice(path, b".photoslibrary")
    {
        return TccPathClass::AppDataOrLibraryDialog;
    }
    if path.starts_with(b"/Volumes/")
        || path == b"/Volumes"
        || matches_dir_segment(path, b"/Documents/", b"/Documents")
        || matches_dir_segment(path, b"/Desktop/", b"/Desktop")
        || matches_dir_segment(path, b"/Downloads/", b"/Downloads")
    {
        return TccPathClass::FdaProtectedFolder;
    }
    TccPathClass::Unrestricted
}

/// Stateful pre-open TCC hazard guard for background agent scans.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PrivacyTccFolderGuard {
    has_full_disk_access: bool,
    audit_epoch: u64,
    refusals: u64,
}

impl PrivacyTccFolderGuard {
    #[must_use]
    pub const fn new(has_full_disk_access: bool) -> Self {
        Self {
            has_full_disk_access,
            audit_epoch: 0,
            refusals: 0,
        }
    }

    #[must_use]
    pub const fn audit_epoch(&self) -> u64 {
        self.audit_epoch
    }

    #[must_use]
    pub const fn refusals(&self) -> u64 {
        self.refusals
    }

    /// Check an unsolicited background path probe against FDA status.
    pub fn check_background_probe(&mut self, path: &[u8]) -> Result<TccPathClass, TccPathClass> {
        let cand_ep = self.audit_epoch.saturating_add(1);
        self.audit_epoch = tcc_audit_epoch_advance(self.audit_epoch, cand_ep);

        let cls = classify_macos_tcc_path(path);
        let max_allowed = if self.has_full_disk_access { 1 } else { 0 };
        if tcc_risk_permitted(cls.risk_level(), max_allowed) {
            Ok(cls)
        } else {
            let cand_ref = self.refusals.saturating_add(1);
            self.refusals = tcc_refusals_clamp(cand_ref, MAX_TCC_REFUSALS);
            Err(cls)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_fda_distinction_between_three_folders_and_app_containers() {
        let mut no_fda = PrivacyTccFolderGuard::new(false);
        assert_eq!(
            no_fda.check_background_probe(b"/fixture-home/astream/src/lib.rs"),
            Ok(TccPathClass::Unrestricted)
        );
        assert_eq!(
            no_fda.check_background_probe(b"/fixture-home/Downloads/foo.tar.gz"),
            Err(TccPathClass::FdaProtectedFolder)
        );

        let mut with_fda = PrivacyTccFolderGuard::new(true);
        // FDA covers Downloads & /Volumes
        assert_eq!(
            with_fda.check_background_probe(b"/fixture-home/Downloads/foo.tar.gz"),
            Ok(TccPathClass::FdaProtectedFolder)
        );
        assert_eq!(
            with_fda.check_background_probe(b"/Volumes/Scratch/build"),
            Ok(TccPathClass::FdaProtectedFolder)
        );
        // FDA does NOT prevent dialogs on other apps' containers or Music/Photos!
        assert_eq!(
            with_fda
                .check_background_probe(b"/fixture-home/Library/Containers/com.apple.mail/Data"),
            Err(TccPathClass::AppDataOrLibraryDialog)
        );
        assert_eq!(with_fda.refusals(), 1);
    }
}
