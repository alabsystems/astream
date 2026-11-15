// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pre-flight macOS TCC privacy-consent surface classifier
//! (`Astream.Cap.TlaPrivacyConsentGate`; `aterm ctl privacy`).
//!
//! On macOS, an unprompted `open` / `readdir` into TCC-protected paths puts a modal consent
//! dialog on the person's screen and blocks the calling process until answered:
//! - **Full Disk Access (`FullDiskAccess::Granted`)** prevents that dialog **only** for the
//!   three desktop folders (`~/Documents`, `~/Desktop`, `~/Downloads`) and external/removable
//!   `/Volumes/...` (`TccSurface::ThreeFoldersOrVolume`, `surface_class = 1`).
//! - Cloud-synced folders (`~/Library/CloudStorage/...`, iCloud `Mobile Documents`), other
//!   apps' containers (`~/Library/Containers/...`, `~/Library/Group Containers/...`), the
//!   Music/Photos libraries, and cross-app `defaults` domains (`surface_class = 2`) **still**
//!   risk a blocking TCC dialog even when `aterm` holds Full Disk Access!

#[cfg(clean_islands)]
#[path = "macos_tcc_preflight_island.rs"]
mod macos_tcc_preflight_island;
#[cfg(clean_islands)]
pub use macos_tcc_preflight_island::{
    tcc_class0_select, tcc_class_ge2_select, tcc_fda_folder_risk, tcc_grant_epoch_advance,
};

/// Mirror of Clean's `tcc_fda_folder_risk` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn tcc_fda_folder_risk(fda_granted: u64) -> u64 {
    if fda_granted < 1 {
        1
    } else {
        0
    }
}

/// Mirror of Clean's `tcc_class_ge2_select` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn tcc_class_ge2_select(surface_class: u64, class1_risk: u64) -> u64 {
    if surface_class < 2 {
        class1_risk
    } else {
        2
    }
}

/// Mirror of Clean's `tcc_class0_select` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn tcc_class0_select(surface_class: u64, nonzero_risk: u64) -> u64 {
    if surface_class < 1 {
        0
    } else {
        nonzero_risk
    }
}

/// Mirror of Clean's `tcc_grant_epoch_advance` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn tcc_grant_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

/// Compose Clean-origin `tcc_class0_select`, `tcc_class_ge2_select`, and `tcc_fda_folder_risk`
/// (`tcc_risk_code_isl`): returns `0` (safe without dialog), `1` (needs FDA), or `2` (always prompts).
#[must_use]
pub const fn tcc_risk_code(surface_class: u64, fda_granted: u64) -> u64 {
    tcc_class0_select(
        surface_class,
        tcc_class_ge2_select(surface_class, tcc_fda_folder_risk(fda_granted)),
    )
}

contract_fn! {
    /// Kernel-certified check that a TCC evaluation carries zero modal-dialog risk
    /// (`risk_code == 0`), linked via `clean-kernel-defeq` to `tcc_probe_safe_without_dialog_isl`.
    #[must_use]
    pub const fn tcc_probe_safe_without_dialog(risk_code: u64) -> bool
    clauses [ensures result == (risk_code == 0)]
    {
        risk_code == 0
    }
}

/// macOS TCC surface classification for a filesystem path or `defaults` query.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TccSurface {
    /// Ordinary workspace, `/tmp`, `/usr`, or `aterm`'s own Application Support/Caches (`class 0`).
    UnrestrictedWorkspace,
    /// `~/Documents`, `~/Desktop`, `~/Downloads`, or `/Volumes/<vol>` — covered by Full Disk Access (`class 1`).
    ThreeFoldersOrVolume,
    /// Cloud-synced directory, other app's container, Music/Photos library, or `defaults` domain —
    /// NOT covered by Full Disk Access alone (`class 2`).
    PerAppOrCloudProtected,
}

impl TccSurface {
    #[must_use]
    const fn class_code(self) -> u64 {
        match self {
            Self::UnrestrictedWorkspace => 0,
            Self::ThreeFoldersOrVolume => 1,
            Self::PerAppOrCloudProtected => 2,
        }
    }
}

/// Whether `aterm` currently holds macOS Full Disk Access (`aterm ctl privacy`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FullDiskAccess {
    /// Full Disk Access is not granted (`0`).
    NotGranted,
    /// Full Disk Access is granted (`1`).
    Granted,
}

impl FullDiskAccess {
    #[must_use]
    const fn code(self) -> u64 {
        match self {
            Self::NotGranted => 0,
            Self::Granted => 1,
        }
    }
}

/// Pre-flight verdict before touching a path on macOS.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TccPreflightVerdict {
    /// Safe to read/stat without raising a macOS privacy dialog.
    AllowSilent,
    /// Blocked unless the user grants Full Disk Access (`NEEDS YOU: grant Full Disk Access to aterm`).
    NeedsFullDiskAccess { surface: TccSurface },
    /// Blocked even WITH Full Disk Access unless the user explicitly requested this look
    /// and is ready to answer a TCC modal prompt.
    NeedsExplicitPersonConsent { surface: TccSurface },
}

#[must_use]
const fn trim_trailing_slashes(mut bytes: &[u8]) -> &[u8] {
    while let [head @ .., b'/'] = bytes {
        bytes = head;
    }
    bytes
}

#[must_use]
const fn strip_byte_prefix<'a>(mut s: &'a [u8], mut prefix: &[u8]) -> Option<&'a [u8]> {
    while let [pb, p_tail @ ..] = prefix {
        let [sb, s_tail @ ..] = s else {
            return None;
        };
        if *pb != *sb {
            return None;
        }
        prefix = p_tail;
        s = s_tail;
    }
    if prefix.is_empty() {
        Some(s)
    } else {
        None
    }
}

#[must_use]
const fn strip_home_prefix_bytes<'a>(path: &'a [u8], home: &[u8]) -> Option<&'a [u8]> {
    let trimmed_home = trim_trailing_slashes(home);
    let Some(rest) = strip_byte_prefix(path, trimmed_home) else {
        return None;
    };
    if rest.is_empty() {
        Some(&[])
    } else if let [b'/', after @ ..] = rest {
        Some(after)
    } else {
        None
    }
}

#[must_use]
const fn seg_matches_or_prefix_bytes(rel: &[u8], folder: &[u8]) -> bool {
    let Some(after) = strip_byte_prefix(rel, folder) else {
        return false;
    };
    matches!(after, [] | [b'/', ..])
}

/// Classify a normalized POSIX path relative to `home_dir` according to macOS TCC boundaries.
#[must_use]
pub const fn classify_macos_path(path: &str, home_dir: &str) -> TccSurface {
    let pb = path.as_bytes();
    if let Some(rest) = strip_byte_prefix(pb, b"/Volumes/") {
        if !rest.is_empty() {
            return TccSurface::ThreeFoldersOrVolume;
        }
    }
    let Some(rel) = strip_home_prefix_bytes(pb, home_dir.as_bytes()) else {
        return TccSurface::UnrestrictedWorkspace;
    };
    if seg_matches_or_prefix_bytes(rel, b"Documents")
        || seg_matches_or_prefix_bytes(rel, b"Desktop")
        || seg_matches_or_prefix_bytes(rel, b"Downloads")
    {
        return TccSurface::ThreeFoldersOrVolume;
    }
    if seg_matches_or_prefix_bytes(rel, b"Music")
        || seg_matches_or_prefix_bytes(rel, b"Pictures")
        || seg_matches_or_prefix_bytes(rel, b"Movies")
        || seg_matches_or_prefix_bytes(rel, b"Library/CloudStorage")
        || seg_matches_or_prefix_bytes(rel, b"Library/Mobile Documents")
        || seg_matches_or_prefix_bytes(rel, b"Library/Containers")
        || seg_matches_or_prefix_bytes(rel, b"Library/Group Containers")
        || seg_matches_or_prefix_bytes(rel, b"Library/Mail")
        || seg_matches_or_prefix_bytes(rel, b"Library/Messages")
        || seg_matches_or_prefix_bytes(rel, b"Library/Safari")
    {
        return TccSurface::PerAppOrCloudProtected;
    }
    TccSurface::UnrestrictedWorkspace
}

/// Stateful macOS TCC pre-flight gate tracking monotone `aterm ctl privacy` audit epochs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MacosPrivacyGate {
    fda: FullDiskAccess,
    epoch: u64,
}

impl MacosPrivacyGate {
    /// Construct a gate at `initial_epoch` with `fda` status.
    #[must_use]
    pub const fn new(fda: FullDiskAccess, initial_epoch: u64) -> Self {
        Self {
            fda,
            epoch: initial_epoch,
        }
    }

    /// Current monotone privacy-audit epoch.
    #[must_use]
    pub const fn epoch(&self) -> u64 {
        self.epoch
    }

    /// Current [`FullDiskAccess`] state.
    #[must_use]
    pub const fn full_disk_access(&self) -> FullDiskAccess {
        self.fda
    }

    /// Refresh [`FullDiskAccess`] from a newer `aterm ctl privacy` snapshot (`cand_epoch >= self.epoch`).
    pub fn update_privacy_snapshot(&mut self, cand_epoch: u64, fda: FullDiskAccess) -> bool {
        if cand_epoch < self.epoch {
            return false;
        }
        self.epoch = tcc_grant_epoch_advance(self.epoch, cand_epoch);
        self.fda = fda;
        true
    }

    /// Evaluate whether `path` can be accessed without triggering a macOS TCC consent dialog.
    #[must_use]
    pub const fn evaluate_path(&self, path: &str, home_dir: &str) -> TccPreflightVerdict {
        let surface = classify_macos_path(path, home_dir);
        let code = tcc_risk_code(surface.class_code(), self.fda.code());
        if tcc_probe_safe_without_dialog(code) {
            TccPreflightVerdict::AllowSilent
        } else if code == 1 {
            TccPreflightVerdict::NeedsFullDiskAccess { surface }
        } else {
            TccPreflightVerdict::NeedsExplicitPersonConsent { surface }
        }
    }

    /// Evaluate a macOS `defaults read <domain>` invocation (always `PerAppOrCloudProtected`
    /// unless reading `aterm`'s own bundle domain).
    #[must_use]
    pub fn evaluate_defaults_domain(&self, domain: &str) -> TccPreflightVerdict {
        if domain == "dev.aterm.app" || domain == "aterm" {
            return TccPreflightVerdict::AllowSilent;
        }
        let surface = TccSurface::PerAppOrCloudProtected;
        let code = tcc_risk_code(surface.class_code(), self.fda.code());
        if tcc_probe_safe_without_dialog(code) {
            TccPreflightVerdict::AllowSilent
        } else {
            TccPreflightVerdict::NeedsExplicitPersonConsent { surface }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fda_unlocks_three_folders_and_volumes_but_never_containers_or_photos() {
        let home = "/fixture-home";
        let mut gate = MacosPrivacyGate::new(FullDiskAccess::NotGranted, 1);

        assert_eq!(
            gate.evaluate_path("/fixture-home/astream/Cargo.toml", home),
            TccPreflightVerdict::AllowSilent
        );
        assert_eq!(
            gate.evaluate_path("/fixture-home/Library/Caches/aterm/build", home),
            TccPreflightVerdict::AllowSilent
        );

        assert_eq!(
            gate.evaluate_path("/fixture-home/Downloads/spec.pdf", home),
            TccPreflightVerdict::NeedsFullDiskAccess {
                surface: TccSurface::ThreeFoldersOrVolume
            }
        );
        assert_eq!(
            gate.evaluate_path("/Volumes/BackupDrive/archive.tar", home),
            TccPreflightVerdict::NeedsFullDiskAccess {
                surface: TccSurface::ThreeFoldersOrVolume
            }
        );

        assert!(gate.update_privacy_snapshot(2, FullDiskAccess::Granted));
        assert_eq!(gate.epoch(), 2);
        assert_eq!(gate.full_disk_access(), FullDiskAccess::Granted);
        assert_eq!(
            gate.evaluate_path("/fixture-home/Downloads/spec.pdf", home),
            TccPreflightVerdict::AllowSilent
        );
        assert_eq!(
            gate.evaluate_path("/Volumes/BackupDrive/archive.tar", home),
            TccPreflightVerdict::AllowSilent
        );

        assert_eq!(
            gate.evaluate_path(
                "/fixture-home/Library/Containers/com.apple.Notes/Data",
                home
            ),
            TccPreflightVerdict::NeedsExplicitPersonConsent {
                surface: TccSurface::PerAppOrCloudProtected
            }
        );
        assert_eq!(
            gate.evaluate_path("/fixture-home/Pictures/Photos Library.photoslibrary", home),
            TccPreflightVerdict::NeedsExplicitPersonConsent {
                surface: TccSurface::PerAppOrCloudProtected
            }
        );
        assert_eq!(
            gate.evaluate_defaults_domain("com.apple.Finder"),
            TccPreflightVerdict::NeedsExplicitPersonConsent {
                surface: TccSurface::PerAppOrCloudProtected
            }
        );
        assert_eq!(
            gate.evaluate_defaults_domain("dev.aterm.app"),
            TccPreflightVerdict::AllowSilent
        );
    }
}
