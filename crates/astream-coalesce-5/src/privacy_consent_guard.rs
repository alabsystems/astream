// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! macOS TCC Privacy Consent & Modal-Dialog Pre-Screener.
//!
//! Enforces the exact `aterm` macOS TCC privacy safety rules lexically (zero syscalls, so
//! inspecting a path NEVER triggers the very TCC modal dialog it guards against!):
//! - `~/Documents`, `~/Desktop`, `~/Downloads`, and `/Volumes/...` trigger a blocking macOS
//!   consent dialog UNLESS `aterm` holds Full Disk Access (`fda_granted == true`).
//! - App containers (`~/Library/Containers/`, `~/Library/Group Containers/`), Cloud-synced
//!   libraries (`~/Library/Mobile Documents/`, `~/Library/CloudStorage/`), `~/Music/`,
//!   `~/Pictures/Photos Library.photoslibrary`, and any `defaults` domain lookup for another
//!   application CAN put a blocking TCC dialog on the operator's screen **even when Full Disk
//!   Access is granted**!
//!
//! Backed by Clean TLA+ Island `Astream.Host.TlaMacPrivacyConsentGuard`
//! (`privacy_consent_guard_island.rs`), proving `blockedProbes <= totalProbes` and
//! `totalProbes <= maxProbeCap`.

#![allow(clippy::match_like_matches_macro)]

#[cfg(clean_islands)]
#[path = "privacy_consent_guard_island.rs"]
mod island;
#[cfg(clean_islands)]
pub use island::{tcc_blocked_clamp, tcc_probes_clamp};

#[cfg(not(clean_islands))]
#[inline]
pub const fn tcc_blocked_clamp(blocked: u64, total: u64) -> u64 {
    if blocked < total {
        blocked
    } else {
        total
    }
}

#[cfg(not(clean_islands))]
#[inline]
pub const fn tcc_probes_clamp(total: u64, max_cap: u64) -> u64 {
    if total < max_cap {
        total
    } else {
        max_cap
    }
}

contract_fn! {
    /// Kernel-certified check that blocked TCC probes never exceed total screened probes.
    #[must_use]
    #[inline]
    pub const fn tcc_blocked_within_total(blocked: u64, total: u64) -> bool
    clauses [ensures result == (blocked <= total)]
    {
        blocked <= total
    }
}

/// Default telemetry counter cap (`1_000_000` probes).
pub const DEFAULT_MAX_PROBE_CAP: u64 = 1_000_000;

/// macOS TCC domain classification for a candidate path or `defaults` domain.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TccConsentVerdict {
    /// Normal workspace or system path: safe to open without raising a TCC dialog.
    SafeNoDialog,
    /// Protected folder (`Documents`, `Desktop`, `Downloads`, `/Volumes/`): safe ONLY because
    /// `aterm` holds Full Disk Access (`fda_granted == true`).
    AllowedViaFullDiskAccess,
    /// Protected folder (`Documents`, `Desktop`, `Downloads`, `/Volumes/`) blocked because
    /// Full Disk Access is NOT granted (`NEEDS YOU: grant Full Disk Access`).
    BlockedNeedsFullDiskAccess,
    /// App container, CloudStorage/iCloud sync folder, Music/Photos library, or foreign
    /// `defaults` domain: can raise a modal TCC dialog EVEN WITH Full Disk Access!
    BlockedAlwaysDialogRisk,
}

const fn strip_prefix_bytes<'a>(mut hay: &'a [u8], mut prefix: &[u8]) -> Option<&'a [u8]> {
    if hay.len() < prefix.len() {
        return None;
    }
    while let &[pb, ref ptail @ ..] = prefix {
        let &[hb, ref htail @ ..] = hay else {
            return None;
        };
        if hb != pb {
            return None;
        }
        prefix = ptail;
        hay = htail;
    }
    Some(hay)
}

const fn match_subpath(rel_after_home: &[u8], sub: &[u8]) -> bool {
    match strip_prefix_bytes(rel_after_home, sub) {
        Some([] | [b'/', ..]) => true,
        _ => false,
    }
}

/// Stateful macOS TCC consent pre-screener certified by `TlaMacPrivacyConsentGuard`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MacPrivacyConsentGuard {
    fda_granted: bool,
    total_probes: u64,
    blocked_probes: u64,
    max_probe_cap: u64,
}

impl MacPrivacyConsentGuard {
    #[inline]
    pub const fn new(fda_granted: bool, max_probe_cap: u64) -> Self {
        let cap = if max_probe_cap == 0 {
            DEFAULT_MAX_PROBE_CAP
        } else {
            max_probe_cap
        };
        Self {
            fda_granted,
            total_probes: 0,
            blocked_probes: 0,
            max_probe_cap: cap,
        }
    }

    #[inline]
    pub const fn fda_granted(&self) -> bool {
        self.fda_granted
    }

    #[inline]
    pub const fn max_probe_cap(&self) -> u64 {
        self.max_probe_cap
    }

    #[inline]
    pub const fn total_probes(&self) -> u64 {
        self.total_probes
    }

    #[inline]
    pub const fn blocked_probes(&self) -> u64 {
        self.blocked_probes
    }

    fn record_verdict(&mut self, verdict: TccConsentVerdict) -> TccConsentVerdict {
        let raw_tot = self.total_probes.saturating_add(1);
        let bounded_tot = tcc_probes_clamp(raw_tot, self.max_probe_cap);
        let is_blocked = matches!(
            verdict,
            TccConsentVerdict::BlockedNeedsFullDiskAccess
                | TccConsentVerdict::BlockedAlwaysDialogRisk
        );
        let raw_blk = if is_blocked {
            self.blocked_probes.saturating_add(1)
        } else {
            self.blocked_probes
        };
        self.total_probes = bounded_tot;
        self.blocked_probes = tcc_blocked_clamp(raw_blk, bounded_tot);
        verdict
    }

    /// Lexically screens `path` relative to `home_dir` (e.g. `"/fixture-home"`).
    pub fn screen_path(&mut self, path: &str, home_dir: &str) -> TccConsentVerdict {
        let raw = path.as_bytes();
        if let Some(after_vol) = strip_prefix_bytes(raw, b"/Volumes/") {
            if !after_vol.is_empty() {
                let v = if self.fda_granted {
                    TccConsentVerdict::AllowedViaFullDiskAccess
                } else {
                    TccConsentVerdict::BlockedNeedsFullDiskAccess
                };
                return self.record_verdict(v);
            }
        }

        let home = home_dir.as_bytes();
        let rel: Option<&[u8]> = if let Some(after_tilde) = strip_prefix_bytes(raw, b"~/") {
            Some(after_tilde)
        } else if !home.is_empty() {
            match strip_prefix_bytes(raw, home) {
                Some(after_home) => strip_prefix_bytes(after_home, b"/"),
                None => None,
            }
        } else {
            None
        };

        let Some(sub) = rel else {
            return self.record_verdict(TccConsentVerdict::SafeNoDialog);
        };

        // Always-dialog-risk domains (FDA does NOT suppress TCC prompts on these!):
        if match_subpath(sub, b"Library/Containers")
            || match_subpath(sub, b"Library/Group Containers")
            || match_subpath(sub, b"Library/Mobile Documents")
            || match_subpath(sub, b"Library/CloudStorage")
            || match_subpath(sub, b"Music")
            || match_subpath(sub, b"Pictures/Photos Library.photoslibrary")
        {
            return self.record_verdict(TccConsentVerdict::BlockedAlwaysDialogRisk);
        }

        // Three user folders covered by Full Disk Access:
        if match_subpath(sub, b"Documents")
            || match_subpath(sub, b"Desktop")
            || match_subpath(sub, b"Downloads")
        {
            let v = if self.fda_granted {
                TccConsentVerdict::AllowedViaFullDiskAccess
            } else {
                TccConsentVerdict::BlockedNeedsFullDiskAccess
            };
            return self.record_verdict(v);
        }

        self.record_verdict(TccConsentVerdict::SafeNoDialog)
    }

    /// Screens a macOS `defaults read <domain>` invocation: any foreign app domain risks a
    /// TCC container prompt unless explicitly asked for by the operator.
    pub fn screen_defaults_domain(&mut self) -> TccConsentVerdict {
        self.record_verdict(TccConsentVerdict::BlockedAlwaysDialogRisk)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn distinguishes_fda_covered_folders_from_always_dialog_containers_and_defaults() {
        let home = "/fixture-home";
        let mut no_fda = MacPrivacyConsentGuard::new(false, 1024);
        assert_eq!(
            no_fda.screen_path("/fixture-home/astream/Cargo.toml", home),
            TccConsentVerdict::SafeNoDialog
        );
        assert_eq!(
            no_fda.screen_path("/fixture-home/Downloads/foo.tar.gz", home),
            TccConsentVerdict::BlockedNeedsFullDiskAccess
        );

        let mut with_fda = MacPrivacyConsentGuard::new(true, 1024);
        assert_eq!(
            with_fda.screen_path("/fixture-home/Downloads/foo.tar.gz", home),
            TccConsentVerdict::AllowedViaFullDiskAccess
        );
        assert_eq!(
            with_fda.screen_path("/Volumes/ExternalSSD/cache", home),
            TccConsentVerdict::AllowedViaFullDiskAccess
        );
        // Even WITH Full Disk Access, other apps' containers, Music, and `defaults` block!
        assert_eq!(
            with_fda.screen_path(
                "/fixture-home/Library/Containers/com.apple.Notes/Data",
                home
            ),
            TccConsentVerdict::BlockedAlwaysDialogRisk
        );
        assert_eq!(
            with_fda.screen_defaults_domain(),
            TccConsentVerdict::BlockedAlwaysDialogRisk
        );
        assert!(tcc_blocked_within_total(
            with_fda.blocked_probes(),
            with_fda.total_probes()
        ));
    }
}
