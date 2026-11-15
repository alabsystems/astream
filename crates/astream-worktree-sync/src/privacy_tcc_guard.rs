// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! macOS TCC privacy-consent path classifier (`~/Documents`, `~/Desktop`, `~/Downloads`,
//! `/Volumes/*`, `~/Library/Containers/*`, `~/Music`, `~/Pictures`) preventing unprompted modal
//! hangs (`aterm` primer, `Astream.Worktree.TlaPrivacyTccGuard`).

#[cfg(clean_islands)]
#[path = "privacy_tcc_guard_island.rs"]
mod privacy_tcc_guard_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tcc_rules_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tcc_checked_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use privacy_tcc_guard_island::{tcc_checked_advance, tcc_rules_clamp};

/// Number of built-in macOS TCC protected-folder classes.
pub const MAX_TCC_CLASSES: u64 = 16;

contract_fn! {
    /// Verified grant check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `tcc_fda_covers_isl`.
    #[must_use]
    pub const fn tcc_fda_covers(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TccPathVerdict {
    SafeWorkspacePath,
    AllowedViaFullDiskAccess,
    BlockedWouldPromptModal,
}

/// Pre-open path filter preventing macOS TCC consent modal hangs.
#[derive(Debug, Clone)]
pub struct MacOsTccGuard {
    home_dir: String,
    aterm_has_fda: bool,
    checks: u64,
}

fn strip_trailing_slashes(mut s: &str) -> &str {
    while let Some(rest) = s.strip_suffix('/') {
        s = rest;
    }
    s
}

fn strip_leading_slashes(mut s: &str) -> &str {
    while let Some(rest) = s.strip_prefix('/') {
        s = rest;
    }
    s
}

fn has_dir_segment_prefix(path: &str, prefix: &str) -> bool {
    if path == prefix {
        return true;
    }
    if let Some(rem) = path.strip_prefix(prefix) {
        return rem.starts_with('/');
    }
    false
}

fn has_unsafe_path_syntax(abs_path: &str) -> bool {
    if !abs_path.starts_with('/') || abs_path.contains('\0') {
        return true;
    }
    for seg in abs_path.split('/') {
        if seg == ".." {
            return true;
        }
    }
    false
}

impl MacOsTccGuard {
    #[must_use]
    pub fn new(home_dir: &str, aterm_has_fda: bool) -> Self {
        let _ = tcc_rules_clamp(8, MAX_TCC_CLASSES);
        let trimmed = strip_trailing_slashes(home_dir);
        let mut owned_home = String::new();
        owned_home.push_str(trimmed);
        Self {
            home_dir: owned_home,
            aterm_has_fda,
            checks: 0,
        }
    }

    pub fn classify_path(&mut self, abs_path: &str) -> TccPathVerdict {
        self.checks = tcc_checked_advance(self.checks, self.checks.saturating_add(1));
        if has_unsafe_path_syntax(abs_path) {
            return TccPathVerdict::BlockedWouldPromptModal;
        }
        let fda_flag = if self.aterm_has_fda { 1u64 } else { 0u64 };
        if has_dir_segment_prefix(abs_path, "/Volumes") {
            return if tcc_fda_covers(fda_flag, 1) {
                TccPathVerdict::AllowedViaFullDiskAccess
            } else {
                TccPathVerdict::BlockedWouldPromptModal
            };
        }
        if !self.home_dir.is_empty() {
            if let Some(after_home) = abs_path.strip_prefix(self.home_dir.as_str()) {
                if after_home.is_empty() || after_home.starts_with('/') {
                    let rel = strip_leading_slashes(after_home);
                    // FDA covers Documents, Desktop, Downloads, and Volumes ONLY!
                    if has_dir_segment_prefix(rel, "Documents")
                        || has_dir_segment_prefix(rel, "Desktop")
                        || has_dir_segment_prefix(rel, "Downloads")
                    {
                        return if tcc_fda_covers(fda_flag, 1) {
                            TccPathVerdict::AllowedViaFullDiskAccess
                        } else {
                            TccPathVerdict::BlockedWouldPromptModal
                        };
                    }
                    // Other apps' containers, Music, and Pictures can raise modal prompts even WITH FDA!
                    if has_dir_segment_prefix(rel, "Library/Containers")
                        || has_dir_segment_prefix(rel, "Library/Group Containers")
                        || has_dir_segment_prefix(rel, "Music")
                        || has_dir_segment_prefix(rel, "Pictures")
                    {
                        return TccPathVerdict::BlockedWouldPromptModal;
                    }
                }
            }
        }
        TccPathVerdict::SafeWorkspacePath
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tcc_guard_enforces_exact_fda_vs_app_container_modal_rules() {
        let mut no_fda = MacOsTccGuard::new("/fixture-home", false);
        assert_eq!(
            no_fda.classify_path("/fixture-home/astream/Cargo.toml"),
            TccPathVerdict::SafeWorkspacePath
        );
        assert_eq!(
            no_fda.classify_path("/fixture-home/Downloads/a.tgz"),
            TccPathVerdict::BlockedWouldPromptModal
        );

        let mut with_fda = MacOsTccGuard::new("/fixture-home", true);
        assert_eq!(
            with_fda.classify_path("/fixture-home/Downloads/a.tgz"),
            TccPathVerdict::AllowedViaFullDiskAccess
        );
        // App containers still prompt even with FDA!
        assert_eq!(
            with_fda.classify_path("/fixture-home/Library/Containers/com.apple.Notes/Data"),
            TccPathVerdict::BlockedWouldPromptModal
        );
    }
}
