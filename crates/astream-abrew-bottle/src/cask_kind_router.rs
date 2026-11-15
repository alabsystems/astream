// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `atpkg-abrew` cask container format router (`aterm` primer: *"installs supported bottles and
//! tar/zip/DMG/single-file casks into its own prefix. Unsupported operations fail"*) rejecting
//! root `.pkg` installers (`Astream.Abrew.TlaCaskKindRouter`).

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
#[path = "cask_kind_router_island.rs"]
mod cask_kind_router_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ab_kind_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ab_cask_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use cask_kind_router_island::{ab_cask_advance, ab_kind_clamp};

/// Highest container code (`0 = UnsupportedPkgOrScript`, `1 = Tar`, `2 = Zip`, `3 = Dmg`, `4 = SingleFile`).
pub const MAX_CASK_KIND: u64 = 4;

contract_fn! {
    /// Verified supported-cask predicate (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ab_cask_supported_isl`.
    #[must_use]
    pub const fn ab_cask_supported(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CaskContainer {
    Tar,
    Zip,
    Dmg,
    SingleFile,
    Unsupported,
}

#[derive(Debug, Clone, Default)]
pub struct CaskRouter {
    routed: u64,
}

impl CaskRouter {
    #[must_use]
    pub const fn new() -> Self {
        Self { routed: 0 }
    }

    pub fn classify_artifact(
        &mut self,
        filename: &str,
        has_pkg_installer: bool,
    ) -> (CaskContainer, bool) {
        let valid_name = is_clean_artifact_filename(filename);
        let (kind, code) = if !valid_name
            || has_pkg_installer
            || ends_with_ascii_ci(filename, b".pkg")
            || ends_with_ascii_ci(filename, b".mpkg")
            || ends_with_ascii_ci(filename, b".sh")
            || ends_with_ascii_ci(filename, b".command")
        {
            (CaskContainer::Unsupported, 0u64)
        } else if ends_with_ascii_ci(filename, b".tar.gz")
            || ends_with_ascii_ci(filename, b".tar.xz")
            || ends_with_ascii_ci(filename, b".tgz")
        {
            (CaskContainer::Tar, 1u64)
        } else if ends_with_ascii_ci(filename, b".zip") {
            (CaskContainer::Zip, 2u64)
        } else if ends_with_ascii_ci(filename, b".dmg") {
            (CaskContainer::Dmg, 3u64)
        } else {
            (CaskContainer::SingleFile, 4u64)
        };
        let clamped = ab_kind_clamp(code, MAX_CASK_KIND);
        self.routed = ab_cask_advance(self.routed, self.routed.saturating_add(1));
        (kind, ab_cask_supported(clamped, 1))
    }
}

fn is_clean_artifact_filename(name: &str) -> bool {
    let bytes = name.as_bytes();
    if bytes.is_empty() || name == "." || name == ".." {
        return false;
    }
    let mut has_non_ws = false;
    let mut i = 0usize;
    while i < bytes.len() {
        let Some(&b) = bytes.get(i) else {
            break;
        };
        if b == b'/' || b == b'\\' || b == 0 {
            return false;
        }
        if !b.is_ascii_whitespace() {
            has_non_ws = true;
        }
        i = i.saturating_add(1);
    }
    has_non_ws
}

fn ends_with_ascii_ci(haystack: &str, suffix_lower: &[u8]) -> bool {
    let hb = haystack.as_bytes();
    if hb.len() < suffix_lower.len() {
        return false;
    }
    let start = hb.len().saturating_sub(suffix_lower.len());
    let mut i = 0usize;
    while i < suffix_lower.len() {
        let Some(&h) = hb.get(start.saturating_add(i)) else {
            return false;
        };
        let Some(&s) = suffix_lower.get(i) else {
            return false;
        };
        if h.to_ascii_lowercase() != s {
            return false;
        }
        i = i.saturating_add(1);
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn admits_dmg_zip_tar_single_file_and_fails_closed_on_pkg() {
        let mut r = CaskRouter::new();
        assert_eq!(
            r.classify_artifact("tool.dmg", false),
            (CaskContainer::Dmg, true)
        );
        assert_eq!(
            r.classify_artifact("driver.pkg", false),
            (CaskContainer::Unsupported, false)
        );
        assert_eq!(
            r.classify_artifact("wrapper.dmg", true),
            (CaskContainer::Unsupported, false)
        );
        assert_eq!(
            r.classify_artifact("DRIVER.PKG", false),
            (CaskContainer::Unsupported, false)
        );
        assert_eq!(
            r.classify_artifact("install.sh", false),
            (CaskContainer::Unsupported, false)
        );
        assert_eq!(
            r.classify_artifact("../evil", false),
            (CaskContainer::Unsupported, false)
        );
    }
}
