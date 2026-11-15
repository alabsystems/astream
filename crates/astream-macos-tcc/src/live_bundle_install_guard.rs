// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Guard preventing `cp`, `install`, or `codesign` onto the live installed `aterm` executable
//! (`~/.local/bin/aterm` or `Contents/MacOS/aterm`), which kills every live `aterm` window via
//! `SIGKILL` code-signing invalidation (`Astream.MacTcc.TlaLiveBundleInstallGuard`).

#[cfg(clean_islands)]
#[path = "live_bundle_install_guard_island.rs"]
mod live_bundle_install_guard_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tcc_path_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tcc_inst_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use live_bundle_install_guard_island::{tcc_inst_advance, tcc_path_clamp};

/// Path safety score (`0 = live aterm executable`, `1 = isolated build artifact`).
pub const SAFE_BUILD_TARGET: u64 = 1;

contract_fn! {
    /// Verified install-target safety check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `tcc_target_writable_isl`.
    #[must_use]
    pub const fn tcc_target_writable(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct LiveBundleGuard {
    checks: u64,
}

fn ends_with_ascii_ci(haystack: &[u8], suffix: &[u8]) -> bool {
    if haystack.len() < suffix.len() {
        return false;
    }
    let start = haystack.len().saturating_sub(suffix.len());
    let Some(tail) = haystack.get(start..) else {
        return false;
    };
    tail.eq_ignore_ascii_case(suffix)
}

fn is_live_aterm_path(dest_path: &str) -> bool {
    let raw = dest_path.trim().as_bytes();
    if raw.is_empty() {
        return true;
    }
    let mut idx = 0usize;
    while idx < raw.len() {
        if raw.get(idx) == Some(&0) {
            return true;
        }
        idx = idx.saturating_add(1);
    }
    let mut end = raw.len();
    while end > 0 {
        if raw.get(end.saturating_sub(1)) == Some(&b'/') {
            end = end.saturating_sub(1);
        } else if end >= 2 && raw.get(end.saturating_sub(2)..end) == Some(b"/.") {
            end = end.saturating_sub(2);
        } else {
            break;
        }
    }
    let Some(norm) = raw.get(..end) else {
        return true;
    };
    if norm.is_empty() {
        return true;
    }
    ends_with_ascii_ci(norm, b"/.local/bin/aterm")
        || norm.eq_ignore_ascii_case(b".local/bin/aterm")
        || ends_with_ascii_ci(norm, b"/Contents/MacOS/aterm")
        || norm.eq_ignore_ascii_case(b"Contents/MacOS/aterm")
}

impl LiveBundleGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self { checks: 0 }
    }

    pub fn allow_binary_write(&mut self, dest_path: &str) -> bool {
        let is_live = is_live_aterm_path(dest_path);
        let safety = tcc_path_clamp(if is_live { 0 } else { 1 }, SAFE_BUILD_TARGET);
        self.checks = tcc_inst_advance(self.checks, self.checks.saturating_add(1));
        tcc_target_writable(safety, SAFE_BUILD_TARGET)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_overwriting_installed_aterm_binary_while_allowing_target_release_path() {
        let mut g = LiveBundleGuard::new();
        assert!(!g.allow_binary_write("/fixture-home/.local/bin/aterm"));
        assert!(!g.allow_binary_write("/Applications/aterm.app/Contents/MacOS/aterm"));
        assert!(g.allow_binary_write("/fixture-home/aterm/target/release/aterm"));
    }
}
