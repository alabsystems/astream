// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! macOS live `aterm` executable overwrite / `codesign` guard
//! (`Astream.Host.TlaAppBundleOverwriteGuard`, Island #283).

#[cfg(clean_islands)]
#[path = "app_bundle_overwrite_guard_island.rs"]
mod app_bundle_overwrite_guard_island;
#[cfg(clean_islands)]
pub use app_bundle_overwrite_guard_island::{bundle_path_len_clamp, bundle_protected_hits_advance};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn bundle_protected_hits_advance(prev: u64, next: u64) -> u64 {
    if prev < next {
        next
    } else {
        prev
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn bundle_path_len_clamp(raw_len: u64, max_len: u64) -> u64 {
    if raw_len < max_len {
        raw_len
    } else {
        max_len
    }
}

/// Maximum path length inspected (`4096` bytes, `PATH_MAX`).
pub const MAX_INSPECTED_PATH_LEN: u64 = 4096;

contract_fn! {
    /// Verified check `is_live_executable == 0`, linked via `clean-kernel-defeq` to
    /// `bundle_mutation_allowed_isl`.
    #[must_use]
    pub const fn bundle_mutation_allowed(is_live_executable: u64) -> bool
    clauses [ensures result == (is_live_executable == 0)]
    {
        is_live_executable == 0
    }
}

/// Binary mutation operation under preflight inspection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryMutationOp {
    Copy,
    Install,
    Move,
    Codesign,
}

/// Classification of a candidate target path for `cp` / `install` / `mv` / `codesign`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TargetBinaryClass {
    /// Safe isolated build output (e.g. `target/release/aterm` or `target/debug/aterm`).
    IsolatedBuildArtifact,
    /// Protected `~/.local/bin/aterm` CLI entrypoint on `PATH`.
    LiveLocalBinAterm,
    /// Protected `*.app/Contents/MacOS/aterm` macOS bundle executable!
    LiveAppBundleMacOsAterm,
}

const fn is_ascii_ws(b: u8) -> bool {
    matches!(b, b' ' | b'\t' | b'\r' | b'\n' | 0x0C)
}

const fn trim_path_bytes(mut s: &[u8]) -> &[u8] {
    while let [head, rest @ ..] = s {
        if is_ascii_ws(*head) {
            s = rest;
        } else {
            break;
        }
    }
    while let [rest @ .., last] = s {
        if is_ascii_ws(*last) || *last == b'/' {
            s = rest;
        } else {
            break;
        }
    }
    s
}

const fn bytes_eq(mut a: &[u8], mut b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    while let [ha, ta @ ..] = a {
        let [hb, tb @ ..] = b else {
            return false;
        };
        if *ha != *hb {
            return false;
        }
        a = ta;
        b = tb;
    }
    true
}

const fn bytes_ends_with(mut hay: &[u8], suffix: &[u8]) -> bool {
    while hay.len() > suffix.len() {
        let [_, rest @ ..] = hay else {
            return false;
        };
        hay = rest;
    }
    bytes_eq(hay, suffix)
}

/// Classify a path string without touching the filesystem.
#[must_use]
pub const fn classify_aterm_binary_target(raw_path: &str) -> TargetBinaryClass {
    let clamped_len = bundle_path_len_clamp(raw_path.len() as u64, MAX_INSPECTED_PATH_LEN) as usize;
    let raw_bytes = raw_path.as_bytes();
    let bounded = if clamped_len < raw_bytes.len() {
        let (head, _) = raw_bytes.split_at(clamped_len);
        head
    } else {
        raw_bytes
    };
    let p = trim_path_bytes(bounded);
    if bytes_ends_with(p, b"/Contents/MacOS/aterm") || bytes_eq(p, b"Contents/MacOS/aterm") {
        return TargetBinaryClass::LiveAppBundleMacOsAterm;
    }
    if bytes_ends_with(p, b"/.local/bin/aterm") || bytes_eq(p, b"~/.local/bin/aterm") {
        return TargetBinaryClass::LiveLocalBinAterm;
    }
    TargetBinaryClass::IsolatedBuildArtifact
}

/// Stateful preflight guard blocking `cp`, `install`, `mv`, and `codesign` against the
/// live `aterm` executable.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AppBundleOverwriteGuard {
    blocked_mutations: u64,
}

impl AppBundleOverwriteGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            blocked_mutations: 0,
        }
    }

    #[must_use]
    pub const fn blocked_mutations(&self) -> u64 {
        self.blocked_mutations
    }

    /// Check whether `op` on `dest_path` is permitted (`Ok(IsolatedBuildArtifact)`) or
    /// blocked (`Err(class)`).
    pub fn check_mutation(
        &mut self,
        _op: BinaryMutationOp,
        dest_path: &str,
    ) -> Result<TargetBinaryClass, TargetBinaryClass> {
        let class = classify_aterm_binary_target(dest_path);
        let live_flag = match class {
            TargetBinaryClass::IsolatedBuildArtifact => 0,
            TargetBinaryClass::LiveLocalBinAterm | TargetBinaryClass::LiveAppBundleMacOsAterm => 1,
        };
        if bundle_mutation_allowed(live_flag) {
            Ok(class)
        } else {
            self.blocked_mutations = bundle_protected_hits_advance(
                self.blocked_mutations,
                self.blocked_mutations.saturating_add(1),
            );
            Err(class)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_live_local_bin_and_app_bundle_and_allows_target_build_dir() {
        let mut g = AppBundleOverwriteGuard::new();
        assert_eq!(
            g.check_mutation(BinaryMutationOp::Copy, "/fixture-home/.local/bin/aterm"),
            Err(TargetBinaryClass::LiveLocalBinAterm)
        );
        assert_eq!(
            g.check_mutation(
                BinaryMutationOp::Codesign,
                "/Applications/aterm.app/Contents/MacOS/aterm",
            ),
            Err(TargetBinaryClass::LiveAppBundleMacOsAterm)
        );
        assert_eq!(g.blocked_mutations(), 2);

        assert_eq!(
            g.check_mutation(
                BinaryMutationOp::Codesign,
                "/fixture-home/aterm/target/release/aterm",
            ),
            Ok(TargetBinaryClass::IsolatedBuildArtifact)
        );
        assert_eq!(g.blocked_mutations(), 2);
    }
}
