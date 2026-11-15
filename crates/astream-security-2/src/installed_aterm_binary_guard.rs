// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! macOS installed `aterm` executable mutation guard (`Astream.Host.TlaInstalledAtermBinaryGuard`).
//!
//! On macOS, `~/.local/bin/aterm` and `Contents/MacOS/aterm` are the running app's mapped
//! executable: overwriting or re-signing them in place (`cp`, `install`, `codesign`) triggers
//! macOS kernel `SIGKILL` (`Code Signature Invalid`) across every open `aterm` window or leaves an
//! unlaunchable bundle. [`InstalledAtermBinaryGuard`] refuses mutations targeting those suffixes
//! and permits executing or signing builds at their `target/...` build output paths.

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
#[path = "installed_aterm_binary_guard_island.rs"]
mod installed_aterm_binary_guard_island;
#[cfg(clean_islands)]
pub use installed_aterm_binary_guard_island::{
    bin_guard_blocked_advance_b123, bin_guard_path_clamp_b123,
};

#[cfg(not(clean_islands))]
/// Clamp inspected destination path length to `max_len`.
#[must_use]
pub const fn bin_guard_path_clamp_b123(cand_len: u64, max_len: u64) -> u64 {
    if cand_len < max_len {
        cand_len
    } else {
        max_len
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance blocked live-executable mutation counter.
#[must_use]
pub const fn bin_guard_blocked_advance_b123(cur_blocked: u64, cand_blocked: u64) -> u64 {
    if cur_blocked < cand_blocked {
        cand_blocked
    } else {
        cur_blocked
    }
}

contract_fn! {
    /// True iff `protected_match == 0` (destination is NOT the installed live `aterm` executable).
    #[must_use]
    pub const fn bin_guard_target_is_safe_b123(protected_match: u64) -> bool
    clauses [ensures result == (protected_match == 0)]
    {
        protected_match == 0
    }
}

pub const MAX_GUARD_PATH_BYTES: u64 = 4096;
const SUFFIX_LOCAL_BIN_ATERM: &[u8] = b"/.local/bin/aterm";
const SUFFIX_BUNDLE_MACOS_ATERM: &[u8] = b"/Contents/MacOS/aterm";

fn ends_with_bytes(haystack: &[u8], suffix: &[u8]) -> bool {
    if haystack.len() < suffix.len() {
        return false;
    }
    let skip = haystack.len().saturating_sub(suffix.len());
    match haystack.get(skip..) {
        Some(tail) => tail == suffix,
        None => false,
    }
}

fn is_installed_aterm_executable(dest_path: &[u8]) -> bool {
    ends_with_bytes(dest_path, SUFFIX_LOCAL_BIN_ATERM)
        || ends_with_bytes(dest_path, SUFFIX_BUNDLE_MACOS_ATERM)
}

/// Verdict for a file-write / `cp` / `install` / `codesign` target path.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryMutationVerdict {
    AdmitBuildOutputPath,
    RefusedLiveInstalledAtermExecutable { blocked_mutations: u64 },
}

/// Guard preventing `cp`, `install`, or `codesign` onto the live installed `aterm` binary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InstalledAtermBinaryGuard {
    target_path_len: u64,
    blocked_mutations: u64,
}

impl Default for InstalledAtermBinaryGuard {
    fn default() -> Self {
        Self::new()
    }
}

impl InstalledAtermBinaryGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            target_path_len: 0,
            blocked_mutations: 0,
        }
    }

    #[must_use]
    pub const fn blocked_mutations(&self) -> u64 {
        self.blocked_mutations
    }

    /// Evaluate whether mutating or signing `dest_path` is safe.
    pub fn check_mutation_target(&mut self, dest_path: &[u8]) -> BinaryMutationVerdict {
        self.target_path_len =
            bin_guard_path_clamp_b123(dest_path.len() as u64, MAX_GUARD_PATH_BYTES);
        let protected_match: u64 = if is_installed_aterm_executable(dest_path) {
            1
        } else {
            0
        };
        if bin_guard_target_is_safe_b123(protected_match) {
            BinaryMutationVerdict::AdmitBuildOutputPath
        } else {
            self.blocked_mutations = bin_guard_blocked_advance_b123(
                self.blocked_mutations,
                self.blocked_mutations.saturating_add(1),
            );
            BinaryMutationVerdict::RefusedLiveInstalledAtermExecutable {
                blocked_mutations: self.blocked_mutations,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_local_bin_and_bundle_executable_while_admitting_target_release_build() {
        let mut guard = InstalledAtermBinaryGuard::new();
        assert_eq!(
            guard.check_mutation_target(b"/fixture-home/.local/bin/aterm"),
            BinaryMutationVerdict::RefusedLiveInstalledAtermExecutable {
                blocked_mutations: 1
            }
        );
        assert_eq!(
            guard.check_mutation_target(b"/Applications/aterm.app/Contents/MacOS/aterm"),
            BinaryMutationVerdict::RefusedLiveInstalledAtermExecutable {
                blocked_mutations: 2
            }
        );
        assert_eq!(
            guard.check_mutation_target(b"/fixture-home/aterm/target/release/aterm"),
            BinaryMutationVerdict::AdmitBuildOutputPath
        );
    }
}
