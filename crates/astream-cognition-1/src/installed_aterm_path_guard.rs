// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! macOS installed `aterm` executable (`~/.local/bin/aterm` & `Contents/MacOS/aterm`) write-blocker
//! (`Astream.Host.TlaInstalledAtermPathGuard`).
//!
//! Enforces the critical macOS `aterm` safety invariant: overwriting or re-codesigning the
//! running `aterm` binary in place (`~/.local/bin/aterm` or `*.app/Contents/MacOS/aterm`) can
//! terminate every live `aterm` window or brick app launch via `CODE SIGNING` page-in kills.

#[cfg(clean_islands)]
#[path = "installed_aterm_path_guard_island.rs"]
mod installed_aterm_path_guard_island;
#[cfg(clean_islands)]
pub use installed_aterm_path_guard_island::{
    guard_epoch_advance_b110, protected_write_blocks_clamp_b110,
};

#[cfg(not(clean_islands))]
/// Clamp blocked installed-binary write attempts to `max_blocks`.
#[must_use]
pub const fn protected_write_blocks_clamp_b110(cand_blocks: u64, max_blocks: u64) -> u64 {
    if cand_blocks < max_blocks {
        cand_blocks
    } else {
        max_blocks
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the binary-protection guard epoch.
#[must_use]
pub const fn guard_epoch_advance_b110(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `blocked_attempts` remains strictly below `max_blocks`.
    #[must_use]
    pub const fn guard_blocks_below_cap_b110(blocked_attempts: u64, max_blocks: u64) -> bool
    clauses [ensures result == (blocked_attempts < max_blocks)]
    {
        blocked_attempts < max_blocks
    }
}

/// Verdict for a proposed `cp` / `install` / `codesign` / `mv` destination path.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InstalledPathVerdict {
    PermittedBuildOutput {
        guard_epoch: u64,
    },
    RefusedProtectedInstalledAterm {
        blocked_attempts: u64,
        guard_epoch: u64,
    },
}

/// Write-blocker protecting the live installed `aterm` executable on macOS.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InstalledAtermPathGuard {
    blocked_attempts: u64,
    max_blocks_cap: u64,
    guard_epoch: u64,
}

impl InstalledAtermPathGuard {
    #[must_use]
    pub const fn new(max_blocks_cap: u64) -> Self {
        let cap = if max_blocks_cap == 0 {
            1024
        } else {
            max_blocks_cap
        };
        Self {
            blocked_attempts: 0,
            max_blocks_cap: cap,
            guard_epoch: 0,
        }
    }

    #[must_use]
    pub const fn blocked_attempts(&self) -> u64 {
        self.blocked_attempts
    }

    /// Inspect `dst_path` before mutating or codesigning it.
    pub fn check_destination(&mut self, dst_path: &[u8]) -> InstalledPathVerdict {
        let next_ep = self.guard_epoch.saturating_add(1);
        self.guard_epoch = guard_epoch_advance_b110(self.guard_epoch, next_ep);

        let is_protected = dst_path.ends_with(b"/.local/bin/aterm")
            || dst_path.ends_with(b"/Contents/MacOS/aterm");
        if is_protected {
            if guard_blocks_below_cap_b110(self.blocked_attempts, self.max_blocks_cap) {
                let cand = self.blocked_attempts.saturating_add(1);
                self.blocked_attempts =
                    protected_write_blocks_clamp_b110(cand, self.max_blocks_cap);
            }
            InstalledPathVerdict::RefusedProtectedInstalledAterm {
                blocked_attempts: self.blocked_attempts,
                guard_epoch: self.guard_epoch,
            }
        } else {
            InstalledPathVerdict::PermittedBuildOutput {
                guard_epoch: self.guard_epoch,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_local_bin_and_app_bundle_aterm_writes_while_allowing_build_dir() {
        let mut g = InstalledAtermPathGuard::new(16);
        assert_eq!(
            g.check_destination(b"/fixture-home/.local/bin/aterm"),
            InstalledPathVerdict::RefusedProtectedInstalledAterm {
                blocked_attempts: 1,
                guard_epoch: 1,
            }
        );
        assert_eq!(
            g.check_destination(b"/Applications/aterm.app/Contents/MacOS/aterm"),
            InstalledPathVerdict::RefusedProtectedInstalledAterm {
                blocked_attempts: 2,
                guard_epoch: 2,
            }
        );
        assert_eq!(
            g.check_destination(b"/fixture-home/aterm/target/release/aterm"),
            InstalledPathVerdict::PermittedBuildOutput { guard_epoch: 3 }
        );
    }
}
