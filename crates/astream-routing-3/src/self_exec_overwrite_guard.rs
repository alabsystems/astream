// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Installed `aterm` executable overwrite & `codesign` clobber guard
//! (`Astream.Host.TlaSelfExecOverwriteGuard`).
//!
//! On macOS (Apple Silicon), mutating or re-signing a mapped executable in place
//! (`~/.local/bin/aterm` or `.../Contents/MacOS/aterm`) invalidates kernel CS
//! pages and `SIGKILL`s every live `aterm` window or leaves an unlaunchable app
//! bundle. Builds must run from their build directory (`target/.../aterm`).

#[cfg(clean_islands)]
#[path = "self_exec_overwrite_guard_island.rs"]
mod self_exec_overwrite_guard_island;
#[cfg(clean_islands)]
pub use self_exec_overwrite_guard_island::{blocked_ops_clamp, exec_fence_epoch_advance};

/// Maximum blocked mutation events counted before saturating.
pub const MAX_TRACKED_BLOCKED_OPS: u64 = 4_096;

const BUNDLE_EXEC_SUFFIX: &[u8] = b"/Contents/MacOS/aterm";
const LOCAL_BIN_SUFFIX: &[u8] = b"/.local/bin/aterm";

#[cfg(not(clean_islands))]
/// Monotonically advance the self-executable protection fence epoch.
#[must_use]
pub const fn exec_fence_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

#[cfg(not(clean_islands))]
/// Clamp blocked mutation count to `max_tracked`.
#[must_use]
pub const fn blocked_ops_clamp(cand_blocked: u64, max_tracked: u64) -> u64 {
    if cand_blocked < max_tracked {
        cand_blocked
    } else {
        max_tracked
    }
}

contract_fn! {
    /// True iff `cand_ino` equals `prot_ino`.
    #[must_use]
    pub const fn inode_matches_protected(prot_ino: u64, cand_ino: u64) -> bool
    clauses [ensures result == (prot_ino == cand_ino)]
    {
        prot_ino == cand_ino
    }
}

/// Refusal reason when a tool attempts to overwrite or re-sign the live `aterm` binary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExecOverwriteRefusal {
    BundleExecutablePath,
    LocalBinExecutablePath,
    LiveExecutableInode { dev: u64, ino: u64 },
}

/// True iff `path` ends with `.../Contents/MacOS/aterm` or `.../.local/bin/aterm`.
#[must_use]
pub fn classify_protected_aterm_path(path: &[u8]) -> Option<ExecOverwriteRefusal> {
    if path.ends_with(BUNDLE_EXEC_SUFFIX) {
        return Some(ExecOverwriteRefusal::BundleExecutablePath);
    }
    if path.ends_with(LOCAL_BIN_SUFFIX) {
        return Some(ExecOverwriteRefusal::LocalBinExecutablePath);
    }
    None
}

/// Stateful guard protecting the running `aterm` executable path and `(dev, ino)` identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SelfExecOverwriteGuard {
    live_dev: u64,
    live_ino: u64,
    fence_epoch: u64,
    blocked_ops: u64,
}

impl SelfExecOverwriteGuard {
    #[must_use]
    pub const fn new(live_dev: u64, live_ino: u64) -> Self {
        Self {
            live_dev,
            live_ino,
            fence_epoch: 0,
            blocked_ops: 0,
        }
    }

    #[must_use]
    pub const fn fence_epoch(&self) -> u64 {
        self.fence_epoch
    }

    #[must_use]
    pub const fn blocked_ops(&self) -> u64 {
        self.blocked_ops
    }

    /// Check a proposed write/install/`codesign` target `(target_path, target_dev_ino)`.
    pub fn check_write_target(
        &mut self,
        target_path: &[u8],
        target_dev_ino: Option<(u64, u64)>,
    ) -> Result<(), ExecOverwriteRefusal> {
        if let Some(refusal) = classify_protected_aterm_path(target_path) {
            self.record_block();
            return Err(refusal);
        }
        if let Some((dev, ino)) = target_dev_ino {
            if self.live_ino != 0
                && dev == self.live_dev
                && inode_matches_protected(self.live_ino, ino)
            {
                self.record_block();
                return Err(ExecOverwriteRefusal::LiveExecutableInode { dev, ino });
            }
        }
        Ok(())
    }

    fn record_block(&mut self) {
        let cand_ep = self.fence_epoch.saturating_add(1);
        self.fence_epoch = exec_fence_epoch_advance(self.fence_epoch, cand_ep);
        let cand_blk = self.blocked_ops.saturating_add(1);
        self.blocked_ops = blocked_ops_clamp(cand_blk, MAX_TRACKED_BLOCKED_OPS);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_bundle_path_local_bin_and_hardlink_inode_while_allowing_build_dir() {
        let mut guard = SelfExecOverwriteGuard::new(16, 900_123);

        // Build output path is permitted!
        assert_eq!(
            guard.check_write_target(b"/fixture-home/aterm/target/release/aterm", Some((16, 555))),
            Ok(())
        );
        assert_eq!(guard.blocked_ops(), 0);

        // Installed ~/.local/bin/aterm is refused!
        assert_eq!(
            guard.check_write_target(b"/fixture-home/.local/bin/aterm", None),
            Err(ExecOverwriteRefusal::LocalBinExecutablePath)
        );
        // App bundle Contents/MacOS/aterm is refused!
        assert_eq!(
            guard.check_write_target(b"/Applications/aterm.app/Contents/MacOS/aterm", None),
            Err(ExecOverwriteRefusal::BundleExecutablePath)
        );
        // Hardlink / symlink resolving to live (dev, ino) is also refused!
        assert_eq!(
            guard.check_write_target(b"/tmp/sneaky-alias", Some((16, 900_123))),
            Err(ExecOverwriteRefusal::LiveExecutableInode {
                dev: 16,
                ino: 900_123,
            })
        );
        assert_eq!(guard.blocked_ops(), 3);
        assert_eq!(guard.fence_epoch(), 3);
    }
}
