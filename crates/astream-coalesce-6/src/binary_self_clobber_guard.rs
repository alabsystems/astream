// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! macOS live-executable self-clobber & codesign protection (`Astream.Host.TlaBinarySelfClobberGuard`).
//!
//! Enforces the `aterm` executable safety invariant:
//! on macOS, `~/.local/bin/aterm` and `<App>.app/Contents/MacOS/aterm` are the installed
//! running application's executable; running `cp`, `install`, `mv`, `ln`, `rsync`, or
//! `codesign` onto them kills every live `aterm` window or leaves an unlaunchable bundle.
//! Agents must execute candidate builds directly from their build output directory
//! (e.g. `target/release/aterm` or `target/debug/aterm`).

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
#[path = "binary_self_clobber_guard_island.rs"]
mod binary_self_clobber_guard_island;
#[cfg(clean_islands)]
pub use binary_self_clobber_guard_island::{clobber_blocked_clamp, clobber_zero_floor};

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn clobber_blocked_clamp(blocked: u64, total: u64) -> u64 {
    if blocked < total {
        blocked
    } else {
        total
    }
}

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn clobber_zero_floor(_attempt: u64) -> u64 {
    0
}

/// Check that two `(st_dev, st_ino)` pairs refer to the same non-zero inode.
#[must_use]
pub const fn clobber_same_inode(src_dev: u64, src_ino: u64, dst_dev: u64, dst_ino: u64) -> bool {
    src_dev == dst_dev && src_ino == dst_ino && 0 < dst_ino
}

contract_fn! {
    /// Verified check that blocked self-clobber attempts never exceed total evaluations,
    /// linked via `clean-kernel-defeq` to `clobber_blocked_within_total_isl`.
    #[must_use]
    pub const fn clobber_blocked_within_total(blocked: u64, total: u64) -> bool
    clauses [ensures result == (blocked <= total)]
    {
        blocked <= total
    }
}

/// Kind of filesystem/signing verb inspected by [`BinarySelfClobberGuard`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryActionKind {
    /// Execute a binary directly (always allowed, including from `target/{debug,release}`).
    Execute,
    /// Copy/overwrite (`cp`, `rsync`).
    Copy,
    /// Install (`install`).
    Install,
    /// Rename/move (`mv`).
    Move,
    /// Symlink replacement (`ln`).
    Symlink,
    /// macOS ad-hoc or identity code-signing (`codesign`).
    Codesign,
}

impl BinaryActionKind {
    /// Classify a command program basename into a [`BinaryActionKind`].
    #[must_use]
    pub fn from_program_name(program: &str) -> Self {
        let base = match program.rsplit_once('/') {
            Some((_, tail)) => tail,
            None => program,
        };
        match base {
            "cp" | "rsync" | " ditto" | "ditto" => Self::Copy,
            "install" | "ginstall" => Self::Install,
            "mv" => Self::Move,
            "ln" => Self::Symlink,
            "codesign" | "ldid" => Self::Codesign,
            _ => Self::Execute,
        }
    }

    /// Returns `true` when this action mutates or re-signs its target executable path.
    #[must_use]
    pub const fn mutates_target(self) -> bool {
        !matches!(self, Self::Execute)
    }
}

/// Decision returned by [`BinarySelfClobberGuard::evaluate`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinaryClobberVerdict {
    /// Safe to proceed (either non-mutating execution or writing to an unprotected build path).
    Allow,
    /// Refused because `action` would overwrite or re-sign a live `aterm` executable.
    BlockProtectedExecutable {
        /// Mutating verb that was intercepted.
        action: BinaryActionKind,
        /// Target path that matched a protected executable rule.
        target_path: String,
        /// Actionable operator/agent guidance.
        remediation: &'static str,
    },
}

/// Guard state tracking protected live executable paths/inodes and blocked clobber attempts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinarySelfClobberGuard {
    live_dev: u64,
    live_ino: u64,
    clobber_count: u64,
    blocked_count: u64,
    total_evaluated: u64,
}

impl BinarySelfClobberGuard {
    /// Construct a new guard anchored to the running host executable's `(st_dev, st_ino)`
    /// (`0, 0` when inode metadata is unavailable).
    #[must_use]
    pub const fn new(live_dev: u64, live_ino: u64) -> Self {
        Self {
            live_dev,
            live_ino,
            clobber_count: 0,
            blocked_count: 0,
            total_evaluated: 0,
        }
    }

    /// Number of permitted clobbers of the live executable (invariant: always `0`).
    #[must_use]
    pub const fn clobber_count(&self) -> u64 {
        self.clobber_count
    }

    /// Clamped count of blocked self-clobber/codesign attempts (`<= total_evaluated`).
    #[must_use]
    pub const fn blocked_count(&self) -> u64 {
        self.blocked_count
    }

    /// Total command/target evaluations performed.
    #[must_use]
    pub const fn total_evaluated(&self) -> u64 {
        self.total_evaluated
    }

    /// Pure lexical check for protected `aterm` executable paths (`~/.local/bin/aterm`
    /// and `*.app/Contents/MacOS/aterm`).
    #[must_use]
    pub fn is_protected_aterm_path(path: &str) -> bool {
        let trimmed = path.trim_end_matches('/');
        if trimmed == "~/.local/bin/aterm" || trimmed.ends_with("/.local/bin/aterm") {
            return true;
        }
        if trimmed.ends_with(".app/Contents/MacOS/aterm")
            || trimmed.ends_with("/Contents/MacOS/aterm")
        {
            return true;
        }
        false
    }

    /// Evaluate `action` against `target_path` (with optional resolved `(target_dev, target_ino)`).
    pub fn evaluate(
        &mut self,
        action: BinaryActionKind,
        target_path: &str,
        target_inode: Option<(u64, u64)>,
    ) -> BinaryClobberVerdict {
        let next_total = self.total_evaluated.saturating_add(1);
        let inode_hit = match target_inode {
            Some((dev, ino)) => clobber_same_inode(self.live_dev, self.live_ino, dev, ino),
            None => false,
        };
        let protected = Self::is_protected_aterm_path(target_path) || inode_hit;
        if action.mutates_target() && protected {
            let next_blocked = self.blocked_count.saturating_add(1);
            self.clobber_count = clobber_zero_floor(next_blocked);
            self.blocked_count = clobber_blocked_clamp(next_blocked, next_total);
            self.total_evaluated = next_total;
            BinaryClobberVerdict::BlockProtectedExecutable {
                action,
                target_path: {
                    let mut s = String::new();
                    s.push_str(target_path);
                    s
                },
                remediation: "run candidate builds from their build path (e.g. target/release/aterm); never cp/install/codesign onto live aterm",
            }
        } else {
            self.clobber_count = clobber_zero_floor(self.blocked_count);
            self.blocked_count = clobber_blocked_clamp(self.blocked_count, next_total);
            self.total_evaluated = next_total;
            BinaryClobberVerdict::Allow
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_cp_install_and_codesign_onto_local_bin_and_app_bundle_aterm() {
        let mut guard = BinarySelfClobberGuard::new(16, 9001);

        let v1 = guard.evaluate(
            BinaryActionKind::from_program_name("/bin/cp"),
            "/fixture-home/.local/bin/aterm",
            None,
        );
        assert!(matches!(
            v1,
            BinaryClobberVerdict::BlockProtectedExecutable {
                action: BinaryActionKind::Copy,
                ..
            }
        ));

        let v2 = guard.evaluate(
            BinaryActionKind::from_program_name("/usr/bin/codesign"),
            "/Applications/aterm.app/Contents/MacOS/aterm",
            None,
        );
        assert!(matches!(
            v2,
            BinaryClobberVerdict::BlockProtectedExecutable {
                action: BinaryActionKind::Codesign,
                ..
            }
        ));

        // Hardlink/symlink alias with matching `(dev, ino)` is also blocked!
        let v3 = guard.evaluate(
            BinaryActionKind::Install,
            "/tmp/alias-to-live-aterm",
            Some((16, 9001)),
        );
        assert!(matches!(
            v3,
            BinaryClobberVerdict::BlockProtectedExecutable {
                action: BinaryActionKind::Install,
                ..
            }
        ));

        // Running from build path or signing a freshly built binary in `target/` is allowed!
        assert_eq!(
            guard.evaluate(
                BinaryActionKind::Codesign,
                "/fixture-home/aterm/target/release/aterm",
                Some((16, 9999)),
            ),
            BinaryClobberVerdict::Allow
        );
        assert_eq!(
            guard.evaluate(
                BinaryActionKind::Execute,
                "/fixture-home/.local/bin/aterm",
                Some((16, 9001)),
            ),
            BinaryClobberVerdict::Allow
        );

        assert_eq!(guard.clobber_count(), 0);
        assert_eq!(guard.blocked_count(), 3);
        assert_eq!(guard.total_evaluated(), 5);
    }
}
