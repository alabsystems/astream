// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `dir_flush_unavailable` vs `file_flush_refused` Darwin `ENOTSUP` / `EIO` / `ENOSPC`
//! cordon classifier (`evidence/manifest.toml` `os.cordon`;
//! `Astream.Engine.TlaDirFlushEnotsupVsEioCordonGuard`).
//!
//! Enforces the exact OS flush-refusal boundary used across `astream-broker::sync_parent_dir`,
//! `asb --seq-file`, `aterm-durable::Flush::dir_best_effort`, and `aterm-link`:
//! - Darwin refusal errnos (`ENOTSUP = 45`, `ENODEV = 19`, `EINVAL = 22`, `ENOTTY = 25`) plus
//!   `Unsupported` / `InvalidInput` ErrorKinds classify as `file_flush_refused` AND
//!   `dir_flush_unavailable`,
//! - `PermissionDenied` and `NotFound` ErrorKinds classify ONLY as `dir_flush_unavailable`
//!   (what opening a parent directory can answer), NEVER `file_flush_refused`,
//! - `EIO` (`5`), `ENOSPC` (`28`), `StorageFull`, and generic `Other` errors NEVER read as
//!   unavailable or refused — they MUST propagate fail-closed!

#[cfg(clean_islands)]
#[path = "dir_flush_enotsup_vs_eio_cordon_guard_island.rs"]
mod dir_flush_enotsup_vs_eio_cordon_guard_island;
#[cfg(clean_islands)]
pub use dir_flush_enotsup_vs_eio_cordon_guard_island::{
    tolerated_dir_flushes_clamp_b152, verified_flushes_advance_b152,
};

/// Darwin `ENODEV` (`19`).
pub const DARWIN_ENODEV: u64 = 19;
/// Darwin `EINVAL` (`22`).
pub const DARWIN_EINVAL: u64 = 22;
/// Darwin `ENOTTY` (`25`).
pub const DARWIN_ENOTTY: u64 = 25;
/// Darwin `ENOTSUP` (`45`, distinct from `EOPNOTSUPP = 102`).
pub const DARWIN_ENOTSUP: u64 = 45;

#[cfg(not(clean_islands))]
/// Clamp tolerated unavailable-dir-flush counter to `max_tracked`.
#[must_use]
pub const fn tolerated_dir_flushes_clamp_b152(cand_tolerated: u64, max_tracked: u64) -> u64 {
    if cand_tolerated < max_tracked {
        cand_tolerated
    } else {
        max_tracked
    }
}

#[cfg(not(clean_islands))]
/// Advance verified durable file flush count monotonically.
#[must_use]
pub const fn verified_flushes_advance_b152(cur_flushes: u64, cand_flushes: u64) -> u64 {
    if cur_flushes < cand_flushes {
        cand_flushes
    } else {
        cur_flushes
    }
}

contract_fn! {
    /// True iff `errno_code` is one of Darwin's four device-refusal errnos (`19, 22, 25, 45`).
    #[must_use]
    pub const fn is_darwin_flush_refusal_errno_b152(is_apple: bool, errno_code: u64) -> bool
    clauses [ensures result == (is_apple && (errno_code == 19 || errno_code == 22 || errno_code == 25 || errno_code == 45))]
    {
        is_apple
            && (errno_code == DARWIN_ENODEV
                || errno_code == DARWIN_EINVAL
                || errno_code == DARWIN_ENOTTY
                || errno_code == DARWIN_ENOTSUP)
    }
}

/// Abstracted `io::ErrorKind` subset relevant to flush classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FlushErrorKind {
    Unsupported,
    InvalidInput,
    PermissionDenied,
    NotFound,
    StorageFull,
    IoOrOther,
}

/// Classification outcome for file flush vs best-effort directory flush.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FlushCordonDecision {
    FileFlushRefusedByDevice,
    FileFlushHardFailureMustPropagate,
    DirFlushUnavailableTolerated { tolerated_count: u64 },
    DirFlushHardFailureMustPropagate,
    FlushSucceeded { verified_flushes: u64 },
}

/// Stateful flush classifier tracking verified flushes and tolerated directory refusals.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FlushCordonClassifier {
    is_apple: bool,
    tolerated_dir_count: u64,
    verified_flushes: u64,
}

impl FlushCordonClassifier {
    #[must_use]
    pub const fn new(is_apple: bool) -> Self {
        Self {
            is_apple,
            tolerated_dir_count: 0,
            verified_flushes: 0,
        }
    }

    pub fn on_flush_ok(&mut self) -> FlushCordonDecision {
        let next = self.verified_flushes.saturating_add(1);
        self.verified_flushes = verified_flushes_advance_b152(self.verified_flushes, next);
        FlushCordonDecision::FlushSucceeded {
            verified_flushes: self.verified_flushes,
        }
    }

    /// Classify a file's own flush error (`file_flush_refused`).
    #[must_use]
    pub const fn classify_file_flush_err(
        &self,
        kind: FlushErrorKind,
        raw_errno: Option<u64>,
    ) -> FlushCordonDecision {
        let kind_refused = matches!(
            kind,
            FlushErrorKind::Unsupported | FlushErrorKind::InvalidInput
        );
        let errno_refused = match raw_errno {
            Some(c) => is_darwin_flush_refusal_errno_b152(self.is_apple, c),
            None => false,
        };
        if kind_refused || errno_refused {
            FlushCordonDecision::FileFlushRefusedByDevice
        } else {
            FlushCordonDecision::FileFlushHardFailureMustPropagate
        }
    }

    /// Classify a directory open/flush error (`dir_flush_unavailable`).
    pub fn classify_dir_flush_err(
        &mut self,
        kind: FlushErrorKind,
        raw_errno: Option<u64>,
    ) -> FlushCordonDecision {
        let kind_unavail = matches!(
            kind,
            FlushErrorKind::Unsupported
                | FlushErrorKind::InvalidInput
                | FlushErrorKind::PermissionDenied
                | FlushErrorKind::NotFound
        );
        let errno_unavail = match raw_errno {
            Some(c) => is_darwin_flush_refusal_errno_b152(self.is_apple, c),
            None => false,
        };
        if kind_unavail || errno_unavail {
            let next = self.tolerated_dir_count.saturating_add(1);
            self.tolerated_dir_count = tolerated_dir_flushes_clamp_b152(next, 1_000_000);
            FlushCordonDecision::DirFlushUnavailableTolerated {
                tolerated_count: self.tolerated_dir_count,
            }
        } else {
            FlushCordonDecision::DirFlushHardFailureMustPropagate
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tolerates_darwin_enotsup_and_dir_perm_denied_while_propagating_eio_and_enospc() {
        let mut c = FlushCordonClassifier::new(true);
        // Darwin ENOTSUP (45) whose kind is IoOrOther -> unavailable on Apple!
        assert_eq!(
            c.classify_dir_flush_err(FlushErrorKind::IoOrOther, Some(DARWIN_ENOTSUP)),
            FlushCordonDecision::DirFlushUnavailableTolerated { tolerated_count: 1 }
        );
        // PermissionDenied is unavailable for DIR open, NEVER for FILE flush!
        assert_eq!(
            c.classify_file_flush_err(FlushErrorKind::PermissionDenied, Some(13)),
            FlushCordonDecision::FileFlushHardFailureMustPropagate
        );
        // EIO (5) and StorageFull (ENOSPC=28) MUST propagate on both dir and file!
        assert_eq!(
            c.classify_dir_flush_err(FlushErrorKind::IoOrOther, Some(5)),
            FlushCordonDecision::DirFlushHardFailureMustPropagate
        );
        assert_eq!(
            c.classify_dir_flush_err(FlushErrorKind::StorageFull, Some(28)),
            FlushCordonDecision::DirFlushHardFailureMustPropagate
        );
    }
}
