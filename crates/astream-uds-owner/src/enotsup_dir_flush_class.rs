// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `astream-sys::dir_flush_unavailable` classifier (`os.cordon`: recognizing Darwin `ENOTSUP (45)`
//! — which `std` leaves uncategorized unlike `EOPNOTSUPP (102)` — alongside `ENODEV`/`EINVAL`/
//! `ENOTTY` while never excusing `EIO (5)` or `ENOSPC (28)`; `Astream.UdsOwn.TlaEnotsupDirFlushClass`).

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
#[path = "enotsup_dir_flush_class_island.rs"]
mod enotsup_dir_flush_class_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn uo_err_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn uo_fls_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use enotsup_dir_flush_class_island::{uo_err_clamp, uo_fls_advance};

/// POSIX errno ceiling (`255`).
pub const MAX_DIR_ERRNO: u64 = 255;

contract_fn! {
    /// Verified tolerated `dir_flush_unavailable` match (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `uo_flush_tolerated_isl`.
    #[must_use]
    pub const fn uo_flush_tolerated(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct DirFlushClassifier {
    classified: u64,
}

impl DirFlushClassifier {
    #[must_use]
    pub const fn new() -> Self {
        Self { classified: 0 }
    }

    pub fn is_dir_flush_unavailable(&mut self, darwin_errno: u64, is_apple: bool) -> bool {
        self.classified = uo_fls_advance(self.classified, self.classified.saturating_add(1));
        if darwin_errno > MAX_DIR_ERRNO {
            return false;
        }
        let code = uo_err_clamp(darwin_errno, MAX_DIR_ERRNO);
        let unavail = match code {
            1 | 2 | 13 | 22 | 102 => true, // EPERM, ENOENT, EACCES, EINVAL, EOPNOTSUPP
            19 | 25 | 45 if is_apple => true, // Darwin ENODEV, ENOTTY, ENOTSUP(45)
            _ => false,                    // EIO(5), ENOSPC(28), etc. NEVER tolerated
        };
        uo_flush_tolerated(if unavail { 1 } else { 0 }, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tolerates_darwin_enotsup_45_and_never_excuses_eio_or_enospc() {
        let mut c = DirFlushClassifier::new();
        assert!(c.is_dir_flush_unavailable(45, true));
        assert!(!c.is_dir_flush_unavailable(5, true));
        assert!(!c.is_dir_flush_unavailable(28, true));
    }
}
