// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `O_NONBLOCK` file-type verifier (`os.cordon`: opening with `O_NONBLOCK` so a named FIFO returns
//! immediately instead of hanging forever waiting for a writer, then rejecting anything other than
//! the expected regular-file or directory `S_IFMT` kind; `Astream.UdsOwn.TlaNonblockingFifoGuard`).

#[cfg(clean_islands)]
#[path = "nonblocking_fifo_guard_island.rs"]
mod nonblocking_fifo_guard_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn uo_ft_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn uo_opn_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use nonblocking_fifo_guard_island::{uo_ft_clamp, uo_opn_advance};

/// POSIX `S_IFMT` mask (`0o170000`).
pub const POSIX_S_IFMT: u64 = 0o170_000;
/// Regular file (`0o100000`).
pub const POSIX_S_IFREG: u64 = 0o100_000;
/// Directory (`0o040000`).
pub const POSIX_S_IFDIR: u64 = 0o040_000;

contract_fn! {
    /// Verified expected-filetype match (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `uo_is_regular_or_dir_isl`.
    #[must_use]
    pub const fn uo_is_regular_or_dir(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct FifoTypeGuard {
    opens_checked: u64,
}

impl FifoTypeGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self { opens_checked: 0 }
    }

    pub fn check_st_mode(&mut self, st_mode: u64, expect_dir: bool) -> bool {
        let kind = uo_ft_clamp(st_mode & POSIX_S_IFMT, POSIX_S_IFMT);
        self.opens_checked =
            uo_opn_advance(self.opens_checked, self.opens_checked.saturating_add(1));
        let ok = if expect_dir {
            kind == POSIX_S_IFDIR
        } else {
            kind == POSIX_S_IFREG
        };
        uo_is_regular_or_dir(if ok { 1 } else { 0 }, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_fifo_named_pipe_and_dir_file_confusion() {
        let mut g = FifoTypeGuard::new();
        assert!(g.check_st_mode(0o100_600, false));
        assert!(!g.check_st_mode(0o010_600, false)); // S_IFIFO
        assert!(!g.check_st_mode(0o040_700, false)); // dir passed to owner_private
        assert!(g.check_st_mode(0o040_700, true));
    }
}
