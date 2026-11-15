// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pre-`execve` file-descriptor hygiene verifier confirming only `stdin`/`stdout`/`stderr` (`0..=2`)
//! survive without `FD_CLOEXEC` into child PTY shells (`Astream.PtySig.TlaCloexecFdHygiene`).

#[cfg(clean_islands)]
#[path = "cloexec_fd_hygiene_island.rs"]
mod cloexec_fd_hygiene_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pty_fd_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pty_audit_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use cloexec_fd_hygiene_island::{pty_audit_advance, pty_fd_clamp};

/// Highest standard stdio descriptor (`2 = stderr`).
pub const MAX_STDIO_FD: u64 = 2;

contract_fn! {
    /// Verified zero-leaked-descriptor check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `pty_no_leaked_fds_isl`.
    #[must_use]
    pub const fn pty_no_leaked_fds(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct CloexecAuditor {
    spawns_audited: u64,
}

impl CloexecAuditor {
    #[must_use]
    pub const fn new() -> Self {
        Self { spawns_audited: 0 }
    }

    pub fn verify_highest_inherited_fd(&mut self, max_open_fd: u64) -> bool {
        let clamped = pty_fd_clamp(max_open_fd, 65_535);
        self.spawns_audited =
            pty_audit_advance(self.spawns_audited, self.spawns_audited.saturating_add(1));
        pty_no_leaked_fds(MAX_STDIO_FD, clamped)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accepts_stdio_only_inheritance_and_flags_leaked_socket_fd() {
        let mut a = CloexecAuditor::new();
        assert!(a.verify_highest_inherited_fd(2));
        assert!(!a.verify_highest_inherited_fd(7));
    }
}
