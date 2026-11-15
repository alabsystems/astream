// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! PTY foreground process-group (`tcgetpgrp`) transition observer distinguishing an idle login
//! shell (`fg_pgid == shell_pgid`) from a running foreground command or agent
//! (`Astream.PtySig.TlaFgPgrpObserver`).

#[cfg(clean_islands)]
#[path = "fg_pgrp_observer_island.rs"]
mod fg_pgrp_observer_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pty_pgrp_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pty_fg_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use fg_pgrp_observer_island::{pty_fg_advance, pty_pgrp_clamp};

/// Maximum tracked POSIX process-group identifier (`4_194_304`).
pub const MAX_POSIX_PGID: u64 = 4_194_304;

contract_fn! {
    /// Verified active foreground child check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `pty_child_active_isl`.
    #[must_use]
    pub const fn pty_child_active(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone)]
pub struct FgPgrpTracker {
    shell_pgid: u64,
    current_fg_pgid: u64,
    transitions: u64,
}

impl FgPgrpTracker {
    #[must_use]
    pub const fn new(shell_pgid: u64) -> Self {
        let clamped = pty_pgrp_clamp(shell_pgid, MAX_POSIX_PGID);
        Self {
            shell_pgid: clamped,
            current_fg_pgid: clamped,
            transitions: 0,
        }
    }

    pub fn update_fg_pgid(&mut self, fg_pgid: u64) -> bool {
        if fg_pgid == 0 || fg_pgid > MAX_POSIX_PGID {
            return false;
        }
        let clamped = pty_pgrp_clamp(fg_pgid, MAX_POSIX_PGID);
        if clamped != self.current_fg_pgid {
            self.current_fg_pgid = clamped;
            self.transitions = pty_fg_advance(self.transitions, self.transitions.saturating_add(1));
        }
        let child_running = clamped != 0 && clamped != self.shell_pgid;
        pty_child_active(if child_running { 1 } else { 0 }, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reports_foreground_child_only_when_fg_pgid_differs_from_shell() {
        let mut t = FgPgrpTracker::new(1000);
        assert!(!t.update_fg_pgid(1000));
        assert!(t.update_fg_pgid(2042));
        assert!(!t.update_fg_pgid(1000));
    }
}
