// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Child PTY `0..=2` stdio fd preservation & single-`waitpid` PID-reuse guard
//! (`Astream.Host.TlaPtyStdioFdReapPidGuard`).
//!
//! Eliminates two POSIX process-lifecycle bugs:
//! 1. **Low PTY fd preservation (`0..=2`)**: when `openpty` allocates `slave_fd` inside `0..=2`
//!    (e.g. daemon with closed stdio), post-`dup2` cleanup MUST NOT `close(slave_fd)` (which would
//!    sever the child's newly wired `stdin`/`stdout`/`stderr`!), closing ONLY `slave_fd >= 3`.
//! 2. **At-most-once `waitpid` reap**: once a child PID has been reaped, its exit code is cached
//!    so a second `reap()` NEVER invokes `waitpid(pid, ...)` against an OS-recycled PID!

#[cfg(clean_islands)]
#[path = "pty_stdio_fd_reap_pid_guard_island.rs"]
mod pty_stdio_fd_reap_pid_guard_island;
#[cfg(clean_islands)]
pub use pty_stdio_fd_reap_pid_guard_island::{
    child_reap_epoch_advance_b142, pty_slave_fd_floor_advance_b142,
};

/// Minimum file descriptor above standard `STDIN(0)`, `STDOUT(1)`, `STDERR(2)`.
pub const FIRST_NON_STDIO_FD: u64 = 3;

#[cfg(not(clean_islands))]
/// Ensure any closeable post-`dup2` descriptor is at least `min_safe_fd` (`3`).
#[must_use]
pub const fn pty_slave_fd_floor_advance_b142(min_safe_fd: u64, raw_fd: u64) -> u64 {
    if min_safe_fd < raw_fd {
        raw_fd
    } else {
        min_safe_fd
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the child-lifecycle reap epoch.
#[must_use]
pub const fn child_reap_epoch_advance_b142(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `waitpid` may legally be invoked (`child_spawned && !already_reaped && child_pid > 0`).
    #[must_use]
    pub const fn waitpid_reap_admissible_b142(
        child_spawned: bool,
        already_reaped: bool,
        child_pid: u64,
    ) -> bool
    clauses [ensures result == (child_spawned && !already_reaped && child_pid > 0)]
    {
        child_spawned && !already_reaped && child_pid > 0
    }
}

/// Post-`dup2(slave_fd, 0..=2)` descriptor action in the child pre-exec hook.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SlaveFdPostDupAction {
    /// `slave_fd` was `0`, `1`, or `2`: keep it open because it IS one of the child's stdio fds!
    KeepStdioFdOpen { stdio_fd: u64 },
    /// `slave_fd >= 3`: safe and required to close the extra descriptor after wiring `0..=2`.
    CloseExtraDescriptor { close_fd: u64 },
}

/// Decision for `ChildHandle::reap()`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChildReapAction {
    IssueKernelWaitpid { child_pid: u64 },
    ReturnCachedExitCode { exit_code: i32, reap_epoch: u64 },
    RefusedUnspawnedChild,
}

#[must_use]
pub const fn classify_post_dup2_slave_fd(raw_slave_fd: u64) -> SlaveFdPostDupAction {
    if raw_slave_fd < FIRST_NON_STDIO_FD {
        SlaveFdPostDupAction::KeepStdioFdOpen {
            stdio_fd: raw_slave_fd,
        }
    } else {
        SlaveFdPostDupAction::CloseExtraDescriptor {
            close_fd: pty_slave_fd_floor_advance_b142(FIRST_NON_STDIO_FD, raw_slave_fd),
        }
    }
}

/// Single-reap PID lifecycle tracker preventing recycled-PID `waitpid` races.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ChildReapGuard {
    child_pid: u64,
    child_spawned: bool,
    already_reaped: bool,
    cached_exit_code: i32,
    reap_epoch: u64,
}

impl ChildReapGuard {
    #[must_use]
    pub const fn spawned(child_pid: u64) -> Self {
        Self {
            child_pid,
            child_spawned: child_pid > 0,
            already_reaped: false,
            cached_exit_code: 0,
            reap_epoch: 0,
        }
    }

    #[must_use]
    pub const fn plan_reap(&self) -> ChildReapAction {
        if waitpid_reap_admissible_b142(self.child_spawned, self.already_reaped, self.child_pid) {
            ChildReapAction::IssueKernelWaitpid {
                child_pid: self.child_pid,
            }
        } else if self.already_reaped {
            ChildReapAction::ReturnCachedExitCode {
                exit_code: self.cached_exit_code,
                reap_epoch: self.reap_epoch,
            }
        } else {
            ChildReapAction::RefusedUnspawnedChild
        }
    }

    pub fn record_waitpid_exit(&mut self, exit_code: i32, cand_epoch: u64) -> ChildReapAction {
        self.reap_epoch = child_reap_epoch_advance_b142(self.reap_epoch, cand_epoch);
        self.already_reaped = true;
        self.cached_exit_code = exit_code;
        ChildReapAction::ReturnCachedExitCode {
            exit_code,
            reap_epoch: self.reap_epoch,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preserves_low_stdio_slave_fd_and_prevents_second_waitpid_on_recycled_pid() {
        assert_eq!(
            classify_post_dup2_slave_fd(2),
            SlaveFdPostDupAction::KeepStdioFdOpen { stdio_fd: 2 }
        );
        assert_eq!(
            classify_post_dup2_slave_fd(7),
            SlaveFdPostDupAction::CloseExtraDescriptor { close_fd: 7 }
        );

        let mut g = ChildReapGuard::spawned(42_100);
        assert_eq!(
            g.plan_reap(),
            ChildReapAction::IssueKernelWaitpid { child_pid: 42_100 }
        );
        g.record_waitpid_exit(0, 1);
        // Second reap returns cached exit code without touching kernel `waitpid(42_100)`!
        assert_eq!(
            g.plan_reap(),
            ChildReapAction::ReturnCachedExitCode {
                exit_code: 0,
                reap_epoch: 1
            }
        );
    }
}
