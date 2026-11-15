// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Released-lock post-stop `retain_before` / `publish` / `close_clean` latch guard
//! (`evidence/manifest.toml` `broker.unclean-generation`;
//! `Astream.Broker.TlaUncleanStopReleaseLatchGuard`).
//!
//! Enforces the critical post-stop successor-safety invariant:
//! - When a `Broker` stops (either cleanly via `close_clean` or under `arm_unclean_stop`, which
//!   skips `close_clean` and leaves `<log>.id` untouched while releasing the lock), the log
//!   handle latches `lock_released = true`,
//! - Once `lock_released == true`, EVERY mutating or sidecar-replacing call (`publish`, `commit`,
//!   `close_clean`, `retain_before`, `retain_before_carrying_state`) is refused naming the
//!   release so a stopped predecessor can NEVER rename a compacted copy over a successor's log!

#[cfg(clean_islands)]
#[path = "unclean_stop_release_latch_guard_island.rs"]
mod unclean_stop_release_latch_guard_island;
#[cfg(clean_islands)]
pub use unclean_stop_release_latch_guard_island::{
    released_flag_clamp_b152, stop_epoch_advance_b152,
};

#[cfg(not(clean_islands))]
/// Clamp `released_code` (`0` = held, `1` = released) to `max_code` (`1`).
#[must_use]
pub const fn released_flag_clamp_b152(cand_code: u64, max_code: u64) -> u64 {
    if cand_code < max_code {
        cand_code
    } else {
        max_code
    }
}

#[cfg(not(clean_islands))]
/// Advance stop/latch epoch monotonically.
#[must_use]
pub const fn stop_epoch_advance_b152(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `released_code == 0` (the `BrokerLog` still holds its exclusive lock).
    #[must_use]
    pub const fn log_mutation_permitted_while_locked_b152(released_code: u64) -> bool
    clauses [ensures result == (released_code == 0)]
    {
        released_code == 0
    }
}

/// Outcome of broker stop or post-stop mutation/compaction check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReleasedLockDecision {
    AdmittedWhileLockHeld,
    StoppedCleanAndLatchedReleased {
        rewrote_clean_sidecar: bool,
        stop_epoch: u64,
    },
    StoppedUncleanSeamAndLatchedReleased {
        rewrote_clean_sidecar: bool,
        stop_epoch: u64,
    },
    RefusedLogLockReleased,
}

/// Sticky lock-release latch protecting successor logs from stopped handles.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UncleanStopReleaseLatch {
    released_code: u64,
    stop_epoch: u64,
}

impl UncleanStopReleaseLatch {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            released_code: 0,
            stop_epoch: 0,
        }
    }

    #[must_use]
    pub const fn is_released(&self) -> bool {
        self.released_code != 0
    }

    /// Gate `publish`, `commit`, `close_clean`, `retain_before`, and `retain_before_carrying_state`.
    #[must_use]
    pub const fn check_mutating_op(&self) -> ReleasedLockDecision {
        if log_mutation_permitted_while_locked_b152(self.released_code) {
            ReleasedLockDecision::AdmittedWhileLockHeld
        } else {
            ReleasedLockDecision::RefusedLogLockReleased
        }
    }

    /// Stop the broker (`unclean_seam == true` skips rewriting `<log>.id` while STILL latching shut!).
    pub fn on_broker_stop(&mut self, unclean_seam: bool) -> ReleasedLockDecision {
        if self.released_code != 0 {
            return ReleasedLockDecision::RefusedLogLockReleased;
        }
        self.released_code = released_flag_clamp_b152(1, 1);
        let next = self.stop_epoch.saturating_add(1);
        self.stop_epoch = stop_epoch_advance_b152(self.stop_epoch, next);
        if unclean_seam {
            ReleasedLockDecision::StoppedUncleanSeamAndLatchedReleased {
                rewrote_clean_sidecar: false,
                stop_epoch: self.stop_epoch,
            }
        } else {
            ReleasedLockDecision::StoppedCleanAndLatchedReleased {
                rewrote_clean_sidecar: true,
                stop_epoch: self.stop_epoch,
            }
        }
    }
}

impl Default for UncleanStopReleaseLatch {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unclean_stop_seam_leaves_sidecar_untouched_yet_latches_retain_before_and_publish_shut() {
        let mut l = UncleanStopReleaseLatch::new();
        assert_eq!(
            l.check_mutating_op(),
            ReleasedLockDecision::AdmittedWhileLockHeld
        );
        assert_eq!(
            l.on_broker_stop(true),
            ReleasedLockDecision::StoppedUncleanSeamAndLatchedReleased {
                rewrote_clean_sidecar: false,
                stop_epoch: 1,
            }
        );
        // Any subsequent retain_before or publish while a successor serves the log is refused!
        assert_eq!(
            l.check_mutating_op(),
            ReleasedLockDecision::RefusedLogLockReleased
        );
        assert_eq!(
            l.on_broker_stop(false),
            ReleasedLockDecision::RefusedLogLockReleased
        );
    }
}
