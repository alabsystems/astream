// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `Closer` zero-timeout guard, idempotent shutdown, & Apple `EINVAL` `socket_hung_up` poll
//! classifier (`evidence/manifest.toml` `broker.any-connection-closer` & `os.cordon`;
//! `Astream.Host.TlaCloserHalfClosedEinvalPollGuard`).
//!
//! Enforces the transport-erased `Closer` & `Subscription::set_read_timeout` OS cordon rules:
//! - `timeout_ms == 0` is refused `InvalidInput` BEFORE calling `setsockopt`,
//! - `Closer::close` is idempotent: the first close shuts down the duplicated descriptor to
//!   unpark blocked readers (`Ok(None)`), and any subsequent close is a pure no-op,
//! - On `setsockopt` failure, `socket_hung_up` (zero-wait `poll`) is consulted ONLY when
//!   `errno == EINVAL` (`22`): if hung up BOTH ways (`both_ways_hung_up == true`), nothing
//!   remains to bound so `Ok` is returned; a live or half-closed socket (`!both_ways_hung_up`)
//!   or any non-`EINVAL` errno keeps the OS error verbatim!

#[cfg(clean_islands)]
#[path = "closer_half_closed_einval_poll_guard_island.rs"]
mod closer_half_closed_einval_poll_guard_island;
#[cfg(clean_islands)]
pub use closer_half_closed_einval_poll_guard_island::{
    closer_close_count_clamp_b150, closer_timeout_epoch_advance_b150,
};

/// POSIX `EINVAL` (`22` on both Darwin and Linux).
pub const POSIX_EINVAL: u64 = 22;

#[cfg(not(clean_islands))]
/// Clamp underlying OS `shutdown` invocations to at most `max_shutdowns` (`1`).
#[must_use]
pub const fn closer_close_count_clamp_b150(cand_closes: u64, max_shutdowns: u64) -> u64 {
    if cand_closes < max_shutdowns {
        cand_closes
    } else {
        max_shutdowns
    }
}

#[cfg(not(clean_islands))]
/// Advance validated timeout-configuration epoch monotonically.
#[must_use]
pub const fn closer_timeout_epoch_advance_b150(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `setsockopt` returned `EINVAL` (`22`) AND zero-wait `poll` confirmed hangup both ways.
    #[must_use]
    pub const fn einval_excused_by_full_hangup_b150(
        errno_code: u64,
        einval_code: u64,
        both_ways_hung_up: bool,
    ) -> bool
    clauses [ensures result == (errno_code == einval_code && both_ways_hung_up)]
    {
        errno_code == einval_code && both_ways_hung_up
    }
}

/// Decision for `Closer` timeout setting and idempotent shutdown.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CloserCordonDecision {
    RefusedZeroTimeoutInvalidInput,
    AppliedSocketTimeout {
        epoch: u64,
    },
    ExcusedEinvalOnFullHangup {
        epoch: u64,
    },
    PropagatedSetsockoptError {
        errno_code: u64,
        polled_hangup: bool,
    },
    IssuedKernelShutdownOnce,
    NoOpAlreadyClosed,
}

/// Tracks idempotent `Closer` shutdown state and timeout configuration epoch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CloserSocketCordonGuard {
    shutdown_count: u64,
    timeout_epoch: u64,
}

impl CloserSocketCordonGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            shutdown_count: 0,
            timeout_epoch: 0,
        }
    }

    #[must_use]
    pub const fn shutdown_count(&self) -> u64 {
        closer_close_count_clamp_b150(self.shutdown_count, 1)
    }

    /// Execute idempotent `Closer::close()`.
    pub fn close(&mut self) -> CloserCordonDecision {
        if self.shutdown_count >= 1 {
            return CloserCordonDecision::NoOpAlreadyClosed;
        }
        self.shutdown_count =
            closer_close_count_clamp_b150(self.shutdown_count.saturating_add(1), 1);
        CloserCordonDecision::IssuedKernelShutdownOnce
    }

    /// Classify `set_read_timeout` / `set_write_timeout` outcome.
    pub fn classify_set_timeout(
        &mut self,
        timeout_ms: u64,
        setsockopt_errno: Option<u64>,
        both_ways_hung_up: bool,
    ) -> CloserCordonDecision {
        if timeout_ms == 0 {
            return CloserCordonDecision::RefusedZeroTimeoutInvalidInput;
        }
        match setsockopt_errno {
            None => {
                let next = self.timeout_epoch.saturating_add(1);
                self.timeout_epoch = closer_timeout_epoch_advance_b150(self.timeout_epoch, next);
                CloserCordonDecision::AppliedSocketTimeout {
                    epoch: self.timeout_epoch,
                }
            }
            Some(errno_code) => {
                let should_poll = errno_code == POSIX_EINVAL;
                if einval_excused_by_full_hangup_b150(
                    errno_code,
                    POSIX_EINVAL,
                    should_poll && both_ways_hung_up,
                ) {
                    let next = self.timeout_epoch.saturating_add(1);
                    self.timeout_epoch =
                        closer_timeout_epoch_advance_b150(self.timeout_epoch, next);
                    CloserCordonDecision::ExcusedEinvalOnFullHangup {
                        epoch: self.timeout_epoch,
                    }
                } else {
                    CloserCordonDecision::PropagatedSetsockoptError {
                        errno_code,
                        polled_hangup: should_poll,
                    }
                }
            }
        }
    }
}

impl Default for CloserSocketCordonGuard {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_zero_timeout_polls_only_einval_excuses_only_full_hangup_and_closes_once() {
        let mut g = CloserSocketCordonGuard::new();
        assert_eq!(
            g.classify_set_timeout(0, None, false),
            CloserCordonDecision::RefusedZeroTimeoutInvalidInput
        );
        // Half-closed or live EINVAL keeps EINVAL:
        assert_eq!(
            g.classify_set_timeout(100, Some(POSIX_EINVAL), false),
            CloserCordonDecision::PropagatedSetsockoptError {
                errno_code: POSIX_EINVAL,
                polled_hangup: true,
            }
        );
        // Non-EINVAL (e.g. EBADF=9) never polls hangup and propagates:
        assert_eq!(
            g.classify_set_timeout(100, Some(9), true),
            CloserCordonDecision::PropagatedSetsockoptError {
                errno_code: 9,
                polled_hangup: false,
            }
        );
        // EINVAL on socket hung up both ways -> excused!
        assert_eq!(
            g.classify_set_timeout(100, Some(POSIX_EINVAL), true),
            CloserCordonDecision::ExcusedEinvalOnFullHangup { epoch: 1 }
        );
        assert_eq!(g.close(), CloserCordonDecision::IssuedKernelShutdownOnce);
        assert_eq!(g.close(), CloserCordonDecision::NoOpAlreadyClosed);
    }
}
