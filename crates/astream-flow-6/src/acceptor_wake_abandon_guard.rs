// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `broker.blocking-accept` shutdown wakeup dialer and bounded stranger-abandonment guard
//! (`Astream.Broker.TlaAcceptorWakeAbandonGuard`, Island #279).
//!
//! Models the shutdown contract of `BrokerHandle` over blocking Unix (`<socket>.wake` hard
//! link) and TCP acceptors:
//! - If both `<socket>` and `<socket>.wake` were removed or now belong to another inode,
//!   shutdown dials nobody and abandons the parked acceptor immediately, leaving any
//!   replacement broker's socket paths intact while still releasing the log lock.
//! - Otherwise, shutdown dials at most `MAX_SHUTDOWN_WAKE_DIALS` (`10`) times until THIS
//!   listener's own acceptor answers; if a stranger (e.g. a `127.0.0.1:P` socket shadowing
//!   `0.0.0.0:P`) consumes all `10` dials without our acceptor waking, shutdown abandons
//!   cleanly at `10` dials instead of spinning forever.

#[cfg(clean_islands)]
#[path = "acceptor_wake_abandon_guard_island.rs"]
mod acceptor_wake_abandon_guard_island;
#[cfg(clean_islands)]
pub use acceptor_wake_abandon_guard_island::{acceptor_abandoned_advance, acceptor_dial_clamp};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn acceptor_dial_clamp(dials: u64, max_dials: u64) -> u64 {
    if dials < max_dials {
        dials
    } else {
        max_dials
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn acceptor_abandoned_advance(prev: u64, next: u64) -> u64 {
    if prev < next {
        next
    } else {
        prev
    }
}

/// Maximum unanswered wakeup dials before abandoning a parked acceptor (`10`, `broker.blocking-accept`).
pub const MAX_SHUTDOWN_WAKE_DIALS: u64 = 10;

contract_fn! {
    /// Verified check `max_dials <= unanswered_dials`, linked via `clean-kernel-defeq` to
    /// `acceptor_should_abandon_isl`.
    #[must_use]
    pub const fn acceptor_should_abandon(unanswered_dials: u64, max_dials: u64) -> bool
    clauses [ensures result == (max_dials <= unanswered_dials)]
    {
        max_dials <= unanswered_dials
    }
}

/// Ownership state of the socket / `.wake` inode at listener shutdown.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WakeTargetOwnership {
    /// Primary socket or `.wake` hard link still names our listener's inode.
    OwnedByThisListener,
    /// Both names are gone or replaced by a different inode; dial nobody!
    MissingOrForeignInode,
}

/// Shutdown step action produced by [`AcceptorWakeGuard`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShutdownWakeStep {
    /// Perform wakeup dial `dial_number` (`1..=max_dials`).
    DialOnce { dial_number: u64 },
    /// Our own acceptor observed the exit signal and woke cleanly; join thread & unlink owned `.wake`.
    JoinedCleanly { dials_used: u64, unlink_wake: bool },
    /// Abandoned parked acceptor (leaving stranger socket untouched) and released log lock.
    Abandoned {
        dials_used: u64,
        total_abandoned: u64,
        release_log_lock: bool,
    },
}

/// Stateful shutdown wakeup guard for a blocking listener acceptor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AcceptorWakeGuard {
    max_dials: u64,
    unanswered_dials: u64,
    abandoned_count: u64,
    finished: bool,
}

impl Default for AcceptorWakeGuard {
    fn default() -> Self {
        Self::new(MAX_SHUTDOWN_WAKE_DIALS)
    }
}

impl AcceptorWakeGuard {
    #[must_use]
    pub const fn new(max_dials: u64) -> Self {
        let cap = if max_dials == 0 {
            1
        } else {
            acceptor_dial_clamp(max_dials, 64)
        };
        Self {
            max_dials: cap,
            unanswered_dials: 0,
            abandoned_count: 0,
            finished: false,
        }
    }

    #[must_use]
    pub const fn max_dials(&self) -> u64 {
        self.max_dials
    }

    #[must_use]
    pub const fn is_finished(&self) -> bool {
        self.finished
    }

    #[must_use]
    pub const fn unanswered_dials(&self) -> u64 {
        self.unanswered_dials
    }

    #[must_use]
    pub const fn abandoned_count(&self) -> u64 {
        self.abandoned_count
    }

    /// Decide the next shutdown step given `ownership` and whether `own_acceptor_exited`.
    pub fn next_step(
        &mut self,
        ownership: WakeTargetOwnership,
        own_acceptor_exited: bool,
    ) -> ShutdownWakeStep {
        if own_acceptor_exited {
            self.finished = true;
            return ShutdownWakeStep::JoinedCleanly {
                dials_used: self.unanswered_dials,
                unlink_wake: ownership == WakeTargetOwnership::OwnedByThisListener,
            };
        }

        if ownership == WakeTargetOwnership::MissingOrForeignInode
            || acceptor_should_abandon(self.unanswered_dials, self.max_dials)
        {
            if !self.finished {
                self.finished = true;
                self.abandoned_count = acceptor_abandoned_advance(
                    self.abandoned_count,
                    self.abandoned_count.saturating_add(1),
                );
            }
            return ShutdownWakeStep::Abandoned {
                dials_used: self.unanswered_dials,
                total_abandoned: self.abandoned_count,
                release_log_lock: true,
            };
        }

        let next_dials =
            acceptor_dial_clamp(self.unanswered_dials.saturating_add(1), self.max_dials);
        self.unanswered_dials = next_dials;
        ShutdownWakeStep::DialOnce {
            dial_number: next_dials,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stranger_taking_every_dial_abandons_after_exactly_ten_dials_and_releases_lock() {
        let mut g = AcceptorWakeGuard::default();
        for expected in 1..=10 {
            assert_eq!(
                g.next_step(WakeTargetOwnership::OwnedByThisListener, false),
                ShutdownWakeStep::DialOnce {
                    dial_number: expected,
                }
            );
        }
        assert_eq!(
            g.next_step(WakeTargetOwnership::OwnedByThisListener, false),
            ShutdownWakeStep::Abandoned {
                dials_used: 10,
                total_abandoned: 1,
                release_log_lock: true,
            }
        );
    }

    #[test]
    fn foreign_inode_dials_nobody_and_leaves_stranger_socket_untouched() {
        let mut g = AcceptorWakeGuard::default();
        assert_eq!(
            g.next_step(WakeTargetOwnership::MissingOrForeignInode, false),
            ShutdownWakeStep::Abandoned {
                dials_used: 0,
                total_abandoned: 1,
                release_log_lock: true,
            }
        );
        assert_eq!(g.unanswered_dials(), 0);
    }
}
