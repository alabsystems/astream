// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Ticket-ordered `.cargo-build` lock coordinator preventing `targo` writer starvation across
//! concurrent `aterm` sessions (`Astream.Worktree.TlaBuildLockFairness`).

#[cfg(clean_islands)]
#[path = "build_lock_fairness_island.rs"]
mod build_lock_fairness_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lock_waiters_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lock_serving_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use build_lock_fairness_island::{lock_serving_advance, lock_waiters_clamp};

/// Maximum queued `.cargo-build` ticket waiters.
pub const MAX_BUILD_LOCK_WAITERS: u64 = 128;

contract_fn! {
    /// Verified ticket turn check (`threshold <= observed`, i.e. `ticket <= now_serving`),
    /// linked via `clean-kernel-defeq` to `lock_turn_reached_isl`.
    #[must_use]
    pub const fn lock_turn_reached(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Fair Lamport/Anderson ticket lock state machine for shared `.cargo-build` target directories.
#[derive(Debug, Clone, Default)]
pub struct BuildTicketLock {
    next_ticket: u64,
    now_serving: u64,
}

impl BuildTicketLock {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            next_ticket: 0,
            now_serving: 0,
        }
    }

    pub fn issue_ticket(&mut self) -> Result<u64, &'static str> {
        let cap = lock_waiters_clamp(MAX_BUILD_LOCK_WAITERS, MAX_BUILD_LOCK_WAITERS);
        if self.next_ticket.saturating_sub(self.now_serving) >= cap {
            return Err("too many build lock waiters");
        }
        let Some(next) = self.next_ticket.checked_add(1) else {
            return Err("ticket counter exhausted");
        };
        let t = self.next_ticket;
        self.next_ticket = next;
        Ok(t)
    }

    #[must_use]
    pub const fn holds_lock(&self, ticket: u64) -> bool {
        ticket == self.now_serving && lock_turn_reached(self.now_serving, ticket)
    }

    pub fn release_ticket(&mut self, ticket: u64) -> Result<u64, &'static str> {
        if ticket != self.now_serving {
            return Err("ticket is not currently holding build lock");
        }
        self.now_serving =
            lock_serving_advance(self.now_serving, self.now_serving.saturating_add(1));
        Ok(self.now_serving)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ticket_lock_grants_strict_fifo_ownership_without_starvation() {
        let mut lk = BuildTicketLock::new();
        let t0 = lk.issue_ticket().unwrap();
        let t1 = lk.issue_ticket().unwrap();
        assert!(lk.holds_lock(t0));
        assert!(!lk.holds_lock(t1));
        assert!(lk.release_ticket(t1).is_err());
        lk.release_ticket(t0).unwrap();
        assert!(lk.holds_lock(t1));
    }
}
