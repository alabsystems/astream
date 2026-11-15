// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Exclusive `/a/bind` endpoint ownership & stale-socket fencing arbiter
//! (`Astream.Broker.TlaBindOwnerLeaseArbiter`).
//!
//! Arbitrates `/a/bind/<name>` ownership in `astream-broker`: rejects conflicting bind attempts
//! while an active connection still holds the name, transfers ownership cleanly after disconnect
//! release, and advances `bind_epoch` monotonically on every ownership transition.

#[cfg(clean_islands)]
#[path = "bind_owner_lease_arbiter_island.rs"]
mod bind_owner_lease_arbiter_island;
#[cfg(clean_islands)]
pub use bind_owner_lease_arbiter_island::{bind_conflicts_clamp_b114, bind_epoch_advance_b114};

#[cfg(not(clean_islands))]
/// Clamp rejected `/a/bind` ownership-conflict count to `max_conflicts`.
#[must_use]
pub const fn bind_conflicts_clamp_b114(cand_conflicts: u64, max_conflicts: u64) -> u64 {
    if cand_conflicts < max_conflicts {
        cand_conflicts
    } else {
        max_conflicts
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the `/a/bind` ownership fencing epoch.
#[must_use]
pub const fn bind_epoch_advance_b114(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `conflicts` remains strictly below `max_conflicts`.
    #[must_use]
    pub const fn bind_conflict_below_cap_b114(conflicts: u64, max_conflicts: u64) -> bool
    clauses [ensures result == (conflicts < max_conflicts)]
    {
        conflicts < max_conflicts
    }
}

/// Outcome of attempting to claim `/a/bind` for a named endpoint.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BindClaimOutcome {
    Bound {
        owner_conn: u64,
        bind_epoch: u64,
    },
    IdempotentRebind {
        owner_conn: u64,
        bind_epoch: u64,
    },
    ConflictHeldByPeer {
        holder_conn: u64,
        bind_epoch: u64,
        conflicts: u64,
    },
}

/// Ownership arbiter for a logical `/a/bind` fabric name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BindOwnerLeaseArbiter {
    holder_conn: Option<u64>,
    bind_epoch: u64,
    conflicts: u64,
    max_conflicts: u64,
}

impl BindOwnerLeaseArbiter {
    #[must_use]
    pub const fn new(max_conflicts: u64) -> Self {
        let cap = if max_conflicts == 0 {
            1024
        } else {
            max_conflicts
        };
        Self {
            holder_conn: None,
            bind_epoch: 0,
            conflicts: 0,
            max_conflicts: cap,
        }
    }

    #[must_use]
    pub const fn holder_conn(&self) -> Option<u64> {
        self.holder_conn
    }

    #[must_use]
    pub const fn bind_epoch(&self) -> u64 {
        self.bind_epoch
    }

    /// Claim ownership for `conn_id` if currently unbound or already owned by `conn_id`.
    pub fn try_claim(&mut self, conn_id: u64) -> BindClaimOutcome {
        match self.holder_conn {
            None => {
                let next_ep = self.bind_epoch.saturating_add(1);
                self.bind_epoch = bind_epoch_advance_b114(self.bind_epoch, next_ep);
                self.holder_conn = Some(conn_id);
                BindClaimOutcome::Bound {
                    owner_conn: conn_id,
                    bind_epoch: self.bind_epoch,
                }
            }
            Some(cur) if cur == conn_id => BindClaimOutcome::IdempotentRebind {
                owner_conn: cur,
                bind_epoch: self.bind_epoch,
            },
            Some(cur) => {
                if bind_conflict_below_cap_b114(self.conflicts, self.max_conflicts) {
                    let cand = self.conflicts.saturating_add(1);
                    self.conflicts = bind_conflicts_clamp_b114(cand, self.max_conflicts);
                }
                BindClaimOutcome::ConflictHeldByPeer {
                    holder_conn: cur,
                    bind_epoch: self.bind_epoch,
                    conflicts: self.conflicts,
                }
            }
        }
    }

    /// Release binding iff `conn_id` is the active owner.
    pub fn release_on_disconnect(&mut self, conn_id: u64) -> bool {
        if self.holder_conn == Some(conn_id) {
            self.holder_conn = None;
            let next_ep = self.bind_epoch.saturating_add(1);
            self.bind_epoch = bind_epoch_advance_b114(self.bind_epoch, next_ep);
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fences_rival_claim_until_owner_disconnects() {
        let mut arb = BindOwnerLeaseArbiter::new(16);
        assert_eq!(
            arb.try_claim(10),
            BindClaimOutcome::Bound {
                owner_conn: 10,
                bind_epoch: 1,
            }
        );
        assert_eq!(
            arb.try_claim(20),
            BindClaimOutcome::ConflictHeldByPeer {
                holder_conn: 10,
                bind_epoch: 1,
                conflicts: 1,
            }
        );
        assert!(arb.release_on_disconnect(10));
        assert_eq!(
            arb.try_claim(20),
            BindClaimOutcome::Bound {
                owner_conn: 20,
                bind_epoch: 3,
            }
        );
    }
}
