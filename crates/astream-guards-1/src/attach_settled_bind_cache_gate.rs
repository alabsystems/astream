// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Lock-free `Attach` settled-bind side-table fast path for a ring that names one principal in
//! several `rw,p=` grants, as `aterm`'s node ring does (four of the eight rules of
//! `GrantCeiling::aterm_node_ring`; `evidence/manifest.toml` `broker.attach-settled-bind`;
//! `Astream.Broker.TlaAttachSettledBindCacheGate`).
//!
//! Models the `binds_settled` optimization in `astream-broker`:
//! - When a ring of N `rw,p=<principal>` grants of one principal attaches, the first grant
//!   binds via `1` writer round trip (copying the binding into the side table AFTER head
//!   promotion and BEFORE sending acks, so the remaining N - 1 `rw,p=` grants settle in `0`
//!   extra round trips), and every subsequent reconnect settles all N `rw,p=` grants with `0`
//!   writer round trips and without acquiring the log mutex (the test below takes N = 4).
//! - A principal collision (`different_principal_on_same_producer_id`) ALWAYS routes to the writer
//!   to return the canonical collision refusal, and a first-time principal on a poisoned log fails
//!   at the writer (`RefusedBindNotPersistedLogPoisoned`).

#[cfg(clean_islands)]
#[path = "attach_settled_bind_cache_gate_island.rs"]
mod attach_settled_bind_cache_gate_island;
#[cfg(clean_islands)]
pub use attach_settled_bind_cache_gate_island::{
    binds_settled_count_advance_b145, writer_round_trips_clamp_b145,
};

/// Maximum writer round trips needed for a single-principal multi-grant ring (`1`).
pub const MAX_SINGLE_PRINCIPAL_RING_RT: u64 = 1;

#[cfg(not(clean_islands))]
/// Monotonically advance `BrokerStats::binds_settled`.
#[must_use]
pub const fn binds_settled_count_advance_b145(cur_settled: u64, cand_settled: u64) -> u64 {
    if cur_settled < cand_settled {
        cand_settled
    } else {
        cur_settled
    }
}

#[cfg(not(clean_islands))]
/// Clamp single-principal connection round trips to `max_conn_rt`.
#[must_use]
pub const fn writer_round_trips_clamp_b145(cand_rt: u64, max_conn_rt: u64) -> u64 {
    if cand_rt < max_conn_rt {
        cand_rt
    } else {
        max_conn_rt
    }
}

contract_fn! {
    /// True iff `producer_id` is in the side table for the exact same `principal_hash` and its
    /// `/a/bind` offset is strictly below `visible_head`.
    #[must_use]
    pub const fn bind_fast_path_settled_b145(
        in_side_table: bool,
        same_principal: bool,
        bind_offset_below_visible_head: bool,
    ) -> bool
    clauses [ensures result == (in_side_table && same_principal && bind_offset_below_visible_head)]
    {
        in_side_table && same_principal && bind_offset_below_visible_head
    }
}

/// Resolution path for an `rw,p=<principal>` grant during `Attach`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AttachBindDecision {
    SettledFromSideTableZeroRoundTrip {
        binds_settled_total: u64,
    },
    BoundViaWriterOneRoundTrip {
        bind_offset: u64,
        conn_round_trips: u64,
    },
    RefusedPrincipalCollisionAtWriter,
    RefusedBindNotPersistedLogPoisoned,
}

/// Single-slot model of the broker's lock-free `settled_binds` side table for a `producer_id`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SettledBindSlot {
    bound_principal_hash: Option<(u64, u64)>, // (principal_hash, bind_offset)
    binds_settled_total: u64,
    conn_round_trips: u64,
}

impl SettledBindSlot {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            bound_principal_hash: None,
            binds_settled_total: 0,
            conn_round_trips: 0,
        }
    }

    pub const fn begin_new_connection(&mut self) {
        self.conn_round_trips = 0;
    }

    pub fn attach_rw_bound_grant(
        &mut self,
        principal_hash: u64,
        visible_head: u64,
        log_poisoned: bool,
    ) -> (AttachBindDecision, u64) {
        if let Some((existing_hash, bind_off)) = self.bound_principal_hash {
            let same = existing_hash == principal_hash;
            let below_head = bind_off < visible_head;
            if bind_fast_path_settled_b145(true, same, below_head) {
                let next = self.binds_settled_total.saturating_add(1);
                self.binds_settled_total =
                    binds_settled_count_advance_b145(self.binds_settled_total, next);
                return (
                    AttachBindDecision::SettledFromSideTableZeroRoundTrip {
                        binds_settled_total: self.binds_settled_total,
                    },
                    visible_head,
                );
            }
            if !same {
                return (
                    AttachBindDecision::RefusedPrincipalCollisionAtWriter,
                    visible_head,
                );
            }
        }
        if log_poisoned {
            return (
                AttachBindDecision::RefusedBindNotPersistedLogPoisoned,
                visible_head,
            );
        }
        // First-time principal: 1 writer round trip appends `/a/bind` at `visible_head`, promotes
        // `visible_head + 1`, and copies into side table BEFORE sending acks!
        let bind_offset = visible_head;
        let new_head = visible_head.saturating_add(1);
        self.bound_principal_hash = Some((principal_hash, bind_offset));
        let next_rt = self.conn_round_trips.saturating_add(1);
        self.conn_round_trips =
            writer_round_trips_clamp_b145(next_rt, MAX_SINGLE_PRINCIPAL_RING_RT);
        (
            AttachBindDecision::BoundViaWriterOneRoundTrip {
                bind_offset,
                conn_round_trips: self.conn_round_trips,
            },
            new_head,
        )
    }
}

impl Default for SettledBindSlot {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn four_rw_grants_take_one_round_trip_on_first_conn_and_zero_on_reconnect() {
        let mut slot = SettledBindSlot::new();
        let mut head = 2;
        // Grant #1 binds via writer (1 round trip, head 2 -> 3):
        let (d1, h1) = slot.attach_rw_bound_grant(0xA7E4, head, false);
        head = h1;
        assert_eq!(
            d1,
            AttachBindDecision::BoundViaWriterOneRoundTrip {
                bind_offset: 2,
                conn_round_trips: 1
            }
        );
        // Grants #2..=#4 settle from side table (3 settled, still 1 round trip):
        for expected_settled in 1..=3 {
            let (d, h) = slot.attach_rw_bound_grant(0xA7E4, head, false);
            head = h;
            assert_eq!(
                d,
                AttachBindDecision::SettledFromSideTableZeroRoundTrip {
                    binds_settled_total: expected_settled
                }
            );
        }
        // Reconnect settles all 4 grants with 0 round trips, even if log later poisons:
        slot.begin_new_connection();
        let (d_reconn, _) = slot.attach_rw_bound_grant(0xA7E4, head, true);
        assert_eq!(
            d_reconn,
            AttachBindDecision::SettledFromSideTableZeroRoundTrip {
                binds_settled_total: 4
            }
        );
        assert_eq!(slot.conn_round_trips, 0);
    }
}
