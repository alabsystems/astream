// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `Request::Stats` (`0x13`) fleet-root read capability & cross-fleet leak-isolation guard
//! (`evidence/manifest.toml` `broker.wire-stats`, `REQUIREMENTS R5`;
//! `Astream.Broker.TlaWireStatsFleetScopeIsolationGuard`).
//!
//! Enforces R5 multi-tenant `WireStats` authorization and sibling-fleet isolation:
//! - On a guarded broker, `Request::Stats { filter }` requires an attached non-expired read
//!   capability covering the WHOLE requested fleet `/f/<F>/>` (`covers_fleet_root == true`) or
//!   global root `/>`: unattached connections, narrow sub-fleet grants (`ro:/f/alpha/in/n1/>`),
//!   and cross-fleet grants (`grant_fleet_id != req_fleet_id`) are refused `ERR_UNAUTHORIZED`,
//! - Returned `producers` and `faces` rows include ONLY entries matching `req_fleet_id` (and
//!   never message bodies)!

#[cfg(clean_islands)]
#[path = "wire_stats_fleet_scope_isolation_guard_island.rs"]
mod wire_stats_fleet_scope_isolation_guard_island;
#[cfg(clean_islands)]
pub use wire_stats_fleet_scope_isolation_guard_island::{
    stats_query_epoch_advance_b154, stats_visible_rows_clamp_b154,
};

/// Upper bound on returned `faces` / `producers` rows per `WireStats` frame (`4_096`).
pub const MAX_WIRE_STATS_ROWS: u64 = 4_096;

#[cfg(not(clean_islands))]
/// Clamp returned `WireStats` row count to `MAX_WIRE_STATS_ROWS`.
#[must_use]
pub const fn stats_visible_rows_clamp_b154(cand_rows: u64, max_rows: u64) -> u64 {
    if cand_rows < max_rows {
        cand_rows
    } else {
        max_rows
    }
}

#[cfg(not(clean_islands))]
/// Advance authorized `Stats` query epoch monotonically.
#[must_use]
pub const fn stats_query_epoch_advance_b154(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff unguarded OR an attached live grant covers either root `/>` or the exact fleet root `/f/<F>/>`.
    #[must_use]
    pub const fn wire_stats_fleet_authorized_b154(
        broker_guarded: bool,
        grant_attached_live: bool,
        covers_global_root: bool,
        covers_whole_fleet_root: bool,
        grant_fleet_matches_req: bool,
    ) -> bool
    clauses [ensures result == (!broker_guarded || (grant_attached_live && (covers_global_root || (covers_whole_fleet_root && grant_fleet_matches_req))))]
    {
        !broker_guarded
            || (grant_attached_live
                && (covers_global_root || (covers_whole_fleet_root && grant_fleet_matches_req)))
    }
}

/// Authorization & row-scoping verdict for `Request::Stats`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WireStatsScopeDecision {
    AuthorizedScopedStats {
        scoped_producers: u64,
        scoped_faces: u64,
        query_epoch: u64,
    },
    RefusedUnauthorizedStats,
    IncludedSameFleetRow,
    ExcludedSiblingFleetRow,
}

/// Enforces fleet-root capability authorization and sibling-fleet row exclusion on `Stats`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WireStatsScopeGuard {
    broker_guarded: bool,
    query_epoch: u64,
}

impl WireStatsScopeGuard {
    #[must_use]
    pub const fn new(broker_guarded: bool) -> Self {
        Self {
            broker_guarded,
            query_epoch: 0,
        }
    }

    /// Authorize `Request::Stats` and bound returned `(producers, faces)` counts.
    pub fn authorize_stats_query(
        &mut self,
        grant_attached_live: bool,
        covers_global_root: bool,
        covers_whole_fleet_root: bool,
        grant_fleet_matches_req: bool,
        matching_producers: u64,
        matching_faces: u64,
    ) -> WireStatsScopeDecision {
        if !wire_stats_fleet_authorized_b154(
            self.broker_guarded,
            grant_attached_live,
            covers_global_root,
            covers_whole_fleet_root,
            grant_fleet_matches_req,
        ) {
            return WireStatsScopeDecision::RefusedUnauthorizedStats;
        }
        let next = self.query_epoch.saturating_add(1);
        self.query_epoch = stats_query_epoch_advance_b154(self.query_epoch, next);
        WireStatsScopeDecision::AuthorizedScopedStats {
            scoped_producers: stats_visible_rows_clamp_b154(
                matching_producers,
                MAX_WIRE_STATS_ROWS,
            ),
            scoped_faces: stats_visible_rows_clamp_b154(matching_faces, MAX_WIRE_STATS_ROWS),
            query_epoch: self.query_epoch,
        }
    }

    /// Filter an attached producer or face row against the requested fleet tag.
    #[must_use]
    pub const fn filter_row_fleet(
        &self,
        req_global_root: bool,
        req_fleet_tag: u64,
        row_fleet_tag: u64,
    ) -> WireStatsScopeDecision {
        if req_global_root || req_fleet_tag == row_fleet_tag {
            WireStatsScopeDecision::IncludedSameFleetRow
        } else {
            WireStatsScopeDecision::ExcludedSiblingFleetRow
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_narrow_subfleet_and_cross_fleet_grants_and_isolates_sibling_rows() {
        let mut g = WireStatsScopeGuard::new(true);
        // Narrow grant `ro:/f/alpha/in/n1/>` (`covers_whole_fleet_root == false`) -> ERR_UNAUTHORIZED!
        assert_eq!(
            g.authorize_stats_query(true, false, false, true, 3, 4),
            WireStatsScopeDecision::RefusedUnauthorizedStats
        );
        // Cross-fleet grant `ro:/f/alpha/>` querying `/f/beta/>` -> ERR_UNAUTHORIZED!
        assert_eq!(
            g.authorize_stats_query(true, false, true, false, 3, 4),
            WireStatsScopeDecision::RefusedUnauthorizedStats
        );
        // Whole-fleet grant `ro:/f/alpha/>` querying `/f/alpha/>` -> authorized & sibling rows excluded!
        assert_eq!(
            g.authorize_stats_query(true, false, true, true, 3, 4),
            WireStatsScopeDecision::AuthorizedScopedStats {
                scoped_producers: 3,
                scoped_faces: 4,
                query_epoch: 1,
            }
        );
        assert_eq!(
            g.filter_row_fleet(false, 10, 20),
            WireStatsScopeDecision::ExcludedSiblingFleetRow
        );
    }
}
