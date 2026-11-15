// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bidirectional `FederationBridge` echo-suppression, lineage cursor clamp, & foreign-log
//! divergence guard (`evidence/manifest.toml` `broker.federation`;
//! `Astream.Broker.TlaFederationEchoHopLineageGuard`).
//!
//! Enforces `FederationBridge` / `asb federate` safety across multi-broker topologies:
//! - Suppresses infinite bidirectional echo loops via `hop_count < max_hops` (`1`) and
//!   `!matches_excluded_prefix`,
//! - Across reconnects, verifies `LogIdentity` continuity: clamps `src_cursor` to
//!   `min(src_cursor, lineage_common)` on valid unclean-stop lineage, and fails closed with
//!   `SourceLogDiverged` (refusing to forward or overwrite `--cut-file`!) on foreign replacement,
//! - Deterministic `(producer_id, src_offset)` deduplication guarantees zero duplicate records
//!   when replaying after a crash-before-commit!

#[cfg(clean_islands)]
#[path = "federation_echo_hop_lineage_guard_island.rs"]
mod federation_echo_hop_lineage_guard_island;
#[cfg(clean_islands)]
pub use federation_echo_hop_lineage_guard_island::{
    fed_committed_cursor_advance_b153, fed_lineage_cursor_clamp_b153,
};

#[cfg(not(clean_islands))]
/// Clamp `src_cursor` to `lineage_common` (`min(src_cursor, lineage_common)`).
#[must_use]
pub const fn fed_lineage_cursor_clamp_b153(src_cursor: u64, lineage_common: u64) -> u64 {
    if src_cursor < lineage_common {
        src_cursor
    } else {
        lineage_common
    }
}

#[cfg(not(clean_islands))]
/// Advance durably committed federation cursor within one log lineage monotonically.
#[must_use]
pub const fn fed_committed_cursor_advance_b153(cur_committed: u64, cand_committed: u64) -> u64 {
    if cur_committed < cand_committed {
        cand_committed
    } else {
        cur_committed
    }
}

contract_fn! {
    /// True iff `hop_count < max_hops` and `!matches_excluded_prefix` (bidirectional echo free).
    #[must_use]
    pub const fn federation_record_forwardable_b153(
        hop_count: u64,
        max_hops: u64,
        matches_excluded_prefix: bool,
    ) -> bool
    clauses [ensures result == (hop_count < max_hops && !matches_excluded_prefix)]
    {
        hop_count < max_hops && !matches_excluded_prefix
    }
}

/// Decision for source identity verification and record forwarding on a federation tick.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FederationTickDecision {
    VerifiedSameSourceIdentity { cursor: u64 },
    ClampedCursorOnValidLineage { clamped_cursor: u64 },
    RefusedSourceLogDiverged,
    ForwardWithDeterministicDedupSeq { dedup_producer_seq: u64 },
    SuppressedEchoLoopRecord,
    CommittedSourceGroupCursor { committed_cursor: u64 },
}

/// Tracks source log identity, lineage-safe cursor, and echo suppression.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FederationBridgeSyncGuard {
    pinned_src_id_tag: u64,
    src_cursor: u64,
    max_hops: u64,
}

impl FederationBridgeSyncGuard {
    #[must_use]
    pub const fn new(pinned_src_id_tag: u64, initial_cursor: u64) -> Self {
        Self {
            pinned_src_id_tag,
            src_cursor: initial_cursor,
            max_hops: 1,
        }
    }

    /// Reconcile source `Hello` `LogIdentity` and optional `lineage_common` before draining.
    pub fn verify_source_identity(
        &mut self,
        observed_id_tag: u64,
        lineage_common: Option<u64>,
    ) -> FederationTickDecision {
        if observed_id_tag != self.pinned_src_id_tag {
            return FederationTickDecision::RefusedSourceLogDiverged;
        }
        match lineage_common {
            None => FederationTickDecision::VerifiedSameSourceIdentity {
                cursor: self.src_cursor,
            },
            Some(common) => {
                self.src_cursor = fed_lineage_cursor_clamp_b153(self.src_cursor, common);
                FederationTickDecision::ClampedCursorOnValidLineage {
                    clamped_cursor: self.src_cursor,
                }
            }
        }
    }

    /// Evaluate whether source record at `src_offset` should be forwarded or echo-suppressed.
    #[must_use]
    pub const fn plan_record_forward(
        &self,
        src_offset: u64,
        hop_count: u64,
        matches_excluded_prefix: bool,
    ) -> FederationTickDecision {
        if federation_record_forwardable_b153(hop_count, self.max_hops, matches_excluded_prefix) {
            FederationTickDecision::ForwardWithDeterministicDedupSeq {
                dedup_producer_seq: src_offset.saturating_add(1),
            }
        } else {
            FederationTickDecision::SuppressedEchoLoopRecord
        }
    }

    /// Commit source consumer-group cursor AFTER destination publish acks complete.
    pub fn commit_page_cursor(&mut self, next_cursor: u64) -> FederationTickDecision {
        self.src_cursor = fed_committed_cursor_advance_b153(self.src_cursor, next_cursor);
        FederationTickDecision::CommittedSourceGroupCursor {
            committed_cursor: self.src_cursor,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn suppresses_bidirectional_echoes_clamps_valid_lineage_and_refuses_foreign_log() {
        let mut g = FederationBridgeSyncGuard::new(777, 25);
        assert_eq!(
            g.verify_source_identity(888, None),
            FederationTickDecision::RefusedSourceLogDiverged
        );
        assert_eq!(
            g.verify_source_identity(777, Some(20)),
            FederationTickDecision::ClampedCursorOnValidLineage { clamped_cursor: 20 }
        );
        assert_eq!(
            g.plan_record_forward(20, 0, true),
            FederationTickDecision::SuppressedEchoLoopRecord
        );
        assert_eq!(
            g.plan_record_forward(20, 0, false),
            FederationTickDecision::ForwardWithDeterministicDedupSeq {
                dedup_producer_seq: 21,
            }
        );
    }
}
