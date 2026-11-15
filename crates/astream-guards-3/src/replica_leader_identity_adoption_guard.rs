// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Replica `LogIdentity` adoption-at-newest & rewritten-log fresh-id-at-gen-0 guard
//! (`evidence/manifest.toml` `broker.log-identity` & `broker.unclean-generation`;
//! `Astream.Broker.TlaReplicaLeaderIdentityAdoptionGuard`).
//!
//! Enforces the replica identity safety rules:
//! - A replica holding `local_head` records (`0..local_head`) keeps its OWN identity through
//!   leader `Replicate` echoes below `local_head - 1`, and adopts the leader's `LogIdentity`
//!   ONLY once a valid matching `Replicate` reaches its newest record (`seq + 1 >= local_head`),
//! - A `Replicate` carrying a mismatched record at `seq < local_head` is refused WITH NO
//!   identity adoption,
//! - If a replica's log is found rewritten on open (`local_rewritten == true`, e.g., an older
//!   copy restored under it), it mints a FRESH `id` at `generation = 0` — NEVER incrementing
//!   its leader's generation!

#[cfg(clean_islands)]
#[path = "replica_leader_identity_adoption_guard_island.rs"]
mod replica_leader_identity_adoption_guard_island;
#[cfg(clean_islands)]
pub use replica_leader_identity_adoption_guard_island::{
    replica_echo_cursor_clamp_b149, replica_head_advance_b149,
};

#[cfg(not(clean_islands))]
/// Clamp verified echo cursor so it never exceeds `local_head`.
#[must_use]
pub const fn replica_echo_cursor_clamp_b149(cand_cursor: u64, local_head: u64) -> u64 {
    if cand_cursor < local_head {
        cand_cursor
    } else {
        local_head
    }
}

#[cfg(not(clean_islands))]
/// Advance replica `local_head` monotonically upon verified append.
#[must_use]
pub const fn replica_head_advance_b149(cur_head: u64, cand_head: u64) -> u64 {
    if cur_head < cand_head {
        cand_head
    } else {
        cur_head
    }
}

contract_fn! {
    /// True iff leader carried an identity, record matched/appended, and `next_seq >= local_head`.
    #[must_use]
    pub const fn replica_reached_newest_for_adoption_b149(
        leader_sent_identity: bool,
        record_valid: bool,
        next_seq: u64,
        local_head: u64,
    ) -> bool
    clauses [ensures result == (leader_sent_identity && record_valid && next_seq >= local_head)]
    {
        leader_sent_identity && record_valid && next_seq >= local_head
    }
}

/// Decision for replica identity state on `Replicate` or rewritten reopen.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReplicaIdentityDecision {
    KeptReplicaOwnIdentity {
        active_id_tag: u64,
        active_gen: u64,
        local_head: u64,
    },
    AdoptedLeaderIdentity {
        leader_id_tag: u64,
        leader_gen: u64,
        local_head: u64,
    },
    RefusedDivergentEchoKeptOwnIdentity {
        seq: u64,
        active_id_tag: u64,
    },
    MintedFreshIdAtGenZeroOnRewrite {
        fresh_id_tag: u64,
    },
}

/// Replica identity adoption guard.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReplicaLeaderIdentityGuard {
    active_id_tag: u64,
    active_gen: u64,
    local_head: u64,
    verified_echo_cursor: u64,
}

impl ReplicaLeaderIdentityGuard {
    #[must_use]
    pub const fn new(own_id_tag: u64, own_gen: u64, local_head: u64) -> Self {
        Self {
            active_id_tag: own_id_tag,
            active_gen: own_gen,
            local_head,
            verified_echo_cursor: 0,
        }
    }

    /// Reopen when local log was rewritten/restored: mints a fresh id at `gen = 0`, NEVER
    /// bumping the leader's generation!
    pub fn on_rewritten_log_reopen(
        &mut self,
        fresh_id_tag: u64,
        restored_head: u64,
    ) -> ReplicaIdentityDecision {
        self.active_id_tag = fresh_id_tag;
        self.active_gen = 0;
        self.local_head = restored_head;
        self.verified_echo_cursor = 0;
        ReplicaIdentityDecision::MintedFreshIdAtGenZeroOnRewrite { fresh_id_tag }
    }

    /// Process a `Replicate` record at `seq` with optional `(leader_id_tag, leader_gen)`.
    pub fn on_replicate_record(
        &mut self,
        seq: u64,
        record_matches_or_appends: bool,
        leader_identity: Option<(u64, u64)>,
    ) -> ReplicaIdentityDecision {
        if !record_matches_or_appends {
            return ReplicaIdentityDecision::RefusedDivergentEchoKeptOwnIdentity {
                seq,
                active_id_tag: self.active_id_tag,
            };
        }
        let next_seq = seq.saturating_add(1);
        let prev_head = self.local_head;
        self.local_head = replica_head_advance_b149(self.local_head, next_seq);
        self.verified_echo_cursor = replica_echo_cursor_clamp_b149(next_seq, self.local_head);

        if let Some((lid, lgen)) = leader_identity {
            if replica_reached_newest_for_adoption_b149(true, true, next_seq, prev_head) {
                self.active_id_tag = lid;
                self.active_gen = lgen;
                return ReplicaIdentityDecision::AdoptedLeaderIdentity {
                    leader_id_tag: lid,
                    leader_gen: lgen,
                    local_head: self.local_head,
                };
            }
        }
        ReplicaIdentityDecision::KeptReplicaOwnIdentity {
            active_id_tag: self.active_id_tag,
            active_gen: self.active_gen,
            local_head: self.local_head,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn adopts_leader_identity_only_at_newest_record_and_mints_gen_zero_on_rewrite() {
        // Replica holding 3 records (offsets 0, 1, 2 -> local_head = 3) with own id 100:
        let mut g = ReplicaLeaderIdentityGuard::new(100, 0, 3);
        // Echoes of 0 and 1 keep replica's own id 100:
        assert_eq!(
            g.on_replicate_record(0, true, Some((999, 4))),
            ReplicaIdentityDecision::KeptReplicaOwnIdentity {
                active_id_tag: 100,
                active_gen: 0,
                local_head: 3,
            }
        );
        // Divergent record at 1 is refused and keeps own id 100:
        assert_eq!(
            g.on_replicate_record(1, false, Some((999, 4))),
            ReplicaIdentityDecision::RefusedDivergentEchoKeptOwnIdentity {
                seq: 1,
                active_id_tag: 100,
            }
        );
        // Matching echo of offset 2 (`next_seq = 3 >= local_head = 3`) adopts leader (999, 4)!
        assert_eq!(
            g.on_replicate_record(2, true, Some((999, 4))),
            ReplicaIdentityDecision::AdoptedLeaderIdentity {
                leader_id_tag: 999,
                leader_gen: 4,
                local_head: 3,
            }
        );
        // Rewritten log reopen mints fresh id 200 at gen 0 (never 999.5)!
        assert_eq!(
            g.on_rewritten_log_reopen(200, 1),
            ReplicaIdentityDecision::MintedFreshIdAtGenZeroOnRewrite { fresh_id_tag: 200 }
        );
        assert_eq!(g.active_gen, 0);
    }
}
