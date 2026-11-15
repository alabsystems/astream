// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Highest-offset candidate selector & epoch-advancing automatic promotion planner
//! (`BrokerLog::promote_replica`, `Astream.LeaseFail.TlaEpochAutoPromote`).

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "epoch_auto_promote_island.rs"]
mod epoch_auto_promote_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lhf_cand_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn lhf_epoch_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use epoch_auto_promote_island::{lhf_cand_clamp, lhf_epoch_advance};

/// Maximum candidate replicas evaluated per failover round (`16`).
pub const MAX_PROMOTE_CANDIDATES: u64 = 16;

contract_fn! {
    /// Verified strictly advancing promotion epoch (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `lhf_promoted_clean_isl`.
    #[must_use]
    pub const fn lhf_promoted_clean(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReplicaCandidate {
    pub node_id: u64,
    pub durable_epoch: u64,
    pub durable_head: u64,
}

#[derive(Debug, Clone, Default)]
pub struct AutoPromotePlanner {
    committed_epoch: u64,
}

impl AutoPromotePlanner {
    #[must_use]
    pub const fn new(initial_epoch: u64) -> Self {
        Self {
            committed_epoch: initial_epoch,
        }
    }

    /// Selects highest `(durable_epoch, durable_head, node_id)` and advances `committed_epoch`.
    pub fn promote_best(&mut self, candidates: &[ReplicaCandidate]) -> Option<(u64, u64)> {
        if candidates.is_empty() || (candidates.len() as u64) > MAX_PROMOTE_CANDIDATES {
            return None;
        }
        let _ = lhf_cand_clamp(candidates.len() as u64, MAX_PROMOTE_CANDIDATES);
        let mut best_opt: Option<ReplicaCandidate> = None;
        let mut idx = 0usize;
        while idx < candidates.len() {
            if let Some(&cand) = candidates.get(idx) {
                let replace = match best_opt {
                    None => true,
                    Some(cur) => {
                        (cand.durable_epoch, cand.durable_head, cand.node_id)
                            > (cur.durable_epoch, cur.durable_head, cur.node_id)
                    }
                };
                if replace {
                    best_opt = Some(cand);
                }
            }
            idx = idx.saturating_add(1);
        }
        let Some(best) = best_opt else {
            return None;
        };
        let base_epoch = if best.durable_epoch > self.committed_epoch {
            best.durable_epoch
        } else {
            self.committed_epoch
        };
        let Some(next_epoch) = base_epoch.checked_add(1) else {
            return None;
        };
        let Some(min_next) = self.committed_epoch.checked_add(1) else {
            return None;
        };
        if !lhf_promoted_clean(next_epoch, min_next) {
            return None;
        }
        self.committed_epoch = lhf_epoch_advance(self.committed_epoch, next_epoch);
        Some((best.node_id, self.committed_epoch))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn promotes_replica_with_highest_epoch_then_head() {
        let mut p = AutoPromotePlanner::new(4);
        let cands = [
            ReplicaCandidate {
                node_id: 1,
                durable_epoch: 4,
                durable_head: 900,
            },
            ReplicaCandidate {
                node_id: 2,
                durable_epoch: 4,
                durable_head: 950,
            },
        ];
        assert_eq!(p.promote_best(&cands), Some((2, 5)));
    }
}
