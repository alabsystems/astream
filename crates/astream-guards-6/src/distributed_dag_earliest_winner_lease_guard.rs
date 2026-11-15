// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Broker-`bt=` `ADLS` lease takeover & earliest-offset `ADAG` zombie-commit convergence guard
//! (`evidence/manifest.toml` `engine.distributed-workflow`;
//! `Astream.Engine.TlaDistributedDagEarliestWinnerLeaseGuard`).
//!
//! Enforces clockless multi-worker step-DAG convergence over `astream-broker` `bt=` stamps:
//! - Active `ADLS` v1 leases (`stamp_bt_ms < active_lease_expiry_bt_ms`) block competing workers
//!   from taking over the step,
//! - Once `stamp_bt_ms >= active_lease_expiry_bt_ms`, the next worker claim in log offset order
//!   takes over the lease with `expiry = max(active_lease_expiry_bt_ms, stamp_bt_ms + ttl_ms)`,
//! - The step's authoritative output is ALWAYS the EARLIEST valid `ADAG` v1 commit offset
//!   (`min(winner_offset, cand_commit_offset)`), fencing late duplicate commits from zombie workers!

#[cfg(clean_islands)]
#[path = "distributed_dag_earliest_winner_lease_guard_island.rs"]
mod distributed_dag_earliest_winner_lease_guard_island;
#[cfg(clean_islands)]
pub use distributed_dag_earliest_winner_lease_guard_island::{
    dag_lease_expiry_advance_b155, dag_winner_offset_min_b155,
};

#[cfg(not(clean_islands))]
/// Select the earliest valid commit offset (`min(cand_off, cur_winner)`).
#[must_use]
pub const fn dag_winner_offset_min_b155(cand_off: u64, cur_winner: u64) -> u64 {
    if cand_off < cur_winner {
        cand_off
    } else {
        cur_winner
    }
}

#[cfg(not(clean_islands))]
/// Advance broker-time lease expiry watermark monotonically.
#[must_use]
pub const fn dag_lease_expiry_advance_b155(cur_expiry_bt: u64, cand_expiry_bt: u64) -> u64 {
    if cur_expiry_bt < cand_expiry_bt {
        cand_expiry_bt
    } else {
        cur_expiry_bt
    }
}

contract_fn! {
    /// True iff no winner is committed yet (`!has_winner`) and `stamp_bt_ms >= cur_expiry_bt`.
    #[must_use]
    pub const fn dag_step_lease_acquirable_b155(
        has_winner: bool,
        stamp_bt_ms: u64,
        cur_expiry_bt: u64,
    ) -> bool
    clauses [ensures result == (!has_winner && stamp_bt_ms >= cur_expiry_bt)]
    {
        !has_winner && stamp_bt_ms >= cur_expiry_bt
    }
}

/// Transition verdict for `ADLS` lease claims and `ADAG` step commits on the shared log.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DistributedStepDecision {
    GrantedOrTookOverLease {
        holder_node_tag: u64,
        expiry_bt_ms: u64,
    },
    RejectedLeaseStillActive {
        holder_node_tag: u64,
        expiry_bt_ms: u64,
    },
    RejectedStepAlreadyCommitted {
        winner_offset: u64,
        winner_node_tag: u64,
    },
    CommittedAuthoritativeWinner {
        winner_offset: u64,
        winner_node_tag: u64,
    },
    IgnoredLateZombieDuplicateCommit {
        authoritative_winner_offset: u64,
        zombie_commit_offset: u64,
    },
}

/// Deterministic log-fold state for a single distributed DAG step.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DistributedStepConvergenceGuard {
    holder_node_tag: u64,
    lease_expiry_bt_ms: u64,
    winner: Option<(u64, u64)>,
}

impl DistributedStepConvergenceGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            holder_node_tag: 0,
            lease_expiry_bt_ms: 0,
            winner: None,
        }
    }

    /// Fold an `ADLS` v1 lease claim stamped at broker time `stamp_bt_ms`.
    pub fn on_lease_claim(
        &mut self,
        node_tag: u64,
        stamp_bt_ms: u64,
        lease_ttl_ms: u64,
    ) -> DistributedStepDecision {
        if let Some((win_off, win_node)) = self.winner {
            return DistributedStepDecision::RejectedStepAlreadyCommitted {
                winner_offset: win_off,
                winner_node_tag: win_node,
            };
        }
        if !dag_step_lease_acquirable_b155(false, stamp_bt_ms, self.lease_expiry_bt_ms) {
            return DistributedStepDecision::RejectedLeaseStillActive {
                holder_node_tag: self.holder_node_tag,
                expiry_bt_ms: self.lease_expiry_bt_ms,
            };
        }
        let cand_exp = stamp_bt_ms.saturating_add(lease_ttl_ms);
        self.holder_node_tag = node_tag;
        self.lease_expiry_bt_ms = dag_lease_expiry_advance_b155(self.lease_expiry_bt_ms, cand_exp);
        DistributedStepDecision::GrantedOrTookOverLease {
            holder_node_tag: self.holder_node_tag,
            expiry_bt_ms: self.lease_expiry_bt_ms,
        }
    }

    /// Fold a valid `ADAG` v1 commit record at `commit_offset`.
    pub fn on_step_commit(
        &mut self,
        commit_offset: u64,
        committer_node_tag: u64,
    ) -> DistributedStepDecision {
        match self.winner {
            None => {
                self.winner = Some((commit_offset, committer_node_tag));
                DistributedStepDecision::CommittedAuthoritativeWinner {
                    winner_offset: commit_offset,
                    winner_node_tag: committer_node_tag,
                }
            }
            Some((cur_win, cur_node)) => {
                let earliest = dag_winner_offset_min_b155(commit_offset, cur_win);
                if earliest < cur_win {
                    self.winner = Some((earliest, committer_node_tag));
                    DistributedStepDecision::CommittedAuthoritativeWinner {
                        winner_offset: earliest,
                        winner_node_tag: committer_node_tag,
                    }
                } else {
                    let _ = cur_node;
                    DistributedStepDecision::IgnoredLateZombieDuplicateCommit {
                        authoritative_winner_offset: cur_win,
                        zombie_commit_offset: commit_offset,
                    }
                }
            }
        }
    }
}

impl Default for DistributedStepConvergenceGuard {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_bt_lease_takeover_and_fences_late_zombie_worker_commits() {
        let mut g = DistributedStepConvergenceGuard::new();
        // Worker 1 acquires lease at bt=1000 for 500ms -> expires at 1500:
        assert_eq!(
            g.on_lease_claim(1, 1_000, 500),
            DistributedStepDecision::GrantedOrTookOverLease {
                holder_node_tag: 1,
                expiry_bt_ms: 1_500,
            }
        );
        // Worker 2 tries at bt=1499 -> blocked by active lease!
        assert_eq!(
            g.on_lease_claim(2, 1_499, 500),
            DistributedStepDecision::RejectedLeaseStillActive {
                holder_node_tag: 1,
                expiry_bt_ms: 1_500,
            }
        );
        // Worker 2 takes over stalled lease at bt=1500 and commits at offset 40:
        assert_eq!(
            g.on_lease_claim(2, 1_500, 500),
            DistributedStepDecision::GrantedOrTookOverLease {
                holder_node_tag: 2,
                expiry_bt_ms: 2_000,
            }
        );
        assert_eq!(
            g.on_step_commit(40, 2),
            DistributedStepDecision::CommittedAuthoritativeWinner {
                winner_offset: 40,
                winner_node_tag: 2,
            }
        );
        // Zombie Worker 1 wakes up late and publishes commit at offset 45 -> ignored!
        assert_eq!(
            g.on_step_commit(45, 1),
            DistributedStepDecision::IgnoredLateZombieDuplicateCommit {
                authoritative_winner_offset: 40,
                zombie_commit_offset: 45,
            }
        );
    }
}
