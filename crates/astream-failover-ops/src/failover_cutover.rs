// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Crash-safe [`astream_wire::Lineage`] promotion coordinator and follower rejoin tracker
//! (`broker.replicated-failover-matrix`, `Astream.Failover.TlaFailoverCutover`).
//!
//! Computes exact bounded `Lineage` chains (`<= Lineage::MAX = 8` steps) across cascading
//! replica-to-leader promotions:
//! - Advances `LogIdentity` generation strictly via Clean-origin `cutover_gen_advance`.
//! - Clamps every historical step's `common` offset to `min(step.common, new_common_head)`
//!   so [`LogIdentity::continues`] returns the exact divergence ceiling across multi-hop failovers!

use astream_wire::{Lineage, LogIdentity};

#[cfg(clean_islands)]
#[path = "failover_cutover_island.rs"]
mod failover_cutover_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cutover_rejoined_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn cutover_gen_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use failover_cutover_island::{cutover_gen_advance, cutover_rejoined_clamp};

/// Maximum `Lineage` steps retained in `<log>.id` Format 2 (`Lineage::MAX`).
pub const MAX_LINEAGE_STEPS_TRACKED: u64 = 8;

contract_fn! {
    /// Verified readiness check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `cutover_ready_isl`.
    #[must_use]
    pub const fn cutover_ready(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Result of promoting a replica's `LogIdentity` + `Lineage` at `common_head`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CutoverOutcome {
    pub prev_identity: LogIdentity,
    pub promoted_identity: LogIdentity,
    pub lineage: Lineage,
    pub common_head: u64,
}

/// Coordinator maintaining `<log>.id` lineage across cascading promotions.
#[derive(Debug, Clone)]
pub struct FailoverCutoverCoordinator {
    current_id: LogIdentity,
    steps: Vec<(u64, u64)>,
    rejoined_followers: u64,
    quorum_followers: u64,
}

impl FailoverCutoverCoordinator {
    #[must_use]
    pub const fn new(initial_id: LogIdentity, quorum_followers: u64) -> Self {
        Self {
            current_id: initial_id,
            steps: Vec::new(),
            rejoined_followers: 0,
            quorum_followers,
        }
    }

    #[must_use]
    pub const fn current_id(&self) -> LogIdentity {
        self.current_id
    }

    /// Promotes to `generation + 1` at `common_head`, clamping older lineage steps and keeping
    /// the newest `MAX_LINEAGE_STEPS_TRACKED` steps for [`Lineage::from_steps`].
    pub fn promote_at(&mut self, common_head: u64) -> Result<CutoverOutcome, &'static str> {
        let prev = self.current_id;
        let cand_gen = match prev.generation.checked_add(1) {
            Some(g) => g,
            None => return Err("generation u64::MAX overflow"),
        };
        let next_gen = cutover_gen_advance(prev.generation, cand_gen);
        let promoted = LogIdentity {
            id: prev.id,
            generation: next_gen,
        };

        for entry in &mut self.steps {
            if entry.1 > common_head {
                entry.1 = common_head;
            }
        }
        self.steps.push((next_gen, common_head));
        let max_keep =
            cutover_rejoined_clamp(MAX_LINEAGE_STEPS_TRACKED, Lineage::MAX as u64) as usize;
        if self.steps.len() > max_keep {
            let drop_n = self.steps.len().saturating_sub(max_keep);
            let old_steps = core::mem::take(&mut self.steps);
            let mut kept = Vec::new();
            let mut idx = drop_n;
            while idx < old_steps.len() {
                if let Some(&step) = old_steps.get(idx) {
                    kept.push(step);
                }
                idx = idx.saturating_add(1);
            }
            self.steps = kept;
        }
        let lineage = match Lineage::from_steps(&self.steps) {
            Some(l) => l,
            None => return Err("invalid rising lineage steps"),
        };
        self.current_id = promoted;
        self.rejoined_followers = 0;
        Ok(CutoverOutcome {
            prev_identity: prev,
            promoted_identity: promoted,
            lineage,
            common_head,
        })
    }

    /// Records a follower completing divergent-tail truncation + rejoin in the current epoch.
    pub fn record_follower_rejoined(&mut self) -> bool {
        let next = self.rejoined_followers.saturating_add(1);
        self.rejoined_followers = cutover_rejoined_clamp(next, u64::MAX);
        cutover_ready(self.rejoined_followers, self.quorum_followers)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cascading_promotions_clamp_lineage_and_satisfy_wire_log_identity_continues() {
        let id0 = LogIdentity::parse("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.0").unwrap();
        let mut coord = FailoverCutoverCoordinator::new(id0, 2);

        let c1 = coord.promote_at(100).unwrap();
        assert_eq!(c1.promoted_identity.continues(id0, &c1.lineage), Some(100));

        // Second promotion after an unclean loss at head 85 clamps the older 100 step down to 85!
        let c2 = coord.promote_at(85).unwrap();
        assert_eq!(c2.promoted_identity.continues(id0, &c2.lineage), Some(85));
        assert_eq!(
            c2.promoted_identity
                .continues(c1.promoted_identity, &c2.lineage),
            Some(85)
        );

        assert!(!coord.record_follower_rejoined());
        assert!(coord.record_follower_rejoined());
    }
}
