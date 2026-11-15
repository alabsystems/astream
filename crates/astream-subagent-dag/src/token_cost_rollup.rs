// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Hierarchical parent<-descendant token & tool-step rollup ledger (`Astream.Subagent.TlaTokenCostRollup`).

#[cfg(clean_islands)]
#[path = "token_cost_rollup_island.rs"]
mod token_cost_rollup_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sub_tokens_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sub_rollup_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use token_cost_rollup_island::{sub_rollup_advance, sub_tokens_clamp};

/// Hard ceiling per conversation tree (`100_000_000` tokens).
pub const MAX_TREE_TOKEN_BUDGET: u64 = 100_000_000;

contract_fn! {
    /// Verified budget ceiling check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `sub_within_ceiling_isl`.
    #[must_use]
    pub const fn sub_within_ceiling(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Monotone token rollup across self + spawned subagents.
#[derive(Debug, Clone)]
pub struct TreeTokenRollup {
    budget: u64,
    self_tokens: u64,
    descendant_tokens: u64,
}

impl TreeTokenRollup {
    #[must_use]
    pub const fn new(budget: u64) -> Self {
        Self {
            budget: sub_tokens_clamp(budget, MAX_TREE_TOKEN_BUDGET),
            self_tokens: 0,
            descendant_tokens: 0,
        }
    }

    pub fn charge_turn(&mut self, self_delta: u64, child_delta: u64) -> bool {
        self.self_tokens = sub_rollup_advance(
            self.self_tokens,
            self.self_tokens.saturating_add(self_delta),
        );
        self.descendant_tokens = sub_rollup_advance(
            self.descendant_tokens,
            self.descendant_tokens.saturating_add(child_delta),
        );
        let total = self.self_tokens.saturating_add(self.descendant_tokens);
        sub_within_ceiling(self.budget, total)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn token_rollup_sums_parent_and_child_turns_against_tree_ceiling() {
        let mut r = TreeTokenRollup::new(50_000);
        assert!(r.charge_turn(10_000, 25_000));
        assert!(!r.charge_turn(5_000, 15_000));
    }
}
