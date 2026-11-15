// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! 0-RTT `ProgramPredictor` rule confidence tracker (`term.predict.watermark-squash`) promoting a
//! deterministic `(command_sha256 -> output_sha256)` rule after identical repetitions and revoking
//! immediately on any divergent output (`Astream.SpecEcho.TlaProgramRuleLearner`).

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

use astream_digest::{ct_eq, Sha256};

#[cfg(clean_islands)]
#[path = "program_rule_learner_island.rs"]
mod program_rule_learner_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn se_rules_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn se_hit_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use program_rule_learner_island::{se_hit_advance, se_rules_clamp};

/// Maximum consecutive confirmations tracked per rule (`64`).
pub const MAX_RULE_CONFIRMATIONS: u64 = 64;

contract_fn! {
    /// Verified 0-RTT rule promotion check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `se_rule_trusted_isl`.
    #[must_use]
    pub const fn se_rule_trusted(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct LearnedCommandRule {
    output_digest: [u8; 32],
    confirmations: u64,
    invalidated: bool,
    total_hits: u64,
}

impl LearnedCommandRule {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            output_digest: [0u8; 32],
            confirmations: 0,
            invalidated: false,
            total_hits: 0,
        }
    }

    pub fn observe_output(&mut self, output_bytes: &[u8]) -> bool {
        if self.invalidated {
            return false;
        }
        let d = Sha256::digest_slice(output_bytes);
        if self.confirmations == 0 {
            self.output_digest = d;
            self.confirmations = 1;
        } else if ct_eq(&self.output_digest, &d) {
            self.confirmations =
                se_rules_clamp(self.confirmations.saturating_add(1), MAX_RULE_CONFIRMATIONS);
            self.total_hits = se_hit_advance(self.total_hits, self.total_hits.saturating_add(1));
        } else {
            self.invalidated = true;
            self.confirmations = 0;
        }
        !self.invalidated && se_rule_trusted(self.confirmations, 2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn promotes_deterministic_output_on_second_match_and_invalidates_on_divergence() {
        let mut r = LearnedCommandRule::new();
        assert!(!r.observe_output(b"On branch main\nnothing to commit\n"));
        assert!(r.observe_output(b"On branch main\nnothing to commit\n"));
        assert!(!r.observe_output(b"On branch feat\n1 modified\n"));
        assert!(!r.observe_output(b"On branch main\nnothing to commit\n"));
    }
}
