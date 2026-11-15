//! Bounded LRU rule cache & divergence invalidator for 0-RTT `ProgramPredictor`.

#[cfg(clean_islands)]
#[path = "program_predictor_lru_island.rs"]
mod program_predictor_lru_island;
#[cfg(clean_islands)]
pub use program_predictor_lru_island::{prog_hit_count_advance, prog_rule_slot_clamp};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn prog_rule_slot_clamp(slot: u64) -> u64 {
    if slot < 64 {
        slot
    } else {
        64
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn prog_hit_count_advance(prev_hits: u64, next_hits: u64) -> u64 {
    if prev_hits < next_hits {
        next_hits
    } else {
        prev_hits
    }
}

contract_fn! {
    #[must_use]
    pub const fn prog_confidence_ready(confirmations: u64) -> bool
    clauses [ensures result == (2 <= confirmations)]
    {
        2 <= confirmations
    }
}

pub const MAX_PROGRAM_RULES: usize = 64;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct LearnedRule {
    cmd_hash: u64,
    output_hash: u64,
    confirmations: u64,
    invalidated: bool,
}

#[derive(Debug, Clone)]
pub struct ProgramPredictorLru {
    rules: Vec<LearnedRule>,
    hits: u64,
}

impl ProgramPredictorLru {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            rules: Vec::new(),
            hits: 0,
        }
    }

    #[must_use]
    pub const fn hits(&self) -> u64 {
        self.hits
    }

    #[must_use]
    pub fn rule_count(&self) -> usize {
        self.rules.len()
    }

    pub fn observe_authoritative(&mut self, cmd_hash: u64, output_hash: u64) {
        for rule in &mut self.rules {
            if rule.cmd_hash == cmd_hash {
                if !rule.invalidated && rule.output_hash == output_hash {
                    rule.confirmations = rule.confirmations.saturating_add(1);
                } else {
                    // Divergent dynamic output permanently invalidates 0-RTT speculation for this command.
                    rule.invalidated = true;
                    rule.confirmations = 0;
                }
                return;
            }
        }
        if self.rules.len() >= MAX_PROGRAM_RULES && !self.rules.is_empty() {
            let old = core::mem::take(&mut self.rules);
            let mut dropped = false;
            for item in old {
                if !dropped {
                    dropped = true;
                } else {
                    self.rules.push(item);
                }
            }
        }
        let next_len = prog_rule_slot_clamp((self.rules.len() as u64).saturating_add(1)) as usize;
        if next_len > self.rules.len() {
            self.rules.push(LearnedRule {
                cmd_hash,
                output_hash,
                confirmations: 1,
                invalidated: false,
            });
        }
    }

    pub fn predict(&mut self, cmd_hash: u64) -> Option<u64> {
        let mut rest = self.rules.as_slice();
        while let [r, tail @ ..] = rest {
            if r.cmd_hash == cmd_hash && !r.invalidated && prog_confidence_ready(r.confirmations) {
                let next = self.hits.saturating_add(1);
                self.hits = prog_hit_count_advance(self.hits, next);
                return Some(r.output_hash);
            }
            rest = tail;
        }
        None
    }
}

impl Default for ProgramPredictorLru {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn speculates_after_two_identical_runs_and_invalidates_on_divergence() {
        let mut lru = ProgramPredictorLru::new();
        lru.observe_authoritative(10, 0xAA);
        assert_eq!(lru.rule_count(), 1);
        assert_eq!(lru.predict(10), None);
        lru.observe_authoritative(10, 0xAA);
        assert_eq!(lru.predict(10), Some(0xAA));
        assert_eq!(lru.hits(), 1);
        lru.observe_authoritative(10, 0xBB);
        assert_eq!(lru.predict(10), None);
    }
}
