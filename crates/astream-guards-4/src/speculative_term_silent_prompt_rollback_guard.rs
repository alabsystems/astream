// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Silent-prompt local-echo abstention & divergent-output rule-invalidation rollback guard
//! (`evidence/manifest.toml` `term.predict.watermark-squash`;
//! `Astream.Term.TlaSpeculativeTermSilentPromptRollbackGuard`).
//!
//! Enforces `SpeculativeTerminal` / `ProgramPredictor` safety across interactive sessions:
//! - When `silent_prompt_active` (`password:` / `passphrase:` / `PIN:`) holds, speculative
//!   local echo and learned `ProgramPredictor` rules ABSTAIN (`AbstainedSilentPrompt`) so
//!   typed secret characters never render speculatively,
//! - When authoritative PTY output diverges from active prediction, `SpeculativeTerminal`
//!   rolls back to the authoritative screen, invalidates the mispredicting rule, and advances
//!   `rollback_epoch` monotonically so `reconciled.eq_full(authoritative)` always holds!

#[cfg(clean_islands)]
#[path = "speculative_term_silent_prompt_rollback_guard_island.rs"]
mod speculative_term_silent_prompt_rollback_guard_island;
#[cfg(clean_islands)]
pub use speculative_term_silent_prompt_rollback_guard_island::{
    active_rules_clamp_b152, rollback_epoch_advance_b152,
};

/// Maximum learned `ProgramPredictor` rules retained in memory (`256`).
pub const MAX_LEARNED_PREDICTOR_RULES: u64 = 256;

#[cfg(not(clean_islands))]
/// Clamp active `ProgramPredictor` rule count to `MAX_LEARNED_PREDICTOR_RULES`.
#[must_use]
pub const fn active_rules_clamp_b152(cand_rules: u64, max_rules: u64) -> u64 {
    if cand_rules < max_rules {
        cand_rules
    } else {
        max_rules
    }
}

#[cfg(not(clean_islands))]
/// Advance authoritative reconciliation / rollback epoch monotonically.
#[must_use]
pub const fn rollback_epoch_advance_b152(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff speculative echo is safe (`!silent_prompt` and `!alt_raw_passthrough`).
    #[must_use]
    pub const fn speculative_echo_safe_b152(
        silent_prompt: bool,
        alt_raw_passthrough: bool,
    ) -> bool
    clauses [ensures result == (!silent_prompt && !alt_raw_passthrough)]
    {
        !silent_prompt && !alt_raw_passthrough
    }
}

/// Decision for speculative input prediction and authoritative PTY output reconciliation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpeculativeTermDecision {
    AbstainedSilentOrRawPrompt,
    AppliedSpeculativePrediction {
        active_rules: u64,
    },
    ConfirmedPredictionHit {
        active_rules: u64,
    },
    RolledBackAndInvalidatedRule {
        active_rules: u64,
        rollback_epoch: u64,
    },
}

/// Coordinates silent-prompt abstention and divergent-output rule invalidation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SpeculativeTermRollbackGuard {
    active_rules: u64,
    rollback_epoch: u64,
}

impl SpeculativeTermRollbackGuard {
    #[must_use]
    pub const fn new(initial_rules: u64) -> Self {
        Self {
            active_rules: active_rules_clamp_b152(initial_rules, MAX_LEARNED_PREDICTOR_RULES),
            rollback_epoch: 0,
        }
    }

    /// Gate speculative keystroke prediction against silent-prompt and raw-mode detectors.
    #[must_use]
    pub const fn decide_keystroke_prediction(
        &self,
        silent_prompt: bool,
        alt_raw_passthrough: bool,
    ) -> SpeculativeTermDecision {
        if !speculative_echo_safe_b152(silent_prompt, alt_raw_passthrough) {
            SpeculativeTermDecision::AbstainedSilentOrRawPrompt
        } else {
            SpeculativeTermDecision::AppliedSpeculativePrediction {
                active_rules: self.active_rules,
            }
        }
    }

    /// Reconcile authoritative PTY output against active prediction (`had_learned_rule`).
    pub fn reconcile_authoritative_output(
        &mut self,
        matches_prediction: bool,
        had_learned_rule: bool,
    ) -> SpeculativeTermDecision {
        if matches_prediction {
            return SpeculativeTermDecision::ConfirmedPredictionHit {
                active_rules: self.active_rules,
            };
        }
        if had_learned_rule && self.active_rules > 0 {
            self.active_rules = active_rules_clamp_b152(
                self.active_rules.saturating_sub(1),
                MAX_LEARNED_PREDICTOR_RULES,
            );
        }
        let next = self.rollback_epoch.saturating_add(1);
        self.rollback_epoch = rollback_epoch_advance_b152(self.rollback_epoch, next);
        SpeculativeTermDecision::RolledBackAndInvalidatedRule {
            active_rules: self.active_rules,
            rollback_epoch: self.rollback_epoch,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn abstains_on_password_prompt_and_rolls_back_invalidating_divergent_learned_rule() {
        let mut g = SpeculativeTermRollbackGuard::new(3);
        assert_eq!(
            g.decide_keystroke_prediction(true, false),
            SpeculativeTermDecision::AbstainedSilentOrRawPrompt
        );
        assert_eq!(
            g.decide_keystroke_prediction(false, false),
            SpeculativeTermDecision::AppliedSpeculativePrediction { active_rules: 3 }
        );
        assert_eq!(
            g.reconcile_authoritative_output(false, true),
            SpeculativeTermDecision::RolledBackAndInvalidatedRule {
                active_rules: 2,
                rollback_epoch: 1,
            }
        );
    }
}
