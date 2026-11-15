// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Restart-safe irreversible side-effect replay ledger
//! (`Astream.Effects.TlaEffectIdempotencyLedgerB96`).
//!
//! When an agent restarts (`aterm ctl @self restart`) and replays its recorded
//! transcript, side-effecting tool invocations (`git push`, HTTP mutations, file
//! writes) at `effect_seq <= committed_watermark` MUST replay their cached outcome
//! digest rather than executing a second time against the external world.

#[cfg(clean_islands)]
#[path = "effect_idempotency_ledger_island.rs"]
mod effect_idempotency_ledger_island;
#[cfg(clean_islands)]
pub use effect_idempotency_ledger_island::{effect_ledger_clamp, effect_seq_advance_b96};

/// Default maximum cached effect receipts retained in the bounded ring.
pub const DEFAULT_MAX_LEDGER_RECEIPTS: usize = 256;

#[cfg(not(clean_islands))]
/// Monotonically advance the committed irreversible-effect sequence watermark.
#[must_use]
pub const fn effect_seq_advance_b96(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}

#[cfg(not(clean_islands))]
/// Clamp retained receipt count to `max_entries`.
#[must_use]
pub const fn effect_ledger_clamp(cand_entries: u64, max_entries: u64) -> u64 {
    if cand_entries < max_entries {
        cand_entries
    } else {
        max_entries
    }
}

contract_fn! {
    /// True iff `effect_seq <= committed_watermark` (`effect_seq` must NOT re-execute).
    #[must_use]
    pub const fn effect_already_committed(effect_seq: u64, committed_watermark: u64) -> bool
    clauses [ensures result == (effect_seq <= committed_watermark)]
    {
        effect_seq <= committed_watermark
    }
}

/// Recorded receipt for a committed external effect (`effect_seq >= 1`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CommittedEffectReceipt {
    pub effect_seq: u64,
    pub intent_digest: u64,
    pub outcome_digest: u64,
}

/// Pre-execution decision for a candidate side effect (`effect_seq >= 1`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EffectGateDecision {
    /// Fresh next effect (`effect_seq == watermark + 1`): execute against world.
    ExecuteLive,
    /// Already committed; replay `outcome_digest` without re-executing!
    ReplayCached { outcome_digest: u64 },
    /// Already committed, receipt aged out of ring -> fail closed rather than double-execute!
    RefuseEvictedReplay { effect_seq: u64, watermark: u64 },
    /// Replay intent digest differs from recorded history -> deterministic divergence fault!
    IntentDivergence {
        effect_seq: u64,
        recorded_intent: u64,
        replayed_intent: u64,
    },
    /// Non-contiguous future `effect_seq > watermark + 1` or invalid `0`.
    OutOfOrderSequence { expected_next: u64, actual: u64 },
}

/// Bounded idempotency ledger for `astream-effects`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EffectIdempotencyLedger {
    committed_watermark: u64,
    max_entries: usize,
    receipts: Vec<CommittedEffectReceipt>,
}

impl Default for EffectIdempotencyLedger {
    fn default() -> Self {
        Self::new(DEFAULT_MAX_LEDGER_RECEIPTS)
    }
}

impl EffectIdempotencyLedger {
    #[must_use]
    pub const fn new(max_entries: usize) -> Self {
        let cap = if max_entries == 0 {
            DEFAULT_MAX_LEDGER_RECEIPTS
        } else {
            max_entries
        };
        Self {
            committed_watermark: 0,
            max_entries: cap,
            receipts: Vec::new(),
        }
    }

    #[must_use]
    pub const fn committed_watermark(&self) -> u64 {
        self.committed_watermark
    }

    #[must_use]
    pub fn retained_count(&self) -> usize {
        effect_ledger_clamp(self.receipts.len() as u64, self.max_entries as u64) as usize
    }

    /// Gate `effect_seq` (`>= 1`) before executing an external effect.
    #[must_use]
    pub fn check_before_exec(&self, effect_seq: u64, intent_digest: u64) -> EffectGateDecision {
        let expected_next = self.committed_watermark.saturating_add(1);
        if effect_seq == 0 || effect_seq > expected_next {
            return EffectGateDecision::OutOfOrderSequence {
                expected_next,
                actual: effect_seq,
            };
        }
        if effect_already_committed(effect_seq, self.committed_watermark) {
            let mut rest = self.receipts.as_slice();
            while let &[rec, ref tail @ ..] = rest {
                if rec.effect_seq == effect_seq {
                    if rec.intent_digest != intent_digest {
                        return EffectGateDecision::IntentDivergence {
                            effect_seq,
                            recorded_intent: rec.intent_digest,
                            replayed_intent: intent_digest,
                        };
                    }
                    return EffectGateDecision::ReplayCached {
                        outcome_digest: rec.outcome_digest,
                    };
                }
                rest = tail;
            }
            return EffectGateDecision::RefuseEvictedReplay {
                effect_seq,
                watermark: self.committed_watermark,
            };
        }
        EffectGateDecision::ExecuteLive
    }

    /// Record completion of `effect_seq == committed_watermark + 1`.
    pub fn record_committed(
        &mut self,
        effect_seq: u64,
        intent_digest: u64,
        outcome_digest: u64,
    ) -> bool {
        if effect_seq != self.committed_watermark.saturating_add(1) {
            return false;
        }
        if self.receipts.len() >= self.max_entries {
            let mut shifted = Vec::new();
            if let &[_, ref tail @ ..] = self.receipts.as_slice() {
                shifted.extend_from_slice(tail);
            }
            self.receipts = shifted;
        }
        self.receipts.push(CommittedEffectReceipt {
            effect_seq,
            intent_digest,
            outcome_digest,
        });
        self.committed_watermark = effect_seq_advance_b96(self.committed_watermark, effect_seq);
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn replays_cached_effects_and_catches_intent_divergence_or_eviction() {
        let mut ledger = EffectIdempotencyLedger::new(2);
        assert_eq!(
            ledger.check_before_exec(1, 0xAA),
            EffectGateDecision::ExecuteLive
        );
        assert!(ledger.record_committed(1, 0xAA, 0x1111));
        assert!(ledger.record_committed(2, 0xBB, 0x2222));

        // Restart replay of seq=1 with matching intent returns cached outcome without re-running!
        assert_eq!(
            ledger.check_before_exec(1, 0xAA),
            EffectGateDecision::ReplayCached {
                outcome_digest: 0x1111,
            }
        );
        // Divergent intent at seq=2 is caught!
        assert_eq!(
            ledger.check_before_exec(2, 0xCC),
            EffectGateDecision::IntentDivergence {
                effect_seq: 2,
                recorded_intent: 0xBB,
                replayed_intent: 0xCC,
            }
        );

        // Committing seq=3 evicts seq=1 from the 2-entry ring; replaying seq=1 fails closed!
        assert!(ledger.record_committed(3, 0xDD, 0x3333));
        assert_eq!(
            ledger.check_before_exec(1, 0xAA),
            EffectGateDecision::RefuseEvictedReplay {
                effect_seq: 1,
                watermark: 3,
            }
        );
    }
}
