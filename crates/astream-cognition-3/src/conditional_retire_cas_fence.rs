// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Compare-and-swap `ConditionalRetire` moot-supersede fence
//! (`Astream.Broker.TlaConditionalRetireCasFence`).
//!
//! Ensures `ConditionalRetire(subject, expected_offset)` retires a retained state entry iff the
//! live offset still equals `expected_offset`, turning stale concurrent retires into safe
//! idempotent `SupersededMoot` outcomes without clobbering newer writes.

#[cfg(clean_islands)]
#[path = "conditional_retire_cas_fence_island.rs"]
mod conditional_retire_cas_fence_island;
#[cfg(clean_islands)]
pub use conditional_retire_cas_fence_island::{retire_moot_clamp_b113, retire_seq_advance_b113};

#[cfg(not(clean_islands))]
/// Clamp mooted `ConditionalRetire` counter to `max_moot`.
#[must_use]
pub const fn retire_moot_clamp_b113(cand_moot: u64, max_moot: u64) -> u64 {
    if cand_moot < max_moot {
        cand_moot
    } else {
        max_moot
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the `ConditionalRetire` evaluation sequence.
#[must_use]
pub const fn retire_seq_advance_b113(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}

contract_fn! {
    /// True iff `expected_offset` matches `live_offset` for CAS retirement.
    #[must_use]
    pub const fn retire_cas_matches_b113(expected_offset: u64, live_offset: u64) -> bool
    clauses [ensures result == (expected_offset == live_offset)]
    {
        expected_offset == live_offset
    }
}

/// Outcome of a `ConditionalRetire` evaluation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConditionalRetireOutcome {
    Retired {
        retired_at_offset: u64,
        seq: u64,
    },
    SupersededMoot {
        live_offset: u64,
        moot_count: u64,
    },
    AheadInvalid {
        expected_offset: u64,
        live_offset: u64,
    },
}

/// CAS evaluator for `ConditionalRetire` over a retained subject offset.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConditionalRetireCasFence {
    moot_count: u64,
    max_moot_cap: u64,
    eval_seq: u64,
}

impl ConditionalRetireCasFence {
    #[must_use]
    pub const fn new(max_moot_cap: u64) -> Self {
        let cap = if max_moot_cap == 0 {
            1024
        } else {
            max_moot_cap
        };
        Self {
            moot_count: 0,
            max_moot_cap: cap,
            eval_seq: 0,
        }
    }

    #[must_use]
    pub const fn moot_count(&self) -> u64 {
        self.moot_count
    }

    /// Evaluate `ConditionalRetire(expected_offset)` against `live_offset` and new `tombstone_offset`.
    pub fn evaluate(
        &mut self,
        expected_offset: u64,
        live_offset: u64,
        tombstone_offset: u64,
    ) -> ConditionalRetireOutcome {
        let next_seq = self.eval_seq.saturating_add(1);
        self.eval_seq = retire_seq_advance_b113(self.eval_seq, next_seq);
        if retire_cas_matches_b113(expected_offset, live_offset) {
            ConditionalRetireOutcome::Retired {
                retired_at_offset: tombstone_offset,
                seq: self.eval_seq,
            }
        } else if expected_offset < live_offset {
            let cand = self.moot_count.saturating_add(1);
            self.moot_count = retire_moot_clamp_b113(cand, self.max_moot_cap);
            ConditionalRetireOutcome::SupersededMoot {
                live_offset,
                moot_count: self.moot_count,
            }
        } else {
            ConditionalRetireOutcome::AheadInvalid {
                expected_offset,
                live_offset,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retires_exact_cas_match_and_moots_superseded_offset() {
        let mut f = ConditionalRetireCasFence::new(16);
        assert_eq!(
            f.evaluate(10, 14, 15),
            ConditionalRetireOutcome::SupersededMoot {
                live_offset: 14,
                moot_count: 1,
            }
        );
        assert_eq!(
            f.evaluate(14, 14, 16),
            ConditionalRetireOutcome::Retired {
                retired_at_offset: 16,
                seq: 2,
            }
        );
    }
}
