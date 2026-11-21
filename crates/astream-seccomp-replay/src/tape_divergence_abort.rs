// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Fail-closed tape divergence abort latch: a short, wrong-kind or diverged tape aborts the replay
//! (`Astream.SecReplay.TlaTapeDivergenceAbort`).

#[cfg(clean_islands)]
#[path = "tape_divergence_abort_island.rs"]
mod tape_divergence_abort_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sec_err_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sec_abort_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use tape_divergence_abort_island::{sec_abort_advance, sec_err_clamp};

/// Zero-tolerance divergence budget (`0` mismatches permitted).
pub const MAX_DIVERGENCE_TOLERANCE: u64 = 0;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TapeAbortReason {
    ShortTape,
    WrongKind,
    UnconsumedTrailing,
}

contract_fn! {
    /// Verified intact zero-divergence replay state (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `sec_tape_intact_isl`.
    #[must_use]
    pub const fn sec_tape_intact(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct TapeDivergenceGuard {
    errors: u64,
    abort_seq: u64,
    reason: Option<TapeAbortReason>,
}

impl TapeDivergenceGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            errors: 0,
            abort_seq: 0,
            reason: None,
        }
    }

    pub fn trip(&mut self, reason: TapeAbortReason) {
        self.errors = self.errors.saturating_add(1);
        if self.reason.is_none() {
            self.reason = Some(reason);
        }
        self.abort_seq = sec_abort_advance(self.abort_seq, self.abort_seq.saturating_add(1));
    }

    #[must_use]
    pub const fn can_finish(&self, consumed: u64, tape_len: u64) -> bool {
        let tol = sec_err_clamp(self.errors, MAX_DIVERGENCE_TOLERANCE);
        tol == self.errors && consumed == tape_len && sec_tape_intact(tape_len, consumed)
    }

    #[must_use]
    pub const fn abort_reason(&self) -> Option<TapeAbortReason> {
        self.reason
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn aborts_on_wrong_kind_or_unconsumed_trailing_tape_entries() {
        let mut g = TapeDivergenceGuard::new();
        assert!(g.can_finish(3, 3));
        assert!(!g.can_finish(2, 3));
        g.trip(TapeAbortReason::WrongKind);
        assert!(!g.can_finish(3, 3));
        assert_eq!(g.abort_reason(), Some(TapeAbortReason::WrongKind));
    }
}
