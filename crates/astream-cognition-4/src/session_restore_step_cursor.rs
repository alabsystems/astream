// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Crash-safe `aterm-restore` step-frame replay cursor
//! (`Astream.Engine.TlaSessionRestoreStepCursor`).
//!
//! Validates step-frame sequence progression during `aterm` session restore:
//! skips zeroed torn-tail extents cleanly on power-loss recovery, clamps per-step
//! byte budgets to `max_step_bytes`, and advances `restored_seq` monotonically.

#[cfg(clean_islands)]
#[path = "session_restore_step_cursor_island.rs"]
mod session_restore_step_cursor_island;
#[cfg(clean_islands)]
pub use session_restore_step_cursor_island::{
    restore_step_bytes_clamp_b115, restore_step_seq_advance_b115,
};

#[cfg(not(clean_islands))]
/// Clamp restored step-frame payload length to `max_step_bytes`.
#[must_use]
pub const fn restore_step_bytes_clamp_b115(step_bytes: u64, max_step_bytes: u64) -> u64 {
    if step_bytes < max_step_bytes {
        step_bytes
    } else {
        max_step_bytes
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `restored_seq`.
#[must_use]
pub const fn restore_step_seq_advance_b115(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}

contract_fn! {
    /// True iff `step_bytes` fits within `max_step_bytes`.
    #[must_use]
    pub const fn restore_step_fits_budget_b115(step_bytes: u64, max_step_bytes: u64) -> bool
    clauses [ensures result == (step_bytes <= max_step_bytes)]
    {
        step_bytes <= max_step_bytes
    }
}

/// Outcome of scanning one step frame during `aterm-restore`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RestoreStepOutcome {
    Applied {
        seq: u64,
        clamped_bytes: u64,
    },
    SkippedStaleOrDuplicate {
        current_seq: u64,
    },
    TornZeroTailStop {
        final_seq: u64,
        zero_bytes_skipped: usize,
    },
    OversizedStepRejected {
        step_bytes: u64,
        max_step_bytes: u64,
    },
}

fn is_all_zero_extent(mut tail: &[u8]) -> bool {
    if tail.is_empty() {
        return false;
    }
    while let [b, rest @ ..] = tail {
        if *b != 0 {
            return false;
        }
        tail = rest;
    }
    true
}

/// Stateful `aterm-restore` step-frame replay cursor.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SessionRestoreStepCursor {
    restored_seq: u64,
    has_any_step: bool,
    last_step_bytes: u64,
    max_step_bytes: u64,
}

impl SessionRestoreStepCursor {
    #[must_use]
    pub const fn new(max_step_bytes: u64) -> Self {
        let cap = if max_step_bytes == 0 {
            256 * 1024
        } else {
            max_step_bytes
        };
        Self {
            restored_seq: 0,
            has_any_step: false,
            last_step_bytes: 0,
            max_step_bytes: cap,
        }
    }

    #[must_use]
    pub const fn restored_seq(&self) -> u64 {
        self.restored_seq
    }

    /// Inspect raw trailing bytes at EOF; cleanly terminates replay if preallocated zero extent.
    #[must_use]
    pub fn classify_eof_tail(&self, trailing: &[u8]) -> Option<RestoreStepOutcome> {
        if is_all_zero_extent(trailing) {
            Some(RestoreStepOutcome::TornZeroTailStop {
                final_seq: self.restored_seq,
                zero_bytes_skipped: trailing.len(),
            })
        } else {
            None
        }
    }

    /// Validate and commit a decoded step frame `(seq, step_bytes)`.
    pub fn accept_step(&mut self, seq: u64, step_bytes: u64) -> RestoreStepOutcome {
        if !restore_step_fits_budget_b115(step_bytes, self.max_step_bytes) {
            return RestoreStepOutcome::OversizedStepRejected {
                step_bytes,
                max_step_bytes: self.max_step_bytes,
            };
        }
        if self.has_any_step && seq <= self.restored_seq {
            return RestoreStepOutcome::SkippedStaleOrDuplicate {
                current_seq: self.restored_seq,
            };
        }
        self.has_any_step = true;
        self.restored_seq = restore_step_seq_advance_b115(self.restored_seq, seq);
        self.last_step_bytes = restore_step_bytes_clamp_b115(step_bytes, self.max_step_bytes);
        RestoreStepOutcome::Applied {
            seq: self.restored_seq,
            clamped_bytes: self.last_step_bytes,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn advances_monotone_steps_and_stops_cleanly_on_zeroed_tail() {
        let mut cur = SessionRestoreStepCursor::new(4096);
        assert_eq!(
            cur.accept_step(1, 512),
            RestoreStepOutcome::Applied {
                seq: 1,
                clamped_bytes: 512
            }
        );
        assert_eq!(
            cur.accept_step(1, 512),
            RestoreStepOutcome::SkippedStaleOrDuplicate { current_seq: 1 }
        );
        assert_eq!(
            cur.classify_eof_tail(&[0u8; 64]),
            Some(RestoreStepOutcome::TornZeroTailStop {
                final_seq: 1,
                zero_bytes_skipped: 64
            })
        );
    }
}
