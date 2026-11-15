// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Write-ahead journalled human notification gate (`aterm-link notify --on … --exec`)
//! (`docs/DESIGN-aterm-fabric.md` §13 line 3827, §15 lines 4056 & 4069;
//! `Astream.Host.TlaNotifyJournalBeforeExecGate`).
//!
//! Enforces `aterm-link notify`'s crash-safe human-push invariants:
//! - Pages ONLY durable records (`record_offset <= durable_head_offset` on the Ordered tier),
//! - Journals the intent BEFORE spawning `--exec <cmd>` so a crash inside the window errs on the
//!   side of a duplicate push rather than a silently missed human alert,
//! - Deduplicates by `journalled_offset`, suppresses unchanged `attention=` re-fires (once per
//!   transition), and rate-limits pushes per notifier window (`pushes_used <= max_pushes`).

#[cfg(clean_islands)]
#[path = "notify_journal_before_exec_gate_island.rs"]
mod notify_journal_before_exec_gate_island;
#[cfg(clean_islands)]
pub use notify_journal_before_exec_gate_island::{
    notify_journal_off_advance_b129, notify_pushes_clamp_b129,
};

#[cfg(not(clean_islands))]
/// Clamp notifier pushes in the current rate-limit window to `max_pushes`.
#[must_use]
pub const fn notify_pushes_clamp_b129(cand_pushes: u64, max_pushes: u64) -> u64 {
    if cand_pushes < max_pushes {
        cand_pushes
    } else {
        max_pushes
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the durable pre-exec journal watermark.
#[must_use]
pub const fn notify_journal_off_advance_b129(cur_off: u64, cand_off: u64) -> u64 {
    if cur_off < cand_off {
        cand_off
    } else {
        cur_off
    }
}

contract_fn! {
    /// True iff `record_offset > journalled_offset && record_offset <= durable_head_offset`.
    #[must_use]
    pub const fn notify_record_durable_and_unseen_b129(
        record_offset: u64,
        journalled_offset: u64,
        durable_head_offset: u64,
    ) -> bool
    clauses [ensures result == (record_offset > journalled_offset && record_offset <= durable_head_offset)]
    {
        record_offset > journalled_offset && record_offset <= durable_head_offset
    }
}

/// Gate verdict before spawning `--exec <cmd>` for a human notification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NotifyExecVerdict {
    /// Write-ahead journal entry must be flushed first, then `--exec` runs.
    JournalThenExec {
        journalled_offset: u64,
        pushes_used: u64,
    },
    /// Record has not yet crossed `durable_head` on Ordered tier -> wait for barrier/flush!
    DeferredUntilDurable {
        record_offset: u64,
        durable_head_offset: u64,
    },
    /// Already journalled at or above `record_offset` -> deduplicated.
    DedupedAlreadyJournalled { journalled_offset: u64 },
    /// Same `attention=` fingerprint as previous transition -> suppressed.
    SuppressedSameAttentionTransition,
    /// Per-notifier rate limit reached in the current window.
    RateLimited { max_pushes: u64 },
}

/// Write-ahead journalled human notification gate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NotifyJournalBeforeExecGate {
    journalled_offset: u64,
    last_attention_fp: u64,
    pushes_used: u64,
    max_pushes_per_window: u64,
}

impl NotifyJournalBeforeExecGate {
    #[must_use]
    pub const fn new(initial_journalled_offset: u64, max_pushes_per_window: u64) -> Self {
        Self {
            journalled_offset: initial_journalled_offset,
            last_attention_fp: 0,
            pushes_used: 0,
            max_pushes_per_window,
        }
    }

    pub fn refill_rate_window(&mut self) {
        self.pushes_used = 0;
    }

    /// Evaluate a candidate notification (`attention_fp = None` for mail/ask, `Some(fp)` for attention transition).
    pub fn evaluate_candidate(
        &mut self,
        record_offset: u64,
        durable_head_offset: u64,
        attention_fp: Option<u64>,
    ) -> NotifyExecVerdict {
        if record_offset == 0 || record_offset <= self.journalled_offset {
            return NotifyExecVerdict::DedupedAlreadyJournalled {
                journalled_offset: self.journalled_offset,
            };
        }
        if record_offset > durable_head_offset {
            return NotifyExecVerdict::DeferredUntilDurable {
                record_offset,
                durable_head_offset,
            };
        }
        let _ok = notify_record_durable_and_unseen_b129(
            record_offset,
            self.journalled_offset,
            durable_head_offset,
        );
        if let Some(fp) = attention_fp {
            if fp != 0 && fp == self.last_attention_fp {
                self.journalled_offset =
                    notify_journal_off_advance_b129(self.journalled_offset, record_offset);
                return NotifyExecVerdict::SuppressedSameAttentionTransition;
            }
        }
        if self.pushes_used >= self.max_pushes_per_window {
            return NotifyExecVerdict::RateLimited {
                max_pushes: self.max_pushes_per_window,
            };
        }
        if let Some(fp) = attention_fp {
            self.last_attention_fp = fp;
        }
        self.journalled_offset =
            notify_journal_off_advance_b129(self.journalled_offset, record_offset);
        self.pushes_used = notify_pushes_clamp_b129(
            self.pushes_used.saturating_add(1),
            self.max_pushes_per_window,
        );
        NotifyExecVerdict::JournalThenExec {
            journalled_offset: self.journalled_offset,
            pushes_used: self.pushes_used,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn waits_for_ordered_durable_head_dedups_attention_transitions_and_rate_limits() {
        let mut gate = NotifyJournalBeforeExecGate::new(0, 2);

        // Undurable record (offset 12 > durable_head 10) waits!
        assert_eq!(
            gate.evaluate_candidate(12, 10, Some(0xABCD)),
            NotifyExecVerdict::DeferredUntilDurable {
                record_offset: 12,
                durable_head_offset: 10,
            }
        );

        // Once durable_head reaches 12, journals BEFORE exec!
        assert_eq!(
            gate.evaluate_candidate(12, 12, Some(0xABCD)),
            NotifyExecVerdict::JournalThenExec {
                journalled_offset: 12,
                pushes_used: 1,
            }
        );
        // Repeated attention fingerprint 0xABCD at offset 15 is suppressed once-per-transition!
        assert_eq!(
            gate.evaluate_candidate(15, 20, Some(0xABCD)),
            NotifyExecVerdict::SuppressedSameAttentionTransition
        );
        // Distinct mail ask at offset 18 consumes push 2; offset 19 hits rate limit!
        assert_eq!(
            gate.evaluate_candidate(18, 20, None),
            NotifyExecVerdict::JournalThenExec {
                journalled_offset: 18,
                pushes_used: 2,
            }
        );
        assert_eq!(
            gate.evaluate_candidate(19, 20, None),
            NotifyExecVerdict::RateLimited { max_pushes: 2 }
        );
    }
}
