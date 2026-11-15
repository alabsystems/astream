// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm-link notify` pre-exec journal (`ATERM_NOTIFY_DUP=1`) & per-subject `attention=` transition
//! dedup (`docs/DESIGN-aterm-fabric.md` §9.3 lines 2691–2722, aterm r3-22;
//! `Astream.Agent.TlaNotifyAttentionTransitionDedup`).
//!
//! Prevents presence republish storms from exhausting the human notifier rate budget:
//! - Journal entry is written BEFORE `<cmd>` executes so an interrupted command re-fires marked
//!   `ATERM_NOTIFY_DUP=1` rather than silently dropping,
//! - Per presence subject, `last_told_attention` records the `attention=` hash last delivered with
//!   `rc == 0`:
//!   * A standing republish carrying `attention == last_told_attention` pages nobody and charges `0`,
//!   * A `clear` (`None`) resets `last_told_attention` (re-arming the subject) and charges `0`,
//!   * A rate-dropped escalation or `rc != 0` command leaves `last_told_attention` UNSET so the next
//!     presence republish offers it again, while the dropped offset itself is terminal!

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

#[cfg(clean_islands)]
#[path = "notify_attention_transition_dedup_island.rs"]
mod notify_attention_transition_dedup_island;
#[cfg(clean_islands)]
pub use notify_attention_transition_dedup_island::{
    notify_budget_clamp_b135, notify_cursor_advance_b135,
};

/// Default per-window outbound notification budget (`16` pages per window).
pub const NOTIFY_BUDGET_DEFAULT: u64 = 16;

#[cfg(not(clean_islands))]
/// Clamp remaining notifier rate-limit tokens to `budget_cap`.
#[must_use]
pub const fn notify_budget_clamp_b135(cand_tokens: u64, budget_cap: u64) -> u64 {
    if cand_tokens < budget_cap {
        cand_tokens
    } else {
        budget_cap
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance terminal processed offset watermark (`offset + 1`).
#[must_use]
pub const fn notify_cursor_advance_b135(cur_cursor: u64, cand_cursor: u64) -> u64 {
    if cur_cursor < cand_cursor {
        cand_cursor
    } else {
        cur_cursor
    }
}

contract_fn! {
    /// True iff `has_attention && !matches_last_told && budget_tokens > 0`.
    #[must_use]
    pub const fn notify_should_fire_cmd_b135(
        has_attention: bool,
        matches_last_told: bool,
        budget_tokens: u64,
    ) -> bool
    clauses [ensures result == (has_attention && !matches_last_told && budget_tokens > 0)]
    {
        has_attention && !matches_last_told && budget_tokens > 0
    }
}

/// Decision when evaluating a presence `attention=` record or an in-doubt journal recovery.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum NotifyOfferVerdict {
    /// Persist pre-exec journal first, then run `<cmd>` (`dup_env_flag` sets `ATERM_NOTIFY_DUP=1`).
    JournalAndRunCmd { offset: u64, dup_env_flag: bool },
    /// Offset already terminal (`offset < cursor`).
    SkippedOffsetAlreadyTerminal,
    /// Presence `attention=` cleared (`None`): re-armed subject, `0` budget spent!
    ClearedAndRearmed,
    /// Standing republish matches `last_told` (`rc == 0`): suppressed, `0` budget spent!
    SuppressedStandingTransition,
    /// Rate budget empty: offset becomes terminal, `last_told` stays unchanged for next republish!
    DroppedRateLimitedTerminalOffset,
}

/// Outbound human notifier state machine for a tracked presence subject + global offset cursor.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct NotifyAttentionDeduper {
    budget_cap: u64,
    budget_tokens: u64,
    terminal_cursor: u64, // offset + 1
    last_told_attention: Option<u64>,
    in_doubt_journal: Option<(u64, u64)>, // (offset, attention_hash)
}

impl NotifyAttentionDeduper {
    #[must_use]
    pub const fn new(since_offset: u64, budget_cap: u64) -> Self {
        let cap = if budget_cap == 0 {
            NOTIFY_BUDGET_DEFAULT
        } else {
            budget_cap
        };
        Self {
            budget_cap: cap,
            budget_tokens: cap,
            terminal_cursor: since_offset,
            last_told_attention: None,
            in_doubt_journal: None,
        }
    }

    #[must_use]
    pub const fn budget_tokens(&self) -> u64 {
        notify_budget_clamp_b135(self.budget_tokens, self.budget_cap)
    }

    #[must_use]
    pub const fn terminal_cursor(&self) -> u64 {
        self.terminal_cursor
    }

    /// Refill rate-limit window up to `budget_cap` (terminal dropped offsets are NEVER re-offered!).
    pub fn refill_budget(&mut self, tokens: u64) {
        self.budget_tokens =
            notify_budget_clamp_b135(self.budget_tokens.saturating_add(tokens), self.budget_cap);
    }

    /// Recover an unfinished pre-exec journal entry on restart (`ATERM_NOTIFY_DUP=1`).
    #[allow(clippy::question_mark)]
    pub fn recover_in_doubt(&self) -> Option<NotifyOfferVerdict> {
        let Some((offset, _)) = self.in_doubt_journal else {
            return None;
        };
        Some(NotifyOfferVerdict::JournalAndRunCmd {
            offset,
            dup_env_flag: true,
        })
    }

    /// Evaluate a presence row at `offset` carrying `attention_hash` (`None` = cleared `-`).
    pub fn evaluate_presence_row(
        &mut self,
        offset: u64,
        attention_hash: Option<u64>,
    ) -> NotifyOfferVerdict {
        if offset < self.terminal_cursor {
            return NotifyOfferVerdict::SkippedOffsetAlreadyTerminal;
        }
        let next_cur = offset.saturating_add(1);
        let Some(att) = attention_hash else {
            self.last_told_attention = None;
            self.terminal_cursor = notify_cursor_advance_b135(self.terminal_cursor, next_cur);
            return NotifyOfferVerdict::ClearedAndRearmed;
        };
        let matches_told = self.last_told_attention == Some(att);
        if matches_told {
            self.terminal_cursor = notify_cursor_advance_b135(self.terminal_cursor, next_cur);
            return NotifyOfferVerdict::SuppressedStandingTransition;
        }
        if !notify_should_fire_cmd_b135(true, false, self.budget_tokens) {
            // Terminal for THIS offset, but `last_told_attention` stays unchanged!
            self.terminal_cursor = notify_cursor_advance_b135(self.terminal_cursor, next_cur);
            return NotifyOfferVerdict::DroppedRateLimitedTerminalOffset;
        }
        self.budget_tokens = self.budget_tokens.saturating_sub(1);
        // Write pre-exec journal BEFORE running `<cmd>`!
        self.in_doubt_journal = Some((offset, att));
        NotifyOfferVerdict::JournalAndRunCmd {
            offset,
            dup_env_flag: false,
        }
    }

    /// Settle the journaled command execution (`rc == 0` commits `last_told_attention`; `rc != 0` leaves unset!).
    pub fn settle_command_exit(&mut self, exit_rc: i32) {
        let Some((offset, att)) = core::mem::take(&mut self.in_doubt_journal) else {
            return;
        };
        self.terminal_cursor =
            notify_cursor_advance_b135(self.terminal_cursor, offset.saturating_add(1));
        if exit_rc == 0 {
            self.last_told_attention = Some(att);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn standing_republish_spends_zero_budget_clear_rearms_and_failed_cmd_retries_on_republish() {
        let mut d = NotifyAttentionDeduper::new(10, 2);
        // First raise at offset 10 fires `<cmd>`:
        assert_eq!(
            d.evaluate_presence_row(10, Some(0xAA)),
            NotifyOfferVerdict::JournalAndRunCmd {
                offset: 10,
                dup_env_flag: false
            }
        );
        // Crash before settle -> recovery re-fires with `ATERM_NOTIFY_DUP=1`!
        assert_eq!(
            d.recover_in_doubt(),
            Some(NotifyOfferVerdict::JournalAndRunCmd {
                offset: 10,
                dup_env_flag: true
            })
        );
        // Command fails (`rc = 1`) -> `last_told_attention` is NOT recorded!
        d.settle_command_exit(1);
        assert_eq!(d.budget_tokens(), 1);
        // Republish at offset 11 offers `0xAA` again!
        assert_eq!(
            d.evaluate_presence_row(11, Some(0xAA)),
            NotifyOfferVerdict::JournalAndRunCmd {
                offset: 11,
                dup_env_flag: false
            }
        );
        d.settle_command_exit(0);
        assert_eq!(d.budget_tokens(), 0);
        // Standing republish at offset 12 is suppressed even with 0 budget!
        assert_eq!(
            d.evaluate_presence_row(12, Some(0xAA)),
            NotifyOfferVerdict::SuppressedStandingTransition
        );
        // Clear at offset 13 re-arms; new raise of `0xAA` at 14 with 0 budget drops 14 terminally
        // without setting `last_told`, so after refill republish at 15 fires!
        assert_eq!(
            d.evaluate_presence_row(13, None),
            NotifyOfferVerdict::ClearedAndRearmed
        );
        assert_eq!(
            d.evaluate_presence_row(14, Some(0xAA)),
            NotifyOfferVerdict::DroppedRateLimitedTerminalOffset
        );
        d.refill_budget(2);
        assert_eq!(
            d.evaluate_presence_row(14, Some(0xAA)),
            NotifyOfferVerdict::SkippedOffsetAlreadyTerminal
        );
        assert_eq!(
            d.evaluate_presence_row(15, Some(0xAA)),
            NotifyOfferVerdict::JournalAndRunCmd {
                offset: 15,
                dup_env_flag: false
            }
        );
    }
}
