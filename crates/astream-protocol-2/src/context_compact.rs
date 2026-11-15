// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Deterministic Prompt-Context Token Budget & Sliding-Window Compaction Planner
//! (`Astream.Agent.TlaContextCompactor`).
//!
//! Long-running `aterm` `/goal` and `autopilot=cruise` sessions execute hundreds of turns until
//! approaching model context limits (`/compact`). For `astream-agent`'s unified replay and
//! counterfactual fork (`fork_session`) to remain 100% deterministic across compactions, the
//! choice of *when* to compact and *which* contiguous turn span `[evict_start..evict_end)` to
//! fold into a summary record must be a pure, deterministic state machine with formally bounded
//! retained token counts (`retained_tokens <= window_budget`) and monotone compaction generation
//! (`prev_gen <= compact_gen`).

#[cfg(clean_islands)]
#[path = "context_compact_island.rs"]
mod context_compact_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ctx_tokens_clamp(retained_tokens: u64, window_budget: u64) -> u64 {
    if retained_tokens < window_budget {
        retained_tokens
    } else {
        window_budget
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ctx_compact_gen_advance(prev_gen: u64, cand_gen: u64) -> u64 {
    if prev_gen < cand_gen {
        cand_gen
    } else {
        prev_gen
    }
}
#[cfg(clean_islands)]
pub use context_compact_island::{ctx_compact_gen_advance, ctx_tokens_clamp};

/// Maximum historical turn entries tracked in one planner instance (`65_536`).
pub const MAX_TRACKED_CONTEXT_TURNS: usize = 65_536;

contract_fn! {
    /// Verified check whether `used_tokens` has reached `trigger_watermark`
    /// (`trigger_watermark <= used_tokens`), linked via `clean-kernel-defeq`
    /// to `ctx_needs_compact_isl`.
    #[must_use]
    pub const fn ctx_needs_compact(used_tokens: u64, trigger_watermark: u64) -> bool
    clauses [ensures result == (trigger_watermark <= used_tokens)]
    {
        trigger_watermark <= used_tokens
    }
}

/// Token accounting record for one transcript turn/step.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TurnTokenSpan {
    /// Monotone turn identifier in the cognition log.
    pub turn_id: u64,
    /// Estimated token weight of this turn (`>= 1`).
    pub tokens: u64,
    /// Pinned turns (e.g. system rules, active `NEEDS YOU` or handoff summary) are never evicted.
    pub pinned: bool,
}

/// Deterministic compaction action computed by [`ContextCompactionPlanner::plan_if_needed`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ContextCompactionPlan {
    /// Current token usage is strictly below `trigger_watermark`; no compaction needed.
    WithinBudget { retained_tokens: u64 },
    /// Summarize and evict `evicted_turn_ids`, replacing them with a summary capped at
    /// `max_summary_tokens` and advancing `compact_gen`.
    Compact {
        new_generation: u64,
        evicted_turn_ids: Vec<u64>,
        evicted_tokens: u64,
        max_summary_tokens: u64,
        projected_retained_tokens: u64,
    },
}

/// Deterministic sliding-window context compaction planner.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContextCompactionPlanner {
    window_budget: u64,
    trigger_watermark: u64,
    target_post_compact: u64,
    keep_recent_turns: usize,
    compact_gen: u64,
    retained_tokens: u64,
}

impl ContextCompactionPlanner {
    /// Create a compaction planner for `window_budget` tokens:
    /// - Triggers when total tokens `>= trigger_watermark` (clamped `<= window_budget`),
    /// - Evicts oldest unpinned turns (preserving at least `keep_recent_turns` trailing turns when
    ///   they fit) until tokens `<= target_post_compact` (clamped `<= trigger_watermark`).
    #[must_use]
    pub const fn new(
        window_budget: u64,
        trigger_watermark: u64,
        target_post_compact: u64,
        keep_recent_turns: usize,
    ) -> Self {
        let budget = if window_budget == 0 { 1 } else { window_budget };
        let trigger = if trigger_watermark == 0 || trigger_watermark > budget {
            budget
        } else {
            trigger_watermark
        };
        let target = if target_post_compact > trigger {
            trigger
        } else {
            target_post_compact
        };
        Self {
            window_budget: budget,
            trigger_watermark: trigger,
            target_post_compact: target,
            keep_recent_turns,
            compact_gen: 0,
            retained_tokens: 0,
        }
    }

    /// Monotone compaction generation (`>= 0`).
    #[must_use]
    pub const fn compact_gen(&self) -> u64 {
        self.compact_gen
    }

    /// Latest clamped retained token count (`<= window_budget`).
    #[must_use]
    pub const fn retained_tokens(&self) -> u64 {
        self.retained_tokens
    }

    /// Configured hard context window budget.
    #[must_use]
    pub const fn window_budget(&self) -> u64 {
        self.window_budget
    }

    /// Inspect `turns` and deterministically plan a `/compact` pass if `trigger_watermark` is reached.
    pub fn plan_if_needed(
        &mut self,
        turns: &[TurnTokenSpan],
        summary_budget_cap: u64,
    ) -> ContextCompactionPlan {
        let capped_len = if turns.len() < MAX_TRACKED_CONTEXT_TURNS {
            turns.len()
        } else {
            MAX_TRACKED_CONTEXT_TURNS
        };
        let slice = match turns.get(..capped_len) {
            Some(s) => s,
            None => turns,
        };

        let mut total_used = 0u64;
        let mut idx = 0usize;
        while idx < slice.len() {
            if let Some(t) = slice.get(idx) {
                total_used = total_used.saturating_add(t.tokens);
            }
            idx = idx.saturating_add(1);
        }

        if !ctx_needs_compact(total_used, self.trigger_watermark) {
            self.retained_tokens = ctx_tokens_clamp(total_used, self.window_budget);
            return ContextCompactionPlan::WithinBudget {
                retained_tokens: self.retained_tokens,
            };
        }

        let protected_tail_start = slice.len().saturating_sub(self.keep_recent_turns);
        let mut evicted_ids = Vec::new();
        let mut evicted_tokens = 0u64;
        let mut remaining = total_used;

        // Pass 1: evict oldest unpinned turns strictly before `protected_tail_start`.
        let mut pos = 0usize;
        while pos < protected_tail_start && remaining > self.target_post_compact {
            if let Some(t) = slice.get(pos) {
                if !t.pinned {
                    evicted_ids.push(t.turn_id);
                    evicted_tokens = evicted_tokens.saturating_add(t.tokens);
                    remaining = remaining.saturating_sub(t.tokens);
                }
            }
            pos = pos.saturating_add(1);
        }

        // Pass 2: if still over `window_budget`, evict into the unpinned tail except the very last turn.
        let hard_stop = slice.len().saturating_sub(1);
        while pos < hard_stop && remaining > self.window_budget {
            if let Some(t) = slice.get(pos) {
                if !t.pinned {
                    evicted_ids.push(t.turn_id);
                    evicted_tokens = evicted_tokens.saturating_add(t.tokens);
                    remaining = remaining.saturating_sub(t.tokens);
                }
            }
            pos = pos.saturating_add(1);
        }

        let headroom = self.target_post_compact.saturating_sub(remaining);
        let max_summary_tokens = if summary_budget_cap < headroom {
            summary_budget_cap
        } else {
            headroom
        };
        let projected = ctx_tokens_clamp(
            remaining.saturating_add(max_summary_tokens),
            self.window_budget,
        );
        self.retained_tokens = projected;
        let cand_gen = self.compact_gen.saturating_add(1);
        self.compact_gen = ctx_compact_gen_advance(self.compact_gen, cand_gen);

        ContextCompactionPlan::Compact {
            new_generation: self.compact_gen,
            evicted_turn_ids: evicted_ids,
            evicted_tokens,
            max_summary_tokens,
            projected_retained_tokens: projected,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clean_twins_match_invariants() {
        assert_eq!(ctx_tokens_clamp(40_000, 128_000), 40_000);
        assert_eq!(ctx_tokens_clamp(200_000, 128_000), 128_000);
        assert_eq!(ctx_compact_gen_advance(2, 3), 3);
        assert_eq!(ctx_compact_gen_advance(3, 1), 3);
        assert!(!ctx_needs_compact(99_999, 100_000));
        assert!(ctx_needs_compact(100_000, 100_000));
    }

    #[test]
    fn preserves_pinned_system_and_recent_tail_while_evicting_oldest_history() {
        let mut planner = ContextCompactionPlanner::new(10_000, 8_000, 5_000, 2);
        let turns = vec![
            TurnTokenSpan {
                turn_id: 0,
                tokens: 1_500,
                pinned: true,
            },
            TurnTokenSpan {
                turn_id: 1,
                tokens: 2_500,
                pinned: false,
            },
            TurnTokenSpan {
                turn_id: 2,
                tokens: 2_500,
                pinned: false,
            },
            TurnTokenSpan {
                turn_id: 3,
                tokens: 1_200,
                pinned: false,
            },
            TurnTokenSpan {
                turn_id: 4,
                tokens: 1_300,
                pinned: false,
            },
        ];

        // Total = 9,000 >= trigger 8,000; turn 0 is pinned, turns 3 & 4 are protected tail (2).
        // Evicts turns 1 & 2 (5,000 tokens), leaving 4,000 + up to 800 summary = 4,800 <= 10,000!
        let plan = planner.plan_if_needed(&turns, 800);
        assert_eq!(
            plan,
            ContextCompactionPlan::Compact {
                new_generation: 1,
                evicted_turn_ids: vec![1, 2],
                evicted_tokens: 5_000,
                max_summary_tokens: 800,
                projected_retained_tokens: 4_800,
            }
        );
        assert_eq!(planner.compact_gen(), 1);
        assert_eq!(planner.retained_tokens(), 4_800);
    }
}
