// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Dual-deadline PTY semantic quiescence + spinner-ceiling wake scheduler
//! (`Astream.Pump.TlaSemanticQuiesceDeadlineFence`).
//!
//! Ensures `astream-pump` (`DESIGN-drive-pipe.md`) reliably wakes turn-based driving agents even
//! when a child REPL emits no `OSC 133` prompt mark or paints an infinite progress spinner:
//! wakes on either quiet-gap (`idle_ms >= quiet_threshold_ms`) or hard turn ceiling (`elapsed_ms >= max_wait_ms`).

#[cfg(clean_islands)]
#[path = "semantic_quiesce_deadline_fence_island.rs"]
mod semantic_quiesce_deadline_fence_island;
#[cfg(clean_islands)]
pub use semantic_quiesce_deadline_fence_island::{
    quiesce_elapsed_clamp_b114, wake_seq_advance_b114,
};

#[cfg(not(clean_islands))]
/// Clamp accumulated turn wait milliseconds to `max_wait_ms`.
#[must_use]
pub const fn quiesce_elapsed_clamp_b114(cand_elapsed: u64, max_wait_ms: u64) -> u64 {
    if cand_elapsed < max_wait_ms {
        cand_elapsed
    } else {
        max_wait_ms
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the pump semantic-wake sequence number.
#[must_use]
pub const fn wake_seq_advance_b114(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}

contract_fn! {
    /// True iff either `idle_ms >= quiet_threshold_ms` or `elapsed_ms >= max_wait_ms`.
    #[must_use]
    pub const fn quiesce_should_wake_b114(
        idle_ms: u64,
        quiet_threshold_ms: u64,
        elapsed_ms: u64,
        max_wait_ms: u64,
    ) -> bool
    clauses [ensures result == (quiet_threshold_ms <= idle_ms || max_wait_ms <= elapsed_ms)]
    {
        quiet_threshold_ms <= idle_ms || max_wait_ms <= elapsed_ms
    }
}

/// Wake decision emitted by `SemanticQuiesceDeadlineFence`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuiesceWakeDecision {
    KeepWaiting { idle_ms: u64, elapsed_ms: u64 },
    WakePromptReady { wake_seq: u64 },
    WakeQuiescent { wake_seq: u64, idle_ms: u64 },
    WakeHardDeadline { wake_seq: u64, elapsed_ms: u64 },
}

/// Stateful dual-deadline wake gate for `aspump`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SemanticQuiesceDeadlineFence {
    quiet_threshold_ms: u64,
    max_wait_ms: u64,
    turn_start_ms: u64,
    last_output_ms: u64,
    wake_seq: u64,
}

impl SemanticQuiesceDeadlineFence {
    #[must_use]
    pub const fn new(quiet_threshold_ms: u64, max_wait_ms: u64, now_ms: u64) -> Self {
        let quiet = if quiet_threshold_ms == 0 {
            250
        } else {
            quiet_threshold_ms
        };
        let hard = if max_wait_ms < quiet {
            quiet.saturating_mul(20)
        } else {
            max_wait_ms
        };
        Self {
            quiet_threshold_ms: quiet,
            max_wait_ms: hard,
            turn_start_ms: now_ms,
            last_output_ms: now_ms,
            wake_seq: 0,
        }
    }

    #[must_use]
    pub const fn wake_seq(&self) -> u64 {
        self.wake_seq
    }

    /// Record PTY output bytes arriving (`saw_osc133_prompt == true` triggers immediate wake).
    pub fn on_output(&mut self, now_ms: u64, saw_osc133_prompt: bool) -> QuiesceWakeDecision {
        self.last_output_ms = now_ms;
        if saw_osc133_prompt {
            let next_seq = self.wake_seq.saturating_add(1);
            self.wake_seq = wake_seq_advance_b114(self.wake_seq, next_seq);
            self.turn_start_ms = now_ms;
            return QuiesceWakeDecision::WakePromptReady {
                wake_seq: self.wake_seq,
            };
        }
        self.on_tick(now_ms)
    }

    /// Evaluate quiet-gap and hard-ceiling deadlines at `now_ms`.
    pub fn on_tick(&mut self, now_ms: u64) -> QuiesceWakeDecision {
        let idle_ms = now_ms.saturating_sub(self.last_output_ms);
        let raw_elapsed = now_ms.saturating_sub(self.turn_start_ms);
        let elapsed_ms = quiesce_elapsed_clamp_b114(raw_elapsed, self.max_wait_ms);
        if !quiesce_should_wake_b114(
            idle_ms,
            self.quiet_threshold_ms,
            elapsed_ms,
            self.max_wait_ms,
        ) {
            return QuiesceWakeDecision::KeepWaiting {
                idle_ms,
                elapsed_ms,
            };
        }
        let next_seq = self.wake_seq.saturating_add(1);
        self.wake_seq = wake_seq_advance_b114(self.wake_seq, next_seq);
        self.turn_start_ms = now_ms;
        self.last_output_ms = now_ms;
        if idle_ms >= self.quiet_threshold_ms {
            QuiesceWakeDecision::WakeQuiescent {
                wake_seq: self.wake_seq,
                idle_ms,
            }
        } else {
            QuiesceWakeDecision::WakeHardDeadline {
                wake_seq: self.wake_seq,
                elapsed_ms,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wakes_on_hard_deadline_even_when_spinner_never_goes_quiet() {
        let mut f = SemanticQuiesceDeadlineFence::new(200, 1_000, 0);
        assert_eq!(
            f.on_output(500, false),
            QuiesceWakeDecision::KeepWaiting {
                idle_ms: 0,
                elapsed_ms: 500,
            }
        );
        assert_eq!(
            f.on_output(1_000, false),
            QuiesceWakeDecision::WakeHardDeadline {
                wake_seq: 1,
                elapsed_ms: 1_000,
            }
        );
    }
}
