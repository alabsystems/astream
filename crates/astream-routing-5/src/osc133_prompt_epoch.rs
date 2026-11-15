// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! OSC 133 semantic prompt & unsent-input Autopilot guard (`Astream.Pump.TlaOsc133PromptEpoch`).
//!
//! Tracks `OSC 133 ; A / B / C / D` shell-integration markers together with human
//! keystroke activity so `aterm` Autopilot (`cruise` / `land`) upholds:
//! *"Nothing is typed while the person types or has input unsent."*

#[cfg(clean_islands)]
#[path = "osc133_prompt_epoch_island.rs"]
mod osc133_prompt_epoch_island;
#[cfg(clean_islands)]
pub use osc133_prompt_epoch_island::{osc133_input_clamp, osc133_turn_advance};

/// Maximum tracked unsent human input bytes at an interactive prompt.
pub const MAX_UNSENT_INPUT_BYTES: u64 = 65_536;

#[cfg(not(clean_islands))]
/// Monotonically advance the semantic shell turn sequence.
#[must_use]
pub const fn osc133_turn_advance(cur_turn: u64, cand_turn: u64) -> u64 {
    if cur_turn < cand_turn {
        cand_turn
    } else {
        cur_turn
    }
}

#[cfg(not(clean_islands))]
/// Clamp tracked unsent human input byte count to `max_input_bytes`.
#[must_use]
pub const fn osc133_input_clamp(cand_bytes: u64, max_input_bytes: u64) -> u64 {
    if cand_bytes < max_input_bytes {
        cand_bytes
    } else {
        max_input_bytes
    }
}

contract_fn! {
    /// True iff `unsent_bytes == zero_expected` (`0`), permitting Autopilot injection.
    #[must_use]
    pub const fn osc133_autopilot_clear(unsent_bytes: u64, zero_expected: u64) -> bool
    clauses [ensures result == (unsent_bytes == zero_expected)]
    {
        unsent_bytes == zero_expected
    }
}

/// Current OSC 133 semantic shell phase.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Osc133Phase {
    /// `133;A`: shell is rendering prompt prefix.
    PromptRendering,
    /// `133;B`: prompt ready for command line input.
    PromptReady,
    /// `133;C`: command execution in flight.
    CommandRunning,
    /// `133;D`: previous command finished with `exit_code`.
    CommandFinished { exit_code: i32 },
}

/// Stateful OSC 133 turn & unsent-input tracker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Osc133PromptTracker {
    phase: Osc133Phase,
    turn_seq: u64,
    unsent_human_bytes: u64,
    last_human_keystroke_ms: u64,
    typing_grace_ms: u64,
}

impl Osc133PromptTracker {
    #[must_use]
    pub const fn new(typing_grace_ms: u64) -> Self {
        Self {
            phase: Osc133Phase::PromptReady,
            turn_seq: 0,
            unsent_human_bytes: 0,
            last_human_keystroke_ms: 0,
            typing_grace_ms,
        }
    }

    #[must_use]
    pub const fn phase(&self) -> Osc133Phase {
        self.phase
    }

    #[must_use]
    pub const fn turn_seq(&self) -> u64 {
        self.turn_seq
    }

    #[must_use]
    pub const fn unsent_human_bytes(&self) -> u64 {
        self.unsent_human_bytes
    }

    /// Record `OSC 133 ; A` (prompt rendering start).
    pub fn on_prompt_start(&mut self) {
        self.phase = Osc133Phase::PromptRendering;
        self.unsent_human_bytes = 0;
    }

    /// Record `OSC 133 ; B` (interactive input ready); advances `turn_seq`.
    pub fn on_command_input_ready(&mut self) -> u64 {
        self.phase = Osc133Phase::PromptReady;
        self.unsent_human_bytes = 0;
        let cand = self.turn_seq.saturating_add(1);
        self.turn_seq = osc133_turn_advance(self.turn_seq, cand);
        self.turn_seq
    }

    /// Record `OSC 133 ; C` (command submitted / executing).
    pub fn on_command_executed(&mut self) {
        self.phase = Osc133Phase::CommandRunning;
        self.unsent_human_bytes = 0;
    }

    /// Record `OSC 133 ; D ; exit_code` (command finished).
    pub fn on_command_finished(&mut self, exit_code: i32) {
        self.phase = Osc133Phase::CommandFinished { exit_code };
        self.unsent_human_bytes = 0;
    }

    /// Track human keystrokes at the prompt (`submitted = true` on Enter / Ctrl-C line clear).
    pub fn on_human_input(
        &mut self,
        added_bytes: u64,
        backspace_bytes: u64,
        submitted: bool,
        now_ms: u64,
    ) {
        self.last_human_keystroke_ms = now_ms;
        if submitted {
            self.unsent_human_bytes = 0;
            return;
        }
        let after_del = self.unsent_human_bytes.saturating_sub(backspace_bytes);
        let cand = after_del.saturating_add(added_bytes);
        self.unsent_human_bytes = osc133_input_clamp(cand, MAX_UNSENT_INPUT_BYTES);
    }

    /// True iff prompt is ready, zero unsent human input exists, and human typing grace has elapsed.
    #[must_use]
    pub const fn can_autopilot_type(&self, now_ms: u64) -> bool {
        if !matches!(self.phase, Osc133Phase::PromptReady) {
            return false;
        }
        if !osc133_autopilot_clear(self.unsent_human_bytes, 0) {
            return false;
        }
        if self.last_human_keystroke_ms != 0
            && now_ms.saturating_sub(self.last_human_keystroke_ms) < self.typing_grace_ms
        {
            return false;
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_autopilot_while_human_has_unsent_input_or_is_typing() {
        let mut tr = Osc133PromptTracker::new(500);
        assert_eq!(tr.on_command_input_ready(), 1);
        assert!(tr.can_autopilot_type(1_000));

        // Person types 4 characters without hitting Enter -> Autopilot blocked indefinitely!
        tr.on_human_input(4, 0, false, 1_100);
        assert!(!tr.can_autopilot_type(10_000));

        // Person backspaces all 4 characters -> still blocked during 500ms typing grace, then clear!
        tr.on_human_input(0, 4, false, 10_200);
        assert!(!tr.can_autopilot_type(10_500));
        assert!(tr.can_autopilot_type(10_700));

        // Command starts running -> Autopilot blocked until next 133;B!
        tr.on_command_executed();
        assert!(!tr.can_autopilot_type(20_000));
        tr.on_command_finished(0);
        assert!(!tr.can_autopilot_type(20_100));
        assert_eq!(tr.on_command_input_ready(), 2);
        assert!(tr.can_autopilot_type(20_200));
    }
}
