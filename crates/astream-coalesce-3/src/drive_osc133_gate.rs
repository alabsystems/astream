// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! OSC-133 / OSC-633 Shell-Integration Authority Handoff & Nested-Prompt Gate.
//!
//! Enforces the `aspump` drive-pipe prompt-ready arbitration contract:
//! 1. Only lifecycle marks `A` (prompt-start), `C` (command-start), and `D` (command-end)
//!    hand prompt-ready authority to OSC-133 and permanently disable glyph-profile fallback.
//!    Non-lifecycle marks (`B`, `E`, `P`, or unknown letters) NEVER blind glyph fallback.
//! 2. Once OSC-133 owns authority, glyph-profile matches (`$`, `%`, `#`, `❯`, `>>>`) are
//!    suppressed unconditionally — preventing stalled progress bars (`45%`) or nested REPL
//!    prompts while `C` is in flight (`in_flight_depth > 0`) from waking a driving agent early.
//!
//! Backed by Clean TLA+ Island `Astream.Pump.TlaOsc133AuthorityGate`
//! (`drive_osc133_gate_island.rs`), proving `inFlightDepth <= maxDepth` and
//! `emittedWakes <= totalLifecycleMarks`.

#![allow(clippy::absurd_extreme_comparisons)]

#[cfg(clean_islands)]
#[path = "drive_osc133_gate_island.rs"]
mod island;
#[cfg(clean_islands)]
pub use island::{osc133_depth_clamp, osc133_wake_clamp};

#[cfg(not(clean_islands))]
#[inline]
pub const fn osc133_depth_clamp(depth: u64, max_depth: u64) -> u64 {
    if depth < max_depth {
        depth
    } else {
        max_depth
    }
}

#[cfg(not(clean_islands))]
#[inline]
pub const fn osc133_wake_clamp(wakes: u64, lifecycle_marks: u64) -> u64 {
    if wakes < lifecycle_marks {
        wakes
    } else {
        lifecycle_marks
    }
}

contract_fn! {
    /// Kernel-certified check that no OSC-133 command is currently in flight (`in_flight_depth <= 0`).
    #[must_use]
    #[inline]
    pub const fn osc133_command_idle(in_flight_depth: u64) -> bool
    clauses [ensures result == (in_flight_depth <= 0)]
    {
        in_flight_depth <= 0
    }
}

/// Default maximum tracked nested command depth (`1` for standard top-level shell integration).
pub const DEFAULT_MAX_COMMAND_DEPTH: u64 = 1;

/// Action emitted to the `aspump` agent wake channel.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PromptGateWake {
    /// Suppress wake (non-lifecycle mark, command still in flight, or glyph suppressed by OSC).
    Suppress,
    /// Authoritative OSC-133 `A` prompt-ready wake.
    OscPromptReady,
    /// Authoritative OSC-133 `D` command-finished wake with optional exit status.
    OscCommandFinished { exit_code: Option<i32> },
    /// Fallback glyph-profile prompt-ready wake (allowed ONLY before any `A`/`C`/`D` mark).
    GlyphFallbackPromptReady,
}

/// Stateful OSC-133/633 prompt-authority gate certified by `TlaOsc133AuthorityGate`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Osc133AuthorityGate {
    osc_owns_authority: bool,
    in_flight_depth: u64,
    max_depth: u64,
    total_lifecycle_marks: u64,
    emitted_wakes: u64,
}

impl Default for Osc133AuthorityGate {
    fn default() -> Self {
        Self::new(DEFAULT_MAX_COMMAND_DEPTH)
    }
}

impl Osc133AuthorityGate {
    #[inline]
    pub const fn new(max_depth: u64) -> Self {
        let cap = if max_depth == 0 { 1 } else { max_depth };
        Self {
            osc_owns_authority: false,
            in_flight_depth: 0,
            max_depth: cap,
            total_lifecycle_marks: 0,
            emitted_wakes: 0,
        }
    }

    #[inline]
    pub const fn osc_owns_authority(&self) -> bool {
        self.osc_owns_authority
    }

    #[inline]
    pub const fn in_flight_depth(&self) -> u64 {
        self.in_flight_depth
    }

    #[inline]
    pub const fn emitted_wakes(&self) -> u64 {
        self.emitted_wakes
    }

    #[inline]
    pub const fn total_lifecycle_marks(&self) -> u64 {
        self.total_lifecycle_marks
    }

    /// Feeds an OSC-133 / OSC-633 mark letter (`b'A'`, `b'B'`, `b'C'`, `b'D'`, `b'E'`, `b'P'`, ...).
    pub fn observe_osc_mark(&mut self, mark_letter: u8, exit_code: Option<i32>) -> PromptGateWake {
        match mark_letter {
            b'A' => {
                self.osc_owns_authority = true;
                let next_marks = self.total_lifecycle_marks.saturating_add(1);
                self.in_flight_depth = osc133_depth_clamp(0, self.max_depth);
                let raw_wakes = self.emitted_wakes.saturating_add(1);
                self.total_lifecycle_marks = next_marks;
                self.emitted_wakes = osc133_wake_clamp(raw_wakes, next_marks);
                PromptGateWake::OscPromptReady
            }
            b'C' => {
                self.osc_owns_authority = true;
                let next_marks = self.total_lifecycle_marks.saturating_add(1);
                let raw_depth = self.in_flight_depth.saturating_add(1);
                self.in_flight_depth = osc133_depth_clamp(raw_depth, self.max_depth);
                self.total_lifecycle_marks = next_marks;
                self.emitted_wakes = osc133_wake_clamp(self.emitted_wakes, next_marks);
                PromptGateWake::Suppress
            }
            b'D' => {
                self.osc_owns_authority = true;
                let next_marks = self.total_lifecycle_marks.saturating_add(1);
                let raw_depth = self.in_flight_depth.saturating_sub(1);
                self.in_flight_depth = osc133_depth_clamp(raw_depth, self.max_depth);
                let raw_wakes = self.emitted_wakes.saturating_add(1);
                self.total_lifecycle_marks = next_marks;
                self.emitted_wakes = osc133_wake_clamp(raw_wakes, next_marks);
                PromptGateWake::OscCommandFinished { exit_code }
            }
            // Non-lifecycle marks (`B`, `E`, `P`, etc.) NEVER claim authority or wake!
            _ => PromptGateWake::Suppress,
        }
    }

    /// Evaluates a settled-screen glyph-profile match (`$`, `%`, `#`, `❯`, `>>>`).
    #[inline]
    pub const fn evaluate_settled_glyph(&self, glyph_matched: bool) -> PromptGateWake {
        if !glyph_matched {
            return PromptGateWake::Suppress;
        }
        if self.osc_owns_authority || !osc133_command_idle(self.in_flight_depth) {
            PromptGateWake::Suppress
        } else {
            PromptGateWake::GlyphFallbackPromptReady
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stray_non_lifecycle_marks_do_not_blind_glyph_profile() {
        let mut gate = Osc133AuthorityGate::default();
        assert_eq!(gate.observe_osc_mark(b'B', None), PromptGateWake::Suppress);
        assert_eq!(gate.observe_osc_mark(b'P', None), PromptGateWake::Suppress);
        assert!(!gate.osc_owns_authority());
        assert_eq!(
            gate.evaluate_settled_glyph(true),
            PromptGateWake::GlyphFallbackPromptReady
        );
    }

    #[test]
    fn lifecycle_mark_permanently_disables_glyph_and_tracks_in_flight_command() {
        let mut gate = Osc133AuthorityGate::default();
        assert_eq!(
            gate.observe_osc_mark(b'A', None),
            PromptGateWake::OscPromptReady
        );
        assert!(gate.osc_owns_authority());
        // Stalled progress bar ending in `%` while command runs (`C`) must NEVER wake!
        assert_eq!(gate.observe_osc_mark(b'C', None), PromptGateWake::Suppress);
        assert_eq!(gate.in_flight_depth(), 1);
        assert_eq!(gate.evaluate_settled_glyph(true), PromptGateWake::Suppress);

        // Command finishes (`D;0`) -> emits authoritative finish wake.
        assert_eq!(
            gate.observe_osc_mark(b'D', Some(0)),
            PromptGateWake::OscCommandFinished { exit_code: Some(0) }
        );
        assert_eq!(gate.in_flight_depth(), 0);
        // Glyph remains permanently disabled even when idle after `D`.
        assert_eq!(gate.evaluate_settled_glyph(true), PromptGateWake::Suppress);
        assert!(gate.emitted_wakes() <= gate.total_lifecycle_marks());
    }
}
