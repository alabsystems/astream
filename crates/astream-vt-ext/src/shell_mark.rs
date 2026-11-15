// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! OSC 133 (`FTCS` / FinalTerm / iTerm2 / WezTerm / Kitty / `aterm` shell integration)
//! semantic command-lifecycle tracker with Clean-verified offset monotonicity and
//! bounded exit-code clamping (`Astream.Term.TlaShellIntegration`).
//!
//! Tracks streaming chunks across arbitrary byte splits to extract structured
//! [`ShellCommandSpan`] records:
//! - `OSC 133 ; A ST` — prompt start (`PromptStart`)
//! - `OSC 133 ; B ST` — command-line input start (`CommandInputStart`)
//! - `OSC 133 ; C ST` — command execution output start (`CommandExecStart`)
//! - `OSC 133 ; D [; <exit>] ST` — command finished (`CommandFinished`)
//!
//! Both `BEL` (`0x07`) and 7-bit `ESC \` (`0x1B 0x5C`) string terminators are accepted.

#![allow(clippy::question_mark)]

#[cfg(clean_islands)]
#[path = "shell_mark_island.rs"]
mod shell_mark_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn shell_offset_advance(cur_off: u64, next_off: u64) -> u64 {
    if cur_off < next_off {
        next_off
    } else {
        cur_off
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn shell_exit_clamp(raw_exit: u64, max_exit: u64) -> u64 {
    if raw_exit < max_exit {
        raw_exit
    } else {
        max_exit
    }
}
#[cfg(clean_islands)]
pub use shell_mark_island::{shell_exit_clamp, shell_offset_advance};

/// Maximum tracked OSC 133 parameter payload bytes before discarding an overlong sequence.
pub const MAX_OSC133_PARAM_BYTES: usize = 128;

/// Maximum retained completed [`ShellCommandSpan`] entries in a [`ShellLifecycleTracker`].
pub const MAX_RETAINED_SHELL_SPANS: usize = 256;

/// Maximum exit code value (`u16::MAX as u64`, covering POSIX `0..=255` and Windows/signal codes).
pub const MAX_SHELL_EXIT_CODE: u64 = 65_535;

contract_fn! {
    /// Kernel-certified span ordering predicate (`start_off <= end_off`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `shell_span_ordered_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn shell_span_ordered(start_off: u64, end_off: u64) -> bool
    clauses [ensures result == (start_off <= end_off)]
    {
        start_off <= end_off
    }
}

/// Phase of an interactive shell prompt/command cycle reported via OSC 133.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShellPhase {
    /// Outside any known OSC 133 cycle.
    Idle,
    /// `OSC 133 ; A` received — shell is rendering `PS1`.
    Prompt,
    /// `OSC 133 ; B` received — user/agent is editing command input.
    Input,
    /// `OSC 133 ; C` received — command is actively executing.
    Executing,
}

/// Discrete OSC 133 mark parsed from a PTY output stream.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Osc133Mark {
    /// `133;A` — prompt start at `offset`.
    PromptStart { offset: u64 },
    /// `133;B` — command input start (prompt end) at `offset`.
    CommandInputStart { offset: u64 },
    /// `133;C` — command execution output start at `offset`.
    CommandExecStart { offset: u64 },
    /// `133;D` or `133;D;<exit>` — command finished at `offset`.
    CommandFinished { offset: u64, exit_code: Option<u64> },
}

/// Completed or synthetic command-lifecycle span with verified non-decreasing offsets.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShellCommandSpan {
    /// Stream offset where the prompt started (`133;A`), or fallback to input/exec offset.
    pub prompt_offset: u64,
    /// Stream offset where command input started (`133;B`), or fallback to exec offset.
    pub input_offset: u64,
    /// Stream offset where command execution started (`133;C`).
    pub exec_offset: u64,
    /// Stream offset where command execution finished (`133;D`), `exec_offset <= finish_offset`.
    pub finish_offset: u64,
    /// Optional clamped exit status (`<= MAX_SHELL_EXIT_CODE`).
    pub exit_code: Option<u64>,
}

impl ShellCommandSpan {
    /// Byte/record span of the command's execution output (`finish_offset - exec_offset`).
    #[must_use]
    pub const fn output_span(&self) -> u64 {
        self.finish_offset.saturating_sub(self.exec_offset)
    }

    /// True if all four lifecycle offsets are monotonically ordered.
    #[must_use]
    pub const fn is_well_ordered(&self) -> bool {
        shell_span_ordered(self.prompt_offset, self.input_offset)
            && shell_span_ordered(self.input_offset, self.exec_offset)
            && shell_span_ordered(self.exec_offset, self.finish_offset)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LexState {
    Ground,
    AfterEsc,
    InOsc,
    OscEsc,
    OscOverflow,
    OscOverflowEsc,
}

/// Streaming OSC 133 command-lifecycle parser and bounded span recorder.
#[derive(Debug, Clone)]
pub struct ShellLifecycleTracker {
    state: LexState,
    buf: Vec<u8>,
    phase: ShellPhase,
    last_offset: u64,
    prompt_off: Option<u64>,
    input_off: Option<u64>,
    exec_off: Option<u64>,
    completed: Vec<ShellCommandSpan>,
}

impl Default for ShellLifecycleTracker {
    fn default() -> Self {
        Self::new()
    }
}

impl ShellLifecycleTracker {
    /// Create a fresh tracker in [`ShellPhase::Idle`].
    #[must_use]
    pub fn new() -> Self {
        let init_cap = if MAX_OSC133_PARAM_BYTES < 64 {
            MAX_OSC133_PARAM_BYTES
        } else {
            64
        };
        Self {
            state: LexState::Ground,
            buf: {
                let _ = init_cap;
                Vec::new()
            },
            phase: ShellPhase::Idle,
            last_offset: 0,
            prompt_off: None,
            input_off: None,
            exec_off: None,
            completed: Vec::new(),
        }
    }

    /// Current shell lifecycle phase.
    #[must_use]
    pub const fn phase(&self) -> ShellPhase {
        self.phase
    }

    /// Monotone high-water stream offset observed so far.
    #[must_use]
    pub const fn last_offset(&self) -> u64 {
        self.last_offset
    }

    /// Completed command spans retained in bounded FIFO order (`<= MAX_RETAINED_SHELL_SPANS`).
    #[must_use]
    pub fn completed_spans(&self) -> &[ShellCommandSpan] {
        &self.completed
    }

    /// Drain all currently retained [`ShellCommandSpan`] entries.
    pub fn take_completed_spans(&mut self) -> Vec<ShellCommandSpan> {
        core::mem::take(&mut self.completed)
    }

    /// Feed a chunk of PTY output arriving at `record_offset`, returning all discrete
    /// [`Osc133Mark`] events completed during this chunk.
    pub fn feed(&mut self, record_offset: u64, bytes: &[u8]) -> Vec<Osc133Mark> {
        self.last_offset = shell_offset_advance(self.last_offset, record_offset);
        let eff_offset = self.last_offset;
        let mut marks = Vec::new();
        let mut rest = bytes;
        while let &[b, ref tail @ ..] = rest {
            match self.state {
                LexState::Ground => {
                    if b == 0x1b {
                        self.state = LexState::AfterEsc;
                    }
                }
                LexState::AfterEsc => {
                    if b == b']' {
                        self.buf.clear();
                        self.state = LexState::InOsc;
                    } else if b == 0x1b {
                        self.state = LexState::AfterEsc;
                    } else {
                        self.state = LexState::Ground;
                    }
                }
                LexState::InOsc => {
                    if b == 0x07 {
                        self.state = LexState::Ground;
                        if let Some(m) = self.finish_osc(eff_offset) {
                            marks.push(m);
                        }
                    } else if b == 0x1b {
                        self.state = LexState::OscEsc;
                    } else if self.buf.len() < MAX_OSC133_PARAM_BYTES {
                        self.buf.push(b);
                    } else {
                        // Overlong OSC payload: drop until terminator.
                        self.buf.clear();
                        self.state = LexState::OscOverflow;
                    }
                }
                LexState::OscEsc => {
                    if b == b'\\' {
                        self.state = LexState::Ground;
                        if let Some(m) = self.finish_osc(eff_offset) {
                            marks.push(m);
                        }
                    } else if b == b']' {
                        self.buf.clear();
                        self.state = LexState::InOsc;
                    } else if b == 0x1b {
                        self.buf.clear();
                        self.state = LexState::AfterEsc;
                    } else {
                        self.buf.clear();
                        self.state = LexState::Ground;
                    }
                }
                LexState::OscOverflow => {
                    if b == 0x07 {
                        self.state = LexState::Ground;
                    } else if b == 0x1b {
                        self.state = LexState::OscOverflowEsc;
                    }
                }
                LexState::OscOverflowEsc => {
                    if b == b'\\' {
                        self.state = LexState::Ground;
                    } else if b == b']' {
                        self.buf.clear();
                        self.state = LexState::InOsc;
                    } else if b == 0x1b {
                        self.state = LexState::AfterEsc;
                    } else {
                        self.state = LexState::Ground;
                    }
                }
            }
            rest = tail;
        }
        marks
    }

    fn finish_osc(&mut self, eff_offset: u64) -> Option<Osc133Mark> {
        let Some(mark) = parse_osc133_payload(&self.buf, eff_offset) else {
            return None;
        };
        self.buf.clear();
        self.apply_mark(mark);
        Some(mark)
    }

    fn apply_mark(&mut self, mark: Osc133Mark) {
        match mark {
            Osc133Mark::PromptStart { offset } => {
                self.phase = ShellPhase::Prompt;
                self.prompt_off = Some(offset);
                self.input_off = None;
                self.exec_off = None;
            }
            Osc133Mark::CommandInputStart { offset } => {
                self.phase = ShellPhase::Input;
                let p = match self.prompt_off {
                    Some(po) => po,
                    None => offset,
                };
                self.prompt_off = Some(p);
                self.input_off = Some(shell_offset_advance(p, offset));
            }
            Osc133Mark::CommandExecStart { offset } => {
                self.phase = ShellPhase::Executing;
                let p = match self.prompt_off {
                    Some(po) => po,
                    None => offset,
                };
                let i = match self.input_off {
                    Some(io) => shell_offset_advance(p, io),
                    None => shell_offset_advance(p, offset),
                };
                let e = shell_offset_advance(i, offset);
                self.prompt_off = Some(p);
                self.input_off = Some(i);
                self.exec_off = Some(e);
            }
            Osc133Mark::CommandFinished { offset, exit_code } => {
                let p = match self.prompt_off {
                    Some(po) => po,
                    None => offset,
                };
                let i = match self.input_off {
                    Some(io) => shell_offset_advance(p, io),
                    None => shell_offset_advance(p, offset),
                };
                let e = match self.exec_off {
                    Some(eo) => shell_offset_advance(i, eo),
                    None => shell_offset_advance(i, offset),
                };
                let f = shell_offset_advance(e, offset);
                let span = ShellCommandSpan {
                    prompt_offset: p,
                    input_offset: i,
                    exec_offset: e,
                    finish_offset: f,
                    exit_code,
                };
                if self.completed.len() >= MAX_RETAINED_SHELL_SPANS {
                    let mut trimmed = Vec::new();
                    let mut dropped = false;
                    for item in core::mem::take(&mut self.completed) {
                        if !dropped {
                            dropped = true;
                        } else {
                            trimmed.push(item);
                        }
                    }
                    self.completed = trimmed;
                }
                self.completed.push(span);
                self.phase = ShellPhase::Idle;
                self.prompt_off = None;
                self.input_off = None;
                self.exec_off = None;
            }
        }
    }
}

fn parse_osc133_payload(payload: &[u8], offset: u64) -> Option<Osc133Mark> {
    let Some(rest) = payload.strip_prefix(b"133;") else {
        return None;
    };
    let Some((&kind, after_kind)) = rest.split_first() else {
        return None;
    };
    match kind {
        b'A' if after_kind.is_empty() || after_kind.starts_with(b";") => {
            Some(Osc133Mark::PromptStart { offset })
        }
        b'B' if after_kind.is_empty() || after_kind.starts_with(b";") => {
            Some(Osc133Mark::CommandInputStart { offset })
        }
        b'C' if after_kind.is_empty() || after_kind.starts_with(b";") => {
            Some(Osc133Mark::CommandExecStart { offset })
        }
        b'D' => {
            if after_kind.is_empty() {
                return Some(Osc133Mark::CommandFinished {
                    offset,
                    exit_code: None,
                });
            }
            let Some(params) = after_kind.strip_prefix(b";") else {
                return None;
            };
            // First semicolon-delimited parameter after `D;` is the integer exit status
            // (subsequent `;aid=...` parameters may follow in FinalTerm/iTerm2).
            let mut end = 0usize;
            while let Some(&b) = params.get(end) {
                if b == b';' {
                    break;
                }
                end = end.saturating_add(1);
            }
            let Some(code_bytes) = params.get(..end) else {
                return None;
            };
            if code_bytes.is_empty() {
                return Some(Osc133Mark::CommandFinished {
                    offset,
                    exit_code: None,
                });
            }
            let Some(raw) = parse_decimal_u64(code_bytes) else {
                return None;
            };
            let clamped = shell_exit_clamp(raw, MAX_SHELL_EXIT_CODE);
            Some(Osc133Mark::CommandFinished {
                offset,
                exit_code: Some(clamped),
            })
        }
        _ => None,
    }
}

fn parse_decimal_u64(bytes: &[u8]) -> Option<u64> {
    if bytes.is_empty() {
        return None;
    }
    let mut acc = 0u64;
    let mut rest = bytes;
    while let &[b, ref tail @ ..] = rest {
        if !b.is_ascii_digit() {
            return None;
        }
        acc = acc
            .saturating_mul(10)
            .saturating_add(b.saturating_sub(b'0') as u64);
        rest = tail;
    }
    Some(acc)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clean_twins_match_invariants() {
        assert_eq!(shell_offset_advance(10, 25), 25);
        assert_eq!(shell_offset_advance(25, 10), 25);
        assert_eq!(shell_exit_clamp(127, MAX_SHELL_EXIT_CODE), 127);
        assert_eq!(
            shell_exit_clamp(999_999, MAX_SHELL_EXIT_CODE),
            MAX_SHELL_EXIT_CODE
        );
        assert!(shell_span_ordered(10, 10));
        assert!(shell_span_ordered(10, 11));
        assert!(!shell_span_ordered(11, 10));
    }

    #[test]
    fn full_lifecycle_across_split_chunks_and_both_terminators() {
        let mut tracker = ShellLifecycleTracker::new();
        assert_eq!(tracker.phase(), ShellPhase::Idle);

        // Split OSC 133;A BEL across two chunks.
        assert!(tracker.feed(10, b"\x1b]133").is_empty());
        let m1 = tracker.feed(10, b";A\x07$ ");
        assert_eq!(m1, vec![Osc133Mark::PromptStart { offset: 10 }]);
        assert_eq!(tracker.phase(), ShellPhase::Prompt);

        // OSC 133;B ST (ESC \)
        let m2 = tracker.feed(12, b"\x1b]133;B\x1b\\cargo test\r\n");
        assert_eq!(m2, vec![Osc133Mark::CommandInputStart { offset: 12 }]);
        assert_eq!(tracker.phase(), ShellPhase::Input);

        // OSC 133;C BEL
        let m3 = tracker.feed(15, b"\x1b]133;C\x07running 42 tests...\r\n");
        assert_eq!(m3, vec![Osc133Mark::CommandExecStart { offset: 15 }]);
        assert_eq!(tracker.phase(), ShellPhase::Executing);

        // OSC 133;D;0;aid=1 ST
        let m4 = tracker.feed(28, b"\x1b]133;D;0;aid=1\x1b\\");
        assert_eq!(
            m4,
            vec![Osc133Mark::CommandFinished {
                offset: 28,
                exit_code: Some(0),
            }]
        );
        assert_eq!(tracker.phase(), ShellPhase::Idle);

        let spans = tracker.take_completed_spans();
        assert_eq!(spans.len(), 1);
        let sp = &spans[0];
        assert_eq!(sp.prompt_offset, 10);
        assert_eq!(sp.input_offset, 12);
        assert_eq!(sp.exec_offset, 15);
        assert_eq!(sp.finish_offset, 28);
        assert_eq!(sp.output_span(), 13);
        assert_eq!(sp.exit_code, Some(0));
        assert!(sp.is_well_ordered());
    }

    #[test]
    fn out_of_order_offsets_and_huge_exit_codes_are_monotone_and_clamped() {
        let mut tracker = ShellLifecycleTracker::new();
        tracker.feed(50, b"\x1b]133;A\x07");
        // Out-of-order lower offset is clamped forward to 50.
        tracker.feed(20, b"\x1b]133;C\x07");
        tracker.feed(10, b"\x1b]133;D;100000\x07");

        let spans = tracker.completed_spans();
        assert_eq!(spans.len(), 1);
        assert!(spans[0].is_well_ordered());
        assert_eq!(spans[0].finish_offset, 50);
        assert_eq!(spans[0].exit_code, Some(MAX_SHELL_EXIT_CODE));
    }

    #[test]
    fn unclosed_and_overlong_osc_sequences_recover_on_subsequent_osc133() {
        let mut tracker = ShellLifecycleTracker::new();
        // Unclosed OSC 0 immediately aborted by a fresh OSC 133;A.
        let m1 = tracker.feed(5, b"\x1b]0;unclosed-title\x1b]133;A\x07");
        assert_eq!(m1, vec![Osc133Mark::PromptStart { offset: 5 }]);

        // Overlong OSC 7 discarded through terminator, followed by valid OSC 133;B.
        let mut overlong = b"\x1b]7;file://host/".to_vec();
        overlong.extend(core::iter::repeat_n(b'a', 512));
        overlong.extend_from_slice(b"\x1b\\\x1b]133;B\x07");
        let m2 = tracker.feed(9, &overlong);
        assert_eq!(m2, vec![Osc133Mark::CommandInputStart { offset: 9 }]);
    }
}
