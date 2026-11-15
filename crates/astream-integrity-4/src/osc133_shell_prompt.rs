// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Split-safe FinalTerm / Semantic Prompts (`OSC 133 ; A / B / C / D`) shell tracker.
//!
//! Modern shells (`zsh`, `bash`, `fish`) under `aterm` emit `OSC 133` semantic prompt
//! markers:
//! - `OSC 133 ; A ST/BEL` — Prompt start
//! - `OSC 133 ; B ST/BEL` — Command-line input start (shell idle awaiting user/agent input)
//! - `OSC 133 ; C ST/BEL` — Command execution start (foreground job running)
//! - `OSC 133 ; D [; <exit_code>] ST/BEL` — Command finished with optional exit code
//!
//! `Osc133Tracker` parses `OSC 133` markers across arbitrary PTY chunk boundaries, clamps
//! exit statuses to `0..=255` via Clean-origin `osc133_exit_clamp`, and advances a monotone
//! `cmd_seq` counter on every completed command.
//!
//! Clean specification: `osc133_shell_prompt_island.rs` (`Astream.Term.TlaOsc133ShellIntegration`).

#![allow(clippy::manual_is_ascii_check)]

#[cfg(clean_islands)]
#[path = "osc133_shell_prompt_island.rs"]
mod osc133_shell_prompt_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn osc133_exit_clamp(cand_exit: u64, max_exit: u64) -> u64 {
    if cand_exit < max_exit {
        cand_exit
    } else {
        max_exit
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn osc133_cmd_seq_advance(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}
#[cfg(clean_islands)]
pub use osc133_shell_prompt_island::{osc133_cmd_seq_advance, osc133_exit_clamp};

/// Maximum POSIX 8-bit wait-status exit code (`255`).
pub const MAX_OSC133_EXIT_CODE: u64 = 255;

/// Maximum buffered `OSC` payload bytes before discarding an oversized sequence.
const MAX_OSC_BUF_LEN: usize = 128;

contract_fn! {
    /// Kernel-certified check that `exit_code <= max_exit`, linked via
    /// `clean-kernel-defeq` to `osc133_exit_within_max_isl`.
    #[must_use]
    pub const fn osc133_exit_within_max(exit_code: u64, max_exit: u64) -> bool
    clauses [ensures result == (exit_code <= max_exit)]
    {
        exit_code <= max_exit
    }
}

/// Current semantic shell lifecycle phase reported via `OSC 133`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Osc133Phase {
    Unknown,
    Prompting,
    AwaitingCommandInput,
    ExecutingCommand,
    CommandFinished { cmd_seq: u64, exit_code: u8 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OscScan {
    Ground,
    Esc,
    OscBody,
    OscEsc,
}

/// Streaming `OSC 133` semantic prompt state tracker.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Osc133Tracker {
    scan: OscScan,
    osc_buf: Vec<u8>,
    osc_overflow: bool,
    phase: Osc133Phase,
    cmd_seq: u64,
    last_exit_code: Option<u8>,
}

impl Default for Osc133Tracker {
    fn default() -> Self {
        Self::new()
    }
}

impl Osc133Tracker {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            scan: OscScan::Ground,
            osc_buf: Vec::new(),
            osc_overflow: false,
            phase: Osc133Phase::Unknown,
            cmd_seq: 0,
            last_exit_code: None,
        }
    }

    #[must_use]
    pub const fn phase(&self) -> Osc133Phase {
        self.phase
    }

    /// True when the shell is sitting at an interactive prompt (`A` or `B`).
    #[must_use]
    pub const fn is_idle_at_prompt(&self) -> bool {
        matches!(
            self.phase,
            Osc133Phase::Prompting | Osc133Phase::AwaitingCommandInput
        )
    }

    /// Monotone count of `OSC 133 ; D` command completions observed.
    #[must_use]
    pub const fn completed_commands(&self) -> u64 {
        self.cmd_seq
    }

    #[must_use]
    pub const fn last_exit_code(&self) -> Option<u8> {
        self.last_exit_code
    }

    /// Feed raw PTY stdout bytes across arbitrary split boundaries.
    pub fn observe_bytes(&mut self, bytes: &[u8]) {
        let mut cur = bytes;
        while let &[b, ref rest @ ..] = cur {
            cur = rest;
            match self.scan {
                OscScan::Ground => {
                    if b == 0x1b {
                        self.scan = OscScan::Esc;
                    }
                }
                OscScan::Esc => {
                    if b == b']' {
                        self.osc_buf.clear();
                        self.osc_overflow = false;
                        self.scan = OscScan::OscBody;
                    } else if b == 0x1b {
                        self.scan = OscScan::Esc;
                    } else {
                        self.scan = OscScan::Ground;
                    }
                }
                OscScan::OscBody => {
                    if b == 0x07 {
                        self.finish_osc();
                        self.scan = OscScan::Ground;
                    } else if b == 0x1b {
                        self.scan = OscScan::OscEsc;
                    } else if !self.osc_overflow {
                        if self.osc_buf.len() < MAX_OSC_BUF_LEN {
                            self.osc_buf.push(b);
                        } else {
                            self.osc_overflow = true;
                        }
                    }
                }
                OscScan::OscEsc => {
                    if b == b'\\' {
                        self.finish_osc();
                        self.scan = OscScan::Ground;
                    } else if b == b']' {
                        self.osc_buf.clear();
                        self.osc_overflow = false;
                        self.scan = OscScan::OscBody;
                    } else {
                        self.scan = OscScan::Ground;
                    }
                }
            }
        }
    }

    fn finish_osc(&mut self) {
        if self.osc_overflow {
            self.osc_buf.clear();
            self.osc_overflow = false;
            return;
        }
        let Some(rest) = self.osc_buf.strip_prefix(b"133;") else {
            self.osc_buf.clear();
            return;
        };
        let &[kind, ref after_kind @ ..] = rest else {
            self.osc_buf.clear();
            return;
        };
        match kind {
            b'A' => {
                self.phase = Osc133Phase::Prompting;
            }
            b'B' => {
                self.phase = Osc133Phase::AwaitingCommandInput;
            }
            b'C' => {
                self.phase = Osc133Phase::ExecutingCommand;
            }
            b'D' => {
                let raw_exit = parse_d_exit_code(after_kind);
                let clamped = osc133_exit_clamp(raw_exit, MAX_OSC133_EXIT_CODE);
                let _ = osc133_exit_within_max(clamped, MAX_OSC133_EXIT_CODE);
                let code_u8 = clamped as u8;
                let next_seq = osc133_cmd_seq_advance(self.cmd_seq, self.cmd_seq.saturating_add(1));
                self.cmd_seq = next_seq;
                self.last_exit_code = Some(code_u8);
                self.phase = Osc133Phase::CommandFinished {
                    cmd_seq: next_seq,
                    exit_code: code_u8,
                };
            }
            _ => {}
        }
        self.osc_buf.clear();
    }
}

fn parse_d_exit_code(tail: &[u8]) -> u64 {
    let Some(after_semi) = tail.strip_prefix(b";") else {
        return 0;
    };
    let mut acc = 0u64;
    let mut digits = 0usize;
    let mut cur = after_semi;
    while let &[b, ref rest @ ..] = cur {
        cur = rest;
        if matches!(b, b'0'..=b'9') {
            acc = acc
                .saturating_mul(10)
                .saturating_add(b.saturating_sub(b'0') as u64);
            digits = digits.saturating_add(1);
        } else {
            break;
        }
    }
    if digits == 0 {
        0
    } else {
        acc
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_split_osc133_lifecycle_and_clamps_exit_code() {
        let mut tr = Osc133Tracker::new();
        tr.observe_bytes(b"\x1b]133;A\x07$ \x1b]133;");
        assert_eq!(tr.phase(), Osc133Phase::Prompting);
        assert!(tr.is_idle_at_prompt());

        tr.observe_bytes(b"B\x1b\\cargo test\r\n\x1b]133;C\x07");
        assert_eq!(tr.phase(), Osc133Phase::ExecutingCommand);
        assert!(!tr.is_idle_at_prompt());

        tr.observe_bytes(b"test result: FAILED\r\n\x1b]133;D;101;aid=9\x1b\\");
        assert_eq!(
            tr.phase(),
            Osc133Phase::CommandFinished {
                cmd_seq: 1,
                exit_code: 101,
            }
        );
        assert_eq!(tr.completed_commands(), 1);
        assert_eq!(tr.last_exit_code(), Some(101));

        // Out-of-range exit status `999` clamps cleanly to `255`.
        tr.observe_bytes(b"\x1b]133;D;999\x07");
        assert_eq!(tr.last_exit_code(), Some(255));
        assert_eq!(tr.completed_commands(), 2);
    }
}
