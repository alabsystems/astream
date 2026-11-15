// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Nested Claude Code PTY drive & crash-reattach deduplication fence
//! (`docs/ROADMAP.md` §"The drive pipe, astream's own" lines 236–238;
//! `Astream.Pump.TlaNestedClaudePtyDriveFence`).
//!
//! Coordinates driving a nested Claude Code TUI session over `astream-host::Driver` + `aspump --profile claude`:
//! - Suppresses Braille/progress-spinner redraw frames (`is_spinner_only`) unless quiet settle
//!   duration `quiet_elapsed_ms >= min_settle_ms` AND prompt composer is ready, preventing false wakes
//!   during streaming tool execution,
//! - Deduplicates PTY command injection by `cmd_seq` (`cmd_seq <= committed_cmd_seq`) so a driver
//!   killed mid-turn and reattached with `--group` never double-types a prompt into the nested agent,
//! - Clamps each injected prompt's byte payload to `max_cmd_bytes`.

#[cfg(clean_islands)]
#[path = "nested_claude_pty_drive_fence_island.rs"]
mod nested_claude_pty_drive_fence_island;
#[cfg(clean_islands)]
pub use nested_claude_pty_drive_fence_island::{
    nested_claude_bytes_clamp_b128, nested_claude_cmd_seq_advance_b128,
};

#[cfg(not(clean_islands))]
/// Clamp a driven PTY prompt payload length to `max_cmd_bytes`.
#[must_use]
pub const fn nested_claude_bytes_clamp_b128(cand_bytes: u64, max_cmd_bytes: u64) -> u64 {
    if cand_bytes < max_cmd_bytes {
        cand_bytes
    } else {
        max_cmd_bytes
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance `committed_cmd_seq` across crash-recovery reattach.
#[must_use]
pub const fn nested_claude_cmd_seq_advance_b128(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}

contract_fn! {
    /// True iff nested Claude TUI is ready for input (`composer_ready && !spinner_active && quiet_ms >= min_settle_ms`).
    #[must_use]
    pub const fn nested_claude_settled_b128(
        composer_ready: bool,
        spinner_active: bool,
        quiet_ms: u64,
        min_settle_ms: u64,
    ) -> bool
    clauses [ensures result == (composer_ready && !spinner_active && quiet_ms >= min_settle_ms)]
    {
        composer_ready && !spinner_active && quiet_ms >= min_settle_ms
    }
}

/// Decision for a nested Claude Code wake evaluation or PTY command drive.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NestedClaudeDriveVerdict {
    SuppressedSpinnerOrUnsettled {
        suppressed_frames: u64,
    },
    SettledWakeReady {
        settled_out_offset: u64,
    },
    DrivenToPty {
        committed_cmd_seq: u64,
        admitted_bytes: u64,
    },
    DedupedCrashRetry {
        committed_cmd_seq: u64,
    },
    RefusedUnsettledPrompt,
}

/// Stateful nested Claude Code PTY drive & crash-reattach deduplication fence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NestedClaudePtyDriveFence {
    min_settle_ms: u64,
    max_cmd_bytes: u64,
    settled: bool,
    settled_out_offset: u64,
    committed_cmd_seq: u64,
    suppressed_frames: u64,
}

impl NestedClaudePtyDriveFence {
    #[must_use]
    pub const fn new(min_settle_ms: u64, max_cmd_bytes: u64) -> Self {
        Self {
            min_settle_ms,
            max_cmd_bytes,
            settled: false,
            settled_out_offset: 0,
            committed_cmd_seq: 0,
            suppressed_frames: 0,
        }
    }

    /// Observe a PTY output frame at `out_offset` from the nested Claude Code TUI.
    pub fn on_pty_frame(
        &mut self,
        out_offset: u64,
        composer_ready: bool,
        spinner_active: bool,
        quiet_ms: u64,
    ) -> NestedClaudeDriveVerdict {
        if !nested_claude_settled_b128(composer_ready, spinner_active, quiet_ms, self.min_settle_ms)
        {
            self.settled = false;
            self.suppressed_frames = self.suppressed_frames.saturating_add(1);
            return NestedClaudeDriveVerdict::SuppressedSpinnerOrUnsettled {
                suppressed_frames: self.suppressed_frames,
            };
        }
        self.settled = true;
        if out_offset > self.settled_out_offset {
            self.settled_out_offset = out_offset;
        }
        NestedClaudeDriveVerdict::SettledWakeReady {
            settled_out_offset: self.settled_out_offset,
        }
    }

    /// Drive a 1-based `cmd_seq` prompt of `cmd_bytes` into the nested PTY, deduplicating retries.
    pub fn drive_prompt(&mut self, cmd_seq: u64, cmd_bytes: u64) -> NestedClaudeDriveVerdict {
        if cmd_seq == 0 || cmd_seq <= self.committed_cmd_seq {
            return NestedClaudeDriveVerdict::DedupedCrashRetry {
                committed_cmd_seq: self.committed_cmd_seq,
            };
        }
        if !self.settled {
            return NestedClaudeDriveVerdict::RefusedUnsettledPrompt;
        }
        self.committed_cmd_seq =
            nested_claude_cmd_seq_advance_b128(self.committed_cmd_seq, cmd_seq);
        self.settled = false;
        NestedClaudeDriveVerdict::DrivenToPty {
            committed_cmd_seq: self.committed_cmd_seq,
            admitted_bytes: nested_claude_bytes_clamp_b128(cmd_bytes, self.max_cmd_bytes),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn suppresses_streaming_spinner_wakes_and_dedups_reattached_driver_command() {
        let mut fence = NestedClaudePtyDriveFence::new(250, 4_096);

        // Braille spinner active during tool call -> suppressed, prompt refused!
        assert_eq!(
            fence.on_pty_frame(100, true, true, 500),
            NestedClaudeDriveVerdict::SuppressedSpinnerOrUnsettled {
                suppressed_frames: 1
            }
        );
        assert_eq!(
            fence.drive_prompt(1, 128),
            NestedClaudeDriveVerdict::RefusedUnsettledPrompt
        );

        // Quiet composer settle (>= 250 ms, no spinner) -> wake ready, command 1 driven once!
        assert_eq!(
            fence.on_pty_frame(140, true, false, 300),
            NestedClaudeDriveVerdict::SettledWakeReady {
                settled_out_offset: 140
            }
        );
        assert_eq!(
            fence.drive_prompt(1, 5_000),
            NestedClaudeDriveVerdict::DrivenToPty {
                committed_cmd_seq: 1,
                admitted_bytes: 4_096,
            }
        );

        // Crash-reattached `--group` driver resends `cmd_seq = 1` -> deduplicated without double-typing!
        assert_eq!(
            fence.drive_prompt(1, 5_000),
            NestedClaudeDriveVerdict::DedupedCrashRetry {
                committed_cmd_seq: 1
            }
        );
    }
}
