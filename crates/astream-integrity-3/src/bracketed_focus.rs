// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! DEC `?1004` Focus-In / Focus-Out (`CSI I` / `CSI O`) mode tracker & burst limiter.
//!
//! TUI editors and agents (Neovim, Helix, Emacs, Claude Code TUI) enable DEC private mode
//! `?1004` (`CSI ? 1004 h`) so the terminal multiplexer emits `ESC [ I` on focus-in and
//! `ESC [ O` on focus-out. Rapid `aterm` pane/tab cycling or macOS Spaces switching can
//! otherwise flood the PTY stdin buffer with redundant `CSI I`/`CSI O` sequences—or leak
//! literal `[I`/`[O` into raw shells after a TUI crashes or disables `?1004` (`CSI ? 1004 l`
//! / `RIS` `ESC c` / `DECSTR` `CSI ! p`).
//!
//! `FocusInOutTracker` tracks `?1004` mode transitions across arbitrary split PTY output
//! chunks, deduplicates idempotent focus states, enforces a per-window burst cap, and only
//! emits `b"\x1b[I"` / `b"\x1b[O"` when `?1004` is active.
//!
//! Clean specification: `bracketed_focus_island.rs` (`Astream.Term.TlaFocusInOutTracker`).

#![allow(clippy::collapsible_if, clippy::manual_is_ascii_check)]

#[cfg(clean_islands)]
#[path = "bracketed_focus_island.rs"]
mod bracketed_focus_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn focus_burst_clamp(cand_transitions: u64, burst_cap: u64) -> u64 {
    if cand_transitions < burst_cap {
        cand_transitions
    } else {
        burst_cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn focus_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}
#[cfg(clean_islands)]
pub use bracketed_focus_island::{focus_burst_clamp, focus_epoch_advance};

/// Canonical VT sequence emitted to PTY stdin when the pane gains focus (`ESC [ I`).
pub const CSI_FOCUS_IN: &[u8; 3] = b"\x1b[I";
/// Canonical VT sequence emitted to PTY stdin when the pane loses focus (`ESC [ O`).
pub const CSI_FOCUS_OUT: &[u8; 3] = b"\x1b[O";

/// Default maximum focus notifications emitted per rate-limit window.
pub const DEFAULT_FOCUS_BURST_CAP: u64 = 16;

contract_fn! {
    /// Kernel-certified check that `transitions <= burst_cap`, linked via
    /// `clean-kernel-defeq` to `focus_burst_within_cap_isl`.
    #[must_use]
    pub const fn focus_burst_within_cap(transitions: u64, burst_cap: u64) -> bool
    clauses [ensures result == (transitions <= burst_cap)]
    {
        transitions <= burst_cap
    }
}

fn clamp_burst_count(cand_transitions: u64, burst_cap: u64) -> u64 {
    let clamped = focus_burst_clamp(cand_transitions, burst_cap);
    let _ = focus_burst_within_cap(clamped, burst_cap);
    clamped
}

/// Decision returned when `aterm` reports a window/pane focus change.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FocusEmission {
    /// Emit `ESC [ I` (`CSI_FOCUS_IN`) to the PTY master.
    SendFocusIn { epoch: u64 },
    /// Emit `ESC [ O` (`CSI_FOCUS_OUT`) to the PTY master.
    SendFocusOut { epoch: u64 },
    /// Suppress emission because DEC `?1004` focus reporting is disabled.
    SuppressedModeOff,
    /// Suppress emission because the pane is already in the requested focus state.
    SuppressedDuplicate,
    /// Suppress emission because the per-window transition burst cap was reached.
    SuppressedRateLimited { burst_cap: u64 },
}

impl FocusEmission {
    /// Bytes to write to PTY stdin, if any.
    #[must_use]
    pub const fn as_pty_bytes(self) -> &'static [u8] {
        match self {
            Self::SendFocusIn { .. } => CSI_FOCUS_IN,
            Self::SendFocusOut { .. } => CSI_FOCUS_OUT,
            Self::SuppressedModeOff
            | Self::SuppressedDuplicate
            | Self::SuppressedRateLimited { .. } => b"",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ScanState {
    Ground,
    Esc,
    CsiEntry,
    CsiBang,
    CsiQuestion,
    CsiQuestionDigits { acc: u32, has_1004: bool },
}

/// Split-safe DEC `?1004` parser and PTY focus-notification gate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FocusInOutTracker {
    scan: ScanState,
    mode_enabled: bool,
    last_emitted_focused: Option<bool>,
    burst_transitions: u64,
    burst_cap: u64,
    window_start_ms: u64,
    window_len_ms: u64,
    focus_epoch: u64,
}

impl FocusInOutTracker {
    /// Create a new tracker with `burst_cap` max emissions per `window_len_ms` window.
    #[must_use]
    pub fn new(burst_cap: u64, window_len_ms: u64) -> Self {
        let cap = if burst_cap == 0 { 1 } else { burst_cap };
        let win = if window_len_ms == 0 {
            1_000
        } else {
            window_len_ms
        };
        Self {
            scan: ScanState::Ground,
            mode_enabled: false,
            last_emitted_focused: None,
            burst_transitions: 0,
            burst_cap: cap,
            window_start_ms: 0,
            window_len_ms: win,
            focus_epoch: 0,
        }
    }

    /// Create a tracker with standard defaults (`16` transitions per `1000ms`).
    #[must_use]
    pub fn with_defaults() -> Self {
        Self::new(DEFAULT_FOCUS_BURST_CAP, 1_000)
    }

    /// Whether DEC `?1004` focus reporting is currently active on the terminal.
    #[must_use]
    pub const fn is_mode_enabled(&self) -> bool {
        self.mode_enabled
    }

    /// Monotone epoch incremented on every emitted `CSI I` / `CSI O` event.
    #[must_use]
    pub const fn focus_epoch(&self) -> u64 {
        self.focus_epoch
    }

    /// Current count of emitted focus transitions within the active rate-limit window.
    #[must_use]
    pub const fn burst_transitions(&self) -> u64 {
        self.burst_transitions
    }

    /// Configured per-window transition cap.
    #[must_use]
    pub const fn burst_cap(&self) -> u64 {
        self.burst_cap
    }

    /// Observe PTY stdout bytes to track `CSI ? 1004 h`, `CSI ? 1004 l`, `ESC c` (RIS),
    /// and `CSI ! p` (DECSTR), even across arbitrary chunk boundaries.
    pub fn observe_pty_output(&mut self, bytes: &[u8]) {
        let mut cur = bytes;
        while let &[b, ref rest @ ..] = cur {
            cur = rest;
            if b == 0x1b {
                self.scan = ScanState::Esc;
                continue;
            }
            if b == 0x18 || b == 0x1a {
                self.scan = ScanState::Ground;
                continue;
            }
            match self.scan {
                ScanState::Ground => {}
                ScanState::Esc => {
                    if b == b'[' {
                        self.scan = ScanState::CsiEntry;
                    } else if b == b'c' {
                        // Full terminal reset (RIS) disables `?1004`.
                        self.disable_mode();
                        self.scan = ScanState::Ground;
                    } else {
                        self.scan = ScanState::Ground;
                    }
                }
                ScanState::CsiEntry => {
                    if b == b'?' {
                        self.scan = ScanState::CsiQuestion;
                    } else if b == b'!' {
                        self.scan = ScanState::CsiBang;
                    } else {
                        self.scan = ScanState::Ground;
                    }
                }
                ScanState::CsiBang => {
                    if b == b'p' {
                        // Soft terminal reset (DECSTR `CSI ! p`) disables `?1004`.
                        self.disable_mode();
                    }
                    self.scan = ScanState::Ground;
                }
                ScanState::CsiQuestion => {
                    if matches!(b, b'0'..=b'9') {
                        self.scan = ScanState::CsiQuestionDigits {
                            acc: b.saturating_sub(b'0') as u32,
                            has_1004: false,
                        };
                    } else {
                        self.scan = ScanState::Ground;
                    }
                }
                ScanState::CsiQuestionDigits { acc, has_1004 } => {
                    if matches!(b, b'0'..=b'9') {
                        let next_acc = acc
                            .saturating_mul(10)
                            .saturating_add(b.saturating_sub(b'0') as u32);
                        self.scan = ScanState::CsiQuestionDigits {
                            acc: next_acc,
                            has_1004,
                        };
                    } else if b == b';' {
                        self.scan = ScanState::CsiQuestionDigits {
                            acc: 0,
                            has_1004: has_1004 || acc == 1004,
                        };
                    } else if b == b'h' {
                        if has_1004 || acc == 1004 {
                            if !self.mode_enabled {
                                self.mode_enabled = true;
                                self.last_emitted_focused = None;
                            }
                        }
                        self.scan = ScanState::Ground;
                    } else if b == b'l' {
                        if has_1004 || acc == 1004 {
                            self.disable_mode();
                        }
                        self.scan = ScanState::Ground;
                    } else {
                        self.scan = ScanState::Ground;
                    }
                }
            }
        }
    }

    fn disable_mode(&mut self) {
        self.mode_enabled = false;
        self.last_emitted_focused = None;
    }

    /// Evaluate a host/tab focus state (`focused = true` -> `CSI I`, `false` -> `CSI O`)
    /// at monotone timestamp `now_ms`.
    pub fn on_focus_change(&mut self, focused: bool, now_ms: u64) -> FocusEmission {
        if now_ms >= self.window_start_ms.saturating_add(self.window_len_ms) {
            self.window_start_ms = now_ms;
            self.burst_transitions = 0;
        }
        if !self.mode_enabled {
            return FocusEmission::SuppressedModeOff;
        }
        if self.last_emitted_focused == Some(focused) {
            return FocusEmission::SuppressedDuplicate;
        }
        if self.burst_transitions >= self.burst_cap {
            return FocusEmission::SuppressedRateLimited {
                burst_cap: self.burst_cap,
            };
        }
        let next_burst =
            clamp_burst_count(self.burst_transitions.saturating_add(1), self.burst_cap);
        self.burst_transitions = next_burst;
        let next_epoch = focus_epoch_advance(self.focus_epoch, self.focus_epoch.saturating_add(1));
        self.focus_epoch = next_epoch;
        self.last_emitted_focused = Some(focused);
        if focused {
            FocusEmission::SendFocusIn { epoch: next_epoch }
        } else {
            FocusEmission::SendFocusOut { epoch: next_epoch }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn suppresses_focus_sequences_when_dec_1004_disabled() {
        let mut tracker = FocusInOutTracker::new(4, 1_000);
        assert!(!tracker.is_mode_enabled());
        let ev = tracker.on_focus_change(true, 100);
        assert_eq!(ev, FocusEmission::SuppressedModeOff);
        assert_eq!(ev.as_pty_bytes(), b"");
    }

    #[test]
    fn tracks_split_csi_1004_enable_deduplicates_and_resets_on_disable() {
        let mut tracker = FocusInOutTracker::new(4, 1_000);
        tracker.observe_pty_output(b"\x1b[?2004;10");
        assert!(!tracker.is_mode_enabled());
        tracker.observe_pty_output(b"04h");
        assert!(tracker.is_mode_enabled());

        let e1 = tracker.on_focus_change(true, 100);
        assert_eq!(e1, FocusEmission::SendFocusIn { epoch: 1 });
        assert_eq!(e1.as_pty_bytes(), b"\x1b[I");

        // Duplicate focus-in is suppressed.
        assert_eq!(
            tracker.on_focus_change(true, 120),
            FocusEmission::SuppressedDuplicate
        );

        let e2 = tracker.on_focus_change(false, 150);
        assert_eq!(e2, FocusEmission::SendFocusOut { epoch: 2 });
        assert_eq!(e2.as_pty_bytes(), b"\x1b[O");

        // Disable via `CSI ? 1004 l`.
        tracker.observe_pty_output(b"\x1b[?1004l");
        assert!(!tracker.is_mode_enabled());
        assert_eq!(
            tracker.on_focus_change(true, 200),
            FocusEmission::SuppressedModeOff
        );
    }

    #[test]
    fn rate_limits_focus_storm_and_recovers_next_window() {
        let mut tracker = FocusInOutTracker::new(2, 500);
        tracker.observe_pty_output(b"\x1b[?1004h");

        assert_eq!(
            tracker.on_focus_change(true, 1_000),
            FocusEmission::SendFocusIn { epoch: 1 }
        );
        assert_eq!(
            tracker.on_focus_change(false, 1_050),
            FocusEmission::SendFocusOut { epoch: 2 }
        );
        assert_eq!(
            tracker.on_focus_change(true, 1_100),
            FocusEmission::SuppressedRateLimited { burst_cap: 2 }
        );
        assert!(tracker.burst_transitions() <= tracker.burst_cap());

        // Window rolls over at 1_500ms.
        assert_eq!(
            tracker.on_focus_change(true, 1_500),
            FocusEmission::SendFocusIn { epoch: 3 }
        );

        // Soft reset `CSI ! p` clears `?1004`.
        tracker.observe_pty_output(b"\x1b[!p");
        assert!(!tracker.is_mode_enabled());
    }
}
