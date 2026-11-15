// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! DEC `?1049` Alternate-Screen & Cursor-Save (`DECSC` / `DECRC`) Scrollback-Isolation Controller
//! (`Astream.Term.TlaAltScreenGuard`).
//!
//! Full-screen TUIs hosted in `aterm` (`vim`, `hx`, `btop`, `less`, Claude Code TUI) enter
//! DEC `?1049h` (saving the main-screen cursor `(row, col, origin_mode, autowrap_pending)` and
//! switching to a scrollback-isolated alternate buffer) and exit via `?1049l` (restoring the
//! saved main-screen cursor, clamped to the current post-`SIGWINCH` viewport `(rows, cols)`!).
//!
//! If a child process crashes (`SIGKILL` / `SIGSEGV` / broken SSH pipe) while inside `?1049h`,
//! the parent shell prompt wakes up stranded in the alternate screen with mouse/paste/cursor-hide
//! modes stuck. [`AltScreenGuard::on_child_exit`] detects `alt_needs_teardown(in_alt_screen, true)`
//! and emits a canonical, idempotent VT recovery sequence returning `aterm` cleanly to the main screen!

#![allow(clippy::question_mark)]

#[cfg(clean_islands)]
#[path = "alt_screen_island.rs"]
mod alt_screen_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn alt_cursor_row_clamp(saved_row: u64, max_row: u64) -> u64 {
    if saved_row < max_row {
        saved_row
    } else {
        max_row
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn alt_cursor_col_clamp(saved_col: u64, max_col: u64) -> u64 {
    if saved_col < max_col {
        saved_col
    } else {
        max_col
    }
}
#[cfg(clean_islands)]
pub use alt_screen_island::{alt_cursor_col_clamp, alt_cursor_row_clamp};

/// Canonical VT recovery sequence emitted when a child exits while stranded in `?1049h`:
/// - `\x1b[?2026l`: end synchronized update,
/// - `\x1b[?2004l`: disable bracketed paste mode,
/// - `\x1b[?1000l\x1b[?1002l\x1b[?1003l\x1b[?1004l\x1b[?1006l`: disable mouse/focus tracking,
/// - `\x1b[?1049l`: exit alternate screen and restore saved cursor,
/// - `\x1b[0m`: reset SGR attributes,
/// - `\x1b[?25h`: show cursor.
pub const ALT_SCREEN_CRASH_TEARDOWN_SEQ: &[u8] =
    b"\x1b[?2026l\x1b[?2004l\x1b[?1000l\x1b[?1002l\x1b[?1003l\x1b[?1004l\x1b[?1006l\x1b[?1049l\x1b[0m\x1b[?25h";

contract_fn! {
    /// Verified check whether an exited child left the terminal stranded inside DEC `?1049h`
    /// (`in_alt_screen && child_exited`), linked via `clean-kernel-defeq` to `alt_needs_teardown_isl`.
    #[must_use]
    pub const fn alt_needs_teardown(in_alt_screen: bool, child_exited: bool) -> bool
    clauses [ensures result == (in_alt_screen && child_exited)]
    {
        in_alt_screen && child_exited
    }
}

/// Saved main-screen cursor snapshot (`DECSC` / `?1049h`).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct SavedCursorState {
    pub row: u32,
    pub col: u32,
    pub origin_mode: bool,
    pub autowrap: bool,
}

/// DEC `?1049` alternate-screen lifecycle & resize-safe cursor restore controller.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AltScreenGuard {
    in_alt_screen: bool,
    saved_main: SavedCursorState,
    saved_alt: SavedCursorState,
    transitions: u64,
}

impl Default for AltScreenGuard {
    fn default() -> Self {
        Self::new()
    }
}

impl AltScreenGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            in_alt_screen: false,
            saved_main: SavedCursorState {
                row: 0,
                col: 0,
                origin_mode: false,
                autowrap: true,
            },
            saved_alt: SavedCursorState {
                row: 0,
                col: 0,
                origin_mode: false,
                autowrap: true,
            },
            transitions: 0,
        }
    }

    /// True while DEC `?1049h` (or `?47h` / `?1047h`) alternate buffer is active.
    #[must_use]
    pub const fn in_alt_screen(&self) -> bool {
        self.in_alt_screen
    }

    /// Scrollback capture is suppressed while `in_alt_screen` is true so full-screen redraws
    /// never pollute the operator's main-screen history.
    #[must_use]
    pub const fn allows_scrollback(&self) -> bool {
        !self.in_alt_screen
    }

    /// Number of main <-> alt transitions observed.
    #[must_use]
    pub const fn transitions(&self) -> u64 {
        self.transitions
    }

    /// Enter DEC `?1049h`, saving `current_main_cursor` when transitioning from the main screen.
    ///
    /// Idempotent if already in the alternate screen (matching XTerm / VTE / Ghostty semantics:
    /// a redundant `?1049h` inside an alt-screen TUI must NOT overwrite `saved_main`!).
    pub fn enter_alt_screen(&mut self, current_main_cursor: SavedCursorState) -> bool {
        if self.in_alt_screen {
            return false;
        }
        self.saved_main = current_main_cursor;
        self.saved_alt = SavedCursorState {
            row: 0,
            col: 0,
            origin_mode: false,
            autowrap: true,
        };
        self.in_alt_screen = true;
        self.transitions = self.transitions.saturating_add(1);
        true
    }

    /// Explicit `DECSC` (`ESC 7` / `CSI s`) cursor save within whichever screen is active.
    pub fn save_cursor(&mut self, cursor: SavedCursorState) {
        if self.in_alt_screen {
            self.saved_alt = cursor;
        } else {
            self.saved_main = cursor;
        }
    }

    /// Explicit `DECRC` (`ESC 8` / `CSI u`) cursor restore clamped to `(viewport_rows, viewport_cols)`.
    #[must_use]
    pub fn restore_cursor(&self, viewport_rows: u32, viewport_cols: u32) -> SavedCursorState {
        let snap = if self.in_alt_screen {
            self.saved_alt
        } else {
            self.saved_main
        };
        clamp_cursor_to_viewport(snap, viewport_rows, viewport_cols)
    }

    /// Exit DEC `?1049l`, returning `Some(restored_main_cursor)` clamped to `(viewport_rows, viewport_cols)`,
    /// or `None` if already on the main screen.
    pub fn exit_alt_screen(
        &mut self,
        viewport_rows: u32,
        viewport_cols: u32,
    ) -> Option<SavedCursorState> {
        if !self.in_alt_screen {
            return None;
        }
        self.in_alt_screen = false;
        self.transitions = self.transitions.saturating_add(1);
        Some(clamp_cursor_to_viewport(
            self.saved_main,
            viewport_rows,
            viewport_cols,
        ))
    }

    /// Inspect child-process exit; if the child crashed/exited while stranded inside `?1049h`,
    /// exits alt-screen state and returns `(teardown_seq, restored_main_cursor)`.
    pub fn on_child_exit(
        &mut self,
        child_exited: bool,
        viewport_rows: u32,
        viewport_cols: u32,
    ) -> Option<(&'static [u8], SavedCursorState)> {
        if !alt_needs_teardown(self.in_alt_screen, child_exited) {
            return None;
        }
        let Some(restored) = self.exit_alt_screen(viewport_rows, viewport_cols) else {
            return None;
        };
        Some((ALT_SCREEN_CRASH_TEARDOWN_SEQ, restored))
    }
}

fn clamp_cursor_to_viewport(
    snap: SavedCursorState,
    viewport_rows: u32,
    viewport_cols: u32,
) -> SavedCursorState {
    let vr = if viewport_rows > 1 { viewport_rows } else { 1 };
    let vc = if viewport_cols > 1 { viewport_cols } else { 1 };
    let max_row = vr.saturating_sub(1) as u64;
    let max_col = vc.saturating_sub(1) as u64;
    let r = alt_cursor_row_clamp(snap.row as u64, max_row) as u32;
    let c = alt_cursor_col_clamp(snap.col as u64, max_col) as u32;
    SavedCursorState {
        row: r,
        col: c,
        origin_mode: snap.origin_mode,
        autowrap: snap.autowrap,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clean_twins_match_invariants() {
        assert_eq!(alt_cursor_row_clamp(10, 23), 10);
        assert_eq!(alt_cursor_row_clamp(50, 23), 23);
        assert_eq!(alt_cursor_col_clamp(40, 79), 40);
        assert_eq!(alt_cursor_col_clamp(120, 79), 79);
        assert!(alt_needs_teardown(true, true));
        assert!(!alt_needs_teardown(false, true));
        assert!(!alt_needs_teardown(true, false));
    }

    #[test]
    fn clamps_restored_cursor_after_shrinking_resize_and_recovers_from_sigkill() {
        let mut g = AltScreenGuard::new();
        assert!(g.allows_scrollback());

        let orig = SavedCursorState {
            row: 38,
            col: 110,
            origin_mode: false,
            autowrap: true,
        };
        assert!(g.enter_alt_screen(orig));
        assert!(!g.allows_scrollback());

        // Redundant enter inside alt-screen does NOT clobber saved_main!
        assert!(!g.enter_alt_screen(SavedCursorState {
            row: 0,
            col: 0,
            origin_mode: true,
            autowrap: false,
        }));

        // Terminal shrinks to 24x80 while TUI is running, then TUI crashes (SIGKILL):
        let (seq, restored) = g.on_child_exit(true, 24, 80).unwrap();
        assert_eq!(seq, ALT_SCREEN_CRASH_TEARDOWN_SEQ);
        assert_eq!(restored.row, 23);
        assert_eq!(restored.col, 79);
        assert!(!g.in_alt_screen());
        assert!(g.allows_scrollback());
    }
}
