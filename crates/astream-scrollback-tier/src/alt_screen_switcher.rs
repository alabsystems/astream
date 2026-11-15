// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! DEC `?1049` primary/alternate screen buffer switcher ensuring full-screen TUIs (`vim`, `htop`,
//! `less`) never append frames into persistent primary scrollback (`Astream.ScrollTier.TlaAltScreenSwitcher`).

#[cfg(clean_islands)]
#[path = "alt_screen_switcher_island.rs"]
mod alt_screen_switcher_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sb_mode_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sb_alt_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use alt_screen_switcher_island::{sb_alt_advance, sb_mode_clamp};

/// Screen buffer mode ceiling (`0 = Primary`, `1 = Alternate1049`).
pub const MAX_SCREEN_MODE: u64 = 1;

contract_fn! {
    /// Verified primary-scrollback append eligibility (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `sb_scrollback_protected_isl`.
    #[must_use]
    pub const fn sb_scrollback_protected(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct AltScreenGuard {
    in_alt_screen: bool,
    saved_cursor_row: u64,
    saved_cursor_col: u64,
    switches: u64,
}

impl AltScreenGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            in_alt_screen: false,
            saved_cursor_row: 0,
            saved_cursor_col: 0,
            switches: 0,
        }
    }

    pub fn enter_1049(&mut self, row: u64, col: u64) {
        if !self.in_alt_screen {
            self.saved_cursor_row = row;
            self.saved_cursor_col = col;
            self.in_alt_screen = true;
            let _ = sb_mode_clamp(1, MAX_SCREEN_MODE);
            self.switches = sb_alt_advance(self.switches, self.switches.saturating_add(1));
        }
    }

    pub fn exit_1049(&mut self) -> (u64, u64) {
        if self.in_alt_screen {
            self.in_alt_screen = false;
            self.switches = sb_alt_advance(self.switches, self.switches.saturating_add(1));
        }
        (self.saved_cursor_row, self.saved_cursor_col)
    }

    #[must_use]
    pub const fn allow_scrollback_append(&self) -> bool {
        let mode = if self.in_alt_screen { 1u64 } else { 0u64 };
        sb_scrollback_protected(0, mode)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_scrollback_writes_while_in_1049_and_restores_saved_cursor() {
        let mut g = AltScreenGuard::new();
        assert!(g.allow_scrollback_append());
        g.enter_1049(14, 7);
        assert!(!g.allow_scrollback_append());
        assert_eq!(g.exit_1049(), (14, 7));
        assert!(g.allow_scrollback_append());
    }
}
