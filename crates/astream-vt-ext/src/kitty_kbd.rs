// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Kitty Keyboard Protocol (`CSI > flags u`, `CSI < n u`, `CSI = flags ; mode u`, `CSI ? u`)
//! progressive enhancement stack and unambiguous key encoder.
//!
//! Modern TUI editors and coding agents inside `aterm` (Neovim, Helix, Claude Code,
//! `codex`) push/pop Kitty keyboard protocol enhancement flags on separate main-screen
//! and alternate-screen stacks so `Shift+Enter`, `Ctrl+I` vs `Tab`, and bare `Esc`
//! transmit unambiguously as `CSI key ; modifiers [: event] u`.
//!
//! Backed by `Astream.Term.TlaKittyKeyboard` (`kitty_stack_depth_clamp`, `kitty_flags_mask`,
//! `kitty_depth_within_cap_isl`), with zero closures and bounded stack depth (`MAX_KITTY_STACK = 16`).

#[cfg(clean_islands)]
#[path = "kitty_kbd_island.rs"]
mod kitty_kbd_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn kitty_stack_depth_clamp(depth: u64, max_depth: u64) -> u64 {
    if depth < max_depth {
        depth
    } else {
        max_depth
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn kitty_flags_mask(raw_flags: u64, allowed_mask: u64) -> u64 {
    if raw_flags < allowed_mask {
        raw_flags
    } else {
        allowed_mask
    }
}
#[cfg(clean_islands)]
pub use kitty_kbd_island::{kitty_flags_mask, kitty_stack_depth_clamp};

contract_fn! {
    /// Contracted check that the Kitty keyboard flag stack depth fits within `cap`.
    #[must_use]
    pub const fn kitty_depth_within_cap(depth: usize, cap: usize) -> bool
    clauses [ensures result == (depth <= cap)]
    {
        depth <= cap
    }
}

/// Maximum entries per Kitty keyboard flag stack (matching Kitty & `aterm`).
pub const MAX_KITTY_STACK: usize = 16;

// Kitty keyboard progressive enhancement bitmask flags.
pub const KITTY_DISAMBIGUATE_ESC: u8 = 0b0000_0001;
pub const KITTY_REPORT_EVENT_TYPES: u8 = 0b0000_0010;
pub const KITTY_REPORT_ALTERNATE_KEYS: u8 = 0b0000_0100;
pub const KITTY_REPORT_ALL_KEYS_AS_ESC: u8 = 0b0000_1000;
pub const KITTY_REPORT_ASSOCIATED_TEXT: u8 = 0b0001_0000;
pub const KITTY_ALL_FLAGS_MASK: u8 = 0b0001_1111;

// Modifier bitmask (`modifiers_param = 1 + bitmask` on wire).
pub const MOD_SHIFT: u8 = 0b0000_0001;
pub const MOD_ALT: u8 = 0b0000_0010;
pub const MOD_CTRL: u8 = 0b0000_0100;
pub const MOD_SUPER: u8 = 0b0000_1000;

/// Key event transition type under `KITTY_REPORT_EVENT_TYPES`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KittyKeyEventKind {
    Press,
    Repeat,
    Release,
}

impl KittyKeyEventKind {
    pub const fn wire_code(self) -> u8 {
        match self {
            KittyKeyEventKind::Press => 1,
            KittyKeyEventKind::Repeat => 2,
            KittyKeyEventKind::Release => 3,
        }
    }
}

/// Update mode for `CSI = flags ; mode u`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KittySetMode {
    /// `mode = 1`: replace current flags with `flags`.
    Assign,
    /// `mode = 2`: bitwise-OR `flags` into current flags.
    BitOr,
    /// `mode = 3`: clear bits in `flags` from current flags.
    BitClear,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct FlagStack {
    entries: [u8; MAX_KITTY_STACK],
    len: usize,
    active: u8,
}

impl FlagStack {
    const fn new() -> Self {
        Self {
            entries: [0u8; MAX_KITTY_STACK],
            len: 0,
            active: 0,
        }
    }

    fn sanitize(raw_flags: u16) -> u8 {
        let masked = (raw_flags as u64) & (KITTY_ALL_FLAGS_MASK as u64);
        kitty_flags_mask(masked, KITTY_ALL_FLAGS_MASK as u64) as u8
    }

    fn push(&mut self, raw_flags: u16) {
        if self.len < MAX_KITTY_STACK {
            if let Some(slot) = self.entries.get_mut(self.len) {
                *slot = self.active;
            }
            self.len =
                kitty_stack_depth_clamp(self.len.saturating_add(1) as u64, MAX_KITTY_STACK as u64)
                    as usize;
        } else {
            let mut i = 0usize;
            while i.saturating_add(1) < MAX_KITTY_STACK {
                let next_val = match self.entries.get(i.saturating_add(1)) {
                    Some(&v) => v,
                    None => 0,
                };
                if let Some(slot) = self.entries.get_mut(i) {
                    *slot = next_val;
                }
                i = i.saturating_add(1);
            }
            if let Some(last) = self.entries.get_mut(MAX_KITTY_STACK - 1) {
                *last = self.active;
            }
        }
        let _ = kitty_depth_within_cap(self.len, MAX_KITTY_STACK);
        self.active = Self::sanitize(raw_flags);
    }

    fn pop(&mut self, count: u16) {
        let n = if count == 0 { 1usize } else { count as usize };
        if n >= self.len {
            self.len = 0;
            self.active = 0;
        } else {
            let new_len = self.len.saturating_sub(n);
            self.active = match self.entries.get(new_len) {
                Some(&v) => v,
                None => 0,
            };
            self.len = kitty_stack_depth_clamp(new_len as u64, MAX_KITTY_STACK as u64) as usize;
        }
        let _ = kitty_depth_within_cap(self.len, MAX_KITTY_STACK);
    }

    fn set(&mut self, raw_flags: u16, mode: KittySetMode) {
        let clean = Self::sanitize(raw_flags);
        let next = match mode {
            KittySetMode::Assign => clean,
            KittySetMode::BitOr => self.active | clean,
            KittySetMode::BitClear => self.active & !clean,
        };
        self.active = Self::sanitize(next as u16);
    }

    fn reset(&mut self) {
        self.len = 0;
        self.active = 0;
    }
}

/// Dual-buffer (main + alternate screen) Kitty keyboard protocol state machine.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KittyKeyboardState {
    main: FlagStack,
    alt: FlagStack,
    alt_active: bool,
}

impl Default for KittyKeyboardState {
    fn default() -> Self {
        Self::new()
    }
}

impl KittyKeyboardState {
    pub const fn new() -> Self {
        Self {
            main: FlagStack::new(),
            alt: FlagStack::new(),
            alt_active: false,
        }
    }

    pub fn set_alt_screen(&mut self, alt_active: bool) {
        if self.alt_active && !alt_active {
            // Leaving alt screen clears alt-screen keyboard enhancements per Kitty spec.
            self.alt.reset();
        }
        self.alt_active = alt_active;
    }

    pub const fn active_flags(&self) -> u8 {
        if self.alt_active {
            self.alt.active
        } else {
            self.main.active
        }
    }

    pub const fn stack_depth(&self) -> usize {
        if self.alt_active {
            self.alt.len
        } else {
            self.main.len
        }
    }

    /// Handle `CSI > flags u`.
    pub fn push_flags(&mut self, raw_flags: u16) {
        if self.alt_active {
            self.alt.push(raw_flags);
        } else {
            self.main.push(raw_flags);
        }
    }

    /// Handle `CSI < count u`.
    pub fn pop_flags(&mut self, count: u16) {
        if self.alt_active {
            self.alt.pop(count);
        } else {
            self.main.pop(count);
        }
    }

    /// Handle `CSI = flags ; mode u`.
    pub fn set_flags(&mut self, raw_flags: u16, mode: KittySetMode) {
        if self.alt_active {
            self.alt.set(raw_flags, mode);
        } else {
            self.main.set(raw_flags, mode);
        }
    }

    /// Format the terminal's reply to `CSI ? u`: `ESC [ ? <flags> u`.
    pub fn query_reply(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(b"\x1b[?");
        push_dec_u32(&mut out, self.active_flags() as u32);
        out.push(b'u');
        out
    }
}

fn push_dec_u32(out: &mut Vec<u8>, mut val: u32) {
    if val == 0 {
        out.push(b'0');
        return;
    }
    let mut rev = [0u8; 10];
    let mut len = 0usize;
    while val > 0 {
        if let Some(slot) = rev.get_mut(len) {
            *slot = b'0'.saturating_add((val % 10) as u8);
            len = len.saturating_add(1);
        }
        val /= 10;
    }
    while len > 0 {
        len = len.saturating_sub(1);
        if let Some(&d) = rev.get(len) {
            out.push(d);
        }
    }
}

/// Encode a key event according to `active_flags` (`CSI u` when disambiguated, or legacy bytes).
pub fn encode_kitty_key(
    codepoint: u32,
    modifiers: u8,
    kind: KittyKeyEventKind,
    active_flags: u8,
) -> Vec<u8> {
    let report_events = (active_flags & KITTY_REPORT_EVENT_TYPES) != 0;
    if kind == KittyKeyEventKind::Release && !report_events {
        return Vec::new();
    }
    let report_all = (active_flags & KITTY_REPORT_ALL_KEYS_AS_ESC) != 0;
    let disambiguate = (active_flags & KITTY_DISAMBIGUATE_ESC) != 0;

    let needs_csi_u = report_all
        || (report_events && kind != KittyKeyEventKind::Press)
        || (disambiguate
            && (codepoint == 27
                || (modifiers != 0 && (codepoint == 13 || codepoint == 9 || codepoint == 127))
                || (modifiers & (MOD_ALT | MOD_CTRL | MOD_SUPER)) != 0));

    if !needs_csi_u {
        if let Some(ch) = char::from_u32(codepoint) {
            let mut tmp = [0u8; 4];
            let s = ch.encode_utf8(&mut tmp);
            let cap = if s.len() < 4 { s.len() } else { 4 };
            let mut out = {
                let _ = cap;
                Vec::new()
            };
            out.extend_from_slice(s.as_bytes());
            return out;
        }
        return Vec::new();
    }

    let mod_param = 1u32.saturating_add((modifiers & 0x0F) as u32);
    let mut out = Vec::new();
    out.extend_from_slice(b"\x1b[");
    push_dec_u32(&mut out, codepoint);
    if report_events && kind != KittyKeyEventKind::Press {
        out.push(b';');
        push_dec_u32(&mut out, mod_param);
        out.push(b':');
        push_dec_u32(&mut out, kind.wire_code() as u32);
    } else if mod_param > 1 {
        out.push(b';');
        push_dec_u32(&mut out, mod_param);
    }
    out.push(b'u');
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stack_pushes_pops_isolates_alt_screen_and_clamps_overflow() {
        let mut st = KittyKeyboardState::new();
        for i in 0..24u16 {
            st.push_flags(i);
            assert!(kitty_depth_within_cap(st.stack_depth(), MAX_KITTY_STACK));
        }
        assert_eq!(st.stack_depth(), MAX_KITTY_STACK);
        assert_eq!(st.active_flags(), 23 & KITTY_ALL_FLAGS_MASK);

        st.set_alt_screen(true);
        assert_eq!(st.active_flags(), 0);
        st.push_flags(KITTY_DISAMBIGUATE_ESC as u16);
        assert_eq!(st.query_reply(), b"\x1b[?1u");

        st.set_alt_screen(false);
        assert_eq!(st.active_flags(), 23 & KITTY_ALL_FLAGS_MASK);
        st.pop_flags(100);
        assert_eq!(st.active_flags(), 0);
        assert_eq!(st.stack_depth(), 0);
    }

    #[test]
    fn encodes_shift_enter_and_key_release_unambiguously() {
        let shift_enter = encode_kitty_key(
            13,
            MOD_SHIFT,
            KittyKeyEventKind::Press,
            KITTY_DISAMBIGUATE_ESC,
        );
        assert_eq!(shift_enter, b"\x1b[13;2u");

        let plain_a = encode_kitty_key(
            b'a' as u32,
            0,
            KittyKeyEventKind::Press,
            KITTY_DISAMBIGUATE_ESC,
        );
        assert_eq!(plain_a, b"a");

        let release_a = encode_kitty_key(
            b'a' as u32,
            0,
            KittyKeyEventKind::Release,
            KITTY_DISAMBIGUATE_ESC | KITTY_REPORT_EVENT_TYPES,
        );
        assert_eq!(release_a, b"\x1b[97;1:3u");
    }
}
