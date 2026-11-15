// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! DEC Private Mode (`?1..=?2026`) Bitmask Snapshot & Bounded VT Restore Emitter.
//!
//! When an `aterm` session attaches across `asb` or forks a counterfactual terminal branch,
//! cell contents alone are insufficient: mouse tracking (`?1000`/`?1002`/`?1003`/`?1006`),
//! bracketed paste (`?2004`), focus events (`?1004`), alternate screen (`?1049`), cursor
//! visibility (`?25`), application cursor keys (`?1`), origin mode (`?6`), autowrap (`?7`),
//! and synchronized output (`?2026`) must be restored atomically without overflowing the
//! bounded attach banner frame.
//!
//! Backed by Clean TLA+ Island `Astream.Term.TlaDecPrivateModeMask`
//! (`decset_mode_snapshot_island.rs`), proving `emittedBytes <= maxRestoreBytes` and
//! `activeBits <= maxModeBits`.

#![allow(clippy::assign_op_pattern)]

#[cfg(clean_islands)]
#[path = "decset_mode_snapshot_island.rs"]
mod island;
#[cfg(clean_islands)]
pub use island::{dec_mode_bits_clamp, dec_restore_bytes_clamp};

#[cfg(not(clean_islands))]
#[inline]
pub const fn dec_restore_bytes_clamp(proposed_bytes: u64, max_bytes: u64) -> u64 {
    if proposed_bytes < max_bytes {
        proposed_bytes
    } else {
        max_bytes
    }
}

#[cfg(not(clean_islands))]
#[inline]
pub const fn dec_mode_bits_clamp(active_bits: u64, max_bits: u64) -> u64 {
    if active_bits < max_bits {
        active_bits
    } else {
        max_bits
    }
}

contract_fn! {
    /// Kernel-certified DEC private mode restore budget check (`proposed_bytes <= max_bytes`).
    #[must_use]
    #[inline]
    pub const fn dec_restore_fits_budget(proposed_bytes: u64, max_bytes: u64) -> bool
    clauses [ensures result == (proposed_bytes <= max_bytes)]
    {
        proposed_bytes <= max_bytes
    }
}

/// Number of canonical DEC private modes tracked in `DecModeSnapshot`.
pub const MAX_TRACKED_DEC_MODES: u64 = 16;

/// Default maximum VT restore byte budget (`256` bytes easily fits all 16 CSI `?Ps h`/`l` codes).
pub const DEFAULT_MAX_RESTORE_BYTES: usize = 256;

/// Canonical DEC private modes (`CSI ? Ps h` / `CSI ? Ps l`) tracked across `aterm` attach/fork.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum DecPrivateMode {
    /// `?1` — DECCKM (Application Cursor Keys).
    AppCursorKeys = 0,
    /// `?6` — DECOM (Origin Mode).
    OriginMode = 1,
    /// `?7` — DECAWM (Auto-Wrap Mode, default ON in VT100/xterm).
    AutoWrap = 2,
    /// `?12` — Cursor Blinking.
    CursorBlink = 3,
    /// `?25` — DECTCEM (Text Cursor Enable Mode, default ON).
    CursorVisible = 4,
    /// `?47` — Legacy Alternate Screen Buffer.
    AltScreenLegacy = 5,
    /// `?1000` — X11 Mouse Button Tracking.
    MouseButton = 6,
    /// `?1002` — Cell-Motion Mouse Tracking.
    MouseCellMotion = 7,
    /// `?1003` — All-Motion Mouse Tracking.
    MouseAllMotion = 8,
    /// `?1004` — FocusIn / FocusOut Event Reporting.
    FocusEvents = 9,
    /// `?1006` — SGR Extended Mouse Coordinates.
    MouseSgr = 10,
    /// `?1047` — Alternate Screen Buffer (clear on exit).
    AltScreen1047 = 11,
    /// `?1048` — Save/Restore Cursor (`DECSC`/`DECRC`).
    SaveCursor1048 = 12,
    /// `?1049` — Save Cursor + Switch to Alternate Screen Buffer.
    AltScreen1049 = 13,
    /// `?2004` — Bracketed Paste Mode.
    BracketedPaste = 14,
    /// `?2026` — Synchronized Output (`BSU`/`ESU`).
    SynchronizedOutput = 15,
}

/// Fixed-order lookup table of all 16 tracked DEC private modes.
pub const ALL_DEC_MODES: [DecPrivateMode; 16] = [
    DecPrivateMode::AppCursorKeys,
    DecPrivateMode::OriginMode,
    DecPrivateMode::AutoWrap,
    DecPrivateMode::CursorBlink,
    DecPrivateMode::CursorVisible,
    DecPrivateMode::AltScreenLegacy,
    DecPrivateMode::MouseButton,
    DecPrivateMode::MouseCellMotion,
    DecPrivateMode::MouseAllMotion,
    DecPrivateMode::FocusEvents,
    DecPrivateMode::MouseSgr,
    DecPrivateMode::AltScreen1047,
    DecPrivateMode::SaveCursor1048,
    DecPrivateMode::AltScreen1049,
    DecPrivateMode::BracketedPaste,
    DecPrivateMode::SynchronizedOutput,
];

impl DecPrivateMode {
    /// Returns the numeric `CSI ? Ps` parameter for this mode.
    #[inline]
    pub const fn code(self) -> u16 {
        match self {
            Self::AppCursorKeys => 1,
            Self::OriginMode => 6,
            Self::AutoWrap => 7,
            Self::CursorBlink => 12,
            Self::CursorVisible => 25,
            Self::AltScreenLegacy => 47,
            Self::MouseButton => 1000,
            Self::MouseCellMotion => 1002,
            Self::MouseAllMotion => 1003,
            Self::FocusEvents => 1004,
            Self::MouseSgr => 1006,
            Self::AltScreen1047 => 1047,
            Self::SaveCursor1048 => 1048,
            Self::AltScreen1049 => 1049,
            Self::BracketedPaste => 2004,
            Self::SynchronizedOutput => 2026,
        }
    }

    /// Maps a numeric `CSI ? Ps` code to its tracked `DecPrivateMode`, if recognized.
    #[inline]
    pub const fn from_code(code: u16) -> Option<Self> {
        match code {
            1 => Some(Self::AppCursorKeys),
            6 => Some(Self::OriginMode),
            7 => Some(Self::AutoWrap),
            12 => Some(Self::CursorBlink),
            25 => Some(Self::CursorVisible),
            47 => Some(Self::AltScreenLegacy),
            1000 => Some(Self::MouseButton),
            1002 => Some(Self::MouseCellMotion),
            1003 => Some(Self::MouseAllMotion),
            1004 => Some(Self::FocusEvents),
            1006 => Some(Self::MouseSgr),
            1047 => Some(Self::AltScreen1047),
            1048 => Some(Self::SaveCursor1048),
            1049 => Some(Self::AltScreen1049),
            2004 => Some(Self::BracketedPaste),
            2026 => Some(Self::SynchronizedOutput),
            _ => None,
        }
    }

    #[inline]
    pub const fn bit(self) -> u64 {
        1u64 << ((self as u8) & 15)
    }
}

/// Compact 16-bit DEC private mode snapshot with VT diff restore generation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DecModeSnapshot {
    mask: u64,
}

impl Default for DecModeSnapshot {
    fn default() -> Self {
        Self::vt_default()
    }
}

impl DecModeSnapshot {
    /// Standard VT/xterm initial mode state (`?7` AutoWrap ON, `?25` CursorVisible ON).
    #[inline]
    pub const fn vt_default() -> Self {
        Self {
            mask: DecPrivateMode::AutoWrap.bit() | DecPrivateMode::CursorVisible.bit(),
        }
    }

    /// Empty snapshot with all tracked modes cleared.
    #[inline]
    pub const fn empty() -> Self {
        Self { mask: 0 }
    }

    /// Reconstructs a snapshot from a raw bitmask, masking off untracked upper bits.
    #[inline]
    pub const fn from_raw_mask(raw: u64) -> Self {
        Self {
            mask: raw & ((1u64 << MAX_TRACKED_DEC_MODES) - 1),
        }
    }

    #[inline]
    pub const fn raw_mask(self) -> u64 {
        self.mask
    }

    /// Clamped count of currently enabled DEC private modes (`<= MAX_TRACKED_DEC_MODES`).
    #[inline]
    pub const fn active_count(self) -> u64 {
        dec_mode_bits_clamp(self.mask.count_ones() as u64, MAX_TRACKED_DEC_MODES)
    }

    #[inline]
    pub const fn is_enabled(self, mode: DecPrivateMode) -> bool {
        (self.mask & mode.bit()) != 0
    }

    #[inline]
    pub fn set(&mut self, mode: DecPrivateMode, enabled: bool) {
        if enabled {
            self.mask = self.mask | (mode.bit());
        } else {
            self.mask = self.mask & (!mode.bit());
        }
    }

    /// Applies a numeric `DECSET` (`enabled = true`) or `DECRST` (`enabled = false`).
    /// Returns `true` if `code` is a tracked mode.
    #[inline]
    pub fn apply_code(&mut self, code: u16, enabled: bool) -> bool {
        match DecPrivateMode::from_code(code) {
            Some(mode) => {
                self.set(mode, enabled);
                true
            }
            None => false,
        }
    }

    /// Emits minimal `ESC [ ? Ps h` / `ESC [ ? Ps l` sequences transforming `baseline` into
    /// `self`, bounded by `max_restore_bytes`.
    ///
    /// Returns `(emitted_bytes, complete)` where `emitted_bytes <= max_restore_bytes` is
    /// certified by `dec_restore_bytes_clamp`, and `complete` is `false` if the budget cut off
    /// remaining mode transitions.
    pub fn emit_diff_from(
        self,
        baseline: Self,
        out: &mut Vec<u8>,
        max_restore_bytes: usize,
    ) -> (usize, bool) {
        if self.mask == baseline.mask {
            return (0, true);
        }
        let cap_u64 = max_restore_bytes as u64;
        let mut emitted: u64 = 0;
        let mut complete = true;

        let mut modes_cur: &[DecPrivateMode] = &ALL_DEC_MODES;
        while let &[mode, ref rest @ ..] = modes_cur {
            let target_on = self.is_enabled(mode);
            let base_on = baseline.is_enabled(mode);
            if target_on != base_on {
                let (seq_buf, seq_len) = encode_dec_csi(mode, target_on);
                let proposed = emitted.saturating_add(seq_len as u64);
                if !dec_restore_fits_budget(proposed, cap_u64) {
                    complete = false;
                    break;
                }
                let clamped = dec_restore_bytes_clamp(proposed, cap_u64);
                if let Some(s) = seq_buf.get(..seq_len) {
                    out.extend_from_slice(s);
                }
                emitted = clamped;
            }
            modes_cur = rest;
        }
        (emitted as usize, complete)
    }
}

/// Formats `ESC [ ? <decimal code> h/l` into a 9-byte stack array without indexing, loops, or `fmt`.
const fn encode_dec_csi(mode: DecPrivateMode, enable: bool) -> ([u8; 9], usize) {
    let fin = if enable { b'h' } else { b'l' };
    match mode {
        DecPrivateMode::AppCursorKeys => ([0x1b, b'[', b'?', b'1', fin, 0, 0, 0, 0], 5),
        DecPrivateMode::OriginMode => ([0x1b, b'[', b'?', b'6', fin, 0, 0, 0, 0], 5),
        DecPrivateMode::AutoWrap => ([0x1b, b'[', b'?', b'7', fin, 0, 0, 0, 0], 5),
        DecPrivateMode::CursorBlink => ([0x1b, b'[', b'?', b'1', b'2', fin, 0, 0, 0], 6),
        DecPrivateMode::CursorVisible => ([0x1b, b'[', b'?', b'2', b'5', fin, 0, 0, 0], 6),
        DecPrivateMode::AltScreenLegacy => ([0x1b, b'[', b'?', b'4', b'7', fin, 0, 0, 0], 6),
        DecPrivateMode::MouseButton => ([0x1b, b'[', b'?', b'1', b'0', b'0', b'0', fin, 0], 8),
        DecPrivateMode::MouseCellMotion => ([0x1b, b'[', b'?', b'1', b'0', b'0', b'2', fin, 0], 8),
        DecPrivateMode::MouseAllMotion => ([0x1b, b'[', b'?', b'1', b'0', b'0', b'3', fin, 0], 8),
        DecPrivateMode::FocusEvents => ([0x1b, b'[', b'?', b'1', b'0', b'0', b'4', fin, 0], 8),
        DecPrivateMode::MouseSgr => ([0x1b, b'[', b'?', b'1', b'0', b'0', b'6', fin, 0], 8),
        DecPrivateMode::AltScreen1047 => ([0x1b, b'[', b'?', b'1', b'0', b'4', b'7', fin, 0], 8),
        DecPrivateMode::SaveCursor1048 => ([0x1b, b'[', b'?', b'1', b'0', b'4', b'8', fin, 0], 8),
        DecPrivateMode::AltScreen1049 => ([0x1b, b'[', b'?', b'1', b'0', b'4', b'9', fin, 0], 8),
        DecPrivateMode::BracketedPaste => ([0x1b, b'[', b'?', b'2', b'0', b'0', b'4', fin, 0], 8),
        DecPrivateMode::SynchronizedOutput => {
            ([0x1b, b'[', b'?', b'2', b'0', b'2', b'6', fin, 0], 8)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vt_default_enables_autowrap_and_cursor_visible() {
        let snap = DecModeSnapshot::vt_default();
        assert!(snap.is_enabled(DecPrivateMode::AutoWrap));
        assert!(snap.is_enabled(DecPrivateMode::CursorVisible));
        assert!(!snap.is_enabled(DecPrivateMode::BracketedPaste));
        assert_eq!(snap.active_count(), 2);
    }

    #[test]
    fn emit_diff_produces_exact_csi_sequences_and_roundtrips() {
        let base = DecModeSnapshot::vt_default();
        let mut target = base;
        assert!(target.apply_code(25, false)); // hide cursor
        assert!(target.apply_code(1006, true)); // SGR mouse
        assert!(target.apply_code(2004, true)); // bracketed paste
        assert!(target.apply_code(2026, true)); // sync output
        assert!(!target.apply_code(9999, true)); // unknown ignored

        let mut bytes = Vec::new();
        let (written, complete) =
            target.emit_diff_from(base, &mut bytes, DEFAULT_MAX_RESTORE_BYTES);
        assert!(complete);
        assert_eq!(written, bytes.len());
        assert_eq!(&bytes, b"\x1b[?25l\x1b[?1006h\x1b[?2004h\x1b[?2026h");
    }

    #[test]
    fn emit_diff_respects_max_restore_bytes_budget() {
        let base = DecModeSnapshot::empty();
        let target = DecModeSnapshot::from_raw_mask(u64::MAX);
        assert_eq!(target.active_count(), MAX_TRACKED_DEC_MODES);

        let mut bytes = Vec::new();
        let (written, complete) = target.emit_diff_from(base, &mut bytes, 18);
        assert!(!complete);
        assert!(written <= 18);
        assert_eq!(written, bytes.len());
        // `?1h` (6) + `?6h` (6) + `?7h` (6) == 18 bytes exact
        assert_eq!(&bytes, b"\x1b[?1h\x1b[?6h\x1b[?7h");
    }
}
