//! Normalized typed screen-ops: the one-parser projection of the raw `Out` byte
//! log (the consolidated wire decision in `docs/DESIGN-astream-term.md` §4).
//!
//! A viewer that receives raw VT bytes must re-parse them against its own
//! (possibly wrong) terminfo/locale — the two-party disagreement class. A
//! [`ScreenOp`] stream is emitted by the **single canonical parser** server-side
//! ([`crate::screen::emit_ops`]), so two viewers cannot disagree; the colours in
//! [`ScreenOp::SetSgr`] are the **resolved pen**, not raw SGR params.
//!
//! Re-applying the op stream ([`crate::screen::apply_ops`]) re-drives the *same*
//! private screen mutators from typed ops — an independent dispatch path that
//! bypasses only the VT state machine — and reproduces a byte-equal screen. The
//! op set is a lossless projection of the current fold's bounded subset, not of
//! full xterm.

use crate::screen::Color;

/// One normalized terminal operation: the top-level mutation a VT dispatch made.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScreenOp {
    /// Write one glyph at the cursor (deferred-wrap and scroll happen on replay).
    Print(char),
    /// Carriage return (cursor to column 0).
    CarriageReturn,
    /// Line feed (cursor down one row, scrolling at the bottom).
    LineFeed,
    /// Horizontal tab.
    Tab,
    /// Backspace.
    Backspace,
    /// Move the cursor up `n` rows.
    CursorUp(u16),
    /// Move the cursor down `n` rows.
    CursorDown(u16),
    /// Move the cursor forward `n` columns.
    CursorForward(u16),
    /// Move the cursor back `n` columns.
    CursorBack(u16),
    /// Move the cursor to `(row, col)`, 0-based.
    MoveTo(u16, u16),
    /// Erase in display (`ED`): 0 below, 1 above, 2/3 all.
    EraseDisplay(u16),
    /// Erase in line (`EL`): 0 right, 1 left, 2 whole line.
    EraseLine(u16),
    /// Set the drawing pen to a **resolved** colour/attribute state.
    SetSgr {
        /// Resolved foreground.
        fg: Color,
        /// Resolved background.
        bg: Color,
        /// Resolved attribute bits.
        attrs: u8,
    },
    /// Set/reset DEC private modes (cursor visibility, alternate screen).
    SetMode {
        /// The mode numbers.
        params: Vec<u16>,
        /// `true` to set, `false` to reset.
        set: bool,
    },
    /// Save the cursor position.
    SaveCursor,
    /// Restore the saved cursor position.
    RestoreCursor,
    /// Set the DEC scrolling region (`DECSTBM`) to 0-based inclusive rows
    /// `[top, bottom]`; homes the cursor. The full screen is `(0, rows-1)`. A
    /// `bottom` past the screen means the last row; a region that is then empty
    /// is ignored (margins and cursor unchanged), as in xterm.
    SetScrollRegion {
        /// Top row of the region (0-based, inclusive).
        top: u16,
        /// Bottom row of the region (0-based, inclusive).
        bottom: u16,
    },
    /// Full reset (`RIS`).
    Reset,
    /// Resize the viewport to `(cols, rows)`.
    Resize(u16, u16),
}
