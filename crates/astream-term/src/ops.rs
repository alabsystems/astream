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

use crate::screen::{Charset, Color, Underline};
use std::fmt;

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
    /// Erase in display (`ED`): 0 below, 1 above, 2 all; 3 (saved lines) has
    /// nothing to erase.
    EraseDisplay(u16),
    /// Erase in line (`EL`): 0 right, 1 left, 2 whole line.
    EraseLine(u16),
    /// Erase `n` characters from the cursor (`ECH`).
    EraseChars(u16),
    /// Insert `n` blank characters at the cursor (`ICH`).
    InsertChars(u16),
    /// Delete `n` characters at the cursor (`DCH`).
    DeleteChars(u16),
    /// Insert `n` blank lines at the cursor row, inside the scrolling region
    /// (`IL`).
    InsertLines(u16),
    /// Delete `n` lines at the cursor row, inside the scrolling region (`DL`).
    DeleteLines(u16),
    /// Reverse index (`RI`): up a row, scrolling the region down at its top.
    ReverseIndex,
    /// Set the drawing pen to a **resolved** palette/default colour and attribute state
    /// (emitted when neither channel carries 24-bit truecolour).
    SetSgr {
        /// Resolved foreground.
        fg: Color,
        /// Resolved background.
        bg: Color,
        /// Resolved attribute bits, bit 1 set when the pen underlines in any style
        /// (applied alone, a single uncoloured underline).
        attrs: u8,
    },
    /// Set the drawing pen when one or both channels carry a **resolved** 24-bit
    /// truecolour `(r, g, b)` value (`38;2;r;g;b`, `38:2::r:g;b`, `48;2;r;g;b`,
    /// `48:2::r:g:b`).
    SetSgrRgb {
        /// Resolved palette/default foreground (`Color::Default` when `fg_rgb` is `Some`).
        fg: Color,
        /// Resolved 24-bit foreground `(r, g, b)`, if active.
        fg_rgb: Option<(u8, u8, u8)>,
        /// Resolved palette/default background (`Color::Default` when `bg_rgb` is `Some`).
        bg: Color,
        /// Resolved 24-bit background `(r, g, b)`, if active.
        bg_rgb: Option<(u8, u8, u8)>,
        /// Resolved attribute bits, bit 1 set when the pen underlines in any style
        /// (applied alone, a single uncoloured underline).
        attrs: u8,
    },
    /// Set the drawing pen's underline: its **resolved** style and colour (`4`, `21`,
    /// `4:n`, `24`, `58`, `59`). Emitted after a [`ScreenOp::SetSgr`] or
    /// [`ScreenOp::SetSgrRgb`] only when the pen's underline is more than that op's bit
    /// 1 says: a style other than single, or a colour.
    SetUnderline {
        /// The style.
        style: Underline,
        /// Resolved palette/default colour (`Color::Default` when `ul_rgb` is `Some`).
        ul: Color,
        /// Resolved 24-bit colour `(r, g, b)`, if active.
        ul_rgb: Option<(u8, u8, u8)>,
    },
    /// Set/reset DEC private modes (cursor visibility, origin mode, alternate
    /// screen).
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
    /// Set (`true`) or reset insert mode (IRM, `CSI 4 h`/`l`).
    SetInsertMode(bool),
    /// Set (`true`) or reset newline mode (LNM, `CSI 20 h`/`l`). The carriage
    /// return it adds to a line feed is its own [`ScreenOp::CarriageReturn`].
    SetNewlineMode(bool),
    /// Designate `charset` into G1 (`g1`) or G0 (`ESC ) F`, `ESC ( F`). A
    /// [`ScreenOp::Print`] carries the glyph already translated; the
    /// designation keeps the state a DECSC saves.
    Designate {
        /// G1 rather than G0.
        g1: bool,
        /// The set designated.
        charset: Charset,
    },
    /// Map G1 (`g1`, SO) or G0 (SI) into GL.
    LockShift {
        /// G1 rather than G0.
        g1: bool,
    },
    /// Set the left and right margins (DECSLRM under DECLRMM) to 0-based
    /// inclusive columns `[left, right]`, `left < right`; homes the cursor.
    SetLeftRightMargins {
        /// The left margin (0-based, inclusive).
        left: u16,
        /// The right margin (0-based, inclusive).
        right: u16,
    },
    /// Scroll the region up `n` lines (`SU`); the cursor stays.
    ScrollUp(u16),
    /// Scroll the region down `n` lines (`SD`); the cursor stays.
    ScrollDown(u16),
    /// Full reset (`RIS`).
    Reset,
    /// Resize the viewport to `(cols, rows)`.
    Resize(u16, u16),
}

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "ops_island.rs"]
mod ops_island;
#[cfg(not(clean_islands))]
pub use crate::twins::op_clamp_scroll_top;
#[cfg(clean_islands)]
pub use ops_island::op_clamp_scroll_top;

contract_fn! {
    /// Kernel-certified check that a `SetScrollRegion` `[top, bottom]` interval is
    /// non-empty (`top <= bottom`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `op_scroll_region_nonempty_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn op_scroll_region_nonempty(top: u16, bottom: u16) -> bool
    clauses [ensures result == (top <= bottom)]
    {
        top <= bottom
    }
}

impl ScreenOp {
    /// If `self` is a [`ScreenOp::SetScrollRegion`] with a non-empty `[top, bottom]`
    /// interval, return its normalized `(top, bottom)` pair.
    #[must_use]
    pub const fn normalized_scroll_region(&self) -> Option<(u16, u16)> {
        match *self {
            ScreenOp::SetScrollRegion { top, bottom } if top <= bottom => {
                let clamped_top = if top < bottom { top } else { bottom };
                Some((clamped_top, bottom))
            }
            _ => None,
        }
    }
}

/// Four-byte magic prefix (`"ASOP"`) of a binary [`ScreenOp`] batch frame.
pub const OPS_WIRE_MAGIC: [u8; 4] = *b"ASOP";

/// Format version of a binary [`ScreenOp`] batch frame.
pub const OPS_WIRE_VERSION: u8 = 1;

/// Maximum number of [`ScreenOp`] entries in one encoded wire batch (`1_048_576`).
pub const MAX_OPS_PER_BATCH: usize = 1 << 20;

/// Maximum number of DEC private mode parameters in one [`ScreenOp::SetMode`]
/// (`129`, matching the canonical VT parser's `CSI_PARAM_MAX + 1` ceiling).
pub const MAX_MODE_PARAMS: usize = 129;

/// Refusal returned by [`encode_ops`] or [`decode_ops`] on malformed or oversized input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OpsWireError {
    /// Input ended before the header or current operation payload completed.
    Truncated,
    /// Header magic did not match [`OPS_WIRE_MAGIC`].
    BadMagic([u8; 4]),
    /// Header version did not match [`OPS_WIRE_VERSION`].
    UnsupportedVersion(u8),
    /// Operation tag byte does not name a known [`ScreenOp`] variant.
    UnknownOpTag(u8),
    /// `Print` carried a `u32` that is not a valid Unicode scalar value.
    InvalidChar(u32),
    /// Boolean field carried a byte other than `0` or `1`.
    InvalidBool(u8),
    /// [`Color`] tag byte was neither `0` (`Default`) nor `1` (`Indexed`), in the op `op`
    /// names ([`ScreenOp::SetSgr`], [`ScreenOp::SetSgrRgb`] or [`ScreenOp::SetUnderline`]).
    InvalidColorTag {
        /// The [`ScreenOp`] variant the colour belongs to.
        op: &'static str,
        /// The tag byte read.
        tag: u8,
    },
    /// [`Charset`] tag byte was neither `0` (`Ascii`) nor `1` (`DecSpecial`).
    InvalidCharsetTag(u8),
    /// [`Underline`] style byte was not one of [`Underline::code`]'s `0..=5`.
    InvalidUnderlineStyle(u8),
    /// Batch exceeded [`MAX_OPS_PER_BATCH`].
    TooManyOps(usize),
    /// [`ScreenOp::SetMode`] exceeded [`MAX_MODE_PARAMS`].
    TooManyModeParams(usize),
    /// Extra trailing bytes remained after decoding the declared operation count.
    TrailingBytes(usize),
}

impl fmt::Display for OpsWireError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OpsWireError::Truncated => write!(f, "truncated ScreenOp wire frame"),
            OpsWireError::BadMagic(m) => write!(f, "bad ScreenOp wire magic: {m:?}"),
            OpsWireError::UnsupportedVersion(v) => {
                write!(f, "unsupported ScreenOp wire version {v}")
            }
            OpsWireError::UnknownOpTag(t) => write!(f, "unknown ScreenOp wire tag 0x{t:02x}"),
            OpsWireError::InvalidChar(c) => {
                write!(f, "invalid Unicode scalar 0x{c:x} in ScreenOp::Print")
            }
            OpsWireError::InvalidBool(b) => write!(f, "invalid bool byte 0x{b:02x} in ScreenOp"),
            OpsWireError::InvalidColorTag { op, tag } => {
                write!(f, "invalid Color wire tag 0x{tag:02x} in ScreenOp::{op}")
            }
            OpsWireError::InvalidCharsetTag(t) => {
                write!(
                    f,
                    "invalid Charset wire tag 0x{t:02x} in ScreenOp::Designate"
                )
            }
            OpsWireError::InvalidUnderlineStyle(s) => {
                write!(
                    f,
                    "invalid Underline style 0x{s:02x} in ScreenOp::SetUnderline"
                )
            }
            OpsWireError::TooManyOps(n) => {
                write!(
                    f,
                    "ScreenOp batch length {n} exceeds MAX_OPS_PER_BATCH ({MAX_OPS_PER_BATCH})"
                )
            }
            OpsWireError::TooManyModeParams(n) => {
                write!(
                    f,
                    "SetMode parameter count {n} exceeds MAX_MODE_PARAMS ({MAX_MODE_PARAMS})"
                )
            }
            OpsWireError::TrailingBytes(n) => {
                write!(f, "{n} unexpected trailing byte(s) after ScreenOp batch")
            }
        }
    }
}

impl std::error::Error for OpsWireError {}

fn put_u16_le(out: &mut Vec<u8>, v: u16) {
    out.extend_from_slice(&v.to_le_bytes());
}

fn put_u32_le(out: &mut Vec<u8>, v: u32) {
    out.extend_from_slice(&v.to_le_bytes());
}

fn put_color(out: &mut Vec<u8>, c: Color) {
    match c {
        Color::Default => out.push(0),
        Color::Indexed(idx) => {
            out.push(1);
            out.push(idx);
        }
    }
}

fn put_opt_rgb(out: &mut Vec<u8>, rgb: Option<(u8, u8, u8)>) {
    match rgb {
        None => out.push(0),
        Some((r, g, b)) => out.extend_from_slice(&[1, r, g, b]),
    }
}

fn take_u8(rest: &[u8]) -> Result<(u8, &[u8]), OpsWireError> {
    let &[b, ref tail @ ..] = rest else {
        return Err(OpsWireError::Truncated);
    };
    Ok((b, tail))
}

fn take_bool(rest: &[u8]) -> Result<(bool, &[u8]), OpsWireError> {
    let (b, tail) = take_u8(rest)?;
    match b {
        0 => Ok((false, tail)),
        1 => Ok((true, tail)),
        other => Err(OpsWireError::InvalidBool(other)),
    }
}

fn take_u16_le(rest: &[u8]) -> Result<(u16, &[u8]), OpsWireError> {
    let &[b0, b1, ref tail @ ..] = rest else {
        return Err(OpsWireError::Truncated);
    };
    Ok((u16::from_le_bytes([b0, b1]), tail))
}

fn take_u32_le(rest: &[u8]) -> Result<(u32, &[u8]), OpsWireError> {
    let &[b0, b1, b2, b3, ref tail @ ..] = rest else {
        return Err(OpsWireError::Truncated);
    };
    Ok((u32::from_le_bytes([b0, b1, b2, b3]), tail))
}

/// Read a [`Color`]; a bad tag is reported against `op`, the variant it belongs to.
fn take_color<'a>(rest: &'a [u8], op: &'static str) -> Result<(Color, &'a [u8]), OpsWireError> {
    let (tag, tail) = take_u8(rest)?;
    match tag {
        0 => Ok((Color::Default, tail)),
        1 => {
            let (idx, tail2) = take_u8(tail)?;
            Ok((Color::Indexed(idx), tail2))
        }
        tag => Err(OpsWireError::InvalidColorTag { op, tag }),
    }
}

type RgbTriple = (u8, u8, u8);

fn take_opt_rgb(rest: &[u8]) -> Result<(Option<RgbTriple>, &[u8]), OpsWireError> {
    let (present, tail) = take_bool(rest)?;
    if !present {
        return Ok((None, tail));
    }
    let (r, t1) = take_u8(tail)?;
    let (g, t2) = take_u8(t1)?;
    let (b, t3) = take_u8(t2)?;
    Ok((Some((r, g, b)), t3))
}

const fn encode_op_group(op: &ScreenOp) -> u8 {
    match op {
        ScreenOp::Print(_)
        | ScreenOp::CarriageReturn
        | ScreenOp::LineFeed
        | ScreenOp::Tab
        | ScreenOp::Backspace
        | ScreenOp::CursorUp(_)
        | ScreenOp::CursorDown(_)
        | ScreenOp::CursorForward(_)
        | ScreenOp::CursorBack(_)
        | ScreenOp::MoveTo(_, _)
        | ScreenOp::SaveCursor
        | ScreenOp::RestoreCursor => 0,
        ScreenOp::EraseDisplay(_)
        | ScreenOp::EraseLine(_)
        | ScreenOp::EraseChars(_)
        | ScreenOp::InsertChars(_)
        | ScreenOp::DeleteChars(_)
        | ScreenOp::InsertLines(_)
        | ScreenOp::DeleteLines(_)
        | ScreenOp::ReverseIndex
        | ScreenOp::ScrollUp(_)
        | ScreenOp::ScrollDown(_) => 1,
        ScreenOp::SetSgr { .. }
        | ScreenOp::SetSgrRgb { .. }
        | ScreenOp::SetUnderline { .. }
        | ScreenOp::SetMode { .. }
        | ScreenOp::SetScrollRegion { .. }
        | ScreenOp::SetInsertMode(_)
        | ScreenOp::SetNewlineMode(_)
        | ScreenOp::Designate { .. }
        | ScreenOp::LockShift { .. }
        | ScreenOp::SetLeftRightMargins { .. }
        | ScreenOp::Reset
        | ScreenOp::Resize(_, _) => 2,
    }
}

fn encode_op_cursor(out: &mut Vec<u8>, op: &ScreenOp) {
    match op {
        ScreenOp::Print(ch) => {
            out.push(0x01);
            put_u32_le(out, *ch as u32);
        }
        ScreenOp::CarriageReturn => out.push(0x02),
        ScreenOp::LineFeed => out.push(0x03),
        ScreenOp::Tab => out.push(0x04),
        ScreenOp::Backspace => out.push(0x05),
        ScreenOp::CursorUp(n) => {
            out.push(0x06);
            put_u16_le(out, *n);
        }
        ScreenOp::CursorDown(n) => {
            out.push(0x07);
            put_u16_le(out, *n);
        }
        ScreenOp::CursorForward(n) => {
            out.push(0x08);
            put_u16_le(out, *n);
        }
        ScreenOp::CursorBack(n) => {
            out.push(0x09);
            put_u16_le(out, *n);
        }
        ScreenOp::MoveTo(r, c) => {
            out.push(0x0A);
            put_u16_le(out, *r);
            put_u16_le(out, *c);
        }
        ScreenOp::SaveCursor => out.push(0x15),
        ScreenOp::RestoreCursor => out.push(0x16),
        _ => {}
    }
}

fn encode_op_edit(out: &mut Vec<u8>, op: &ScreenOp) {
    match op {
        ScreenOp::EraseDisplay(m) => {
            out.push(0x0B);
            put_u16_le(out, *m);
        }
        ScreenOp::EraseLine(m) => {
            out.push(0x0C);
            put_u16_le(out, *m);
        }
        ScreenOp::EraseChars(n) => {
            out.push(0x0D);
            put_u16_le(out, *n);
        }
        ScreenOp::InsertChars(n) => {
            out.push(0x0E);
            put_u16_le(out, *n);
        }
        ScreenOp::DeleteChars(n) => {
            out.push(0x0F);
            put_u16_le(out, *n);
        }
        ScreenOp::InsertLines(n) => {
            out.push(0x10);
            put_u16_le(out, *n);
        }
        ScreenOp::DeleteLines(n) => {
            out.push(0x11);
            put_u16_le(out, *n);
        }
        ScreenOp::ReverseIndex => out.push(0x12),
        ScreenOp::ScrollUp(n) => {
            out.push(0x1D);
            put_u16_le(out, *n);
        }
        ScreenOp::ScrollDown(n) => {
            out.push(0x1E);
            put_u16_le(out, *n);
        }
        _ => {}
    }
}

fn encode_op_style_or_mode(out: &mut Vec<u8>, op: &ScreenOp) -> Result<(), OpsWireError> {
    match op {
        ScreenOp::SetSgr { fg, bg, attrs } => {
            out.push(0x13);
            put_color(out, *fg);
            put_color(out, *bg);
            out.push(*attrs);
        }
        ScreenOp::SetMode { params, set } => {
            if params.len() > MAX_MODE_PARAMS {
                return Err(OpsWireError::TooManyModeParams(params.len()));
            }
            out.push(0x14);
            out.push(u8::from(*set));
            put_u16_le(out, params.len() as u16);
            for &p in params {
                put_u16_le(out, p);
            }
        }
        ScreenOp::SetScrollRegion { top, bottom } => {
            out.push(0x17);
            put_u16_le(out, *top);
            put_u16_le(out, *bottom);
        }
        ScreenOp::SetInsertMode(set) => {
            out.push(0x18);
            out.push(u8::from(*set));
        }
        ScreenOp::SetNewlineMode(set) => {
            out.push(0x19);
            out.push(u8::from(*set));
        }
        ScreenOp::Designate { g1, charset } => {
            out.push(0x1A);
            out.push(u8::from(*g1));
            out.push(match charset {
                Charset::Ascii => 0,
                Charset::DecSpecial => 1,
            });
        }
        ScreenOp::LockShift { g1 } => {
            out.push(0x1B);
            out.push(u8::from(*g1));
        }
        ScreenOp::SetLeftRightMargins { left, right } => {
            out.push(0x1C);
            put_u16_le(out, *left);
            put_u16_le(out, *right);
        }
        ScreenOp::Reset => out.push(0x1F),
        ScreenOp::Resize(cols, rows) => {
            out.push(0x20);
            put_u16_le(out, *cols);
            put_u16_le(out, *rows);
        }
        ScreenOp::SetSgrRgb {
            fg,
            fg_rgb,
            bg,
            bg_rgb,
            attrs,
        } => {
            out.push(0x21);
            put_color(out, *fg);
            put_opt_rgb(out, *fg_rgb);
            put_color(out, *bg);
            put_opt_rgb(out, *bg_rgb);
            out.push(*attrs);
        }
        ScreenOp::SetUnderline { style, ul, ul_rgb } => {
            out.push(0x22);
            out.push(style.code());
            put_color(out, *ul);
            put_opt_rgb(out, *ul_rgb);
        }
        _ => {}
    }
    Ok(())
}

fn encode_one_op(out: &mut Vec<u8>, op: &ScreenOp) -> Result<(), OpsWireError> {
    match encode_op_group(op) {
        0 => encode_op_cursor(out, op),
        1 => encode_op_edit(out, op),
        _ => encode_op_style_or_mode(out, op)?,
    }
    Ok(())
}

/// Encode a slice of normalized [`ScreenOp`]s into a self-describing, versioned
/// binary batch (`"ASOP"` + `v1` + `count: u32 LE` + tagged ops) suitable for
/// publishing over `astream-broker` to cross-machine viewers.
///
/// # Errors
/// Returns [`OpsWireError::TooManyOps`] if `ops.len() > MAX_OPS_PER_BATCH`, or
/// [`OpsWireError::TooManyModeParams`] if any [`ScreenOp::SetMode`] carries more
/// than [`MAX_MODE_PARAMS`] parameters.
pub fn encode_ops(ops: &[ScreenOp]) -> Result<Vec<u8>, OpsWireError> {
    if ops.len() > MAX_OPS_PER_BATCH {
        return Err(OpsWireError::TooManyOps(ops.len()));
    }
    let mut out = Vec::new();
    out.extend_from_slice(&OPS_WIRE_MAGIC);
    out.push(OPS_WIRE_VERSION);
    put_u32_le(&mut out, ops.len() as u32);
    for op in ops {
        encode_one_op(&mut out, op)?;
    }
    Ok(out)
}

fn decode_op_low(tag: u8, tail: &[u8]) -> Result<(ScreenOp, &[u8]), OpsWireError> {
    match tag {
        0x01 => {
            let (raw, t) = take_u32_le(tail)?;
            let Some(ch) = char::from_u32(raw) else {
                return Err(OpsWireError::InvalidChar(raw));
            };
            Ok((ScreenOp::Print(ch), t))
        }
        0x02 => Ok((ScreenOp::CarriageReturn, tail)),
        0x03 => Ok((ScreenOp::LineFeed, tail)),
        0x04 => Ok((ScreenOp::Tab, tail)),
        0x05 => Ok((ScreenOp::Backspace, tail)),
        0x06 => {
            let (n, t) = take_u16_le(tail)?;
            Ok((ScreenOp::CursorUp(n), t))
        }
        0x07 => {
            let (n, t) = take_u16_le(tail)?;
            Ok((ScreenOp::CursorDown(n), t))
        }
        0x08 => {
            let (n, t) = take_u16_le(tail)?;
            Ok((ScreenOp::CursorForward(n), t))
        }
        0x09 => {
            let (n, t) = take_u16_le(tail)?;
            Ok((ScreenOp::CursorBack(n), t))
        }
        0x0A => {
            let (r, t1) = take_u16_le(tail)?;
            let (c, t2) = take_u16_le(t1)?;
            Ok((ScreenOp::MoveTo(r, c), t2))
        }
        0x0B => {
            let (m, t) = take_u16_le(tail)?;
            Ok((ScreenOp::EraseDisplay(m), t))
        }
        0x0C => {
            let (m, t) = take_u16_le(tail)?;
            Ok((ScreenOp::EraseLine(m), t))
        }
        0x0D => {
            let (n, t) = take_u16_le(tail)?;
            Ok((ScreenOp::EraseChars(n), t))
        }
        0x0E => {
            let (n, t) = take_u16_le(tail)?;
            Ok((ScreenOp::InsertChars(n), t))
        }
        0x0F => {
            let (n, t) = take_u16_le(tail)?;
            Ok((ScreenOp::DeleteChars(n), t))
        }
        0x10 => {
            let (n, t) = take_u16_le(tail)?;
            Ok((ScreenOp::InsertLines(n), t))
        }
        0x11 => {
            let (n, t) = take_u16_le(tail)?;
            Ok((ScreenOp::DeleteLines(n), t))
        }
        other => Err(OpsWireError::UnknownOpTag(other)),
    }
}

fn decode_op_high(tag: u8, tail: &[u8]) -> Result<(ScreenOp, &[u8]), OpsWireError> {
    match tag {
        0x12 => Ok((ScreenOp::ReverseIndex, tail)),
        0x13 => {
            let (fg, t1) = take_color(tail, "SetSgr")?;
            let (bg, t2) = take_color(t1, "SetSgr")?;
            let (attrs, t3) = take_u8(t2)?;
            Ok((ScreenOp::SetSgr { fg, bg, attrs }, t3))
        }
        0x14 => {
            let (set, t1) = take_bool(tail)?;
            let (len_u16, mut t2) = take_u16_le(t1)?;
            let plen = len_u16 as usize;
            if plen > MAX_MODE_PARAMS {
                return Err(OpsWireError::TooManyModeParams(plen));
            }
            let mut params = Vec::new();
            let mut p_idx = 0usize;
            while p_idx < plen {
                let (p, next_t) = take_u16_le(t2)?;
                params.push(p);
                t2 = next_t;
                p_idx = p_idx.saturating_add(1);
            }
            Ok((ScreenOp::SetMode { params, set }, t2))
        }
        0x15 => Ok((ScreenOp::SaveCursor, tail)),
        0x16 => Ok((ScreenOp::RestoreCursor, tail)),
        0x17 => {
            let (top, t1) = take_u16_le(tail)?;
            let (bottom, t2) = take_u16_le(t1)?;
            Ok((ScreenOp::SetScrollRegion { top, bottom }, t2))
        }
        0x18 => {
            let (set, t) = take_bool(tail)?;
            Ok((ScreenOp::SetInsertMode(set), t))
        }
        0x19 => {
            let (set, t) = take_bool(tail)?;
            Ok((ScreenOp::SetNewlineMode(set), t))
        }
        0x1A => {
            let (g1, t1) = take_bool(tail)?;
            let (cs_tag, t2) = take_u8(t1)?;
            let charset = match cs_tag {
                0 => Charset::Ascii,
                1 => Charset::DecSpecial,
                other => return Err(OpsWireError::InvalidCharsetTag(other)),
            };
            Ok((ScreenOp::Designate { g1, charset }, t2))
        }
        0x1B => {
            let (g1, t) = take_bool(tail)?;
            Ok((ScreenOp::LockShift { g1 }, t))
        }
        0x1C => {
            let (left, t1) = take_u16_le(tail)?;
            let (right, t2) = take_u16_le(t1)?;
            Ok((ScreenOp::SetLeftRightMargins { left, right }, t2))
        }
        0x1D => {
            let (n, t) = take_u16_le(tail)?;
            Ok((ScreenOp::ScrollUp(n), t))
        }
        0x1E => {
            let (n, t) = take_u16_le(tail)?;
            Ok((ScreenOp::ScrollDown(n), t))
        }
        0x1F => Ok((ScreenOp::Reset, tail)),
        0x20 => {
            let (cols, t1) = take_u16_le(tail)?;
            let (rows, t2) = take_u16_le(t1)?;
            Ok((ScreenOp::Resize(cols, rows), t2))
        }
        0x21 => {
            let (fg, t1) = take_color(tail, "SetSgrRgb")?;
            let (fg_rgb, t2) = take_opt_rgb(t1)?;
            let (bg, t3) = take_color(t2, "SetSgrRgb")?;
            let (bg_rgb, t4) = take_opt_rgb(t3)?;
            let (attrs, t5) = take_u8(t4)?;
            Ok((
                ScreenOp::SetSgrRgb {
                    fg,
                    fg_rgb,
                    bg,
                    bg_rgb,
                    attrs,
                },
                t5,
            ))
        }
        0x22 => {
            let (code, t1) = take_u8(tail)?;
            let style =
                Underline::from_code(code).ok_or(OpsWireError::InvalidUnderlineStyle(code))?;
            let (ul, t2) = take_color(t1, "SetUnderline")?;
            let (ul_rgb, t3) = take_opt_rgb(t2)?;
            Ok((ScreenOp::SetUnderline { style, ul, ul_rgb }, t3))
        }
        other => Err(OpsWireError::UnknownOpTag(other)),
    }
}

fn decode_one_op(rest: &[u8]) -> Result<(ScreenOp, &[u8]), OpsWireError> {
    let (tag, tail) = take_u8(rest)?;
    if tag <= 0x11 {
        decode_op_low(tag, tail)
    } else {
        decode_op_high(tag, tail)
    }
}

/// Decode a binary [`ScreenOp`] batch frame produced by [`encode_ops`].
///
/// Hostile-input safe: rejects truncated frames, bad magic/version, surrogate
/// codepoints, out-of-range tags, oversized counts, and trailing bytes without
/// panicking or pre-allocating beyond the remaining input bytes.
pub fn decode_ops(bytes: &[u8]) -> Result<Vec<ScreenOp>, OpsWireError> {
    let &[m0, m1, m2, m3, ver, ref after_ver @ ..] = bytes else {
        return Err(OpsWireError::Truncated);
    };
    let magic = [m0, m1, m2, m3];
    if magic != OPS_WIRE_MAGIC {
        return Err(OpsWireError::BadMagic(magic));
    }
    if ver != OPS_WIRE_VERSION {
        return Err(OpsWireError::UnsupportedVersion(ver));
    }
    let (count_u32, mut rest) = take_u32_le(after_ver)?;
    let count = count_u32 as usize;
    if count > MAX_OPS_PER_BATCH {
        return Err(OpsWireError::TooManyOps(count));
    }
    // Grow lazily as elements are decoded so a tiny header with a huge declared
    // `count` never pre-allocates before failing with `Truncated`.
    let mut ops = Vec::new();
    let mut i = 0usize;
    while i < count {
        let (op, next) = decode_one_op(rest)?;
        ops.push(op);
        rest = next;
        i = i.saturating_add(1);
    }
    if !rest.is_empty() {
        return Err(OpsWireError::TrailingBytes(rest.len()));
    }
    Ok(ops)
}
