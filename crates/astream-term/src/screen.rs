//! A pure VT/ECMA-48 screen: the deterministic fold of recorded output.
//!
//! [`fold`] turns an ordered slice of [`Record`]s into a [`Screen`] with no
//! clock, no randomness, and no I/O, so the same records always yield a
//! byte-identical screen ([`Screen::serialize`]). That purity is the spine of
//! the astream-term replay guarantee.
//!
//! ### Scope
//!
//! A deliberately bounded but real VT subset: C0 controls (CR/LF/TAB/BS, and
//! VT/FF as line feeds), index (IND/NEL/RI), CSI cursor motion
//! (CUU/CUD/CUF/CUB/CNL/CPL/CHA/VPA/CUP), erase (ED/EL/ECH), insert and delete
//! (ICH/DCH/IL/DL), SGR (the 16- and 256-colour palettes plus 24-bit truecolour
//! in both the `;` and the `:` sub-parameter form; bold, reverse, italic, blink
//! (5 and 6 alike, as xterm), crossed-out and concealed, each with its reset;
//! the underline's style ([`Underline`]) and colour (below); faint is not
//! modelled), East Asian wide glyphs, zero-width Unicode combining marks (up to
//! [`MAX_COMBINING`] per cell), the alternate screen (`?1049`/`?47`/`?1047`),
//! cursor visibility (`?25`), save/restore cursor (DECSC/DECRC and `CSI s`/`u`,
//! one slot per screen buffer as in xterm), the DEC scrolling region (`DECSTBM`),
//! left/right margins (DECLRMM `?69` and DECSLRM `CSI Pl ; Pr s`),
//! origin mode (DECOM, `?6`), insert and newline mode (IRM and LNM, `CSI 4 h`,
//! `CSI 20 h`), scroll up and down
//! (SU/SD, `CSI S`/`CSI T`), RIS, and inline [`Record::Resize`]. The scroll
//! region is cross-validated against the production aterm engine (see
//! `term.fold.scroll-region`).
//!
//! Everything else in the byte stream is **consumed, never painted**, following
//! the ECMA-48 parser: OSC/DCS/APC/PM/SOS string sequences (window titles,
//! OSC-133 shell marks, image payloads) are swallowed up to their terminator
//! (`ESC \`, or BEL for OSC); escapes outside the subset (charset
//! designations other than the G0/G1 ones below, `ESC =`/`ESC >`) and CSI
//! sequences outside it (any with an intermediate byte, or a private marker
//! other than `?`) are skipped whole;
//! CMY/CMYK SGR (`38;3;…`, `38;4;…`, `38:3:…`, `38;3:…`) and truncated extended-colour
//! forms, on 38, 48 and 58 alike, are consumed *with* their values and leave the pen
//! unchanged; DEL, and C1 controls arriving
//! as UTF-8 (U+0080..U+009F), are ignored; malformed UTF-8 (overlong,
//! surrogate, truncated, a stray continuation or 8-bit byte) yields one U+FFFD
//! per maximal subpart (Unicode 3.9) — a control character never lands in a
//! cell. `ESC` anywhere begins a new escape, and a
//! C0 control executes inside an unfinished CSI.
//!
//! Simplifications, documented so they are never mistaken for fidelity — each is
//! deterministic:
//!
//! * **Deferred line wrap** is modelled with xterm's last-column semantics: after
//!   the last column is painted the cursor reports `col == cols`, and the next
//!   glyph wraps. CR/LF/BS/CUB/CUF/CUU/CUD/CUP resolve the pending wrap back
//!   onto the last column first — so BS after a full line lands on the
//!   second-to-last column (`abcde BS X` on 5 columns is `abcXe`) — and so do
//!   ED/EL 0-2, which then erase from that column: xterm's `ClearRight` clears
//!   from `cur_col` inclusive, the parked glyph, and every erase ends in
//!   `ResetWrap` (util.c). TAB leaves the wrap pending, `ED 3` touches neither
//!   the screen nor the wrap, and DECSC/DECRC round-trip it (a restored cursor
//!   wraps on its next glyph, as in aterm/xterm). Scrolling honours the
//!   `DECSTBM` region, and CUU/CUD (and CNL/CPL) stop at its margins as in
//!   xterm.
//! * **Every blank the fold makes honours background-colour-erase** (`bce`):
//!   `ED`/`EL`, a line scrolled in, and the alternate-screen clears fill with
//!   the current SGR background, as xterm's `ClearCells` / `ScrnClearLines`
//!   write the current colour pair, not a hardcoded default blank
//!   (reverse-video bce is out of scope). Cross-validated against aterm.
//! * **One alternate buffer, as in xterm**: it is allocated blank on first
//!   use and persists across switches and across RIS (xterm's `ReallyReset`
//!   clears it only if it is up), with its own DECSC slot, which RIS keeps too.
//!   `?47` only switches; `?1047` switches and clears it on the way out;
//!   `?1049` saves the cursor, switches and clears it on the way in (even when
//!   already up), and restores the cursor on the way out (even when not up).
//!   Each clear is xterm's `ClearScreen` (charproc.c `srm_ALTBUF`,
//!   `srm_OPT_ALTBUF`, `srm_OPT_ALTBUF_CURSOR`), which resets the pending
//!   wrap. The cursor is otherwise shared between the buffers and never moved
//!   by a switch.
//! * **24-bit truecolour SGR** (`38;2;r;g;b`, `48;2;r;g;b`, `38:2::r:g:b`,
//!   `38:2:cs:r:g:b`, `38:2:r:g:b`, the same groups after `38;`, and their `48` counterparts)
//!   resolves onto [`Cell::fg_rgb`] / [`Cell::bg_rgb`] (including `bce` erases and DECSC/DECRC),
//!   while palette/default SGR codes clear the corresponding RGB override. A channel
//!   past 255 is clamped to 255, as aterm clamps it; the standards leave it undefined,
//!   xterm's `parse_extended_colors` drops the colour and Ghostty truncates the value.
//!   ICH/DCH/IL/DL and ECH follow xterm's `InsertChar`/`DeleteChar`/`InsertLine`/
//!   `DeleteLine`/`ClearRight`: each resets a pending wrap where it acts,
//!   IL/DL act only on a cursor inside the scrolling region and move it to
//!   the left margin, and every vacated cell takes the bce blank.
//! * **The underline** has a style and a colour, on [`Cell::underline`] and
//!   [`Cell::ul`] / [`Cell::ul_rgb`], as kitty, VTE and aterm keep them (xterm
//!   has no colour: its `CASE_SGR` has no 58). 4 is a single underline and 21 a
//!   double one; `4:0` to `4:5` name none, single, double, curly, dotted and
//!   dashed, and `4:n` past 5 is a single one, as aterm draws it; 24 takes it
//!   off. 58 sets the colour in every spelling 38 takes (`58;5;n`, `58;2;r;g;b`,
//!   and the colon groups with and without a colour-space id, under the one
//!   rule of `Screen::sgr`), 59 takes it off, and SGR 0 resets both. A glyph
//!   takes both from the pen, whether or not it is underlined, as it takes the
//!   foreground; DECSC saves them with the rest of the pen, and a bce blank
//!   carries neither.
//! * **Left/right margins** follow xterm's `LEFT_RIGHT` flag. Under DECLRMM
//!   `CSI Pl ; Pr s` is DECSLRM, not a cursor save: a pair with `left <
//!   right` (a left of 0 is 1; a right absent, 0 or past the screen is the
//!   last column) sets the margins and homes the cursor, any other pair
//!   changes nothing; resetting DECLRMM puts the margins back to the full
//!   width and leaves the cursor, and RIS and a resize reset them too (a
//!   resize keeps the mode). Inside the margins they bound what xterm bounds:
//!   a glyph wraps at the right margin onto the left one (from left of the
//!   left margin too; from past the right one at the screen's edge), CR goes
//!   to the left margin (to column 0 from left of it, but always to the margin
//!   under origin mode), CUF and TAB stop at the right margin and CUB and BS
//!   at the left one unless the cursor is already beyond it, and IRM, ICH and
//!   DCH shift only up to the right margin. Every scroll (LF/IND/NEL at the
//!   bottom margin, RI at the top one, SU/SD, IL/DL and a wrap) moves only
//!   the rectangle between the margins, the cells beside it stay; an index
//!   or reverse index from a cursor outside the margins is a plain cursor
//!   motion that the scrolling region stops, and ICH, DCH, IL and DL there
//!   change nothing, a pending wrap included (xterm returns before
//!   `ResetWrap`). Under origin mode CUP/HVP and CHA count columns from the
//!   left margin and stop at the right one, VPA keeps the column so counted,
//!   and a restored cursor stops at the right margin. ED, EL and ECH ignore
//!   the margins, as in xterm. A wrap pending on a right margin short of the
//!   last column is its own state (DECSC saves it, DECRC puts it back
//!   wherever the column lands, as xterm's `do_wrap = sc->wrap_flag`; a TAB
//!   keeps it and, where the line runs on past that column, as after a DECLRMM
//!   reset, carries it to the next stop), reported by [`Screen::cursor`] one
//!   past that column as at the screen's edge and told apart by
//!   [`Screen::wrap_pending`]. One deliberate difference: a TAB from
//!   past the right margin runs to the screen's edge, where xterm pulls the
//!   cursor back onto the margin.
//! * **Origin mode** is xterm's `ORIGIN` flag read through `CursorSet`
//!   (cursor.c): setting or resetting `?6` homes the cursor (to the top margin
//!   when set), CUP/HVP and VPA count rows from the top margin and stop at the
//!   bottom one, CHA keeps the cursor's row counted from the top margin
//!   (`CursorRow`, never below 0), and DECSTBM homes to the top margin. A
//!   restored cursor is `CursorSet` from the restored flags: under origin mode
//!   its row stops at the bottom margin, not the top one. DECSC saves the
//!   flag (`DECSC_FLAGS` holds `ORIGIN`), a restore of a slot never saved
//!   clears it, and RIS clears it.
//! * **Insert mode** (IRM, the ANSI mode 4) shifts the rest of the line right
//!   before each glyph lands, as xterm's `WriteText` runs `InsertChar` first;
//!   what passes the last column is lost. **Newline mode** (LNM, ANSI mode
//!   20) makes LF, VT and FF return the carriage after the line feed, as
//!   xterm's `CASE_VMOT` does under `LINEFEED` (IND and NEL are untouched).
//!   DECSC saves neither mode; RIS clears both.
//! * **SU/SD** (`CSI n S`, `CSI n T`) scroll the region up or down `n` lines
//!   (xterm `xtermScroll`/`RevScroll`) wherever the cursor is, never move it,
//!   and keep a pending wrap; lines scrolled in take the bce blank. As in
//!   xterm's `CASE_TRACK_MOUSE`, only a lone nonzero (or defaulted) parameter
//!   is SD: `CSI 0 T` and a `T` with more than one parameter start highlight
//!   mouse tracking, which the fold consumes with no effect.
//! * **Character sets**: G0 and G1, each ASCII (`ESC ( B`, `ESC ) B`) or DEC
//!   Special Graphics (`ESC ( 0`, `ESC ) 0`, xterm's table in
//!   [`dec_special_graphic`]), with SO/SI mapping G1/G0 into GL; a byte in
//!   `0x20..=0x7E` paints the glyph GL's set gives it, and a decoded UTF-8
//!   character paints itself. DECSC saves the sets and the shift, a restore
//!   of a slot never saved resets them (xterm `resetCharsets`: ASCII in G0
//!   and G1, G0 in GL), and RIS resets them. G2/G3, single shifts, the
//!   national and 96-character sets are not modelled: their designations
//!   are consumed and change nothing.
//! * **East Asian wide characters** take two cells: a lead ([`Cell::width`] 2)
//!   holding the glyph and a spacer after it (width 0) that carries the same
//!   rendition (xterm's `HIDDEN_CHAR`, Ghostty's `spacer_tail`). A character is
//!   wide when Unicode's East Asian Width calls it Wide or Fullwidth and it
//!   takes a column at all, and a regional indicator is wide too
//!   ([`is_wide_char`]): [`char_display_width`] measures each codepoint alone,
//!   as aterm measures it, its zero-width set ([`is_combining_mark`]) included,
//!   so U+302A..U+302D, U+3099/U+309A and U+16FE4, marks that East Asian Width
//!   calls Wide, take no column (xterm's combining table, Ghostty, aterm). A
//!   wide glyph with one column left before the line end (the right margin, or
//!   the screen's edge from past it) wraps first, and the column it skips takes
//!   the bce blank, as aterm, Ghostty (`spacer_head`) and Alacritty
//!   (`LEADING_WIDE_CHAR_SPACER`) blank it; xterm's `dotext` alone leaves that
//!   cell as it was. A wrap pending after a wide glyph sits on its spacer. On a
//!   screen one column wide a wide glyph prints as a narrow space in the pen,
//!   as aterm and Ghostty print it (xterm's `dotext` gives up on the glyph,
//!   and on any narrow glyph it read with it in the same pass, then prints
//!   what follows).
//!   **No operation leaves half a wide glyph.** A write, an erase, ICH, DCH and
//!   IRM that would cut one (xterm repairs its `DamagedCells` with
//!   `ClearCells`, Ghostty calls `splitCellBoundary`) first blank both of its
//!   cells with the bce blank, one straddling the right margin included; a
//!   scroll between left/right margins first turns each glyph straddling a
//!   margin into two narrow blanks that keep their renditions and lose their
//!   marks (Ghostty's `rowWillBeShifted` with `clearGrapheme`; xterm leaves the
//!   halves torn); a narrowing resize that cuts a spacer off leaves its lead a
//!   default blank.
//! * **Grapheme clusters**: a zero-width code point ([`is_combining_mark`]: a
//!   combining mark, a variation selector, the zero-width (non-)joiner or
//!   another format control) attaches, up to [`MAX_COMBINING`] per cell, without
//!   advancing the cursor: to the glyph parked under a pending wrap, else to the
//!   one left of the cursor, a wide glyph's lead rather than its spacer. At
//!   column 0 or the left margin none precedes it, even on a row that continues
//!   the one above, so it takes the cursor's own cell (xterm's `char_was_written`
//!   cleared by CR or a motion, Alacritty), the lead if that cell is a spacer; a
//!   glyph printed up to the left margin from outside it still precedes the cursor
//!   until a motion comes ([`Screen::stepped_onto_margin`](Screen)).
//!   After a motion elsewhere the cell left of the cursor is still the one, as in
//!   aterm and Ghostty (xterm takes the cursor's own there). A glyph aterm joins to
//!   the cluster before it attaches the same way: a skin-tone modifier after a wide
//!   emoji modifier base, the second regional indicator of a flag, and a glyph
//!   other than ASCII after a `U+200D` that was the last thing printed.
//!   `U+FE0F` (VS16) widens a text-default emoji to two columns where the line
//!   has room for its spacer, and `U+FE0E` (VS15) narrows a wide glyph to one,
//!   leaving the cursor where it is. Neither resolves a pending wrap. aterm's differential oracle compares all of
//!   this cell by cell, marks included.
//! * DECSC/DECRC save and restore the cursor position (with a pending wrap)
//!   and the SGR rendition, as xterm's `CursorSave`/`CursorRestore` do; a
//!   restore from a slot never saved homes the cursor and resets the
//!   rendition (xterm's zeroed `SavedCursor`). Origin mode is saved with them
//!   (above), and so are the character sets (below). There is no
//!   scrollback, so `ED 3` (xterm's
//!   "erase saved lines", `do_erase_display` case 3) changes nothing here: the
//!   visible screen is not saved lines.
//! * **Resize clips/extends**; it does not reflow wrapped lines. A wrap pending at the edge
//!   (`col == cols`) keeps its next write, the column after the glyph: a widening leaves the
//!   cursor there and a narrowing leaves it waiting on the new edge. A cursor whose own cell a
//!   narrowing cuts off is clamped onto the last column with no wrap, as xterm clamps it, and a
//!   wrap pending at a right margin stays pending on its column, clipped to the new width
//!   (aterm's `resize-keeps-the-next-write` without reflow, which aterm's differential VT oracle
//!   holds both engines to). A DECSC slot stays where it was saved.
//! * Grid dimensions are clamped to `1..=`[`MAX_DIM`] so hostile input cannot
//!   trigger an unbounded allocation (panic-free, like `astream-wire`).

use crate::ops::ScreenOp;
use crate::record::Record;

/// Where [`Screen::serialize_into`] writes its encoding: a byte buffer, or a
/// hasher that consumes it without buffering.
pub(crate) trait ByteSink {
    fn extend_from_slice(&mut self, bytes: &[u8]);
}

impl ByteSink for Vec<u8> {
    fn extend_from_slice(&mut self, bytes: &[u8]) {
        Vec::extend_from_slice(self, bytes);
    }
}

/// Largest grid edge the fold will allocate, in cells. A guard against a hostile
/// [`Record::Resize`] requesting a multi-gigabyte grid.
pub const MAX_DIM: u16 = 1000;

/// An SGR colour: the terminal default, or a palette index (`0..=255`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Color {
    /// The terminal's default foreground/background.
    Default,
    /// A palette index: `0..=7` standard, `8..=15` bright, `16..=255` extended.
    Indexed(u8),
}

/// The style of a cell's underline (SGR 4, 21 and `4:0`..`4:5`; off with 24).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Underline {
    /// No underline (24, `4:0`, SGR 0).
    #[default]
    None,
    /// One straight line (4, `4:1`, and `4:n` past 5).
    Single,
    /// Two straight lines (21, `4:2`).
    Double,
    /// A wavy line (`4:3`), the squiggle editors draw under a diagnostic.
    Curly,
    /// A dotted line (`4:4`).
    Dotted,
    /// A dashed line (`4:5`).
    Dashed,
}

impl Underline {
    /// The style `4:n` names: `0` is none, `1` to `5` the styles in order, and
    /// any higher a single line, as aterm draws it.
    #[must_use]
    pub const fn from_sgr(n: u16) -> Underline {
        match n {
            0 => Underline::None,
            2 => Underline::Double,
            3 => Underline::Curly,
            4 => Underline::Dotted,
            5 => Underline::Dashed,
            _ => Underline::Single,
        }
    }

    /// The style's `4:n` number, `0..=5`.
    #[must_use]
    pub const fn code(self) -> u8 {
        match self {
            Underline::None => 0,
            Underline::Single => 1,
            Underline::Double => 2,
            Underline::Curly => 3,
            Underline::Dotted => 4,
            Underline::Dashed => 5,
        }
    }

    /// The style numbered `code` by [`Self::code`]; `None` for any other byte.
    #[must_use]
    pub const fn from_code(code: u8) -> Option<Underline> {
        match code {
            0 => Some(Underline::None),
            1 => Some(Underline::Single),
            2 => Some(Underline::Double),
            3 => Some(Underline::Curly),
            4 => Some(Underline::Dotted),
            5 => Some(Underline::Dashed),
            _ => None,
        }
    }
}

/// The attribute bit the encodings ([`Screen::serialize`], [`encode_cell_bytes`],
/// [`crate::ops::ScreenOp::SetSgr`]) set for an underlined cell or pen, whatever its
/// style: bit 1, where the fold kept its one underline bit before the underline had a
/// style, so a screen or op stream that has no other underline keeps its bytes. A
/// style other than single, and a colour, ride in extensions of their own.
pub const WIRE_UNDERLINE: u8 = 1 << 1;

/// Cell attribute bits (a bitset in [`Cell::attrs`]). Bit 1 is no attribute: the
/// underline is [`Cell::underline`].
pub mod attr {
    /// Bold / increased intensity.
    pub const BOLD: u8 = 1 << 0;
    /// Reverse video (swap fg/bg).
    pub const REVERSE: u8 = 1 << 2;
    /// Faint / dim — used to render an unconfirmed speculative echo.
    pub const FAINT: u8 = 1 << 3;
    /// Italic (SGR 3, off with 23).
    pub const ITALIC: u8 = 1 << 4;
    /// Blinking, slow or rapid alike (SGR 5 and 6, off with 25).
    pub const BLINK: u8 = 1 << 5;
    /// Crossed out (SGR 9, off with 29).
    pub const STRIKE: u8 = 1 << 6;
    /// Concealed, xterm's `INVISIBLE` (SGR 8, off with 28).
    pub const CONCEAL: u8 = 1 << 7;
}

/// Maximum number of zero-width Unicode combining marks stored inline per [`Cell`].
pub const MAX_COMBINING: usize = 16;

/// `Emoji=Yes` ranges with `Emoji_Presentation=No` (Unicode 16.0 `Text_Default_Emoji`,
/// matching `aterm-grapheme::emoji_presentation::TEXT_DEFAULT_EMOJI`): sorted, disjoint
/// inclusive `(lo, hi)` codepoint ranges widened from 1 to 2 columns by `U+FE0F` (VS16).
const TEXT_DEFAULT_EMOJI_RANGES: [(u32, u32); 119] = [
    (0x0023, 0x0023),
    (0x002A, 0x002A),
    (0x0030, 0x0039),
    (0x00A9, 0x00A9),
    (0x00AE, 0x00AE),
    (0x203C, 0x203C),
    (0x2049, 0x2049),
    (0x2122, 0x2122),
    (0x2139, 0x2139),
    (0x2194, 0x2199),
    (0x21A9, 0x21AA),
    (0x2328, 0x2328),
    (0x23CF, 0x23CF),
    (0x23ED, 0x23EF),
    (0x23F1, 0x23F2),
    (0x23F8, 0x23FA),
    (0x24C2, 0x24C2),
    (0x25AA, 0x25AB),
    (0x25B6, 0x25B6),
    (0x25C0, 0x25C0),
    (0x25FB, 0x25FC),
    (0x2600, 0x2604),
    (0x260E, 0x260E),
    (0x2611, 0x2611),
    (0x2618, 0x2618),
    (0x261D, 0x261D),
    (0x2620, 0x2620),
    (0x2622, 0x2623),
    (0x2626, 0x2626),
    (0x262A, 0x262A),
    (0x262E, 0x262F),
    (0x2638, 0x263A),
    (0x2640, 0x2640),
    (0x2642, 0x2642),
    (0x265F, 0x2660),
    (0x2663, 0x2663),
    (0x2665, 0x2666),
    (0x2668, 0x2668),
    (0x267B, 0x267B),
    (0x267E, 0x267E),
    (0x2692, 0x2692),
    (0x2694, 0x2697),
    (0x2699, 0x2699),
    (0x269B, 0x269C),
    (0x26A0, 0x26A0),
    (0x26A7, 0x26A7),
    (0x26B0, 0x26B1),
    (0x26C8, 0x26C8),
    (0x26CF, 0x26CF),
    (0x26D1, 0x26D1),
    (0x26D3, 0x26D3),
    (0x26E9, 0x26E9),
    (0x26F0, 0x26F1),
    (0x26F4, 0x26F4),
    (0x26F7, 0x26F9),
    (0x2702, 0x2702),
    (0x2708, 0x2709),
    (0x270C, 0x270D),
    (0x270F, 0x270F),
    (0x2712, 0x2712),
    (0x2714, 0x2714),
    (0x2716, 0x2716),
    (0x271D, 0x271D),
    (0x2721, 0x2721),
    (0x2733, 0x2734),
    (0x2744, 0x2744),
    (0x2747, 0x2747),
    (0x2763, 0x2764),
    (0x27A1, 0x27A1),
    (0x2934, 0x2935),
    (0x2B05, 0x2B07),
    (0x3030, 0x3030),
    (0x303D, 0x303D),
    (0x3297, 0x3297),
    (0x3299, 0x3299),
    (0x1F170, 0x1F171),
    (0x1F17E, 0x1F17F),
    (0x1F202, 0x1F202),
    (0x1F237, 0x1F237),
    (0x1F321, 0x1F321),
    (0x1F324, 0x1F32C),
    (0x1F336, 0x1F336),
    (0x1F37D, 0x1F37D),
    (0x1F396, 0x1F397),
    (0x1F399, 0x1F39B),
    (0x1F39E, 0x1F39F),
    (0x1F3CB, 0x1F3CE),
    (0x1F3D4, 0x1F3DF),
    (0x1F3F3, 0x1F3F3),
    (0x1F3F5, 0x1F3F5),
    (0x1F3F7, 0x1F3F7),
    (0x1F43F, 0x1F43F),
    (0x1F441, 0x1F441),
    (0x1F4FD, 0x1F4FD),
    (0x1F549, 0x1F54A),
    (0x1F56F, 0x1F570),
    (0x1F573, 0x1F579),
    (0x1F587, 0x1F587),
    (0x1F58A, 0x1F58D),
    (0x1F590, 0x1F590),
    (0x1F5A5, 0x1F5A5),
    (0x1F5A8, 0x1F5A8),
    (0x1F5B1, 0x1F5B2),
    (0x1F5BC, 0x1F5BC),
    (0x1F5C2, 0x1F5C4),
    (0x1F5D1, 0x1F5D3),
    (0x1F5DC, 0x1F5DE),
    (0x1F5E1, 0x1F5E1),
    (0x1F5E3, 0x1F5E3),
    (0x1F5E8, 0x1F5E8),
    (0x1F5EF, 0x1F5EF),
    (0x1F5F3, 0x1F5F3),
    (0x1F5FA, 0x1F5FA),
    (0x1F6CB, 0x1F6CB),
    (0x1F6CD, 0x1F6CF),
    (0x1F6E0, 0x1F6E5),
    (0x1F6E9, 0x1F6E9),
    (0x1F6F0, 0x1F6F0),
    (0x1F6F3, 0x1F6F3),
];

/// Returns `true` when `U+FE0F` (VS16) widens narrow base glyph `ch` to two columns
/// (`Emoji=Yes` & `Emoji_Presentation=No`, matching `aterm-grapheme::is_vs16_emoji_capable`).
#[must_use]
pub const fn is_vs16_emoji_capable(ch: char) -> bool {
    let u = ch as u32;
    let mut lo = 0usize;
    let mut hi = TEXT_DEFAULT_EMOJI_RANGES.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if mid >= TEXT_DEFAULT_EMOJI_RANGES.len() {
            return false;
        }
        let (start, end) = TEXT_DEFAULT_EMOJI_RANGES[mid];
        if u < start {
            hi = mid;
        } else if u > end {
            lo = mid + 1;
        } else {
            return true;
        }
    }
    false
}

/// The code points that take no column, as aterm's `char_width` measures them
/// (Unicode 16.0.0): the nonspacing and enclosing marks, the format controls
/// but the soft hyphen (the zero-width space and (non-)joiner, the bidi
/// controls, the word joiner, the byte-order mark among them), the conjoining
/// Hangul vowels and finals, the variation selectors and the tag plane.
/// Ascending and disjoint, adjacent ranges merged; aterm's differential VT
/// oracle holds the two measures equal code point by code point.
const ZERO_WIDTH_RANGES: [(u32, u32); 368] = [
    (0x0300, 0x036F),
    (0x0483, 0x0489),
    (0x0591, 0x05BD),
    (0x05BF, 0x05BF),
    (0x05C1, 0x05C2),
    (0x05C4, 0x05C5),
    (0x05C7, 0x05C7),
    (0x0600, 0x0605),
    (0x0610, 0x061A),
    (0x061C, 0x061C),
    (0x064B, 0x065F),
    (0x0670, 0x0670),
    (0x06D6, 0x06DD),
    (0x06DF, 0x06E4),
    (0x06E7, 0x06E8),
    (0x06EA, 0x06ED),
    (0x070F, 0x070F),
    (0x0711, 0x0711),
    (0x0730, 0x074A),
    (0x07A6, 0x07B0),
    (0x07EB, 0x07F3),
    (0x07FD, 0x07FD),
    (0x0816, 0x0819),
    (0x081B, 0x0823),
    (0x0825, 0x0827),
    (0x0829, 0x082D),
    (0x0859, 0x085B),
    (0x0890, 0x0891),
    (0x0897, 0x089F),
    (0x08CA, 0x0902),
    (0x093A, 0x093A),
    (0x093C, 0x093C),
    (0x0941, 0x0948),
    (0x094D, 0x094D),
    (0x0951, 0x0957),
    (0x0962, 0x0963),
    (0x0981, 0x0981),
    (0x09BC, 0x09BC),
    (0x09C1, 0x09C4),
    (0x09CD, 0x09CD),
    (0x09E2, 0x09E3),
    (0x09FE, 0x09FE),
    (0x0A01, 0x0A02),
    (0x0A3C, 0x0A3C),
    (0x0A41, 0x0A42),
    (0x0A47, 0x0A48),
    (0x0A4B, 0x0A4D),
    (0x0A51, 0x0A51),
    (0x0A70, 0x0A71),
    (0x0A75, 0x0A75),
    (0x0A81, 0x0A82),
    (0x0ABC, 0x0ABC),
    (0x0AC1, 0x0AC5),
    (0x0AC7, 0x0AC8),
    (0x0ACD, 0x0ACD),
    (0x0AE2, 0x0AE3),
    (0x0AFA, 0x0AFF),
    (0x0B01, 0x0B01),
    (0x0B3C, 0x0B3C),
    (0x0B3F, 0x0B3F),
    (0x0B41, 0x0B44),
    (0x0B4D, 0x0B4D),
    (0x0B55, 0x0B56),
    (0x0B62, 0x0B63),
    (0x0B82, 0x0B82),
    (0x0BC0, 0x0BC0),
    (0x0BCD, 0x0BCD),
    (0x0C00, 0x0C00),
    (0x0C04, 0x0C04),
    (0x0C3C, 0x0C3C),
    (0x0C3E, 0x0C40),
    (0x0C46, 0x0C48),
    (0x0C4A, 0x0C4D),
    (0x0C55, 0x0C56),
    (0x0C62, 0x0C63),
    (0x0C81, 0x0C81),
    (0x0CBC, 0x0CBC),
    (0x0CBF, 0x0CBF),
    (0x0CC6, 0x0CC6),
    (0x0CCC, 0x0CCD),
    (0x0CE2, 0x0CE3),
    (0x0D00, 0x0D01),
    (0x0D3B, 0x0D3C),
    (0x0D41, 0x0D44),
    (0x0D4D, 0x0D4D),
    (0x0D62, 0x0D63),
    (0x0D81, 0x0D81),
    (0x0DCA, 0x0DCA),
    (0x0DD2, 0x0DD4),
    (0x0DD6, 0x0DD6),
    (0x0E31, 0x0E31),
    (0x0E34, 0x0E3A),
    (0x0E47, 0x0E4E),
    (0x0EB1, 0x0EB1),
    (0x0EB4, 0x0EBC),
    (0x0EC8, 0x0ECE),
    (0x0F18, 0x0F19),
    (0x0F35, 0x0F35),
    (0x0F37, 0x0F37),
    (0x0F39, 0x0F39),
    (0x0F71, 0x0F7E),
    (0x0F80, 0x0F84),
    (0x0F86, 0x0F87),
    (0x0F8D, 0x0F97),
    (0x0F99, 0x0FBC),
    (0x0FC6, 0x0FC6),
    (0x102D, 0x1030),
    (0x1032, 0x1037),
    (0x1039, 0x103A),
    (0x103D, 0x103E),
    (0x1058, 0x1059),
    (0x105E, 0x1060),
    (0x1071, 0x1074),
    (0x1082, 0x1082),
    (0x1085, 0x1086),
    (0x108D, 0x108D),
    (0x109D, 0x109D),
    (0x1160, 0x11FF),
    (0x135D, 0x135F),
    (0x1712, 0x1714),
    (0x1732, 0x1733),
    (0x1752, 0x1753),
    (0x1772, 0x1773),
    (0x17B4, 0x17B5),
    (0x17B7, 0x17BD),
    (0x17C6, 0x17C6),
    (0x17C9, 0x17D3),
    (0x17DD, 0x17DD),
    (0x180B, 0x180F),
    (0x1885, 0x1886),
    (0x18A9, 0x18A9),
    (0x1920, 0x1922),
    (0x1927, 0x1928),
    (0x1932, 0x1932),
    (0x1939, 0x193B),
    (0x1A17, 0x1A18),
    (0x1A1B, 0x1A1B),
    (0x1A56, 0x1A56),
    (0x1A58, 0x1A5E),
    (0x1A60, 0x1A60),
    (0x1A62, 0x1A62),
    (0x1A65, 0x1A6C),
    (0x1A73, 0x1A7C),
    (0x1A7F, 0x1A7F),
    (0x1AB0, 0x1ACE),
    (0x1B00, 0x1B03),
    (0x1B34, 0x1B34),
    (0x1B36, 0x1B3A),
    (0x1B3C, 0x1B3C),
    (0x1B42, 0x1B42),
    (0x1B6B, 0x1B73),
    (0x1B80, 0x1B81),
    (0x1BA2, 0x1BA5),
    (0x1BA8, 0x1BA9),
    (0x1BAB, 0x1BAD),
    (0x1BE6, 0x1BE6),
    (0x1BE8, 0x1BE9),
    (0x1BED, 0x1BED),
    (0x1BEF, 0x1BF1),
    (0x1C2C, 0x1C33),
    (0x1C36, 0x1C37),
    (0x1CD0, 0x1CD2),
    (0x1CD4, 0x1CE0),
    (0x1CE2, 0x1CE8),
    (0x1CED, 0x1CED),
    (0x1CF4, 0x1CF4),
    (0x1CF8, 0x1CF9),
    (0x1DC0, 0x1DFF),
    (0x200B, 0x200F),
    (0x202A, 0x202E),
    (0x2060, 0x2064),
    (0x2066, 0x206F),
    (0x20D0, 0x20F0),
    (0x2CEF, 0x2CF1),
    (0x2D7F, 0x2D7F),
    (0x2DE0, 0x2DFF),
    (0x302A, 0x302D),
    (0x3099, 0x309A),
    (0xA66F, 0xA672),
    (0xA674, 0xA67D),
    (0xA69E, 0xA69F),
    (0xA6F0, 0xA6F1),
    (0xA802, 0xA802),
    (0xA806, 0xA806),
    (0xA80B, 0xA80B),
    (0xA825, 0xA826),
    (0xA82C, 0xA82C),
    (0xA8C4, 0xA8C5),
    (0xA8E0, 0xA8F1),
    (0xA8FF, 0xA8FF),
    (0xA926, 0xA92D),
    (0xA947, 0xA951),
    (0xA980, 0xA982),
    (0xA9B3, 0xA9B3),
    (0xA9B6, 0xA9B9),
    (0xA9BC, 0xA9BD),
    (0xA9E5, 0xA9E5),
    (0xAA29, 0xAA2E),
    (0xAA31, 0xAA32),
    (0xAA35, 0xAA36),
    (0xAA43, 0xAA43),
    (0xAA4C, 0xAA4C),
    (0xAA7C, 0xAA7C),
    (0xAAB0, 0xAAB0),
    (0xAAB2, 0xAAB4),
    (0xAAB7, 0xAAB8),
    (0xAABE, 0xAABF),
    (0xAAC1, 0xAAC1),
    (0xAAEC, 0xAAED),
    (0xAAF6, 0xAAF6),
    (0xABE5, 0xABE5),
    (0xABE8, 0xABE8),
    (0xABED, 0xABED),
    (0xD7B0, 0xD7C6),
    (0xD7CB, 0xD7FB),
    (0xFB1E, 0xFB1E),
    (0xFE00, 0xFE0F),
    (0xFE20, 0xFE2F),
    (0xFEFF, 0xFEFF),
    (0xFFF9, 0xFFFB),
    (0x101FD, 0x101FD),
    (0x102E0, 0x102E0),
    (0x10376, 0x1037A),
    (0x10A01, 0x10A03),
    (0x10A05, 0x10A06),
    (0x10A0C, 0x10A0F),
    (0x10A38, 0x10A3A),
    (0x10A3F, 0x10A3F),
    (0x10AE5, 0x10AE6),
    (0x10D24, 0x10D27),
    (0x10D69, 0x10D6D),
    (0x10EAB, 0x10EAC),
    (0x10EFC, 0x10EFF),
    (0x10F46, 0x10F50),
    (0x10F82, 0x10F85),
    (0x11001, 0x11001),
    (0x11038, 0x11046),
    (0x11070, 0x11070),
    (0x11073, 0x11074),
    (0x1107F, 0x11081),
    (0x110B3, 0x110B6),
    (0x110B9, 0x110BA),
    (0x110BD, 0x110BD),
    (0x110C2, 0x110C2),
    (0x110CD, 0x110CD),
    (0x11100, 0x11102),
    (0x11127, 0x1112B),
    (0x1112D, 0x11134),
    (0x11173, 0x11173),
    (0x11180, 0x11181),
    (0x111B6, 0x111BE),
    (0x111C9, 0x111CC),
    (0x111CF, 0x111CF),
    (0x1122F, 0x11231),
    (0x11234, 0x11234),
    (0x11236, 0x11237),
    (0x1123E, 0x1123E),
    (0x11241, 0x11241),
    (0x112DF, 0x112DF),
    (0x112E3, 0x112EA),
    (0x11300, 0x11301),
    (0x1133B, 0x1133C),
    (0x11340, 0x11340),
    (0x11366, 0x1136C),
    (0x11370, 0x11374),
    (0x113BB, 0x113C0),
    (0x113CE, 0x113CE),
    (0x113D0, 0x113D0),
    (0x113D2, 0x113D2),
    (0x113E1, 0x113E2),
    (0x11438, 0x1143F),
    (0x11442, 0x11444),
    (0x11446, 0x11446),
    (0x1145E, 0x1145E),
    (0x114B3, 0x114B8),
    (0x114BA, 0x114BA),
    (0x114BF, 0x114C0),
    (0x114C2, 0x114C3),
    (0x115B2, 0x115B5),
    (0x115BC, 0x115BD),
    (0x115BF, 0x115C0),
    (0x115DC, 0x115DD),
    (0x11633, 0x1163A),
    (0x1163D, 0x1163D),
    (0x1163F, 0x11640),
    (0x116AB, 0x116AB),
    (0x116AD, 0x116AD),
    (0x116B0, 0x116B5),
    (0x116B7, 0x116B7),
    (0x1171D, 0x1171D),
    (0x1171F, 0x1171F),
    (0x11722, 0x11725),
    (0x11727, 0x1172B),
    (0x1182F, 0x11837),
    (0x11839, 0x1183A),
    (0x1193B, 0x1193C),
    (0x1193E, 0x1193E),
    (0x11943, 0x11943),
    (0x119D4, 0x119D7),
    (0x119DA, 0x119DB),
    (0x119E0, 0x119E0),
    (0x11A01, 0x11A0A),
    (0x11A33, 0x11A38),
    (0x11A3B, 0x11A3E),
    (0x11A47, 0x11A47),
    (0x11A51, 0x11A56),
    (0x11A59, 0x11A5B),
    (0x11A8A, 0x11A96),
    (0x11A98, 0x11A99),
    (0x11C30, 0x11C36),
    (0x11C38, 0x11C3D),
    (0x11C3F, 0x11C3F),
    (0x11C92, 0x11CA7),
    (0x11CAA, 0x11CB0),
    (0x11CB2, 0x11CB3),
    (0x11CB5, 0x11CB6),
    (0x11D31, 0x11D36),
    (0x11D3A, 0x11D3A),
    (0x11D3C, 0x11D3D),
    (0x11D3F, 0x11D45),
    (0x11D47, 0x11D47),
    (0x11D90, 0x11D91),
    (0x11D95, 0x11D95),
    (0x11D97, 0x11D97),
    (0x11EF3, 0x11EF4),
    (0x11F00, 0x11F01),
    (0x11F36, 0x11F3A),
    (0x11F40, 0x11F40),
    (0x11F42, 0x11F42),
    (0x11F5A, 0x11F5A),
    (0x13430, 0x13440),
    (0x13447, 0x13455),
    (0x1611E, 0x16129),
    (0x1612D, 0x1612F),
    (0x16AF0, 0x16AF4),
    (0x16B30, 0x16B36),
    (0x16F4F, 0x16F4F),
    (0x16F8F, 0x16F92),
    (0x16FE4, 0x16FE4),
    (0x1BC9D, 0x1BC9E),
    (0x1BCA0, 0x1BCA3),
    (0x1CF00, 0x1CF2D),
    (0x1CF30, 0x1CF46),
    (0x1D167, 0x1D169),
    (0x1D173, 0x1D182),
    (0x1D185, 0x1D18B),
    (0x1D1AA, 0x1D1AD),
    (0x1D242, 0x1D244),
    (0x1DA00, 0x1DA36),
    (0x1DA3B, 0x1DA6C),
    (0x1DA75, 0x1DA75),
    (0x1DA84, 0x1DA84),
    (0x1DA9B, 0x1DA9F),
    (0x1DAA1, 0x1DAAF),
    (0x1E000, 0x1E006),
    (0x1E008, 0x1E018),
    (0x1E01B, 0x1E021),
    (0x1E023, 0x1E024),
    (0x1E026, 0x1E02A),
    (0x1E08F, 0x1E08F),
    (0x1E130, 0x1E136),
    (0x1E2AE, 0x1E2AE),
    (0x1E2EC, 0x1E2EF),
    (0x1E4EC, 0x1E4EF),
    (0x1E5EE, 0x1E5EF),
    (0x1E8D0, 0x1E8D6),
    (0x1E944, 0x1E94A),
    (0xE0000, 0xE0FFF),
];

/// Whether `u` lies in one of `ranges`, which ascend and are disjoint.
const fn in_ranges(u: u32, ranges: &[(u32, u32)]) -> bool {
    let mut lo = 0usize;
    let mut hi = ranges.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        // Never taken (`lo <= mid < hi <= len`): it states at the index what
        // the verified lane cannot carry through the loop for a long table.
        if mid >= ranges.len() {
            return false;
        }
        let (first, last) = ranges[mid];
        if u < first {
            hi = mid;
        } else if u > last {
            lo = mid + 1;
        } else {
            return true;
        }
    }
    false
}

/// Returns `true` when `ch` takes no column (`ZERO_WIDTH_RANGES`: a combining
/// or enclosing mark, a variation selector, the zero-width (non-)joiner
/// `\u{200C}`/`\u{200D}`, another format control, a conjoining Hangul vowel or
/// final, a tag): it attaches to the active base cell without advancing the
/// cursor.
#[must_use]
pub const fn is_combining_mark(ch: char) -> bool {
    let u = ch as u32;
    // The first zero-width code point is U+0300.
    u >= 0x0300 && in_ranges(u, &ZERO_WIDTH_RANGES)
}

/// The East Asian Width Wide (W) and Fullwidth (F) ranges of Unicode 16.0.0
/// (`EastAsianWidth.txt`), adjacent ranges merged, ascending. Plane 3 stops at
/// the end of CJK Extension H (U+323AF), where aterm and xterm stop, though
/// East Asian Width defaults the unassigned rest of the plane to Wide.
const WIDE_RANGES: [(u32, u32); 122] = [
    (0x1100, 0x115F),
    (0x231A, 0x231B),
    (0x2329, 0x232A),
    (0x23E9, 0x23EC),
    (0x23F0, 0x23F0),
    (0x23F3, 0x23F3),
    (0x25FD, 0x25FE),
    (0x2614, 0x2615),
    (0x2630, 0x2637),
    (0x2648, 0x2653),
    (0x267F, 0x267F),
    (0x268A, 0x268F),
    (0x2693, 0x2693),
    (0x26A1, 0x26A1),
    (0x26AA, 0x26AB),
    (0x26BD, 0x26BE),
    (0x26C4, 0x26C5),
    (0x26CE, 0x26CE),
    (0x26D4, 0x26D4),
    (0x26EA, 0x26EA),
    (0x26F2, 0x26F3),
    (0x26F5, 0x26F5),
    (0x26FA, 0x26FA),
    (0x26FD, 0x26FD),
    (0x2705, 0x2705),
    (0x270A, 0x270B),
    (0x2728, 0x2728),
    (0x274C, 0x274C),
    (0x274E, 0x274E),
    (0x2753, 0x2755),
    (0x2757, 0x2757),
    (0x2795, 0x2797),
    (0x27B0, 0x27B0),
    (0x27BF, 0x27BF),
    (0x2B1B, 0x2B1C),
    (0x2B50, 0x2B50),
    (0x2B55, 0x2B55),
    (0x2E80, 0x2E99),
    (0x2E9B, 0x2EF3),
    (0x2F00, 0x2FD5),
    (0x2FF0, 0x303E),
    (0x3041, 0x3096),
    (0x3099, 0x30FF),
    (0x3105, 0x312F),
    (0x3131, 0x318E),
    (0x3190, 0x31E5),
    (0x31EF, 0x321E),
    (0x3220, 0x3247),
    (0x3250, 0xA48C),
    (0xA490, 0xA4C6),
    (0xA960, 0xA97C),
    (0xAC00, 0xD7A3),
    (0xF900, 0xFAFF),
    (0xFE10, 0xFE19),
    (0xFE30, 0xFE52),
    (0xFE54, 0xFE66),
    (0xFE68, 0xFE6B),
    (0xFF01, 0xFF60),
    (0xFFE0, 0xFFE6),
    (0x16FE0, 0x16FE4),
    (0x16FF0, 0x16FF1),
    (0x17000, 0x187F7),
    (0x18800, 0x18CD5),
    (0x18CFF, 0x18D08),
    (0x1AFF0, 0x1AFF3),
    (0x1AFF5, 0x1AFFB),
    (0x1AFFD, 0x1AFFE),
    (0x1B000, 0x1B122),
    (0x1B132, 0x1B132),
    (0x1B150, 0x1B152),
    (0x1B155, 0x1B155),
    (0x1B164, 0x1B167),
    (0x1B170, 0x1B2FB),
    (0x1D300, 0x1D356),
    (0x1D360, 0x1D376),
    (0x1F004, 0x1F004),
    (0x1F0CF, 0x1F0CF),
    (0x1F18E, 0x1F18E),
    (0x1F191, 0x1F19A),
    (0x1F200, 0x1F202),
    (0x1F210, 0x1F23B),
    (0x1F240, 0x1F248),
    (0x1F250, 0x1F251),
    (0x1F260, 0x1F265),
    (0x1F300, 0x1F320),
    (0x1F32D, 0x1F335),
    (0x1F337, 0x1F37C),
    (0x1F37E, 0x1F393),
    (0x1F3A0, 0x1F3CA),
    (0x1F3CF, 0x1F3D3),
    (0x1F3E0, 0x1F3F0),
    (0x1F3F4, 0x1F3F4),
    (0x1F3F8, 0x1F43E),
    (0x1F440, 0x1F440),
    (0x1F442, 0x1F4FC),
    (0x1F4FF, 0x1F53D),
    (0x1F54B, 0x1F54E),
    (0x1F550, 0x1F567),
    (0x1F57A, 0x1F57A),
    (0x1F595, 0x1F596),
    (0x1F5A4, 0x1F5A4),
    (0x1F5FB, 0x1F64F),
    (0x1F680, 0x1F6C5),
    (0x1F6CC, 0x1F6CC),
    (0x1F6D0, 0x1F6D2),
    (0x1F6D5, 0x1F6D7),
    (0x1F6DC, 0x1F6DF),
    (0x1F6EB, 0x1F6EC),
    (0x1F6F4, 0x1F6FC),
    (0x1F7E0, 0x1F7EB),
    (0x1F7F0, 0x1F7F0),
    (0x1F90C, 0x1F93A),
    (0x1F93C, 0x1F945),
    (0x1F947, 0x1F9FF),
    (0x1FA70, 0x1FA7C),
    (0x1FA80, 0x1FA89),
    (0x1FA8F, 0x1FAC6),
    (0x1FACE, 0x1FADC),
    (0x1FADF, 0x1FAE9),
    (0x1FAF0, 0x1FAF8),
    (0x20000, 0x2FFFD),
    (0x30000, 0x323AF),
];

/// Whether `ch` is a regional indicator (U+1F1E6..U+1F1FF), one half of a flag.
const fn is_regional_indicator(ch: char) -> bool {
    let u = ch as u32;
    u >= 0x1F1E6 && u <= 0x1F1FF
}

/// Whether `ch` is an emoji skin-tone modifier (U+1F3FB..U+1F3FF, UTS #51).
const fn is_emoji_modifier(ch: char) -> bool {
    let u = ch as u32;
    u >= 0x1F3FB && u <= 0x1F3FF
}

/// `Emoji_Modifier_Base=Yes` of Unicode 16.0.0 (`emoji-data.txt`), adjacent
/// ranges merged, ascending: the glyphs a skin-tone modifier joins (UTS #51).
const EMOJI_MODIFIER_BASE_RANGES: [(u32, u32); 40] = [
    (0x261D, 0x261D),
    (0x26F9, 0x26F9),
    (0x270A, 0x270D),
    (0x1F385, 0x1F385),
    (0x1F3C2, 0x1F3C4),
    (0x1F3C7, 0x1F3C7),
    (0x1F3CA, 0x1F3CC),
    (0x1F442, 0x1F443),
    (0x1F446, 0x1F450),
    (0x1F466, 0x1F478),
    (0x1F47C, 0x1F47C),
    (0x1F481, 0x1F483),
    (0x1F485, 0x1F487),
    (0x1F48F, 0x1F48F),
    (0x1F491, 0x1F491),
    (0x1F4AA, 0x1F4AA),
    (0x1F574, 0x1F575),
    (0x1F57A, 0x1F57A),
    (0x1F590, 0x1F590),
    (0x1F595, 0x1F596),
    (0x1F645, 0x1F647),
    (0x1F64B, 0x1F64F),
    (0x1F6A3, 0x1F6A3),
    (0x1F6B4, 0x1F6B6),
    (0x1F6C0, 0x1F6C0),
    (0x1F6CC, 0x1F6CC),
    (0x1F90C, 0x1F90C),
    (0x1F90F, 0x1F90F),
    (0x1F918, 0x1F91F),
    (0x1F926, 0x1F926),
    (0x1F930, 0x1F939),
    (0x1F93C, 0x1F93E),
    (0x1F977, 0x1F977),
    (0x1F9B5, 0x1F9B6),
    (0x1F9B8, 0x1F9B9),
    (0x1F9BB, 0x1F9BB),
    (0x1F9CD, 0x1F9CF),
    (0x1F9D1, 0x1F9DD),
    (0x1FAC3, 0x1FAC5),
    (0x1FAF0, 0x1FAF8),
];

/// Whether `ch` is an emoji a skin-tone modifier joins ([`EMOJI_MODIFIER_BASE_RANGES`]).
const fn is_emoji_modifier_base(ch: char) -> bool {
    in_ranges(ch as u32, &EMOJI_MODIFIER_BASE_RANGES)
}

/// Returns `true` when `ch` occupies two grid columns, as aterm draws it: an
/// East Asian Wide or Fullwidth character (`WIDE_RANGES`, the `wcwidth == 2`
/// of UAX #11) that takes a column at all ([`is_combining_mark`] wins, so
/// U+302A..U+302D, U+3099/U+309A and U+16FE4, marks that East Asian Width
/// calls Wide, take none, as in xterm's `wcwidth`), or a regional indicator,
/// which aterm draws two columns wide though East Asian Width leaves it
/// Neutral (xterm draws it one).
#[must_use]
pub const fn is_wide_char(ch: char) -> bool {
    let u = ch as u32;
    // Nothing below the first range is wide.
    if u < 0x1100 || is_combining_mark(ch) {
        return false;
    }
    is_regional_indicator(ch) || in_ranges(u, &WIDE_RANGES)
}

/// Terminal column width of `ch`, each codepoint measured alone as aterm
/// measures it: `0` for a zero-width code point ([`is_combining_mark`]), `2`
/// for a wide one ([`is_wide_char`]), and `1` otherwise.
#[must_use]
pub const fn char_display_width(ch: char) -> u8 {
    if is_combining_mark(ch) {
        0
    } else if is_wide_char(ch) {
        2
    } else {
        1
    }
}

/// One character cell of the grid.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Cell {
    /// The base displayed character (`' '` for a blank or wide continuation cell).
    pub ch: char,
    /// Foreground palette/default colour (`Color::Default` when `fg_rgb` is `Some`).
    pub fg: Color,
    /// Background palette/default colour (`Color::Default` when `bg_rgb` is `Some`).
    pub bg: Color,
    /// Resolved 24-bit foreground `(r, g, b)` when painted under truecolour SGR.
    pub fg_rgb: Option<(u8, u8, u8)>,
    /// Resolved 24-bit background `(r, g, b)` when painted or erased under truecolour SGR.
    pub bg_rgb: Option<(u8, u8, u8)>,
    /// Attribute bits (see [`attr`]).
    pub attrs: u8,
    /// The underline's style.
    pub underline: Underline,
    /// The underline's palette/default colour (`Color::Default` when `ul_rgb` is `Some`);
    /// the default is the foreground's.
    pub ul: Color,
    /// The underline's resolved 24-bit colour `(r, g, b)`, when 58 set one.
    pub ul_rgb: Option<(u8, u8, u8)>,
    /// Up to [`MAX_COMBINING`] zero-width combining / ZWJ continuation codepoints attached
    /// to [`Self::ch`], in arrival order (`'\0'` in unused trailing slots).
    pub combining: [char; MAX_COMBINING],
    /// Count of active combining codepoints in [`Self::combining`] (`0..=MAX_COMBINING as u8`).
    pub combining_len: u8,
    /// Column width of this cell: `1` for normal narrow cells, `2` for the lead cell
    /// of a wide character, and `0` for its adjacent right-hand spacer cell.
    pub width: u8,
}

impl Cell {
    /// An empty cell: a single-width space with default colours, no RGB overrides,
    /// no attributes, no underline, and no combining marks.
    pub const BLANK: Cell = Cell {
        ch: ' ',
        fg: Color::Default,
        bg: Color::Default,
        fg_rgb: None,
        bg_rgb: None,
        attrs: 0,
        underline: Underline::None,
        ul: Color::Default,
        ul_rgb: None,
        combining: ['\0'; MAX_COMBINING],
        combining_len: 0,
        width: 1,
    };

    /// Append a zero-width combining mark `ch` if capacity below [`MAX_COMBINING`] remains.
    pub const fn push_combining(&mut self, ch: char) {
        let cur = combining_cap_clamp(self.combining_len as u64, MAX_COMBINING as u64) as usize;
        if cur < MAX_COMBINING {
            self.combining[cur] = ch;
            self.combining_len = (cur + 1) as u8;
        }
    }

    const fn last_combining(&self) -> Option<char> {
        let len = self.combining_len as usize;
        let idx = if len < MAX_COMBINING {
            len
        } else {
            MAX_COMBINING
        };
        if idx == 0 {
            None
        } else {
            Some(self.combining[idx - 1])
        }
    }

    /// Active combining marks attached to this cell.
    #[must_use]
    pub fn combining_marks(&self) -> &[char] {
        let len = (self.combining_len as usize).min(MAX_COMBINING);
        self.combining.get(..len).unwrap_or(&[])
    }
}

/// A 94-character set the fold can designate into G0 or G1 (SCS, `ESC ( F`
/// and `ESC ) F`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Charset {
    /// US ASCII (`F` = `B`): every byte is itself.
    #[default]
    Ascii,
    /// DEC Special Graphics (`F` = `0`): `0x5F..=0x7E` are the line-drawing
    /// and symbol glyphs ([`dec_special_graphic`]).
    DecSpecial,
}

/// The glyph DEC Special Graphics draws for the ASCII byte `b`, as xterm's
/// table has it (charsets.c; `_` is xterm's blank, where the DEC manual
/// shows a no-break space). Every byte outside `0x5F..=0x7E` is itself.
#[must_use]
pub const fn dec_special_graphic(b: u8) -> char {
    match b {
        b'_' => ' ',
        b'`' => '\u{25c6}',
        b'a' => '\u{2592}',
        b'b' => '\u{2409}',
        b'c' => '\u{240c}',
        b'd' => '\u{240d}',
        b'e' => '\u{240a}',
        b'f' => '\u{00b0}',
        b'g' => '\u{00b1}',
        b'h' => '\u{2424}',
        b'i' => '\u{240b}',
        b'j' => '\u{2518}',
        b'k' => '\u{2510}',
        b'l' => '\u{250c}',
        b'm' => '\u{2514}',
        b'n' => '\u{253c}',
        b'o' => '\u{23ba}',
        b'p' => '\u{23bb}',
        b'q' => '\u{2500}',
        b'r' => '\u{23bc}',
        b's' => '\u{23bd}',
        b't' => '\u{251c}',
        b'u' => '\u{2524}',
        b'v' => '\u{2534}',
        b'w' => '\u{252c}',
        b'x' => '\u{2502}',
        b'y' => '\u{2264}',
        b'z' => '\u{2265}',
        b'{' => '\u{03c0}',
        b'|' => '\u{2260}',
        b'}' => '\u{00a3}',
        b'~' => '\u{00b7}',
        other => other as char,
    }
}

/// The character-set state: what G0 and G1 hold, and which one GL maps
/// (SI/LS0 maps G0, SO/LS1 maps G1). xterm's `resetCharsets` puts ASCII in
/// every G-set and G0 in GL.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
struct Charsets {
    g0: Charset,
    g1: Charset,
    /// GL is G1 (after SO), not G0.
    shifted: bool,
}

impl Charsets {
    const fn ascii_gl(self) -> bool {
        matches!(if self.shifted { self.g1 } else { self.g0 }, Charset::Ascii)
    }

    /// The glyph an ASCII byte paints through GL.
    const fn translate(self, b: u8) -> char {
        let set = if self.shifted { self.g1 } else { self.g0 };
        match set {
            Charset::Ascii => b as char,
            Charset::DecSpecial => dec_special_graphic(b),
        }
    }

    /// One byte: G0's set, G1's, and the shift.
    const fn encode(self) -> u8 {
        (self.g0 as u8) | ((self.g1 as u8) << 1) | ((self.shifted as u8) << 2)
    }
}

/// The current drawing pen (SGR state).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Pen {
    fg: Color,
    bg: Color,
    fg_rgb: Option<(u8, u8, u8)>,
    bg_rgb: Option<(u8, u8, u8)>,
    attrs: u8,
    underline: Underline,
    ul: Color,
    ul_rgb: Option<(u8, u8, u8)>,
}

/// What DECSC saves (xterm `CursorSave2`, within this fold's state): the
/// position, a pending wrap as `col == cols`, the SGR pen, origin mode, and
/// the character sets (`sc->gsets`, `sc->curgl`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct SavedCursor {
    row: u16,
    col: u16,
    pen: Pen,
    origin: bool,
    charsets: Charsets,
    /// The saved cursor had a wrap pending on `col`, short of the last
    /// column (see [`Screen::margin_wrap`]).
    margin_wrap: bool,
}

impl Pen {
    const fn reset() -> Pen {
        Pen {
            fg: Color::Default,
            bg: Color::Default,
            fg_rgb: None,
            bg_rgb: None,
            attrs: 0,
            underline: Underline::None,
            ul: Color::Default,
            ul_rgb: None,
        }
    }

    /// The pen a [`crate::ops::ScreenOp::SetSgr`]-shaped op names: its colours, and
    /// `attrs` with [`WIRE_UNDERLINE`] read as a single underline. The underline
    /// takes no colour; a [`crate::ops::ScreenOp::SetUnderline`] after it sets the rest.
    const fn from_wire(
        fg: Color,
        fg_rgb: Option<(u8, u8, u8)>,
        bg: Color,
        bg_rgb: Option<(u8, u8, u8)>,
        attrs: u8,
    ) -> Pen {
        Pen {
            fg,
            bg,
            fg_rgb,
            bg_rgb,
            attrs: attrs & !WIRE_UNDERLINE,
            underline: if attrs & WIRE_UNDERLINE != 0 {
                Underline::Single
            } else {
                Underline::None
            },
            ul: Color::Default,
            ul_rgb: None,
        }
    }

    /// The attribute byte the encodings write for this pen ([`WIRE_UNDERLINE`]).
    const fn wire_attrs(&self) -> u8 {
        wire_attrs(self.attrs, self.underline)
    }

    /// The underline is more than [`Self::wire_attrs`] says: a style other than
    /// none or single, a colour, or an `attrs` that holds [`WIRE_UNDERLINE`] itself.
    const fn underline_ext(&self) -> bool {
        underline_ext(self.attrs, self.underline, self.ul, self.ul_rgb)
    }

    const fn set_ul_color(&mut self, c: Color) {
        self.ul = c;
        self.ul_rgb = None;
    }

    const fn set_ul_rgb(&mut self, r: u8, g: u8, b: u8) {
        self.ul = Color::Default;
        self.ul_rgb = Some((r, g, b));
    }

    const fn set_fg_color(&mut self, c: Color) {
        self.fg = c;
        self.fg_rgb = None;
    }

    const fn set_fg_rgb(&mut self, r: u8, g: u8, b: u8) {
        self.fg = Color::Default;
        self.fg_rgb = Some((r, g, b));
    }

    const fn set_bg_color(&mut self, c: Color) {
        self.bg = c;
        self.bg_rgb = None;
    }

    const fn set_bg_rgb(&mut self, r: u8, g: u8, b: u8) {
        self.bg = Color::Default;
        self.bg_rgb = Some((r, g, b));
    }
}

// Tiny runs keep the scalar path. The test-only switch retains the original
// byte-at-a-time loop as an oracle without affecting the production benchmark.
const ASCII_SPAN_MIN: usize = 2;

#[cfg(test)]
mod ascii_work {
    use std::cell::Cell;
    thread_local! {
        static ENABLED: Cell<bool> = const { Cell::new(true) };
        static WORK: Cell<(usize, usize)> = const { Cell::new((0, 0)) };
    }
    pub(super) fn enabled() -> bool {
        ENABLED.with(Cell::get)
    }
    pub(super) fn set(enabled: bool) {
        ENABLED.with(|value| value.set(enabled));
    }
    pub(super) fn record(bytes: usize) {
        WORK.with(|value| {
            let (runs, total) = value.get();
            value.set((runs.saturating_add(1), total.saturating_add(bytes)));
        });
    }
    pub(super) fn take() -> (usize, usize) {
        WORK.with(|value| value.replace((0, 0)))
    }
}

#[cfg(test)]
#[path = "ascii_span_tests.rs"]
mod ascii_span_tests;

// Width controls at 80/120/240 columns place the fixed setup crossover near
// twelve cells. Shorter spans retain the original point-copy kernel.
const ROW_COPY_MIN: usize = 12;
// Bound each transfer to the ordinary-row regime: one 240-cell memcpy
// regressed, while two transfers of at most 128 cells retained the gains.
const ROW_COPY_CHUNK: usize = 128;

#[cfg(test)]
#[path = "serialization_scan_tests.rs"]
mod serialization_scan_tests;

/// Contiguous physical rows with a logical origin. Only whole-viewport scrolls
/// rotate the origin; every exposed cell, range, encoding and equality is logical.
#[derive(Clone)]
struct Grid {
    cells: Vec<Cell>,
    origin: usize,
}

/// Exact extension counts gathered while writing the mandatory base encoding.
/// They are local to one immutable serialization, with no cached mutation state.
#[derive(Clone, Copy, Default)]
struct CellExtensionCounts {
    extended: u32,
    wide: u32,
    deep: u32,
    underline: u32,
}

impl CellExtensionCounts {
    #[inline]
    fn observe(&mut self, cell: &Cell) {
        if cell_has_ext(cell) {
            self.extended = self.extended.saturating_add(1);
        }
        if cell.width != 1 {
            self.wide = self.wide.saturating_add(1);
        }
        if cell_has_deep_combining(cell) {
            self.deep = self.deep.saturating_add(1);
        }
        if cell_underline_ext(cell) {
            self.underline = self.underline.saturating_add(1);
        }
    }
}

type GridCells<'a> = std::iter::Chain<std::slice::Iter<'a, Cell>, std::slice::Iter<'a, Cell>>;

impl Grid {
    fn new(cells: Vec<Cell>) -> Self {
        Self { cells, origin: 0 }
    }
    const fn len(&self) -> usize {
        self.cells.len()
    }
    #[inline]
    fn physical(&self, index: usize) -> usize {
        let len = self.cells.len();
        // The flat case has exactly Vec's own bounds check. Invalid logical
        // indices remain invalid rather than wrapping into a live physical cell.
        if self.origin == 0 || index >= len {
            return index;
        }
        let before_wrap = len.saturating_sub(self.origin);
        if index < before_wrap {
            self.origin + index
        } else {
            index - before_wrap
        }
    }
    #[inline]
    fn get(&self, index: usize) -> Option<&Cell> {
        self.cells.get(self.physical(index))
    }
    #[inline]
    fn get_mut(&mut self, index: usize) -> Option<&mut Cell> {
        let at = self.physical(index);
        self.cells.get_mut(at)
    }
    // A row never crosses the physical cut: every rotation is row-aligned.
    fn span(&self, from: usize, to: usize) -> Option<&[Cell]> {
        if from > to || to > self.len() {
            return None;
        }
        if from == to {
            return self.cells.get(0..0);
        }
        let at = self.physical(from);
        self.cells.get(at..at.saturating_add(to - from))
    }
    fn span_mut(&mut self, from: usize, to: usize) -> Option<&mut [Cell]> {
        if from > to || to > self.len() {
            return None;
        }
        if from == to {
            return self.cells.get_mut(0..0);
        }
        let at = self.physical(from);
        self.cells.get_mut(at..at.saturating_add(to - from))
    }
    /// Copy a complete contiguous logical span between disjoint physical spans.
    /// Whole-row alignment makes each scroll source/destination contiguous even
    /// across the logical origin. Other ranges can use the caller's cell path.
    #[inline(never)]
    fn copy_span(&mut self, from: usize, to: usize, len: usize) -> bool {
        if from == to || len == 0 {
            return true;
        }
        let Some(from_end) = from.checked_add(len) else {
            return false;
        };
        let Some(to_end) = to.checked_add(len) else {
            return false;
        };
        if from_end > self.len() || to_end > self.len() {
            return false;
        }
        let from = self.physical(from);
        let to = self.physical(to);
        let (source, dest) = if from < to {
            let Some((before, after)) = self.cells.split_at_mut_checked(to) else {
                return false;
            };
            let Some(end) = from.checked_add(len) else {
                return false;
            };
            let Some(source) = before.get(from..end) else {
                return false;
            };
            let Some(dest) = after.get_mut(..len) else {
                return false;
            };
            (source, dest)
        } else {
            let Some((before, after)) = self.cells.split_at_mut_checked(from) else {
                return false;
            };
            let Some(end) = to.checked_add(len) else {
                return false;
            };
            let Some(source) = after.get(..len) else {
                return false;
            };
            let Some(dest) = before.get_mut(to..end) else {
                return false;
            };
            (source, dest)
        };
        // Both checked slices have len cells. Bound each transfer to the
        // ordinary-row copy regime while mapping a large row only once.
        for (dest, source) in dest
            .chunks_mut(ROW_COPY_CHUNK)
            .zip(source.chunks(ROW_COPY_CHUNK))
        {
            dest.copy_from_slice(source);
        }
        true
    }

    fn slices(&self) -> [&[Cell]; 2] {
        let (before, after) = self.cells.split_at(self.origin);
        [after, before]
    }
    fn for_each(&self, mut f: impl FnMut(&Cell)) {
        for span in self.slices() {
            for cell in span {
                f(cell);
            }
        }
    }
    fn for_each_indexed(&self, mut f: impl FnMut(usize, &Cell)) {
        let mut base = 0;
        for span in self.slices() {
            for (at, cell) in span.iter().enumerate() {
                f(base + at, cell);
            }
            base += span.len();
        }
    }
    #[cfg(test)]
    fn any(&self, mut predicate: impl FnMut(&Cell) -> bool) -> bool {
        let [after, before] = self.slices();
        after.iter().any(&mut predicate) || before.iter().any(predicate)
    }
    #[cfg(test)]
    fn count_if(&self, mut predicate: impl FnMut(&Cell) -> bool) -> u32 {
        let mut count = 0u32;
        self.for_each(|cell| {
            if predicate(cell) {
                count = count.saturating_add(1);
            }
        });
        count
    }
    fn with_range_mut(&mut self, from: usize, to: usize, mut f: impl FnMut(&mut [Cell])) {
        if from > to || to > self.len() || from == to {
            return;
        }
        let at = self.physical(from);
        let first = (to - from).min(self.len().saturating_sub(at));
        if let Some(span) = self.cells.get_mut(at..at.saturating_add(first)) {
            f(span);
        }
        let rest = (to - from).saturating_sub(first);
        if rest > 0 {
            if let Some(span) = self.cells.get_mut(..rest) {
                f(span);
            }
        }
    }
    fn fill(&mut self, from: usize, to: usize, blank: Cell) {
        self.with_range_mut(from, to, |span| span.fill(blank));
    }
    fn iter(&self) -> GridCells<'_> {
        let (before, after) = self.cells.split_at(self.origin);
        after.iter().chain(before.iter())
    }
    fn rotate_up(&mut self, cells: usize) {
        if self.cells.is_empty() {
            return;
        }
        let shift = cells % self.len();
        let before_wrap = self.len() - self.origin;
        self.origin = if shift >= before_wrap {
            shift - before_wrap
        } else {
            self.origin + shift
        };
    }
    fn rotate_down(&mut self, cells: usize) {
        if self.cells.is_empty() {
            return;
        }
        let shift = cells % self.len();
        self.origin = if shift <= self.origin {
            self.origin - shift
        } else {
            self.len() - (shift - self.origin)
        };
    }
}

impl<'a> IntoIterator for &'a Grid {
    type Item = &'a Cell;
    type IntoIter = GridCells<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl PartialEq for Grid {
    fn eq(&self, other: &Self) -> bool {
        if self.origin == other.origin {
            self.cells == other.cells
        } else {
            self.iter().eq(other.iter())
        }
    }
}
impl Eq for Grid {}
impl std::fmt::Debug for Grid {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

#[inline]
fn rotated_scroll_enabled() -> bool {
    #[cfg(test)]
    {
        scroll_work::enabled()
    }
    #[cfg(not(test))]
    {
        true
    }
}

#[cfg(test)]
mod scroll_work {
    use std::cell::Cell;
    thread_local! {
        static ENABLED: Cell<bool> = const { Cell::new(true) };
        static MOVED: Cell<usize> = const { Cell::new(0) };
    }
    pub(super) fn enabled() -> bool {
        ENABLED.with(Cell::get)
    }
    pub(super) fn set(enabled: bool) {
        ENABLED.with(|value| value.set(enabled));
    }
    pub(super) fn moved(n: usize) {
        MOVED.with(|value| value.set(value.get().saturating_add(n)));
    }
    pub(super) fn take() -> usize {
        MOVED.with(|value| value.replace(0))
    }
}

#[cfg(test)]
#[path = "scroll_grid_tests.rs"]
mod scroll_grid_tests;

/// A terminal screen: the foldable state. Build one with [`fold`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Screen {
    cols: u16,
    rows: u16,
    grid: Grid,
    row: u16,
    col: u16,
    pen: Pen,
    cursor_visible: bool,
    altscreen: bool,
    /// The buffer not on screen: the main grid while the alternate screen is
    /// up, and the alternate grid while the main one is (`None` until the
    /// alternate screen is first entered).
    inactive: Option<Grid>,
    /// The main screen's DECSC slot (`ESC 7` / `CSI s`, and the `?1049` round
    /// trip). Never consumed by a restore.
    saved_cursor: Option<SavedCursor>,
    /// The alternate screen's own DECSC slot (xterm `sc[1]`): a DECSC issued
    /// there never clobbers the main slot, and it lasts as long as the
    /// alternate buffer does.
    alt_saved_cursor: Option<SavedCursor>,
    /// Top row of the DEC scrolling region (`DECSTBM`), 0-based inclusive.
    scroll_top: u16,
    /// Bottom row of the DEC scrolling region (`DECSTBM`), 0-based inclusive.
    /// `(scroll_top, scroll_bottom) == (0, rows-1)` means the full screen scrolls.
    scroll_bottom: u16,
    /// Origin mode (DECOM, `?6`): cursor addressing counts from the top margin.
    origin: bool,
    /// Insert mode (IRM, ANSI mode 4): a glyph shifts the line right first.
    insert: bool,
    /// Newline mode (LNM, ANSI mode 20): LF, VT and FF also return the
    /// carriage.
    newline: bool,
    /// G0, G1 and the GL shift.
    charsets: Charsets,
    /// Left/right margin mode (DECLRMM, `?69`): `CSI s` is DECSLRM, not a
    /// cursor save.
    lrmm: bool,
    /// The left margin (DECSLRM), 0-based inclusive; 0 unless DECLRMM set it.
    left: u16,
    /// The right margin, 0-based inclusive; `cols - 1` unless DECLRMM set it.
    right: u16,
    /// A wrap is pending with the cursor ON `col`, short of the screen's
    /// last column (at a right margin, or where a restore or a margin reset
    /// left it). A wrap pending on the last column is `col == cols` instead,
    /// so each pending wrap has one spelling.
    margin_wrap: bool,
    /// Application cursor keys mode (DECCKM, `?1`).
    app_cursor_keys: bool,
    /// Focus-in / focus-out event reporting (`?1004`).
    focus_events: bool,
    /// Bracketed paste mode (`?2004`).
    bracketed_paste: bool,
    /// DEC `?2026` synchronized output mode (`BSU` `?2026h` .. `ESU` `?2026l`).
    synchronized_output: bool,
    /// The last code point printed was `U+200D` (or a glyph that joined after it): a glyph
    /// after anything else starts a cell of its own, even beside a cell whose last mark is a
    /// joiner, as aterm's `last_combining_was_zwj` has it.
    joiner_open: bool,
    /// The cursor stands on the left margin past column 0 because printing the glyph left of it
    /// put it there, from outside the margin: that glyph still takes a mark, where a cursor a
    /// motion put there has none before it. A print sets it and every motion clears it, as
    /// aterm's `follows_glyph` has it (xterm's `char_was_written` on this one column).
    stepped_onto_margin: bool,
}

/// Maximum byte length of a sanitized `OSC 0` / `OSC 2` window title retained on [`Folder`].
pub const MAX_OSC_TITLE_BYTES: usize = 512;

/// Maximum byte length of a decoded `OSC 7` working-directory path retained on [`Folder`].
pub const MAX_OSC_CWD_BYTES: usize = 1024;

/// Fold an ordered slice of records into the screen they produce.
///
/// `cols`/`rows` are the initial viewport size (clamped to `1..=`[`MAX_DIM`]).
/// [`Record::In`] and [`Record::Exit`] are ignored — input does not paint.
pub fn fold(cols: u16, rows: u16, records: &[Record]) -> Screen {
    let mut folder = Folder::new(cols, rows);
    for rec in records {
        folder.apply(rec);
    }
    folder.into_screen()
}

/// A resumable terminal fold: the [`Screen`] plus the live parser state, so it
/// can be advanced record-by-record and **cloned to snapshot the exact
/// mid-stream state** — including a parser paused mid-escape-sequence or
/// mid-string-sequence (when an escape, or an OSC/DCS payload, is split across
/// two `Out` records). Cloning a `Folder` at offset `K` and feeding it only the
/// records after `K` reproduces the same screen as folding the whole log: this
/// is what makes `/a/state` + log-tail resume exact rather than approximate.
///
/// Also tracks out-of-band session metadata (`OSC 0`/`2` window [`title`](Self::title)
/// and `OSC 7` working directory [`cwd`](Self::cwd)) without perturbing [`Screen`]
/// visual digests or [`ScreenOp`] projection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Folder {
    screen: Screen,
    parser: Parser,
    title: String,
    cwd: String,
    sync_bytes: usize,
}

impl Folder {
    /// A fresh folder over a blank screen of the given size.
    pub fn new(cols: u16, rows: u16) -> Folder {
        Folder {
            screen: Screen::new(cols, rows),
            parser: Parser::new(),
            title: String::new(),
            cwd: String::new(),
            sync_bytes: 0,
        }
    }

    /// A fresh folder with normalized [`ScreenOp`] recording enabled, so each
    /// [`Folder::apply`] appends the emitted ops for incremental draining via
    /// [`Folder::take_ops`].
    pub fn new_recording(cols: u16, rows: u16) -> Folder {
        let mut f = Self::new(cols, rows);
        f.parser.recording = true;
        f
    }

    /// Enable or disable incremental [`ScreenOp`] recording on this folder.
    pub fn set_recording(&mut self, recording: bool) {
        self.parser.recording = recording;
    }

    /// Drain the [`ScreenOp`]s recorded since the last call (empty unless
    /// recording is enabled via [`Folder::new_recording`] or [`Folder::set_recording`]).
    pub fn take_ops(&mut self) -> Vec<ScreenOp> {
        std::mem::take(&mut self.parser.ops)
    }

    /// Discard any partial mid-record VT escape, OSC/DCS string, or multibyte
    /// UTF-8 sequence in the parser — and unlatch any mid-frame DEC `?2026`
    /// synchronized-output hold — while keeping the painted [`Screen`], committed
    /// [`title`](Self::title) / [`cwd`](Self::cwd), and any already-recorded
    /// [`ScreenOp`]s intact.
    ///
    /// Call this across a stream discontinuity (such as a broker retention
    /// `Gap`) where intermediate `Out` chunks were dropped: without resetting,
    /// an unterminated pre-gap OSC/DCS (`State::Str`) would swallow post-gap
    /// printable bytes, a dropped `\x1b[?2026l` would keep synchronized output
    /// latched, and a partial CSI/UTF-8 prefix would splice onto the first
    /// post-gap byte.
    pub fn reset_escape(&mut self) {
        self.parser.reset_escape();
        self.screen.synchronized_output = false;
        self.sync_bytes = 0;
    }

    /// Advance by one record. `In`/`Exit` do not paint (only echoed `Out` does).
    pub fn apply(&mut self, record: &Record) {
        match record {
            Record::Out(bytes) => {
                self.parser.feed(
                    &mut self.screen,
                    &mut self.title,
                    &mut self.cwd,
                    &mut self.sync_bytes,
                    bytes,
                );
            }
            Record::Resize { cols, rows } => {
                self.screen.resize(*cols, *rows);
                self.parser.rec(ScreenOp::Resize(*cols, *rows));
            }
            Record::In { .. } | Record::Exit { .. } => {}
        }
    }

    /// The current screen.
    pub const fn screen(&self) -> &Screen {
        &self.screen
    }

    /// Whether DEC `?2026` synchronized output is currently active **and** within
    /// the [`crate::events::MAX_SYNC_OUTPUT_BYTES`] safety budget.
    #[must_use]
    pub const fn in_sync_update(&self) -> bool {
        self.screen.synchronized_output
            && crate::events::sync_within_budget(
                self.sync_bytes as u64,
                crate::events::MAX_SYNC_OUTPUT_BYTES as u64,
            )
    }

    /// Number of `Out` bytes accumulated inside the current open DEC `?2026`
    /// synchronized-output frame (`0` when `?2026` is inactive, clamped at
    /// [`crate::events::MAX_SYNC_OUTPUT_BYTES`]).
    #[must_use]
    pub const fn sync_output_bytes(&self) -> usize {
        self.sync_bytes
    }

    /// Current sanitized window title set by `OSC 0;<title>` or `OSC 2;<title>`
    /// (empty until set, cleared by `ESC c` RIS, C0/C1 controls stripped, capped at
    /// [`MAX_OSC_TITLE_BYTES`]).
    #[must_use]
    pub fn title(&self) -> &str {
        &self.title
    }

    /// Current working directory path reported by `OSC 7;<file://host/path>`
    /// (percent-decoded, empty until set, cleared by `OSC 7;` or `ESC c` RIS, capped at
    /// [`MAX_OSC_CWD_BYTES`]).
    #[must_use]
    pub fn cwd(&self) -> &str {
        &self.cwd
    }

    /// Consume the folder, returning its screen.
    pub fn into_screen(self) -> Screen {
        self.screen
    }
}

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "screen_island.rs"]
mod screen_island;
#[cfg(not(clean_islands))]
pub use crate::twins::screen_clamp_dim;
#[cfg(clean_islands)]
pub use screen_island::screen_clamp_dim;

#[cfg(clean_islands)]
#[path = "color_island.rs"]
mod color_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{color_clamp_channel, combining_cap_clamp};
#[cfg(clean_islands)]
pub use color_island::{color_clamp_channel, combining_cap_clamp};

#[cfg(clean_islands)]
#[path = "wide_island.rs"]
mod wide_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{wide_cell_width_clamp, wide_spacer_col_clamp};
#[cfg(clean_islands)]
pub use wide_island::{wide_cell_width_clamp, wide_spacer_col_clamp};

#[cfg(clean_islands)]
#[path = "vs_island.rs"]
mod vs_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{vs_cursor_advance_clamp, vs_width_clamp};
#[cfg(clean_islands)]
pub use vs_island::{vs_cursor_advance_clamp, vs_width_clamp};

contract_fn! {
    /// Kernel-certified bounds check that a variation-selector cell width `width`
    /// is at most `max_width` (`width <= max_width`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `vs_width_valid_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn vs_width_valid(width: u64, max_width: u64) -> bool
    clauses [ensures result == (width <= max_width)]
    {
        width <= max_width
    }
}

contract_fn! {
    /// Kernel-certified bounds check that a cell width tag `w` lies in `0..=2`
    /// (`0` = wide continuation spacer, `1` = narrow cell, `2` = wide lead cell).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `cell_width_is_valid_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn cell_width_is_valid(w: u8) -> bool
    clauses [ensures result == (w <= 2)]
    {
        w <= 2
    }
}

contract_fn! {
    /// Kernel-certified bounds check that a screen row/column coordinate `coord`
    /// lies strictly within dimension `dim` (`coord < dim`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `screen_coord_in_bounds_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn screen_coord_in_bounds(coord: u16, dim: u16) -> bool
    clauses [ensures result == (coord < dim)]
    {
        coord < dim
    }
}

contract_fn! {
    /// Kernel-certified bounds check that a cell's inline combining-mark count
    /// `len` is at most `cap` (`len <= cap`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `combining_len_within_cap_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn combining_len_within_cap(len: u8, cap: u8) -> bool
    clauses [ensures result == (len <= cap)]
    {
        len <= cap
    }
}

/// Maximum total cells a single screen grid may allocate (`MAX_DIM * MAX_DIM`).
const MAX_GRID_CELLS: usize = (MAX_DIM as usize) * (MAX_DIM as usize);

fn blank_grid(cols: u16, rows: u16) -> Grid {
    let n = (cols as usize)
        .saturating_mul(rows as usize)
        .min(MAX_GRID_CELLS);
    let cap = if n < MAX_GRID_CELLS {
        n
    } else {
        MAX_GRID_CELLS
    };
    let mut grid = Vec::with_capacity(cap);
    let mut i = 0usize;
    while i < n {
        grid.push(Cell::BLANK);
        i = i.saturating_add(1);
    }
    Grid::new(grid)
}

impl Screen {
    /// A blank screen of the given size (each edge clamped to `1..=`[`MAX_DIM`]).
    pub fn new(cols: u16, rows: u16) -> Screen {
        let cols = screen_clamp_dim(cols.max(1) as u64, MAX_DIM as u64) as u16;
        let rows = screen_clamp_dim(rows.max(1) as u64, MAX_DIM as u64) as u16;
        Screen {
            cols,
            rows,
            grid: blank_grid(cols, rows),
            row: 0,
            col: 0,
            pen: Pen::reset(),
            cursor_visible: true,
            altscreen: false,
            inactive: None,
            saved_cursor: None,
            alt_saved_cursor: None,
            scroll_top: 0,
            scroll_bottom: rows.saturating_sub(1),
            origin: false,
            insert: false,
            newline: false,
            charsets: Charsets {
                g0: Charset::Ascii,
                g1: Charset::Ascii,
                shifted: false,
            },
            lrmm: false,
            left: 0,
            right: cols.saturating_sub(1),
            margin_wrap: false,
            app_cursor_keys: false,
            focus_events: false,
            bracketed_paste: false,
            synchronized_output: false,
            joiner_open: false,
            stepped_onto_margin: false,
        }
    }

    /// Current `(cols, rows)`.
    pub const fn dims(&self) -> (u16, u16) {
        (self.cols, self.rows)
    }

    /// Cursor position as `(row, col)`, 0-based. While a line-wrap is pending
    /// `col` is one past the column the cursor is on (deferred wrap: `cols` at
    /// the screen's edge, one past the right margin under DECSLRM) until the
    /// next glyph wraps or cursor motion resolves it; [`Self::wrap_pending`]
    /// tells that apart from a cursor really standing there.
    pub const fn cursor(&self) -> (u16, u16) {
        if self.margin_wrap {
            (self.row, self.col.saturating_add(1))
        } else {
            (self.row, self.col)
        }
    }

    /// Whether a wrap is pending: the next glyph goes on the next line.
    pub const fn wrap_pending(&self) -> bool {
        self.col >= self.cols || self.margin_wrap
    }

    /// The left and right margins, 0-based inclusive (`(0, cols - 1)` unless
    /// DECSLRM set them).
    pub const fn lr_margins(&self) -> (u16, u16) {
        (self.left, self.right)
    }

    /// Whether the cursor is currently visible (`?25`).
    pub const fn cursor_visible(&self) -> bool {
        self.cursor_visible
    }

    /// Whether the alternate screen is active.
    pub const fn is_altscreen(&self) -> bool {
        self.altscreen
    }

    /// Whether application cursor keys mode (`DECCKM`, `?1`) is active.
    #[must_use]
    pub const fn app_cursor_keys(&self) -> bool {
        self.app_cursor_keys
    }

    /// Whether focus-event reporting (`?1004`) is active.
    #[must_use]
    pub const fn focus_events(&self) -> bool {
        self.focus_events
    }

    /// Whether bracketed paste mode (`?2004`) is active.
    #[must_use]
    pub const fn bracketed_paste(&self) -> bool {
        self.bracketed_paste
    }

    /// Whether DEC `?2026` synchronized output (`BSU` `?2026h` .. `ESU` `?2026l`) is active.
    #[must_use]
    pub const fn synchronized_output(&self) -> bool {
        self.synchronized_output
    }

    /// The cell at `(row, col)`, or `None` if out of bounds.
    pub fn cell(&self, row: u16, col: u16) -> Option<&Cell> {
        if screen_coord_in_bounds(row, self.rows) && screen_coord_in_bounds(col, self.cols) {
            self.grid.get(self.idx(row, col))
        } else {
            None
        }
    }

    /// Overlay a single cell. Used by speculative echo to paint an unconfirmed
    /// prediction onto a copy of the authoritative screen. No-op if out of bounds.
    pub fn set_cell(&mut self, row: u16, col: u16, cell: Cell) {
        if screen_coord_in_bounds(row, self.rows) && screen_coord_in_bounds(col, self.cols) {
            let i = self.idx(row, col);
            if let Some(slot) = self.grid.get_mut(i) {
                *slot = cell;
            }
        }
    }

    /// The text of a row, including any attached zero-width combining marks per cell,
    /// with trailing blanks trimmed: a wide glyph appears once (its spacer adds
    /// nothing). Empty if out of bounds.
    pub fn line_text(&self, row: u16) -> String {
        if row >= self.rows {
            return String::new();
        }
        let start = self.idx(row, 0);
        let end = start.saturating_add(self.cols as usize);
        let mut line = String::new();
        for c in self.grid.span(start, end).unwrap_or(&[]) {
            if c.width == 0 {
                continue;
            }
            line.push(c.ch);
            for &m in c.combining_marks() {
                line.push(m);
            }
        }
        line.truncate(line.trim_end().len());
        line
    }

    /// A deterministic byte encoding of the **entire** screen state — the visible
    /// grid, cursor, modes, the current SGR pen, the saved cursors and the
    /// inactive buffer's grid. Two screens are equal under the derived `Eq` iff
    /// they serialize to the same bytes (the encoding is self-delimiting, hence
    /// injective); that is what the replay/fork/cut/echo oracles and
    /// [`crate::render::frame_hash`] rely on, and what the replay claim pins.
    pub fn serialize(&self) -> Vec<u8> {
        let mut out = Vec::new();
        self.serialize_into(&mut out);
        out
    }

    /// [`serialize`](Self::serialize), streamed into `out` instead of collected, so
    /// a consumer that only hashes the encoding never materializes it.
    pub(crate) fn serialize_into<S: ByteSink>(&self, out: &mut S) {
        out.extend_from_slice(&encode_screen_header(
            self.cols,
            self.rows,
            self.row,
            self.col,
            self.cursor_visible,
            self.altscreen,
        ));
        let mut active_counts = CellExtensionCounts::default();
        self.grid.for_each(|cell| {
            out.extend_from_slice(&encode_cell_bytes(cell));
            active_counts.observe(cell);
        });
        // Internal state that derived `Eq` distinguishes but the grid alone does
        // not — without these, two unequal screens could serialize identically
        // (e.g. a pending SGR pen with nothing yet printed). The grid length is
        // fixed by cols*rows above, so what follows is self-delimiting.
        out.extend_from_slice(&encode_pen_bytes(
            self.pen.fg,
            self.pen.bg,
            self.pen.wire_attrs(),
        ));
        match self.saved_cursor {
            Some(saved) => out.extend_from_slice(&encode_saved_cursor_bytes(
                saved.row,
                saved.col,
                saved.pen.fg,
                saved.pen.bg,
                saved.pen.wire_attrs(),
            )),
            None => out.extend_from_slice(&[0]),
        }
        match self.alt_saved_cursor {
            Some(saved) => out.extend_from_slice(&encode_saved_cursor_bytes(
                saved.row,
                saved.col,
                saved.pen.fg,
                saved.pen.bg,
                saved.pen.wire_attrs(),
            )),
            None => out.extend_from_slice(&[0]),
        }
        let mut inactive_counts = CellExtensionCounts::default();
        match &self.inactive {
            Some(cells) => {
                out.extend_from_slice(&[1]);
                out.extend_from_slice(&encode_u32_le_bytes(cells.len() as u32));
                cells.for_each(|cell| {
                    out.extend_from_slice(&encode_cell_bytes(cell));
                    inactive_counts.observe(cell);
                });
            }
            None => out.extend_from_slice(&[0]),
        }
        out.extend_from_slice(&encode_scroll_region_bytes(
            self.scroll_top,
            self.scroll_bottom,
        ));
        // The state the fold gained after this encoding was fixed, written only
        // when some of it is away from its reset value: every screen an earlier
        // fold could make keeps its bytes (and its pinned hashes). It stays
        // injective because everything above is self-delimiting (a decoder
        // knows where it ends), so the trailer is either absent or starts with
        // its own tag byte.
        let modes = encode_modes_bytes(
            [
                self.origin,
                self.insert,
                self.newline,
                self.lrmm,
                self.margin_wrap,
            ],
            self.saved_cursor
                .map_or([false; 2], |s| [s.origin, s.margin_wrap]),
            self.alt_saved_cursor
                .map_or([false; 2], |s| [s.origin, s.margin_wrap]),
        );
        // The character sets in use and as each DECSC slot saved them (an
        // empty slot reads as the reset sets, all zero).
        let charsets = [
            self.charsets.encode(),
            self.saved_cursor.map_or(0, |s| s.charsets.encode()),
            self.alt_saved_cursor.map_or(0, |s| s.charsets.encode()),
        ];
        let margins = encode_scroll_region_bytes(self.left, self.right);
        let full_width = encode_scroll_region_bytes(0, self.cols.saturating_sub(1));
        if modes != MODES_AT_RESET || charsets != [0; 3] || margins != full_width {
            out.extend_from_slice(&[1]);
            out.extend_from_slice(&modes);
            out.extend_from_slice(&charsets);
            out.extend_from_slice(&margins);
        }
        // Tag-2 extension trailer for 24-bit truecolour (`fg_rgb` / `bg_rgb`) and
        // per-cell zero-width combining marks: emitted ONLY when any cell, pen, or
        // saved-cursor slot carries extended colour or combining state, keeping every
        // non-truecolour / non-combining screen byte-identical to its pinned digest
        // while preserving strict `s1 == s2 <=> s1.serialize() == s2.serialize()`
        // injectivity across all reachable and caller-constructed `Cell` values.
        let saved_has_rgb = match self.saved_cursor {
            Some(s) => pen_has_rgb(s.pen),
            None => false,
        };
        let alt_saved_has_rgb = match self.alt_saved_cursor {
            Some(s) => pen_has_rgb(s.pen),
            None => false,
        };
        if pen_has_rgb(self.pen)
            || saved_has_rgb
            || alt_saved_has_rgb
            || active_counts.extended > 0
            || inactive_counts.extended > 0
        {
            out.extend_from_slice(&[2]);
            emit_opt_rgb(out, self.pen.fg_rgb);
            emit_opt_rgb(out, self.pen.bg_rgb);
            if let Some(s) = self.saved_cursor {
                emit_opt_rgb(out, s.pen.fg_rgb);
                emit_opt_rgb(out, s.pen.bg_rgb);
            }
            if let Some(s) = self.alt_saved_cursor {
                emit_opt_rgb(out, s.pen.fg_rgb);
                emit_opt_rgb(out, s.pen.bg_rgb);
            }
            emit_ext_cells(out, &self.grid, active_counts.extended);
            if let Some(cells) = &self.inactive {
                emit_ext_cells(out, cells, inactive_counts.extended);
            }
        }
        // Tag-3 extension trailer for non-unit cell widths (`width != 1`, e.g. wide
        // CJK/emoji lead `width = 2` and spacer `width = 0`): emitted ONLY when some
        // cell carries `width != 1`, keeping every narrow screen byte-identical to its
        // pinned digest while preserving strict `Eq <=> serialize()` injectivity.
        if active_counts.wide > 0 || inactive_counts.wide > 0 {
            out.extend_from_slice(&[3]);
            emit_wide_cells(out, &self.grid, active_counts.wide);
            if let Some(cells) = &self.inactive {
                emit_wide_cells(out, cells, inactive_counts.wide);
            }
        }
        // Tag-4 extension trailer for session DEC private modes (`?1` DECCKM,
        // `?1004` focus reporting, `?2004` bracketed paste, `?2026` synchronized
        // output): emitted ONLY when at least one mode is set, preserving byte
        // identity for every reset-mode screen and strict `Eq <=> serialize()`
        // injectivity across `emit_ops`/`apply_ops` and raw `fold`.
        let ext_modes = (self.app_cursor_keys as u8)
            | ((self.focus_events as u8) << 1)
            | ((self.bracketed_paste as u8) << 2)
            | ((self.synchronized_output as u8) << 3)
            | ((self.joiner_open as u8) << 4)
            | ((self.stepped_onto_margin as u8) << 5);
        if ext_modes != 0 {
            out.extend_from_slice(&[4, ext_modes]);
        }
        // Tag-5 extension trailer for deep inline combining marks (`combining[4..16]` or
        // `combining_len > 4`): emitted ONLY when some cell carries more than 4 combining
        // marks, keeping every <=4-mark screen byte-identical to its pinned digest while
        // preserving strict `Eq <=> serialize()` injectivity up to `MAX_COMBINING = 16`.
        if active_counts.deep > 0 || inactive_counts.deep > 0 {
            out.extend_from_slice(&[5]);
            emit_deep_combining_cells(out, &self.grid, active_counts.deep);
            if let Some(cells) = &self.inactive {
                emit_deep_combining_cells(out, cells, inactive_counts.deep);
            }
        }
        // Tag-6 extension trailer for the underline beyond the attribute byte's
        // [`WIRE_UNDERLINE`] (a style other than none or single, an underline colour):
        // emitted ONLY when the pen, a saved pen or some cell has one, so every screen
        // whose underlines are single and uncoloured keeps the bytes it had when the
        // fold knew one underline, and `Eq <=> serialize()` stays strict. It names the
        // pen and each saved pen in full, then the cells that need it by index.
        let saved_ul = self.saved_cursor.is_some_and(|s| s.pen.underline_ext());
        let alt_saved_ul = self.alt_saved_cursor.is_some_and(|s| s.pen.underline_ext());
        if self.pen.underline_ext()
            || saved_ul
            || alt_saved_ul
            || active_counts.underline > 0
            || inactive_counts.underline > 0
        {
            out.extend_from_slice(&[6]);
            emit_underline_pen(out, self.pen);
            if let Some(s) = self.saved_cursor {
                emit_underline_pen(out, s.pen);
            }
            if let Some(s) = self.alt_saved_cursor {
                emit_underline_pen(out, s.pen);
            }
            emit_underline_cells(out, &self.grid, active_counts.underline);
            if let Some(cells) = &self.inactive {
                emit_underline_cells(out, cells, inactive_counts.underline);
            }
        }
    }

    // --- internal mutators ------------------------------------------------

    const fn idx(&self, row: u16, col: u16) -> usize {
        (row as usize)
            .saturating_mul(self.cols as usize)
            .saturating_add(col as usize)
    }

    /// Resolve a pending wrap back onto the column the cursor is on (the last
    /// one for `col == cols`): what xterm's cursor-motion primitives and
    /// erases do to the last-column flag (`ResetWrap`) before they move or
    /// clear (CR/LF/BS/CUB/CUU/CUD/CUP, ED/EL). TAB deliberately does not.
    const fn clear_pending_wrap(&mut self) {
        let last_col = self.cols.saturating_sub(1);
        if self.col > last_col {
            self.col = last_col;
        }
        self.margin_wrap = false;
        self.stepped_onto_margin = false;
    }

    /// Leave a wrap pending with the cursor on column `col`, in the one
    /// spelling each has: `col == cols` on the last column, the
    /// [`Self::margin_wrap`] flag short of it.
    const fn set_wrap_at(&mut self, col: u16) {
        let last_col = self.cols.saturating_sub(1);
        if col >= last_col {
            self.col = self.cols;
            self.margin_wrap = false;
        } else {
            self.col = col;
            self.margin_wrap = true;
        }
    }

    /// Whether column `col` lies within the left/right margins (xterm
    /// `ScrnIsColInMargins`; always, without DECSLRM margins).
    const fn in_lr_margins(&self, col: u16) -> bool {
        col >= self.left && col <= self.right
    }

    /// The column the cursor is on: a wrap pending at the screen's edge is
    /// on the last column.
    const fn grid_col(&self) -> u16 {
        let last_col = self.cols.saturating_sub(1);
        if self.col < last_col {
            self.col
        } else {
            last_col
        }
    }

    /// The last column a line runs to from column `col`, where a glyph leaves
    /// a wrap pending and where CUF and TAB stop: the right margin, or the
    /// screen's edge for a cursor already past it (xterm `CursorForward`).
    const fn line_end(&self, col: u16) -> u16 {
        if col <= self.right {
            self.right
        } else {
            self.cols.saturating_sub(1)
        }
    }

    /// The column [`Cell::width`] of the cell at `(row, col)` (1 off the grid).
    #[inline]
    fn width_at(&self, row: u16, col: u16) -> u8 {
        if col >= self.cols {
            return 1;
        }
        match self.grid.get(self.idx(row, col)) {
            Some(c) => c.width,
            None => 1,
        }
    }

    /// Whether a glyph precedes the cursor for a cluster to continue: one parked
    /// under a pending wrap, or the one left of the cursor. Column 0 has none, and
    /// a left margin none unless a print stepped onto it
    /// ([`Self::stepped_onto_margin`]).
    const fn has_active_base(&self) -> bool {
        self.wrap_pending() || (self.col > 0 && (self.col != self.left || self.stepped_onto_margin))
    }

    /// The cell a zero-width mark, or a glyph joining a cluster after a
    /// `U+200D`, attaches to: the parked glyph under a pending wrap, else the
    /// one left of the cursor (the cursor's own cell where
    /// [`Self::has_active_base`] finds none), and a wide glyph's lead rather
    /// than its spacer.
    fn active_base_col(&self) -> u16 {
        let prev_col = if self.wrap_pending() {
            self.grid_col()
        } else if self.has_active_base() {
            self.col.saturating_sub(1)
        } else {
            self.col
        };
        if prev_col > 0 && self.width_at(self.row, prev_col) == 0 {
            return prev_col.saturating_sub(1);
        }
        prev_col
    }

    /// The boundary before column `b` of row `row` is about to be cut by a
    /// write, an erase or a shift: if a wide glyph straddles it (its spacer is
    /// at `b`), blank both of its cells with the bce blank, so no half of it
    /// survives (Ghostty's `splitCellBoundary`; xterm repairs the same
    /// `DamagedCells` with `ClearCells`, which writes the current colours).
    #[inline]
    fn split_at(&mut self, row: u16, b: u16) {
        if b == 0 || self.width_at(row, b) != 0 {
            return;
        }
        let blank = self.bce_blank();
        let i = self.idx(row, b);
        self.grid
            .fill(i.saturating_sub(1), i.saturating_add(1), blank);
    }

    /// A cell in the current pen: a glyph (`width` 1, or 2 for a wide one's
    /// lead) or a wide glyph's spacer (`' '`, `width` 0).
    const fn pen_cell(&self, ch: char, width: u8) -> Cell {
        Cell {
            ch,
            fg: self.pen.fg,
            bg: self.pen.bg,
            fg_rgb: self.pen.fg_rgb,
            bg_rgb: self.pen.bg_rgb,
            attrs: self.pen.attrs,
            underline: self.pen.underline,
            ul: self.pen.ul,
            ul_rgb: self.pen.ul_rgb,
            combining: ['\0'; MAX_COMBINING],
            combining_len: 0,
            width,
        }
    }

    /// Widen an `Emoji=Yes, Emoji_Presentation=No` narrow base cell (`width == 1`) to 2
    /// columns when `U+FE0F` (VS16) attaches (`Astream.Term.TlaVariationWidth::WidenVs16`),
    /// matching `aterm`'s `widen_previous_cell_for_vs16` and `GridColumns::step`.
    fn try_widen_vs16(&mut self) -> bool {
        if !self.has_active_base() || self.cols < 2 {
            return false;
        }
        let target_col = self.active_base_col();
        let row = self.row;
        let base_idx = self.idx(row, target_col);
        let Some(base_copy) = self.grid.get(base_idx).copied() else {
            return false;
        };
        let end = self.line_end(target_col);
        if base_copy.width != 1 || target_col >= end || !is_vs16_emoji_capable(base_copy.ch) {
            return false;
        }
        let widened_width = vs_width_clamp(2, 2) as u8;
        let spacer_col =
            wide_spacer_col_clamp(target_col.saturating_add(1) as u64, end as u64) as u16;
        self.split_at(row, spacer_col);
        self.split_at(row, spacer_col.saturating_add(1));
        let mut lead = base_copy;
        lead.width = widened_width;
        lead.push_combining('\u{FE0F}');
        if let Some(slot) = self.grid.get_mut(base_idx) {
            *slot = lead;
        }
        let spacer = Cell {
            ch: ' ',
            fg: base_copy.fg,
            bg: base_copy.bg,
            fg_rgb: base_copy.fg_rgb,
            bg_rgb: base_copy.bg_rgb,
            attrs: base_copy.attrs,
            underline: base_copy.underline,
            ul: base_copy.ul,
            ul_rgb: base_copy.ul_rgb,
            combining: ['\0'; MAX_COMBINING],
            combining_len: 0,
            width: 0,
        };
        let si = self.idx(row, spacer_col);
        if let Some(slot) = self.grid.get_mut(si) {
            *slot = spacer;
        }
        // A selector resolves no wrap. One pending here sits mid-line, the margin it was parked
        // on having gone (DECLRMM reset, a resize), and stays where it is, as aterm keeps it.
        if self.wrap_pending() {
        } else if spacer_col >= end {
            self.set_wrap_at(spacer_col);
        } else {
            self.col =
                vs_cursor_advance_clamp(spacer_col.saturating_add(1) as u64, end as u64) as u16;
            self.margin_wrap = false;
            self.note_print_end();
        }
        true
    }

    /// Narrow a wide base cell (`width == 2`) to 1 column when `U+FE0E` (VS15) attaches
    /// (`Astream.Term.TlaVariationWidth::NarrowVs15`), matching `aterm`'s
    /// `narrow_previous_cell_for_vs15` and `GridColumns::step`.
    fn try_narrow_vs15(&mut self) -> bool {
        if !self.has_active_base() {
            return false;
        }
        let target_col = self.active_base_col();
        let row = self.row;
        let base_idx = self.idx(row, target_col);
        let Some(base_copy) = self.grid.get(base_idx).copied() else {
            return false;
        };
        let end = self.line_end(target_col);
        if base_copy.width != 2 || target_col >= end {
            return false;
        }
        let narrowed_width = vs_width_clamp(1, 2) as u8;
        let mut lead = base_copy;
        lead.width = narrowed_width;
        lead.push_combining('\u{FE0E}');
        if let Some(slot) = self.grid.get_mut(base_idx) {
            *slot = lead;
        }
        let spacer_col =
            vs_cursor_advance_clamp(target_col.saturating_add(1) as u64, end as u64) as u16;
        if spacer_col < self.cols && self.width_at(row, spacer_col) == 0 {
            let si = self.idx(row, spacer_col);
            if let Some(slot) = self.grid.get_mut(si) {
                *slot = Cell::BLANK;
            }
        }
        true
    }

    /// Borrow one logical row; rotated storage can map the row once here.
    fn row_cells_mut(&mut self, row: u16) -> Option<&mut [Cell]> {
        let from = self.idx(row, 0);
        self.grid
            .span_mut(from, from.saturating_add(self.cols as usize))
    }

    /// Paint a printable GL-byte prefix within this row. ASCII cannot continue
    /// a grapheme cluster; DEC glyphs are narrow and can join only after a ZWJ.
    /// Every interior cell is fully overwritten, so only wide pairs crossing
    /// external boundaries need a surviving BCE blank. Wrap and insert mode
    /// retain scalar paths, as do DEC glyphs while a ZWJ join remains open.
    fn put_ascii_run<const DEC: bool>(&mut self, bytes: &[u8]) -> usize {
        if self.insert || self.wrap_pending() || (DEC && self.joiner_open) {
            return 0;
        }
        let col = self.col;
        let end = self.line_end(col);
        let available = end.saturating_sub(col).saturating_add(1) as usize;
        let count = bytes
            .iter()
            .take(available)
            .take_while(|&&b| (0x20..=0x7e).contains(&b))
            .count();
        if count < ASCII_SPAN_MIN {
            return 0;
        }
        let blank = self.bce_blank();
        let template = self.pen_cell(' ', 1);
        let start = col as usize;
        let stop = start.saturating_add(count);
        let Some(row) = self.row_cells_mut(self.row) else {
            return 0;
        };
        if start > 0 && row.get(start).is_some_and(|cell| cell.width == 0) {
            if let Some(cell) = row.get_mut(start - 1) {
                *cell = blank;
            }
        }
        if row.get(stop).is_some_and(|cell| cell.width == 0) {
            if let Some(cell) = row.get_mut(stop) {
                *cell = blank;
            }
        }
        let Some(span) = row.get_mut(start..stop) else {
            return 0;
        };
        for (cell, &b) in span.iter_mut().zip(bytes) {
            *cell = Cell {
                ch: if DEC {
                    dec_special_graphic(b)
                } else {
                    b as char
                },
                ..template
            };
        }
        self.joiner_open = false;
        let last = col.saturating_add(count as u16).saturating_sub(1);
        if last >= end {
            self.set_wrap_at(last);
        } else {
            self.col = last.saturating_add(1);
        }
        self.note_print_end();
        #[cfg(test)]
        ascii_work::record(count);
        count
    }

    fn put(&mut self, ch: char) {
        // Each codepoint measured alone; the clamp keeps a width the cells can
        // hold (`wide_island`).
        let width = wide_cell_width_clamp(char_display_width(ch) as u64, 2) as u8;
        if width == 0 {
            self.joiner_open = ch == '\u{200D}';
            if ch == '\u{FE0F}' && self.try_widen_vs16() {
                return;
            }
            if ch == '\u{FE0E}' && self.try_narrow_vs15() {
                return;
            }
            let target_col = self.active_base_col();
            let i = self.idx(self.row, target_col);
            if let Some(slot) = self.grid.get_mut(i) {
                slot.push_combining(ch);
            }
            return;
        }
        // A glyph that continues the grapheme cluster before it attaches to
        // that cell without advancing the cursor or resolving a pending wrap
        // ([`joins_cluster`]).
        let may_join = is_emoji_modifier(ch)
            || is_regional_indicator(ch)
            || (self.joiner_open && !ch.is_ascii());
        #[cfg(test)]
        let may_join = may_join || !scroll_work::enabled();
        if may_join && self.has_active_base() {
            let joiner_open = self.joiner_open;
            let base_idx = self.idx(self.row, self.active_base_col());
            if let Some(base) = self.grid.get_mut(base_idx) {
                if joins_cluster(base, ch, joiner_open) {
                    base.push_combining(ch);
                    return;
                }
            }
        }
        self.joiner_open = false;
        // Deferred wrap: a pending wrap resolves on the next glyph.
        if self.wrap_pending() {
            self.wrap_line();
        }
        let row = self.row;
        if width == 2 && self.cols < 2 {
            // A screen one column wide has no room for a wide glyph: it
            // prints as a narrow space in the pen, as aterm and Ghostty print
            // it (`printCell(0, .narrow)`). xterm's dotext gives up on the
            // glyph, and on any narrow glyph it read with it in the same pass.
            return self.put(' ');
        }
        if width == 2 && self.col >= self.line_end(self.col) {
            // One column left before the line end: that column takes the bce
            // blank and the glyph wraps onto the next line. xterm's dotext
            // forces the wrap and leaves the column as it was; aterm, Ghostty
            // (`spacer_head`) and Alacritty blank it.
            let col = self.col;
            self.split_at(row, col);
            self.split_at(row, col.saturating_add(1));
            let i = self.idx(row, col);
            let blank = self.bce_blank();
            if let Some(slot) = self.grid.get_mut(i) {
                *slot = blank;
            }
            self.wrap_line();
        }
        let columns = width as u16;
        if self.insert {
            // IRM: xterm's WriteText runs InsertChar for the glyph's columns
            // before it writes, so the line shifts right under the glyph and
            // what passes the right margin is lost. The shift's blanks are
            // overwritten at once, so their colour never shows.
            self.insert_chars(columns);
        }
        let row = self.row;
        let col = self.col;
        let end = self.line_end(col);
        #[cfg(test)]
        if !scroll_work::enabled() {
            self.place_glyph_at_points(row, col, end, ch, width);
        } else {
            self.place_glyph_in_row(row, col, end, ch, width);
        }
        #[cfg(not(test))]
        self.place_glyph_in_row(row, col, end, ch, width);
        // The next glyph goes to the right, or wraps once the line ends at
        // the glyph's last column.
        let last = col.saturating_add(columns.saturating_sub(1));
        if last >= end {
            self.set_wrap_at(last);
        } else {
            self.col = last.saturating_add(1);
        }
        self.note_print_end();
    }

    /// Complete a scalar write after wrapping and insert-mode shifting. Both
    /// wide-pair boundary repairs and the lead/spacer writes share one row map.
    fn place_glyph_in_row(&mut self, row: u16, col: u16, end: u16, ch: char, width: u8) {
        let lead = self.pen_cell(ch, width);
        let spacer = self.pen_cell(' ', 0);
        let blank = self.bce_blank();
        let Some(row) = self.row_cells_mut(row) else {
            return;
        };
        // Keep the same left-then-right repair order as split_at, including
        // orphan spacers installed through the public cell overlay API.
        for boundary in [col as usize, col.saturating_add(width as u16) as usize] {
            if boundary > 0 && row.get(boundary).is_some_and(|cell| cell.width == 0) {
                if let Some(pair) = row.get_mut(boundary - 1..=boundary) {
                    pair.fill(blank);
                }
            }
        }
        if let Some(slot) = row.get_mut(col as usize) {
            *slot = lead;
        }
        if width == 2 {
            let spacer_col = wide_spacer_col_clamp(col.saturating_add(1) as u64, end as u64);
            if let Some(slot) = row.get_mut(spacer_col as usize) {
                *slot = spacer;
            }
        }
    }

    // Retain the original point-placement sequence as an independent oracle.
    #[cfg(test)]
    fn place_glyph_at_points(&mut self, row: u16, col: u16, end: u16, ch: char, width: u8) {
        let columns = width as u16;
        // A wide glyph the write cuts into, on either side, goes whole.
        self.split_at(row, col);
        self.split_at(row, col.saturating_add(columns));
        let i = self.idx(row, col);
        let lead = self.pen_cell(ch, width);
        if let Some(slot) = self.grid.get_mut(i) {
            *slot = lead;
        }
        if width == 2 {
            // The glyph fits: `col < end` here, so the spacer lands on `col + 1`.
            let spacer_col = wide_spacer_col_clamp(col.saturating_add(1) as u64, end as u64) as u16;
            let spacer = self.pen_cell(' ', 0);
            let si = self.idx(row, spacer_col);
            if let Some(slot) = self.grid.get_mut(si) {
                *slot = spacer;
            }
        }
    }

    /// A print moved the cursor: onto the left margin past column 0 only from outside it, with
    /// the glyph it printed left of the cursor.
    const fn note_print_end(&mut self) {
        self.stepped_onto_margin = self.left > 0 && self.col == self.left;
    }

    /// xterm `WrapLine`: an index from the column the wrap was pending on
    /// (so the margins' test sees it), then the left margin.
    fn wrap_line(&mut self) {
        self.line_feed();
        self.col = self.left;
    }

    /// CR (xterm `CarriageReturn`): to the left margin from at or right of
    /// it, or under origin mode; to column 0 from left of it.
    const fn carriage_return(&mut self) {
        self.clear_pending_wrap();
        self.col = if self.origin || self.col >= self.left {
            self.left
        } else {
            0
        };
    }

    fn line_feed(&mut self) {
        // LF is a cursor-down: it resolves a pending wrap (xterm CursorDown),
        // so `abcd LF Z` on four columns puts Z on the last column of the next
        // row rather than wrapping a second time.
        self.clear_pending_wrap();
        if self.row == self.scroll_bottom {
            // At the bottom of the scrolling region the region scrolls up,
            // for a cursor within the left/right margins (xterm
            // `xtermIndex`); outside them this is `CursorDown`, which stops
            // at the bottom margin.
            if self.in_lr_margins(self.col) {
                self.scroll_up();
            }
        } else if self.row.saturating_add(1) < self.rows {
            self.row = self.row.saturating_add(1);
        }
    }

    /// Scroll the active region `[scroll_top, scroll_bottom]` up one line: the top
    /// row of the region is discarded and a blank row appears at its bottom. Rows
    /// outside the region are untouched. With the default full-screen region this
    /// is the ordinary full-screen scroll. The new row takes the current SGR
    /// background (xterm screen.c `ScrnClearLines` fills with `xtermColorPair`).
    fn scroll_up(&mut self) {
        self.shift_up(self.scroll_top, 1);
    }

    /// Copy row `src`'s span between the left and right margins onto row
    /// `dst`'s (the whole row without DECSLRM margins).
    #[inline]
    fn copy_span(&mut self, src: u16, dst: u16) {
        let from = self.idx(src, self.left);
        let to = self.idx(dst, self.left);
        let len = (self.right.saturating_sub(self.left) as usize).saturating_add(1);
        #[cfg(test)]
        scroll_work::moved(len);
        if len >= ROW_COPY_MIN && rotated_scroll_enabled() && self.grid.copy_span(from, to, len) {
            return;
        }
        self.copy_span_cells(from, to, len);
    }

    /// Original scalar copy, retained as the dense oracle and for ranges that
    /// are invalid, overlap, or do not fit contiguous physical slices.
    fn copy_span_cells(&mut self, from: usize, to: usize, len: usize) {
        let mut i = 0usize;
        while i < len {
            if let Some(&cell) = self.grid.get(from.saturating_add(i)) {
                if let Some(slot) = self.grid.get_mut(to.saturating_add(i)) {
                    *slot = cell;
                }
            }
            i = i.saturating_add(1);
        }
    }

    /// Fill row `row`'s span between the left and right margins with the bce
    /// blank.
    fn blank_span(&mut self, row: u16) {
        let at = self.idx(row, self.left);
        let len = (self.right.saturating_sub(self.left) as usize).saturating_add(1);
        self.fill(at, at.saturating_add(len));
    }

    /// Rows `[from, scroll_bottom]` move up `n` (`1 <= n <= scroll_bottom -
    /// from + 1`) between the left and right margins: the top `n` of them are
    /// discarded, `n` bce-blank rows appear at the bottom margin, and cells
    /// outside the margins stay (xterm scrolls the rectangle). The scroll
    /// (`from == scroll_top`) and DL (`from == row`).
    fn shift_up(&mut self, from: u16, n: u16) {
        // Zero-count typed ops keep the historical dense fallback (which blanks
        // the region); parsed CSI counts are normalized before they reach here.
        if n > 0
            && from == 0
            && self.scroll_bottom == self.rows.saturating_sub(1)
            && self.left == 0
            && self.right >= self.cols.saturating_sub(1)
            && rotated_scroll_enabled()
        {
            let cells = (n as usize)
                .saturating_mul(self.cols as usize)
                .min(self.grid.len());
            self.grid.rotate_up(cells);
            let from = self.grid.len().saturating_sub(cells);
            let blank = self.bce_blank();
            self.grid.fill(from, self.grid.len(), blank);
            return;
        }
        self.split_margins(from);
        let bottom = self.scroll_bottom;
        let mut r = from;
        while r <= bottom {
            let src = r.saturating_add(n);
            if src <= bottom && src > r {
                self.copy_span(src, r);
            } else {
                self.blank_span(r);
            }
            if r == u16::MAX {
                break;
            }
            r = r.saturating_add(1);
        }
    }

    /// Rows `[from, scroll_bottom]` move down `n` (`1 <= n <= scroll_bottom -
    /// from + 1`) between the left and right margins: the bottom `n` of them
    /// are discarded, `n` bce-blank rows open at `from`, and cells outside
    /// the margins stay. RI's reverse scroll (`from == scroll_top`) and IL
    /// (`from == row`).
    fn shift_down(&mut self, from: u16, n: u16) {
        if n > 0
            && from == 0
            && self.scroll_bottom == self.rows.saturating_sub(1)
            && self.left == 0
            && self.right >= self.cols.saturating_sub(1)
            && rotated_scroll_enabled()
        {
            let cells = (n as usize)
                .saturating_mul(self.cols as usize)
                .min(self.grid.len());
            self.grid.rotate_down(cells);
            let blank = self.bce_blank();
            self.grid.fill(0, cells, blank);
            return;
        }
        self.split_margins(from);
        let mut r = self.scroll_bottom;
        while r >= from {
            match r.checked_sub(n) {
                Some(src) if src >= from && src < r => self.copy_span(src, r),
                _ => self.blank_span(r),
            }
            if r == 0 {
                break;
            }
            r = r.saturating_sub(1);
        }
    }

    /// Before rows `[from, scroll_bottom]` move between left/right margins
    /// narrower than the screen, every wide glyph straddling one of them, which
    /// the move would split, becomes two narrow blanks that keep their
    /// renditions, as Ghostty's `rowWillBeShifted` clears them (xterm leaves
    /// the halves torn). Without such margins nothing straddles anything.
    fn split_margins(&mut self, from: u16) {
        if self.left == 0 && self.right >= self.cols.saturating_sub(1) {
            return;
        }
        let (left, right) = (self.left, self.right);
        let mut r = from;
        while r <= self.scroll_bottom {
            if left > 0 && self.width_at(r, left) == 0 {
                self.unpair(r, left.saturating_sub(1));
            }
            if self.width_at(r, right) == 2 {
                self.unpair(r, right);
            }
            if r == u16::MAX {
                break;
            }
            r = r.saturating_add(1);
        }
    }

    /// The wide glyph whose lead is at `(row, lead)` becomes two narrow blanks,
    /// each cell keeping its colours and attributes.
    fn unpair(&mut self, row: u16, lead: u16) {
        let i = self.idx(row, lead);
        self.grid.with_range_mut(i, i.saturating_add(2), |cells| {
            for cell in cells {
                cell.ch = ' ';
                cell.width = 1;
                cell.combining = ['\0'; MAX_COMBINING];
                cell.combining_len = 0;
            }
        });
    }

    /// RI (`ESC M`, xterm `RevIndex`): at the top margin, for a cursor within
    /// the left/right margins, the region scrolls down a line; anywhere else
    /// it is CUU 1 (which stops at the top margin from inside the region and
    /// at row 0 from above it). Either way the wrap resets.
    fn reverse_index(&mut self) {
        self.clear_pending_wrap();
        if self.row == self.scroll_top && self.in_lr_margins(self.col) {
            self.shift_down(self.scroll_top, 1);
        } else {
            self.cursor_up(1);
        }
    }

    /// ICH (xterm `InsertChar`): for a cursor within the left/right margins
    /// the wrap resets, `n` bce blanks open at the cursor and the rest of the
    /// line up to the right margin shifts right, what passes the margin
    /// lost. Outside the margins nothing changes, a pending wrap included
    /// (xterm returns before its `ResetWrap`). A wide glyph the shift would
    /// split goes whole first: one whose spacer is under the cursor, one whose
    /// spacer would pass the right margin, and one straddling that margin
    /// (xterm's `RepairInsertChar`; Ghostty's `insertBlanks`).
    fn insert_chars(&mut self, n: u16) {
        if !self.in_lr_margins(self.grid_col()) {
            return;
        }
        self.clear_pending_wrap();
        let n16 = n.min(self.right.saturating_sub(self.col).saturating_add(1));
        let row = self.row;
        self.split_at(row, self.col);
        self.split_at(row, self.right.saturating_sub(n16).saturating_add(1));
        self.split_at(row, self.right.saturating_add(1));
        let n = n16 as usize;
        let at = self.idx(self.row, self.col);
        let end = self
            .idx(self.row, self.right)
            .saturating_add(1)
            .min(self.grid.len());
        let src_end = end.saturating_sub(n).max(at);
        let dst_start = at.saturating_add(n).min(end);
        let copy_len = src_end.saturating_sub(at);
        let mut i = copy_len;
        while i > 0 {
            i = i.saturating_sub(1);
            if let Some(&cell) = self.grid.get(at.saturating_add(i)) {
                if let Some(dst) = self.grid.get_mut(dst_start.saturating_add(i)) {
                    *dst = cell;
                }
            }
        }
        let blank = self.bce_blank();
        self.grid.fill(at, dst_start, blank);
    }

    /// DCH (xterm `DeleteChar`): for a cursor within the left/right margins
    /// the wrap resets, `n` cells go at the cursor, the rest of the line up
    /// to the right margin shifts left, and `n` bce blanks fill in at the
    /// margin. Outside the margins nothing changes, a pending wrap included.
    /// A wide glyph the deletion would split goes whole first: at the cursor,
    /// at the end of the deleted run and at the right margin (Ghostty's
    /// `deleteChars`; xterm's `DamagedCurCells` repair).
    fn delete_chars(&mut self, n: u16) {
        if !self.in_lr_margins(self.grid_col()) {
            return;
        }
        self.clear_pending_wrap();
        let n16 = n.min(self.right.saturating_sub(self.col).saturating_add(1));
        let row = self.row;
        self.split_at(row, self.col);
        self.split_at(row, self.col.saturating_add(n16));
        self.split_at(row, self.right.saturating_add(1));
        let n = n16 as usize;
        let at = self.idx(self.row, self.col);
        let end = self
            .idx(self.row, self.right)
            .saturating_add(1)
            .min(self.grid.len());
        let src_start = at.saturating_add(n).min(end);
        let copy_len = end.saturating_sub(src_start);
        let mut i = 0usize;
        while i < copy_len {
            if let Some(&cell) = self.grid.get(src_start.saturating_add(i)) {
                if let Some(dst) = self.grid.get_mut(at.saturating_add(i)) {
                    *dst = cell;
                }
            }
            i = i.saturating_add(1);
        }
        let blank = self.bce_blank();
        let fill_start = end.saturating_sub(n).max(at);
        self.grid.fill(fill_start, end, blank);
    }

    /// ECH (xterm `do_erase_char` -> `ClearRight(n)`): `n` cells from the
    /// cursor (the parked glyph, from a pending wrap) take the bce blank, and
    /// so does all of a wide glyph the run cuts into (xterm `ClearRight`'s
    /// repair, Ghostty's `eraseChars`).
    fn erase_chars(&mut self, n: u16) {
        self.clear_pending_wrap();
        let n16 = n.min(self.cols.saturating_sub(self.col));
        let row = self.row;
        self.split_at(row, self.col);
        self.split_at(row, self.col.saturating_add(n16));
        let n = n16 as usize;
        let at = self.idx(self.row, self.col);
        self.fill(at, at.saturating_add(n));
    }

    /// IL / DL (xterm `InsertLine`/`DeleteLine`): nothing outside the
    /// scrolling region or the left/right margins (and the wrap stays);
    /// inside both, the cursor goes to the left margin (resolving any wrap)
    /// and `n` lines open (IL) or close (DL) at its row between the margins,
    /// bounded by the bottom margin.
    fn insert_lines(&mut self, n: u16, insert: bool) {
        if self.row < self.scroll_top
            || self.row > self.scroll_bottom
            || !self.in_lr_margins(self.grid_col())
        {
            return;
        }
        self.margin_wrap = false;
        self.stepped_onto_margin = false;
        self.col = self.left;
        let n = n.min(
            self.scroll_bottom
                .saturating_sub(self.row)
                .saturating_add(1),
        );
        if insert {
            self.shift_down(self.row, n);
        } else {
            self.shift_up(self.row, n);
        }
    }

    /// `DECSTBM`: set the scrolling region to 0-based inclusive `[top, bottom]`
    /// and home the cursor (to the new top margin under origin mode: xterm's
    /// `CursorSet(screen, 0, 0, xw->flags)`). As in xterm's `CASE_DECSTBM`, a
    /// `bottom` past the screen means the last row, and a region that is empty
    /// after that clamp (`top >= bottom`) is ignored entirely: neither the
    /// margins nor the cursor change.
    const fn set_scroll_region(&mut self, top: u16, bottom: u16) {
        let last_row = self.rows.saturating_sub(1);
        let bottom = if bottom < last_row { bottom } else { last_row };
        if top < bottom {
            self.scroll_top = top;
            self.scroll_bottom = bottom;
            self.home();
        }
    }

    /// xterm's `CursorSet(screen, 0, 0, xw->flags)`: the top-left corner, or
    /// the corner of the margins under origin mode. Resolves a wrap.
    const fn home(&mut self) {
        self.margin_wrap = false;
        self.stepped_onto_margin = false;
        if self.origin {
            self.row = self.scroll_top;
            self.col = self.left;
        } else {
            self.row = 0;
            self.col = 0;
        }
    }

    /// DECSLRM (`CSI Pl ; Pr s` under DECLRMM, xterm `CASE_DECSLRM`): with
    /// `left < right` (0-based, `right` already clamped to the screen) set
    /// the left and right margins and home the cursor; otherwise nothing.
    const fn set_lr_margins(&mut self, left: u16, right: u16) {
        let last_col = self.cols.saturating_sub(1);
        let right = if right < last_col { right } else { last_col };
        if left < right {
            self.left = left;
            self.right = right;
            self.home();
        }
    }

    /// The absolute column of column `rel` as cursor addressing counts it:
    /// from the left margin and stopping at the right one under origin mode
    /// (xterm `CursorSet`), from column 0 otherwise (where
    /// [`Self::move_to`] clamps it to the screen).
    const fn addressed_col(&self, rel: u16) -> u16 {
        if self.origin {
            let col = self.left.saturating_add(rel);
            if col < self.right {
                col
            } else {
                self.right
            }
        } else {
            rel
        }
    }

    /// The cursor's column as an addressing column: xterm's `CursorCol`,
    /// counted from the left margin under origin mode and never below 0.
    const fn cursor_col_addressed(&self) -> u16 {
        if self.origin {
            self.grid_col().saturating_sub(self.left)
        } else {
            self.grid_col()
        }
    }

    /// The absolute row of row `rel` counted as cursor addressing counts it:
    /// from the top margin and stopping at the bottom one under origin mode
    /// (xterm `CursorSet`), from row 0 otherwise (where [`Self::move_to`]
    /// clamps it to the screen).
    const fn addressed_row(&self, rel: u16) -> u16 {
        if self.origin {
            let row = self.scroll_top.saturating_add(rel);
            if row < self.scroll_bottom {
                row
            } else {
                self.scroll_bottom
            }
        } else {
            rel
        }
    }

    /// The cursor's row as an addressing row: xterm's `CursorRow`, counted
    /// from the top margin under origin mode and never below 0.
    const fn cursor_row_addressed(&self) -> u16 {
        if self.origin {
            self.row.saturating_sub(self.scroll_top)
        } else {
            self.row
        }
    }

    /// SU (xterm `xtermScroll`): the region scrolls up `n` lines, bce blanks
    /// entering at its bottom. The cursor stays, and so does a pending wrap.
    fn scroll_up_lines(&mut self, n: u16) {
        let height = self
            .scroll_bottom
            .saturating_sub(self.scroll_top)
            .saturating_add(1);
        self.shift_up(self.scroll_top, n.min(height));
    }

    /// SD (xterm `RevScroll`): the region scrolls down `n` lines, bce blanks
    /// entering at its top. The cursor stays, and so does a pending wrap.
    fn scroll_down_lines(&mut self, n: u16) {
        let height = self
            .scroll_bottom
            .saturating_sub(self.scroll_top)
            .saturating_add(1);
        self.shift_down(self.scroll_top, n.min(height));
    }

    const fn tab(&mut self) {
        self.stepped_onto_margin = false;
        // Advance to the next 8-column tab stop, not past the line's end: the
        // right margin, or the screen's edge for a cursor already past it (as
        // aterm and Ghostty; xterm's TabToNextStop pulls such a cursor back
        // onto the margin, a backward tab this fold does not make).
        let col = self.grid_col();
        let next = (col / 8).saturating_add(1).saturating_mul(8);
        let end = self.line_end(col);
        let to = if next < end { next } else { end };
        // A pending wrap survives a TAB (xterm's TabToNextStop never touches the
        // last-column flag): the next glyph still wraps, from wherever the tab
        // left the cursor. On a line end the tab goes nowhere; a wrap left
        // short of one (on a right margin a DECLRMM reset or a DECSLRM moved
        // aside) rides it to the next stop.
        if self.wrap_pending() {
            if to > col {
                self.set_wrap_at(to);
            }
            return;
        }
        self.col = to;
    }

    const fn backspace(&mut self) {
        // From a pending wrap the cursor is ON the last column (xterm), so BS
        // lands on the second-to-last: `abcde BS X` is `abcXe`, never `abcdX`.
        self.cursor_back(1);
    }

    const fn move_to(&mut self, row: u16, col: u16) {
        let last_row = self.rows.saturating_sub(1);
        let last_col = self.cols.saturating_sub(1);
        self.margin_wrap = false;
        self.stepped_onto_margin = false;
        self.row = if row < last_row { row } else { last_row };
        self.col = if col < last_col { col } else { last_col };
    }

    /// CUU. As in xterm's `CursorUp`, a cursor at or below the top margin stops
    /// at it; one above the region may go to row 0.
    const fn cursor_up(&mut self, n: u16) {
        self.clear_pending_wrap();
        let min = if self.row >= self.scroll_top {
            self.scroll_top
        } else {
            0
        };
        let sub = self.row.saturating_sub(n);
        self.row = if sub > min { sub } else { min };
    }

    /// CUD. As in xterm's `CursorDown`, a cursor at or above the bottom margin
    /// stops at it; one below the region may go to the last row.
    const fn cursor_down(&mut self, n: u16) {
        self.clear_pending_wrap();
        let max = if self.row <= self.scroll_bottom {
            self.scroll_bottom
        } else {
            self.rows.saturating_sub(1)
        };
        // saturating_add: a CSI param up to 65535 must not overflow u16.
        let add = self.row.saturating_add(n);
        self.row = if add < max { add } else { max };
    }

    /// CUF (xterm `CursorForward`): stops at the right margin, or at the
    /// screen's edge for a cursor already past it.
    const fn cursor_forward(&mut self, n: u16) {
        self.clear_pending_wrap();
        let add = self.col.saturating_add(n);
        let end = self.line_end(self.col);
        self.col = if add < end { add } else { end };
    }

    /// CUB and BS (xterm `CursorBack`): resolve a pending wrap onto its
    /// column, then move left, stopping at the left margin, or at column 0
    /// for a cursor already left of it ("we have to let it go").
    const fn cursor_back(&mut self, n: u16) {
        self.clear_pending_wrap();
        let stop = if self.col >= self.left { self.left } else { 0 };
        let sub = self.col.saturating_sub(n);
        self.col = if sub > stop { sub } else { stop };
    }

    /// The grid index erase-to-end starts at, and the one erase-to-cursor ends
    /// before: the cursor cell, inclusive both ways. Called after the pending
    /// wrap is resolved, so a parked glyph is the cursor cell and is erased
    /// either way (xterm `ClearRight` clears from `cur_col`, `ClearLeft`
    /// through it).
    const fn erase_bounds(&self) -> (usize, usize) {
        let at = self.idx(self.row, self.col);
        (at, at.saturating_add(1))
    }

    /// An erase from the cursor to the end (`mode` 0) or from the start
    /// through the cursor (1) on the cursor's row cuts the row at the
    /// cursor: a wide glyph it cuts into is erased whole (xterm's
    /// `ClearRight` and `ClearLeft` repair the `DamagedCurCells`).
    fn split_for_erase(&mut self, mode: u16) {
        let (row, col) = (self.row, self.col);
        match mode {
            0 => self.split_at(row, col),
            1 => self.split_at(row, col.saturating_add(1)),
            _ => {}
        }
    }

    fn erase_display(&mut self, mode: u16) {
        if mode > 2 {
            // `ED 3` erases saved lines, and there are none; any other
            // parameter is ignored. Neither resets the wrap (xterm
            // `do_erase_display` has no `ResetWrap` outside cases 0-2).
            return;
        }
        self.clear_pending_wrap();
        self.split_for_erase(mode);
        let (from_cursor, through_cursor) = self.erase_bounds();
        let last = self.grid.len();
        match mode {
            0 => self.fill(from_cursor, last), // cursor to end
            1 => self.fill(0, through_cursor), // start to cursor (inclusive)
            _ => self.fill(0, last),           // entire display
        }
    }

    fn erase_line(&mut self, mode: u16) {
        if mode > 2 {
            return;
        }
        self.clear_pending_wrap();
        self.split_for_erase(mode);
        let start = self.idx(self.row, 0);
        let end = start.saturating_add(self.cols as usize);
        let (from_cursor, through_cursor) = self.erase_bounds();
        match mode {
            0 => self.fill(from_cursor, end),      // cursor to end of line
            1 => self.fill(start, through_cursor), // start of line to cursor
            _ => self.fill(start, end),            // whole line
        }
    }

    /// An erased cell under background-colour-erase (`bce`): a space carrying the
    /// **current SGR background** (including 24-bit `bg_rgb`), so `ED`/`EL` after
    /// `\x1b[44m` or `\x1b[48;2;r;g;bm` paints that background, not a hardcoded
    /// default blank. It carries no attribute and no underline, colour included.
    /// (Reverse-video bce is out of scope.)
    const fn bce_blank(&self) -> Cell {
        Cell {
            ch: ' ',
            fg: Color::Default,
            bg: self.pen.bg,
            fg_rgb: None,
            bg_rgb: self.pen.bg_rgb,
            attrs: 0,
            underline: Underline::None,
            ul: Color::Default,
            ul_rgb: None,
            combining: ['\0'; MAX_COMBINING],
            combining_len: 0,
            width: 1,
        }
    }

    fn fill(&mut self, from: usize, to: usize) {
        let blank = self.bce_blank();
        let to = to.min(self.grid.len());
        self.grid.fill(from, to, blank);
    }

    /// Apply an SGR parameter list. `sub[i]` marks `params[i]` as a `:`
    /// sub-parameter of the preceding parameter (`38:5:196`, `38:2::r:g:b`) rather than a
    /// `;`-separated parameter of its own; a colon group is handled as one unit, and a
    /// sub-parameter is never a code: one a semicolon colour's values stopped short of
    /// (`38;5;9:4`) is skipped, where xterm runs it as a code. An empty last element is an
    /// element (`38:2:cs:r:g:` has a blue of 0, as in xterm's `CASE_ESC_COLON`), and aterm's
    /// parser delivers it alike.
    ///
    /// **One rule for 38, 48 and 58, aterm's `handle_sgr_with_subparams` too.** A colon on
    /// the code or on the selector makes a group that is all the colour's (`38:2:…`,
    /// `38;2:…`: "after the first colon, colons must be used", xterm's ctlseqs), and the
    /// group is read by [`parse_colon_colour`]. Otherwise it is all semicolons, read by
    /// [`parse_extended`].
    fn sgr(&mut self, params: &[u16], sub: &[bool]) {
        if params.is_empty() {
            self.pen = Pen::reset();
            return;
        }
        let mut i = 0;
        while let Some(&param) = params.get(i) {
            let end = colon_group_end(sub, i, params.len());
            if matches!(sub.get(i), Some(&true)) {
                i = end;
                continue;
            }
            if end > i.saturating_add(1) {
                if let Some(group) = params.get(i..end) {
                    self.sgr_colon(group);
                }
                i = end;
                continue;
            }
            match param {
                0 => self.pen = Pen::reset(),
                1 => self.pen.attrs |= attr::BOLD,
                3 => self.pen.attrs |= attr::ITALIC,
                4 => self.pen.underline = Underline::Single,
                // xterm's CASE_SGR: 5 (slow) and 6 (rapid) both set BLINK.
                5 | 6 => self.pen.attrs |= attr::BLINK,
                7 => self.pen.attrs |= attr::REVERSE,
                8 => self.pen.attrs |= attr::CONCEAL,
                9 => self.pen.attrs |= attr::STRIKE,
                // The double underline (xterm `ATR_DBL_UNDER`).
                21 => self.pen.underline = Underline::Double,
                22 => self.pen.attrs &= !attr::BOLD,
                23 => self.pen.attrs &= !attr::ITALIC,
                24 => self.pen.underline = Underline::None,
                25 => self.pen.attrs &= !attr::BLINK,
                27 => self.pen.attrs &= !attr::REVERSE,
                28 => self.pen.attrs &= !attr::CONCEAL,
                29 => self.pen.attrs &= !attr::STRIKE,
                30..=37 => self.pen.set_fg_color(sgr_fg_std(param)),
                39 => self.pen.set_fg_color(Color::Default),
                40..=47 => self.pen.set_bg_color(sgr_bg_std(param)),
                49 => self.pen.set_bg_color(Color::Default),
                90..=97 => self.pen.set_fg_color(sgr_fg_bright(param)),
                100..=107 => self.pen.set_bg_color(sgr_bg_bright(param)),
                38 => match parse_extended(params, sub, &mut i) {
                    Some(ExtendedColor::Palette(idx)) => self.pen.set_fg_color(Color::Indexed(idx)),
                    Some(ExtendedColor::Rgb(r, g, b)) => self.pen.set_fg_rgb(r, g, b),
                    None => {}
                },
                48 => match parse_extended(params, sub, &mut i) {
                    Some(ExtendedColor::Palette(idx)) => self.pen.set_bg_color(Color::Indexed(idx)),
                    Some(ExtendedColor::Rgb(r, g, b)) => self.pen.set_bg_rgb(r, g, b),
                    None => {}
                },
                58 => match parse_extended(params, sub, &mut i) {
                    Some(ExtendedColor::Palette(idx)) => self.pen.set_ul_color(Color::Indexed(idx)),
                    Some(ExtendedColor::Rgb(r, g, b)) => self.pen.set_ul_rgb(r, g, b),
                    None => {}
                },
                59 => self.pen.set_ul_color(Color::Default),
                _ => {}
            }
            i = i.saturating_add(1);
        }
    }

    /// One colon group: `g[0]` is the code, `g[1..]` its sub-parameters.
    const fn sgr_colon(&mut self, g: &[u16]) {
        let &[code, ref tail @ ..] = g else {
            return;
        };
        match code {
            // `4:n`: the style `n` names (`4:0` none); what follows `n` is nothing.
            4 => {
                if let &[n, ..] = tail {
                    self.pen.underline = Underline::from_sgr(n);
                }
            }
            38 => match parse_colon_colour(tail) {
                Some(ExtendedColor::Palette(idx)) => self.pen.set_fg_color(Color::Indexed(idx)),
                Some(ExtendedColor::Rgb(r, g, b)) => self.pen.set_fg_rgb(r, g, b),
                None => {}
            },
            48 => match parse_colon_colour(tail) {
                Some(ExtendedColor::Palette(idx)) => self.pen.set_bg_color(Color::Indexed(idx)),
                Some(ExtendedColor::Rgb(r, g, b)) => self.pen.set_bg_rgb(r, g, b),
                None => {}
            },
            58 => match parse_colon_colour(tail) {
                Some(ExtendedColor::Palette(idx)) => self.pen.set_ul_color(Color::Indexed(idx)),
                Some(ExtendedColor::Rgb(r, g, b)) => self.pen.set_ul_rgb(r, g, b),
                None => {}
            },
            _ => {} // any other sub-parameterised code
        }
    }

    fn set_mode(&mut self, params: &[u16], set: bool) {
        for &p in params {
            match p {
                1 => self.app_cursor_keys = set,
                25 => self.cursor_visible = set,
                // DECOM: either way the cursor homes (xterm `srm_DECOM` runs
                // `CursorSet(screen, 0, 0, xw->flags)` with the new flag).
                6 => {
                    self.origin = set;
                    self.home();
                }
                // DECLRMM (xterm `srm_DECLRMM`): resetting it puts the
                // margins back to the full width; the cursor stays.
                69 => {
                    self.lrmm = set;
                    if !set {
                        self.left = 0;
                        self.right = self.cols.saturating_sub(1);
                    }
                }
                1004 => self.focus_events = set,
                2004 => self.bracketed_paste = set,
                2026 => self.synchronized_output = set,
                // `?1049` is DECSC + switch + clear on set, switch + DECRC on reset
                // (xterm `srm_OPT_ALTBUF_CURSOR`), each half unconditional but the
                // switch: a second set clears again, a stray reset still restores.
                // The save goes to the SAME per-buffer slot DECSC uses, so a later
                // bare `ESC 8` on the main screen restores what `?1049h` saved.
                1049 => {
                    if set {
                        self.save_cursor();
                        self.enter_alt();
                        self.clear_screen();
                    } else {
                        self.leave_alt();
                        self.restore_cursor();
                    }
                }
                // `?1047` clears the alternate buffer on the way out, if it is up
                // (xterm `srm_OPT_ALTBUF`); `?47` only switches (`srm_ALTBUF`).
                // The cursor is shared and stays.
                1047 => {
                    if set {
                        self.enter_alt();
                    } else {
                        if self.altscreen {
                            self.clear_screen();
                        }
                        self.leave_alt();
                    }
                }
                47 => {
                    if set {
                        self.enter_alt();
                    } else {
                        self.leave_alt();
                    }
                }
                _ => {}
            }
        }
    }

    /// SCS: put `charset` in G1 (`g1`) or G0.
    const fn designate(&mut self, g1: bool, charset: Charset) {
        if g1 {
            self.charsets.g1 = charset;
        } else {
            self.charsets.g0 = charset;
        }
    }

    /// SM/RM (`CSI Pm h`/`l`, no private marker): the ANSI modes. IRM (4) and
    /// LNM (20) are modelled; the rest are consumed.
    fn set_ansi_mode(&mut self, params: &[u16], set: bool) {
        for &p in params {
            match p {
                4 => self.insert = set,
                20 => self.newline = set,
                _ => {}
            }
        }
    }

    /// Swap the alternate buffer onto the screen (xterm `ToAlternate`): the one
    /// a previous visit left, or a blank one on the first visit.
    fn enter_alt(&mut self) {
        if self.altscreen {
            return;
        }
        let alt = match self.inactive.take() {
            Some(grid) => grid,
            None => blank_grid(self.cols, self.rows),
        };
        self.inactive = Some(std::mem::replace(&mut self.grid, alt));
        self.altscreen = true;
        self.stepped_onto_margin = false;
    }

    /// Swap the main buffer back (xterm `FromAlternate`), keeping the alternate
    /// one for the next visit.
    fn leave_alt(&mut self) {
        if !self.altscreen {
            return;
        }
        if let Some(main) = self.inactive.take() {
            self.inactive = Some(std::mem::replace(&mut self.grid, main));
        }
        self.altscreen = false;
        self.stepped_onto_margin = false;
    }

    /// xterm's `ClearScreen` (util.c): reset the pending wrap and fill the
    /// whole active grid with the bce blank. The cursor does not move.
    fn clear_screen(&mut self) {
        self.clear_pending_wrap();
        let last = self.grid.len();
        self.fill(0, last);
    }

    /// DECSC: save the cursor and the pen into the active buffer's slot (one
    /// per buffer, as xterm) — a save inside the alternate screen never
    /// clobbers the main slot.
    const fn save_cursor(&mut self) {
        let saved = SavedCursor {
            row: self.row,
            col: self.col,
            pen: self.pen,
            origin: self.origin,
            charsets: self.charsets,
            margin_wrap: self.margin_wrap,
        };
        let slot = if self.altscreen {
            &mut self.alt_saved_cursor
        } else {
            &mut self.saved_cursor
        };
        *slot = Some(saved);
    }

    /// DECRC: restore the cursor, the pen and origin mode from the active
    /// buffer's slot without consuming it (a saved pending wrap is kept). With
    /// nothing saved the cursor homes, the pen resets and origin mode is off,
    /// per DEC STD 070 and xterm (whose `CursorRestore` then reads a zeroed
    /// `SavedCursor`). The position goes through `CursorSet` under the
    /// restored flags, the row given relative to the top margin under origin
    /// mode: xterm adds the margin back and clamps the sum to `[0, bottom
    /// margin]`, so a row saved above the region stays where it was.
    const fn restore_cursor(&mut self) {
        let slot = if self.altscreen {
            self.alt_saved_cursor
        } else {
            self.saved_cursor
        };
        let saved = match slot {
            Some(s) => s,
            None => SavedCursor {
                row: 0,
                col: 0,
                pen: Pen::reset(),
                origin: false,
                charsets: Charsets {
                    g0: Charset::Ascii,
                    g1: Charset::Ascii,
                    shifted: false,
                },
                margin_wrap: false,
            },
        };
        self.origin = saved.origin;
        self.charsets = saved.charsets;
        let last_row = if saved.origin {
            self.scroll_bottom
        } else {
            self.rows.saturating_sub(1)
        };
        self.row = if saved.row < last_row {
            saved.row
        } else {
            last_row
        };
        // The column the same way: under origin mode it stops at the right
        // margin. Then xterm puts back the saved wrap flag (`do_wrap =
        // sc->wrap_flag`) wherever the column landed.
        let last_col = if saved.origin {
            self.right
        } else {
            self.cols.saturating_sub(1)
        };
        let saved_col = if saved.col < last_col {
            saved.col
        } else {
            last_col
        };
        self.col = saved_col;
        self.margin_wrap = false;
        self.stepped_onto_margin = false;
        if saved.col >= self.cols || saved.margin_wrap {
            self.set_wrap_at(saved_col);
        }
        self.pen = saved.pen;
    }

    /// RIS, as xterm's full `ReallyReset` (charproc.c): the SGR colours reset,
    /// then `FromAlternate(xw, True)` clears the alternate buffer if it is up and
    /// leaves it, `ClearScreen` clears the main one, and the cursor is homed and
    /// saved into the main slot (`CursorSave`, `sc[0]`: home and the reset pen,
    /// which a restore of an empty slot gives too). The alternate buffer and its
    /// DECSC slot (`sc[1]`) SURVIVE: nothing in the reset frees one or touches
    /// the other, so a `?47h` after a RIS on the main screen shows what the last
    /// visit left, and a DECRC there restores what it saved.
    fn reset(&mut self) {
        let (cols, rows) = (self.cols, self.rows);
        let alt = if self.altscreen {
            // `grid` is the alternate buffer: `FromAlternate`'s clear, in the
            // colours the reset has already put back.
            Some(blank_grid(cols, rows))
        } else {
            self.inactive.take()
        };
        let alt_saved_cursor = self.alt_saved_cursor;
        *self = Screen::new(cols, rows);
        self.inactive = alt;
        self.alt_saved_cursor = alt_saved_cursor;
    }

    fn resize(&mut self, cols: u16, rows: u16) {
        let cols = cols.clamp(1, MAX_DIM);
        let rows = rows.clamp(1, MAX_DIM);
        self.grid = reflow(&self.grid, self.cols, self.rows, cols, rows);
        if let Some(other) = &self.inactive {
            self.inactive = Some(reflow(other, self.cols, self.rows, cols, rows));
        }
        let edge_wrap = self.col >= self.cols;
        self.cols = cols;
        self.rows = rows;
        self.row = self.row.min(rows.saturating_sub(1));
        if self.margin_wrap {
            // A wrap pending short of the old edge stays on its column,
            // clipped to the new width.
            self.margin_wrap = false;
            self.set_wrap_at(self.col.min(cols.saturating_sub(1)));
        } else if edge_wrap {
            // A wrap pending at the edge (`col == cols`): its next write is
            // the column after the glyph, which a widening has room for and a
            // narrowing leaves waiting on the new edge.
            self.col = self.col.min(cols);
        } else {
            // The cursor's own cell, cut off by a narrowing: clamped onto the
            // last column with no wrap, as xterm clamps it.
            self.col = self.col.min(cols.saturating_sub(1));
        }
        // A resize invalidates the scrolling region and the left/right
        // margins: reset them to the full screen.
        self.scroll_top = 0;
        self.scroll_bottom = rows.saturating_sub(1);
        self.left = 0;
        self.right = cols.saturating_sub(1);
        self.stepped_onto_margin = false;
    }
}

/// Encode the 10-byte screen header `(cols, rows, row, col, cursor_visible, altscreen)`.
#[must_use]
pub const fn encode_screen_header(
    cols: u16,
    rows: u16,
    row: u16,
    col: u16,
    cursor_visible: bool,
    altscreen: bool,
) -> [u8; 10] {
    [
        cols as u8,
        (cols >> 8) as u8,
        rows as u8,
        (rows >> 8) as u8,
        row as u8,
        (row >> 8) as u8,
        col as u8,
        (col >> 8) as u8,
        cursor_visible as u8,
        altscreen as u8,
    ]
}

/// Decode a 10-byte screen header into `(cols, rows, row, col, cursor_visible, altscreen)`.
#[must_use]
pub const fn decode_screen_header(raw: &[u8; 10]) -> (u16, u16, u16, u16, bool, bool) {
    let cols = (raw[0] as u16) | ((raw[1] as u16) << 8);
    let rows = (raw[2] as u16) | ((raw[3] as u16) << 8);
    let row = (raw[4] as u16) | ((raw[5] as u16) << 8);
    let col = (raw[6] as u16) | ((raw[7] as u16) << 8);
    let cursor_visible = raw[8] != 0;
    let altscreen = raw[9] != 0;
    (cols, rows, row, col, cursor_visible, altscreen)
}

/// Encode one [`Cell`] into its 9-byte canonical screen serialization: its last byte
/// is the attribute byte with [`WIRE_UNDERLINE`] set for an underline of any style.
#[must_use]
pub const fn encode_cell_bytes(cell: &Cell) -> [u8; 9] {
    let cp = cell.ch as u32;
    let (ft, fv) = match cell.fg {
        Color::Default => (0u8, 0u8),
        Color::Indexed(n) => (1u8, n),
    };
    let (bt, bv) = match cell.bg {
        Color::Default => (0u8, 0u8),
        Color::Indexed(n) => (1u8, n),
    };
    [
        cp as u8,
        (cp >> 8) as u8,
        (cp >> 16) as u8,
        (cp >> 24) as u8,
        ft,
        fv,
        bt,
        bv,
        wire_attrs(cell.attrs, cell.underline),
    ]
}

/// Decode a 9-byte canonical cell record into `(codepoint, fg, bg, attrs)`.
#[must_use]
pub const fn decode_cell_bytes(raw: &[u8; 9]) -> (u32, Color, Color, u8) {
    let cp = (raw[0] as u32)
        | ((raw[1] as u32) << 8)
        | ((raw[2] as u32) << 16)
        | ((raw[3] as u32) << 24);
    let fg = if raw[4] == 0 {
        Color::Default
    } else {
        Color::Indexed(raw[5])
    };
    let bg = if raw[6] == 0 {
        Color::Default
    } else {
        Color::Indexed(raw[7])
    };
    (cp, fg, bg, raw[8])
}

/// Encode the 5-byte pen state `(fg, bg, attrs)`.
#[must_use]
pub const fn encode_pen_bytes(fg: Color, bg: Color, attrs: u8) -> [u8; 5] {
    let (ft, fv) = match fg {
        Color::Default => (0u8, 0u8),
        Color::Indexed(n) => (1u8, n),
    };
    let (bt, bv) = match bg {
        Color::Default => (0u8, 0u8),
        Color::Indexed(n) => (1u8, n),
    };
    [ft, fv, bt, bv, attrs]
}

/// Decode a 5-byte pen state into `(fg, bg, attrs)`.
#[must_use]
pub const fn decode_pen_bytes(raw: &[u8; 5]) -> (Color, Color, u8) {
    let fg = if raw[0] == 0 {
        Color::Default
    } else {
        Color::Indexed(raw[1])
    };
    let bg = if raw[2] == 0 {
        Color::Default
    } else {
        Color::Indexed(raw[3])
    };
    (fg, bg, raw[4])
}

/// Encode an active saved-cursor slot into its 10-byte serialization (`1 || row || col || pen`).
#[must_use]
pub const fn encode_saved_cursor_bytes(
    row: u16,
    col: u16,
    fg: Color,
    bg: Color,
    attrs: u8,
) -> [u8; 10] {
    let (ft, fv) = match fg {
        Color::Default => (0u8, 0u8),
        Color::Indexed(n) => (1u8, n),
    };
    let (bt, bv) = match bg {
        Color::Default => (0u8, 0u8),
        Color::Indexed(n) => (1u8, n),
    };
    [
        1,
        row as u8,
        (row >> 8) as u8,
        col as u8,
        (col >> 8) as u8,
        ft,
        fv,
        bt,
        bv,
        attrs,
    ]
}

/// Decode a 10-byte saved-cursor slot into `(present, row, col, fg, bg, attrs)`.
#[must_use]
pub const fn decode_saved_cursor_bytes(raw: &[u8; 10]) -> (bool, u16, u16, Color, Color, u8) {
    let present = raw[0] != 0;
    let row = (raw[1] as u16) | ((raw[2] as u16) << 8);
    let col = (raw[3] as u16) | ((raw[4] as u16) << 8);
    let fg = if raw[5] == 0 {
        Color::Default
    } else {
        Color::Indexed(raw[6])
    };
    let bg = if raw[7] == 0 {
        Color::Default
    } else {
        Color::Indexed(raw[8])
    };
    (present, row, col, fg, bg, raw[9])
}

/// Encode the 4-byte scroll region `(scroll_top, scroll_bottom)`.
#[must_use]
pub const fn encode_scroll_region_bytes(scroll_top: u16, scroll_bottom: u16) -> [u8; 4] {
    [
        scroll_top as u8,
        (scroll_top >> 8) as u8,
        scroll_bottom as u8,
        (scroll_bottom >> 8) as u8,
    ]
}

/// Decode a 4-byte scroll region into `(scroll_top, scroll_bottom)`.
#[must_use]
pub const fn decode_scroll_region_bytes(raw: &[u8; 4]) -> (u16, u16) {
    let top = (raw[0] as u16) | ((raw[1] as u16) << 8);
    let bottom = (raw[2] as u16) | ((raw[3] as u16) << 8);
    (top, bottom)
}

/// Encode the modes the fold gained after its encoding was fixed. `now` is
/// origin, insert, newline and left/right margin mode, then a wrap pending
/// short of the last column; `main` and `alt` are origin mode and such a
/// wrap as each DECSC slot saved them (`false` for an empty slot).
#[must_use]
pub const fn encode_modes_bytes(now: [bool; 5], main: [bool; 2], alt: [bool; 2]) -> [u8; 2] {
    let [origin, insert, newline, lrmm, margin_wrap] = now;
    [
        (origin as u8)
            | ((insert as u8) << 1)
            | ((newline as u8) << 2)
            | ((lrmm as u8) << 3)
            | ((margin_wrap as u8) << 4),
        (main[0] as u8) | ((alt[0] as u8) << 1) | ((main[1] as u8) << 2) | ((alt[1] as u8) << 3),
    ]
}

/// [`encode_modes_bytes`] of a screen with every one of those modes at its
/// reset value: such a screen writes no trailer.
const MODES_AT_RESET: [u8; 2] = encode_modes_bytes([false; 5], [false; 2], [false; 2]);

/// Encode a `u32` length field in little-endian bytes.
#[must_use]
pub const fn encode_u32_le_bytes(v: u32) -> [u8; 4] {
    [v as u8, (v >> 8) as u8, (v >> 16) as u8, (v >> 24) as u8]
}

/// Decode a `u32` length field from little-endian bytes.
#[must_use]
pub const fn decode_u32_le_bytes(raw: &[u8; 4]) -> u32 {
    (raw[0] as u32) | ((raw[1] as u32) << 8) | ((raw[2] as u32) << 16) | ((raw[3] as u32) << 24)
}

const fn pen_has_rgb(pen: Pen) -> bool {
    pen.fg_rgb.is_some() || pen.bg_rgb.is_some()
}

/// The attribute byte the encodings write: `attrs` with [`WIRE_UNDERLINE`] set
/// when `underline` is any style.
const fn wire_attrs(attrs: u8, underline: Underline) -> u8 {
    if matches!(underline, Underline::None) {
        attrs
    } else {
        attrs | WIRE_UNDERLINE
    }
}

/// [`wire_attrs`] does not say all of this underline: its style is neither none
/// nor single, it has a colour, or `attrs` itself holds [`WIRE_UNDERLINE`] (which
/// no fold sets, but a caller's [`Cell`] can), so the byte would read the same as
/// for another cell.
const fn underline_ext(
    attrs: u8,
    underline: Underline,
    ul: Color,
    ul_rgb: Option<(u8, u8, u8)>,
) -> bool {
    !matches!(underline, Underline::None | Underline::Single)
        || !matches!(ul, Color::Default)
        || ul_rgb.is_some()
        || attrs & WIRE_UNDERLINE != 0
}

const fn cell_underline_ext(c: &Cell) -> bool {
    underline_ext(c.attrs, c.underline, c.ul, c.ul_rgb)
}

/// One underline in full, for the Tag-6 trailer: a byte holding the style's
/// [`Underline::code`] and, in bit 3, whether `attrs` holds [`WIRE_UNDERLINE`];
/// the palette colour as a tag and a value; the 24-bit colour.
fn emit_underline<S: ByteSink>(
    out: &mut S,
    attrs: u8,
    underline: Underline,
    ul: Color,
    ul_rgb: Option<(u8, u8, u8)>,
) {
    let raw_bit = ((attrs & WIRE_UNDERLINE != 0) as u8) << 3;
    let (ut, uv) = match ul {
        Color::Default => (0u8, 0u8),
        Color::Indexed(n) => (1u8, n),
    };
    out.extend_from_slice(&[underline.code() | raw_bit, ut, uv]);
    emit_opt_rgb(out, ul_rgb);
}

fn emit_underline_pen<S: ByteSink>(out: &mut S, pen: Pen) {
    emit_underline(out, pen.attrs, pen.underline, pen.ul, pen.ul_rgb);
}

/// Every cell [`cell_underline_ext`] holds for: their count, then each one's index
/// and [`emit_underline`].
fn emit_underline_cells<S: ByteSink>(out: &mut S, cells: &Grid, count: u32) {
    out.extend_from_slice(&encode_u32_le_bytes(count));
    if count == 0 {
        return;
    }
    cells.for_each_indexed(|idx, c| {
        if cell_underline_ext(c) {
            out.extend_from_slice(&encode_u32_le_bytes(idx as u32));
            emit_underline(out, c.attrs, c.underline, c.ul, c.ul_rgb);
        }
    });
}

const fn cell_has_ext(c: &Cell) -> bool {
    c.fg_rgb.is_some()
        || c.bg_rgb.is_some()
        || c.combining_len != 0
        || c.combining[0] != '\0'
        || c.combining[1] != '\0'
        || c.combining[2] != '\0'
        || c.combining[3] != '\0'
}

fn emit_opt_rgb<S: ByteSink>(out: &mut S, rgb: Option<(u8, u8, u8)>) {
    match rgb {
        None => out.extend_from_slice(&[0]),
        Some((r, g, b)) => out.extend_from_slice(&[1, r, g, b]),
    }
}

fn emit_ext_cells<S: ByteSink>(out: &mut S, cells: &Grid, count: u32) {
    out.extend_from_slice(&encode_u32_le_bytes(count));
    if count == 0 {
        return;
    }
    cells.for_each_indexed(|idx, c| {
        if cell_has_ext(c) {
            out.extend_from_slice(&encode_u32_le_bytes(idx as u32));
            emit_opt_rgb(out, c.fg_rgb);
            emit_opt_rgb(out, c.bg_rgb);
            out.extend_from_slice(&[c.combining_len]);
            for &m in &c.combining[..4] {
                out.extend_from_slice(&encode_u32_le_bytes(m as u32));
            }
        }
    });
}

const fn cell_has_deep_combining(c: &Cell) -> bool {
    if c.combining_len > 4 {
        return true;
    }
    let mut k = 4usize;
    while k < MAX_COMBINING {
        if c.combining[k] != '\0' {
            return true;
        }
        k += 1;
    }
    false
}

fn emit_deep_combining_cells<S: ByteSink>(out: &mut S, cells: &Grid, count: u32) {
    out.extend_from_slice(&encode_u32_le_bytes(count));
    if count == 0 {
        return;
    }
    cells.for_each_indexed(|idx, c| {
        if cell_has_deep_combining(c) {
            out.extend_from_slice(&encode_u32_le_bytes(idx as u32));
            for &m in &c.combining[4..MAX_COMBINING] {
                out.extend_from_slice(&encode_u32_le_bytes(m as u32));
            }
        }
    });
}

/// Whether glyph `ch` continues the grapheme cluster that `base`, the glyph
/// before it, holds, as aterm joins one: a skin-tone modifier after a wide
/// emoji modifier base (wide of itself or by a `\u{FE0F}` it holds), the
/// second regional indicator of a flag, and a glyph other than ASCII after an
/// attached `\u{200D}` (Zero-Width Joiner) that was the last thing printed.
fn joins_cluster(base: &Cell, ch: char, joiner_open: bool) -> bool {
    (is_emoji_modifier(ch)
        && base.width == 2
        && is_emoji_modifier_base(base.ch)
        && (char_display_width(base.ch) == 2 || base.combining_marks().contains(&'\u{FE0F}')))
        || (is_regional_indicator(ch)
            && is_regional_indicator(base.ch)
            && !base
                .combining_marks()
                .iter()
                .any(|&m| is_regional_indicator(m)))
        || (joiner_open && !ch.is_ascii() && base.last_combining() == Some('\u{200D}'))
}

fn emit_wide_cells<S: ByteSink>(out: &mut S, cells: &Grid, count: u32) {
    out.extend_from_slice(&encode_u32_le_bytes(count));
    if count == 0 {
        return;
    }
    cells.for_each_indexed(|idx, c| {
        if c.width != 1 {
            out.extend_from_slice(&encode_u32_le_bytes(idx as u32));
            out.extend_from_slice(&[c.width]);
        }
    });
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExtendedColor {
    Palette(u8),
    Rgb(u8, u8, u8),
}

/// Clip/extend a grid into new dimensions, copying the overlapping top-left
/// region and healing any wide character split by a narrower `new_cols` clip.
/// Does not reflow wrapped lines (a later rung).
fn reflow(old: &Grid, old_cols: u16, old_rows: u16, new_cols: u16, new_rows: u16) -> Grid {
    let new_cols = new_cols.clamp(1, MAX_DIM);
    let new_rows = new_rows.clamp(1, MAX_DIM);
    let mut g = blank_grid(new_cols, new_rows);
    let rows = old_rows.min(new_rows);
    let cols = old_cols.min(new_cols);
    for r in 0..rows {
        for c in 0..cols {
            let dst_idx = (r as usize)
                .saturating_mul(new_cols as usize)
                .saturating_add(c as usize);
            let src_idx = (r as usize)
                .saturating_mul(old_cols as usize)
                .saturating_add(c as usize);
            if let (Some(dst), Some(&src)) = (g.get_mut(dst_idx), old.get(src_idx)) {
                *dst = src;
            }
        }
        // A wide glyph whose spacer the narrowing cut off goes whole: its
        // lead on the new last column becomes a blank.
        if new_cols < old_cols {
            let last = (r as usize)
                .saturating_mul(new_cols as usize)
                .saturating_add(new_cols as usize)
                .saturating_sub(1);
            if let Some(cell) = g.get_mut(last) {
                if cell.width == 2 {
                    *cell = Cell::BLANK;
                }
            }
        }
    }
    g
}

/// One past the last sub-parameter of the colon group that starts at `params[start]`.
fn colon_group_end(sub: &[bool], start: usize, len: usize) -> usize {
    let mut end = start.saturating_add(1);
    while end < len && matches!(sub.get(end), Some(&true)) {
        end = end.saturating_add(1);
    }
    end
}

/// Parse the colour after a `38`/`48`/`58` at `params[*i]` that carries no colon of its own,
/// advancing `i` to the last parameter it consumed.
///
/// A selector that opens a colon group (`;2:cs:r:g:b`, `;5:n`) is that group, read as
/// [`parse_colon_colour`] reads the same group after `38:`, and it ends the colour.
///
/// Otherwise it is all semicolons, a form T.416 does not have and konsole gave programs: `;5;n`
/// selects a palette colour; `;2;r;g;b` selects a 24-bit RGB colour with no id (or leaves the pen
/// unchanged if truncated). CMY `;3;c;m;y` and CMYK `;4;c;m;y;k` are consumed *with* their values
/// and leave the pen unchanged, where xterm consumes the selector and runs the values as SGR
/// codes: nothing renders these colours and a colour's values are not attributes. Any other
/// selector consumes itself.
#[allow(clippy::manual_map)]
fn parse_extended(params: &[u16], sub: &[bool], i: &mut usize) -> Option<ExtendedColor> {
    let last = params.len().saturating_sub(1);
    let i1 = i.saturating_add(1);
    let i2 = i.saturating_add(2);
    let group_end = colon_group_end(sub, i1, params.len());
    if group_end > i2 {
        *i = group_end.saturating_sub(1);
        return params.get(i1..group_end).and_then(parse_colon_colour);
    }
    let (after_selector, colour) = match params.get(i1) {
        None => return None,
        Some(5) => {
            let col = match params.get(i2) {
                Some(&n) => Some(ExtendedColor::Palette(
                    color_clamp_channel(n as u64, 255) as u8
                )),
                None => None,
            };
            (1usize, col)
        }
        Some(2) => {
            let i3 = i.saturating_add(3);
            let i4 = i.saturating_add(4);
            let col = match (params.get(i2), params.get(i3), params.get(i4)) {
                (Some(&r), Some(&g), Some(&b)) => Some(ExtendedColor::Rgb(
                    color_clamp_channel(r as u64, 255) as u8,
                    color_clamp_channel(g as u64, 255) as u8,
                    color_clamp_channel(b as u64, 255) as u8,
                )),
                _ => None,
            };
            (3, col)
        }
        Some(3) => (3, None),
        Some(4) => (4, None),
        Some(_) => (0, None),
    };
    *i = i1.saturating_add(after_selector).min(last);
    colour
}

const fn sgr_fg_std(param: u16) -> Color {
    if param >= 30 && param <= 37 {
        Color::Indexed((param - 30) as u8)
    } else {
        Color::Default
    }
}

const fn sgr_bg_std(param: u16) -> Color {
    if param >= 40 && param <= 47 {
        Color::Indexed((param - 40) as u8)
    } else {
        Color::Default
    }
}

const fn sgr_fg_bright(param: u16) -> Color {
    if param >= 90 && param <= 97 {
        // 90..=97 -> bright palette 8..=15 (`param - 82`).
        Color::Indexed((param - 82) as u8)
    } else {
        Color::Default
    }
}

const fn sgr_bg_bright(param: u16) -> Color {
    if param >= 100 && param <= 107 {
        // 100..=107 -> bright palette 8..=15 (`param - 92`).
        Color::Indexed((param - 92) as u8)
    } else {
        Color::Default
    }
}

/// A colour's colon group, its selector first, wherever the first colon fell (`38:2:…`, `38;2:…`).
/// `5:n` selects a palette colour. `2:cs:r:g:b` selects a 24-bit RGB colour, the second element
/// the colour-space id (ITU T.416 13.1.8, empty in `2::r:g:b`) and any past the blue its elements
/// 6 to 8, none of which means anything here. `2:r:g:b`, which programs emit, has no id slot: only
/// the count tells them apart, four values or three, as in xterm's `parse_extended_colors`,
/// Ghostty, kitty and iTerm2. A shorter group, and any other selector (CMY `3:cs:c:m:y`, CMYK
/// `4:cs:c:m:y:k`), leaves the pen unchanged.
const fn parse_colon_colour(sub: &[u16]) -> Option<ExtendedColor> {
    match *sub {
        [5, n, ..] => Some(ExtendedColor::Palette(
            color_clamp_channel(n as u64, 255) as u8
        )),
        [2, _cs, r, g, b, ..] => Some(ExtendedColor::Rgb(
            color_clamp_channel(r as u64, 255) as u8,
            color_clamp_channel(g as u64, 255) as u8,
            color_clamp_channel(b as u64, 255) as u8,
        )),
        [2, r, g, b] => Some(ExtendedColor::Rgb(
            color_clamp_channel(r as u64, 255) as u8,
            color_clamp_channel(g as u64, 255) as u8,
            color_clamp_channel(b as u64, 255) as u8,
        )),
        _ => None,
    }
}

const fn utf8_acc_step(acc: u32, b: u8) -> u32 {
    (acc << 6) | (b & 0x3f) as u32
}

#[allow(clippy::implicit_saturating_sub)]
const fn utf8_needed_dec(needed: u8) -> u8 {
    if needed > 1 {
        needed - 1
    } else {
        0
    }
}

const fn csi_acc_digit(cur: u16, c: u8) -> u16 {
    if c >= b'0' && c <= b'9' {
        cur.saturating_mul(10).saturating_add((c - b'0') as u16)
    } else {
        cur
    }
}

const fn csi_count0(nums: &[u16]) -> u16 {
    match nums {
        &[0, ..] | &[] => 1,
        &[n, ..] => n,
    }
}

const fn csi_coord0(nums: &[u16]) -> u16 {
    match nums {
        &[0, ..] | &[] => 0,
        &[n, ..] => n.saturating_sub(1),
    }
}

const fn csi_coord1(nums: &[u16]) -> u16 {
    if let &[_, n, ..] = nums {
        n.saturating_sub(1)
    } else {
        0
    }
}

#[allow(clippy::match_ref_pats)]
const fn csi_mode0(nums: &[u16]) -> u16 {
    match nums {
        &[m, ..] => m,
        &[] => 0,
    }
}

const fn csi_bottom0(nums: &[u16], rows: u16) -> u16 {
    if let &[_, n, ..] = nums {
        if n == 0 {
            rows.saturating_sub(1)
        } else {
            n.saturating_sub(1)
        }
    } else {
        rows.saturating_sub(1)
    }
}

// --- the byte-level VT parser --------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum State {
    Ground,
    Esc,
    /// `ESC` plus an intermediate byte (`ESC ( B`): the final byte is still to
    /// come, and the whole sequence is consumed without effect.
    EscIntermediate,
    Csi,
    /// Inside an OSC/DCS/APC/PM/SOS string: bytes are swallowed — never painted
    /// — until the terminator (`ESC \`; BEL too when `bel_ends`, i.e. OSC).
    Str {
        bel_ends: bool,
    },
    /// Mid UTF-8 multibyte sequence: bytes still needed, the accumulated
    /// codepoint, and the range `[lo, hi]` the next byte must fall in to keep
    /// the sequence well-formed (Unicode Table 3-7: narrower than `80..=BF`
    /// only for the byte after `E0`, `ED`, `F0` and `F4`).
    Utf8 {
        needed: u8,
        acc: u32,
        lo: u8,
        hi: u8,
    },
}

/// The most CSI parameter bytes the parser will accumulate. Every sequence this
/// fold models is far shorter (the longest, a truecolour SGR with both a
/// foreground and a background, is ~30 bytes); past the cap the CSI is ignored
/// outright, the way xterm treats one that overruns its own parameter limit.
/// This is what bounds the parser's state: `params` is the only buffer that
/// survives a record boundary, and an unterminated `ESC [` followed by an endless
/// run of `1;` would otherwise grow it for the life of the session.
const CSI_PARAM_MAX: usize = 128;

/// Hard cap on raw OSC payload bytes buffered for `OSC 0`/`2` title or `OSC 7` CWD
/// extraction (`7;` + host + 3x percent-encoded [`MAX_OSC_CWD_BYTES`]). Any longer
/// OSC (such as an `OSC 52` clipboard blob) drops its buffer immediately and uses
/// zero additional heap.
const MAX_OSC_CAPTURE_BYTES: usize = 3350;

const fn osc_hex_nibble(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some((b - b'a').saturating_add(10)),
        b'A'..=b'F' => Some((b - b'A').saturating_add(10)),
        _ => None,
    }
}

fn sanitize_osc_title(raw: &[u8]) -> String {
    let mut out = String::new();
    for chunk in raw.utf8_chunks() {
        for ch in chunk.valid().chars() {
            if ch.is_control() {
                continue;
            }
            if out.len().saturating_add(ch.len_utf8()) > MAX_OSC_TITLE_BYTES {
                return out;
            }
            out.push(ch);
        }
        if !chunk.invalid().is_empty() {
            let repl = char::REPLACEMENT_CHARACTER;
            if out.len().saturating_add(repl.len_utf8()) > MAX_OSC_TITLE_BYTES {
                return out;
            }
            out.push(repl);
        }
    }
    out
}

fn decode_osc7_cwd(raw: &[u8]) -> Option<String> {
    if raw.is_empty() {
        return Some(String::new());
    }
    let decoded = if let &[b'f', b'i', b'l', b'e', b':', b'/', b'/', ref after_scheme @ ..] = raw {
        let mut scan = after_scheme;
        let mut path_enc: Option<&[u8]> = None;
        while let &[c, ref tail @ ..] = scan {
            if c == b'/' {
                path_enc = Some(scan);
                break;
            }
            scan = tail;
        }
        let mut enc = path_enc?;
        let mut buf = Vec::new();
        while let &[b0, ref tail @ ..] = enc {
            if buf.len() >= MAX_OSC_CWD_BYTES {
                return None;
            }
            if b0 == b'%' {
                let &[h1, h2, ref tail2 @ ..] = tail else {
                    return None;
                };
                let (Some(hi), Some(lo)) = (osc_hex_nibble(h1), osc_hex_nibble(h2)) else {
                    return None;
                };
                buf.push((hi << 4) | lo);
                enc = tail2;
            } else {
                buf.push(b0);
                enc = tail;
            }
        }
        buf
    } else if matches!(raw, &[b'/', ..]) {
        if raw.len() > MAX_OSC_CWD_BYTES {
            return None;
        }
        raw.to_vec()
    } else {
        return None;
    };
    let Ok(s) = core::str::from_utf8(&decoded) else {
        return None;
    };
    for ch in s.chars() {
        if ch.is_control() {
            return None;
        }
    }
    Some(s.to_string())
}

fn apply_osc_metadata(raw: &[u8], title: &mut String, cwd: &mut String) {
    match raw {
        [b'0' | b'2', b';', body @ ..] => {
            *title = sanitize_osc_title(body);
        }
        [b'7', b';', body @ ..] => {
            if let Some(decoded) = decode_osc7_cwd(body) {
                *cwd = decoded;
            }
        }
        _ => {}
    }
}

/// A persistent byte→action state machine. Persisting it across [`Parser::feed`]
/// calls is what lets an escape sequence (or a multibyte glyph) span two `Out`
/// records without corrupting the fold. Its state is bounded: a small enum, two
/// bytes, at most [`CSI_PARAM_MAX`] parameter bytes, and at most
/// [`MAX_OSC_CAPTURE_BYTES`] OSC metadata bytes.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Parser {
    state: State,
    /// CSI parameter bytes (`0-9`, `;`, `:`) collected so far.
    params: String,
    /// The CSI private-marker byte (`?`, `>`, `=`, `<`), or 0 for none.
    marker: u8,
    /// The CSI is malformed or outside the subset (an intermediate byte, or a
    /// marker after parameters): its final byte dispatches nothing.
    csi_ignore: bool,
    /// The first intermediate byte of the escape being read (`(` in
    /// `ESC ( 0`), and whether a second one followed it.
    esc_inter: u8,
    esc_inter_more: bool,
    /// Bounded capture buffer for an in-flight OSC string (`OSC 0`/`2`/`7`).
    osc_buf: Vec<u8>,
    osc_active: bool,
    osc_overflow: bool,
    osc_esc_pending: bool,
    /// When `true`, each top-level dispatch records its [`ScreenOp`] into `ops`.
    /// Off for the normal fold; on only inside [`emit_ops`].
    recording: bool,
    ops: Vec<ScreenOp>,
}

impl Parser {
    fn new() -> Parser {
        Parser {
            state: State::Ground,
            params: String::new(),
            marker: 0,
            csi_ignore: false,
            esc_inter: 0,
            esc_inter_more: false,
            osc_buf: Vec::new(),
            osc_active: false,
            osc_overflow: false,
            osc_esc_pending: false,
            recording: false,
            ops: Vec::new(),
        }
    }

    fn clear_osc(&mut self) {
        self.osc_buf.clear();
        self.osc_active = false;
        self.osc_overflow = false;
        self.osc_esc_pending = false;
    }

    fn finish_osc(&mut self, title: &mut String, cwd: &mut String) {
        if self.osc_active && !self.osc_overflow {
            apply_osc_metadata(&self.osc_buf, title, cwd);
        }
        self.clear_osc();
    }

    fn reset_escape(&mut self) {
        self.state = State::Ground;
        self.params.clear();
        self.marker = 0;
        self.csi_ignore = false;
        self.esc_inter = 0;
        self.esc_inter_more = false;
        self.clear_osc();
    }

    /// Record one top-level op (no-op unless recording). Internal mutator
    /// cascades (deferred-wrap line-feed, line-feed scroll) are deliberately NOT
    /// recorded — they reproduce deterministically when the op is re-applied.
    fn rec(&mut self, op: ScreenOp) {
        if self.recording {
            self.ops.push(op);
        }
    }

    // Preserve the original for-loop independently of the batched loop, so a
    // test can compare parser transitions and byte accounting as well as paint.
    #[cfg(test)]
    fn feed_scalar(
        &mut self,
        screen: &mut Screen,
        title: &mut String,
        cwd: &mut String,
        sync_bytes: &mut usize,
        bytes: &[u8],
    ) {
        for &b in bytes {
            let was_sync = screen.synchronized_output;
            match self.state {
                State::Ground => self.ground(screen, b),
                State::Esc => self.escape(screen, title, cwd, b),
                State::EscIntermediate => self.esc_intermediate(screen, b),
                State::Csi => self.csi(screen, b),
                State::Str { bel_ends } => self.string(title, cwd, b, bel_ends),
                State::Utf8 {
                    needed,
                    acc,
                    lo,
                    hi,
                } => self.utf8_cont(screen, b, needed, acc, (lo, hi)),
            }
            if screen.synchronized_output && was_sync {
                *sync_bytes = crate::events::sync_bytes_clamp(
                    (*sync_bytes as u64).saturating_add(1),
                    crate::events::MAX_SYNC_OUTPUT_BYTES as u64,
                ) as usize;
            } else {
                *sync_bytes = 0;
            }
        }
    }

    fn feed(
        &mut self,
        screen: &mut Screen,
        title: &mut String,
        cwd: &mut String,
        sync_bytes: &mut usize,
        bytes: &[u8],
    ) {
        #[cfg(test)]
        if !ascii_work::enabled() {
            self.feed_scalar(screen, title, cwd, sync_bytes, bytes);
            return;
        }
        let mut remaining = bytes;
        while let Some((&b, tail)) = remaining.split_first() {
            let was_sync = screen.synchronized_output;
            match self.state {
                State::Ground => {
                    if (0x20..=0x7e).contains(&b) && remaining.len() >= ASCII_SPAN_MIN {
                        let ascii = screen.charsets.ascii_gl();
                        let consumed = if ascii {
                            screen.put_ascii_run::<false>(remaining)
                        } else {
                            screen.put_ascii_run::<true>(remaining)
                        };
                        if consumed > 0 {
                            if self.recording {
                                if ascii {
                                    self.ops.extend(
                                        remaining[..consumed]
                                            .iter()
                                            .map(|&byte| ScreenOp::Print(byte as char)),
                                    );
                                } else {
                                    self.ops.extend(
                                        remaining[..consumed].iter().map(|&byte| {
                                            ScreenOp::Print(dec_special_graphic(byte))
                                        }),
                                    );
                                }
                            }
                            remaining = &remaining[consumed..];
                            *sync_bytes = if screen.synchronized_output && was_sync {
                                crate::events::sync_bytes_clamp(
                                    (*sync_bytes as u64).saturating_add(consumed as u64),
                                    crate::events::MAX_SYNC_OUTPUT_BYTES as u64,
                                ) as usize
                            } else {
                                0
                            };
                            continue;
                        }
                    }
                    self.ground(screen, b);
                }
                State::Esc => self.escape(screen, title, cwd, b),
                State::EscIntermediate => self.esc_intermediate(screen, b),
                State::Csi => self.csi(screen, b),
                State::Str { bel_ends } => self.string(title, cwd, b, bel_ends),
                State::Utf8 {
                    needed,
                    acc,
                    lo,
                    hi,
                } => self.utf8_cont(screen, b, needed, acc, (lo, hi)),
            }
            remaining = tail;
            if screen.synchronized_output && was_sync {
                *sync_bytes = crate::events::sync_bytes_clamp(
                    (*sync_bytes as u64).saturating_add(1),
                    crate::events::MAX_SYNC_OUTPUT_BYTES as u64,
                ) as usize;
            } else {
                *sync_bytes = 0;
            }
        }
    }

    fn ground(&mut self, screen: &mut Screen, b: u8) {
        match b {
            0x1b => self.state = State::Esc,
            // VT and FF are line feeds too (xterm `CASE_VMOT`: "form feed, line
            // feed, vertical tab" all take `xtermIndex`).
            // Under LNM each also returns the carriage (`if (xw->flags &
            // LINEFEED) CarriageReturn(xw)`).
            b'\n' | 0x0b | 0x0c => {
                screen.line_feed();
                self.rec(ScreenOp::LineFeed);
                if screen.newline {
                    screen.carriage_return();
                    self.rec(ScreenOp::CarriageReturn);
                }
            }
            b'\r' => {
                screen.carriage_return();
                self.rec(ScreenOp::CarriageReturn);
            }
            b'\t' => {
                screen.tab();
                self.rec(ScreenOp::Tab);
            }
            0x08 => {
                screen.backspace();
                self.rec(ScreenOp::Backspace);
            }
            // SO (LS1) maps G1 into GL, SI (LS0) maps G0 back.
            0x0e | 0x0f => {
                let g1 = b == 0x0e;
                screen.charsets.shifted = g1;
                self.rec(ScreenOp::LockShift { g1 });
            }
            0x00..=0x1f | 0x7f => {} // other C0 controls and DEL: ignored
            // A GL byte paints the glyph the set mapped into GL gives it; the
            // op carries that glyph.
            0x20..=0x7e => {
                let ch = screen.charsets.translate(b);
                screen.put(ch);
                self.rec(ScreenOp::Print(ch));
            }
            _ => self.begin_utf8(screen, b),
        }
    }

    /// Emit U+FFFD for one maximal subpart of ill-formed UTF-8.
    fn replacement(&mut self, screen: &mut Screen) {
        screen.put('\u{fffd}');
        self.rec(ScreenOp::Print('\u{fffd}'));
    }

    /// A byte at or above 0x80 in the ground state. Malformed input is replaced
    /// one U+FFFD per MAXIMAL SUBPART (Unicode 3.9, "U+FFFD Substitution of
    /// Maximal Subparts"; the WHATWG decoder and aterm do the same): a byte
    /// that cannot start a well-formed sequence (`80..=C1`, `F5..=FF`) is one
    /// subpart on its own, and so the overlong `C0 80` is two replacements and
    /// the surrogate `ED A0 80` three, never one for the whole run. The
    /// replacements are cells, so the count decides where every later glyph
    /// lands.
    fn begin_utf8(&mut self, screen: &mut Screen, b: u8) {
        let (needed, acc, lo, hi) = match b {
            0xc2..=0xdf => (1u8, (b & 0x1f) as u32, 0x80, 0xbf),
            0xe0 => (2u8, 0, 0xa0, 0xbf),
            0xed => (2u8, 0x0d, 0x80, 0x9f),
            0xe1..=0xef => (2u8, (b & 0x0f) as u32, 0x80, 0xbf),
            0xf0 => (3u8, 0, 0x90, 0xbf),
            0xf4 => (3u8, 0x04, 0x80, 0x8f),
            0xf1..=0xf3 => (3u8, (b & 0x07) as u32, 0x80, 0xbf),
            _ => return self.replacement(screen),
        };
        self.state = State::Utf8 {
            needed,
            acc,
            lo,
            hi,
        };
    }

    fn utf8_cont(&mut self, screen: &mut Screen, b: u8, needed: u8, acc: u32, range: (u8, u8)) {
        if !(range.0..=range.1).contains(&b) {
            // The subpart so far ends here: replace it, then reprocess `b`
            // fresh (it may start a sequence, or be a control or ASCII).
            self.state = State::Ground;
            self.replacement(screen);
            self.ground(screen, b);
            return;
        }
        let acc = utf8_acc_step(acc, b);
        if needed > 1 {
            self.state = State::Utf8 {
                needed: utf8_needed_dec(needed),
                acc,
                lo: 0x80,
                hi: 0xbf,
            };
            return;
        }
        self.state = State::Ground;
        if (0x80..=0x9f).contains(&acc) {
            // A validly encoded C1 control: not modelled, ignored.
            return;
        }
        // Table 3-7's ranges exclude overlongs and surrogates, so every
        // completed sequence is a scalar value.
        let ch = char::from_u32(acc).unwrap_or('\u{fffd}');
        screen.put(ch);
        self.rec(ScreenOp::Print(ch));
    }

    fn escape(&mut self, screen: &mut Screen, title: &mut String, cwd: &mut String, b: u8) {
        if self.osc_esc_pending {
            self.osc_esc_pending = false;
            if b == b'\\' {
                self.finish_osc(title, cwd);
                self.state = State::Ground;
                return;
            }
            self.clear_osc();
        }
        match b {
            b'[' => {
                self.params.clear();
                self.marker = 0;
                self.csi_ignore = false;
                self.state = State::Csi;
            }
            b']' => {
                self.clear_osc();
                self.osc_active = true;
                self.state = State::Str { bel_ends: true }; // OSC
            }
            b'P' | b'X' | b'^' | b'_' => {
                self.clear_osc();
                self.state = State::Str { bel_ends: false }; // DCS/SOS/PM/APC
            }
            // IND is a line feed (xterm `xtermIndex`), NEL a line feed and a
            // carriage return, RI the reverse index.
            b'D' => {
                screen.line_feed();
                self.rec(ScreenOp::LineFeed);
                self.state = State::Ground;
            }
            b'E' => {
                screen.line_feed();
                screen.carriage_return();
                self.rec(ScreenOp::LineFeed);
                self.rec(ScreenOp::CarriageReturn);
                self.state = State::Ground;
            }
            b'M' => {
                screen.reverse_index();
                self.rec(ScreenOp::ReverseIndex);
                self.state = State::Ground;
            }
            b'7' => {
                screen.save_cursor();
                self.rec(ScreenOp::SaveCursor);
                self.state = State::Ground;
            }
            b'8' => {
                screen.restore_cursor();
                self.rec(ScreenOp::RestoreCursor);
                self.state = State::Ground;
            }
            b'c' => {
                screen.reset();
                title.clear();
                cwd.clear();
                self.rec(ScreenOp::Reset);
                self.state = State::Ground;
            }
            // ESC ( B etc.: remember the intermediate for the final byte.
            0x20..=0x2f => {
                self.esc_inter = b;
                self.esc_inter_more = false;
                self.state = State::EscIntermediate;
            }
            0x1b => {} // ESC ESC: stay, treat the next byte as the escape
            0x18 | 0x1a => self.state = State::Ground, // CAN/SUB abort
            0x00..=0x1f => self.ground(screen, b), // a C0 control executes; the escape continues
            0x7f => {}
            0x30..=0x7e => self.state = State::Ground, // other two-byte escapes: consumed
            _ => {
                // An 8-bit byte cannot continue an escape: abort and reprocess it.
                self.state = State::Ground;
                self.ground(screen, b);
            }
        }
    }

    fn esc_intermediate(&mut self, screen: &mut Screen, b: u8) {
        match b {
            0x1b => self.state = State::Esc,
            0x18 | 0x1a => self.state = State::Ground,
            0x00..=0x1f => self.ground(screen, b),
            0x20..=0x2f => self.esc_inter_more = true,
            0x7f => {}
            // The final byte. SCS into G0 (`ESC ( F`) or G1 (`ESC ) F`) of
            // ASCII (`B`) or DEC Special Graphics (`0`) designates it; any
            // other set, a G2/G3 or 96-character designation, a two-byte
            // set name (`ESC ( % 5`) and every other escape with an
            // intermediate is consumed, leaving the designations as they
            // were (xterm ignores a set it cannot name).
            0x30..=0x7e => {
                self.state = State::Ground;
                let charset = match b {
                    b'B' => Some(Charset::Ascii),
                    b'0' => Some(Charset::DecSpecial),
                    _ => None,
                };
                if let (false, b'(' | b')', Some(charset)) =
                    (self.esc_inter_more, self.esc_inter, charset)
                {
                    let g1 = self.esc_inter == b')';
                    screen.designate(g1, charset);
                    self.rec(ScreenOp::Designate { g1, charset });
                }
            }
            _ => {
                self.state = State::Ground;
                self.ground(screen, b);
            }
        }
    }

    /// An OSC/DCS/APC/PM/SOS string body: swallowed byte by byte. `ESC` ends it
    /// (as `ESC \`, or as the start of a new escape), BEL ends an OSC, CAN/SUB
    /// abort; nothing is ever painted, while bounded `OSC 0`/`2`/`7` payloads are
    /// extracted into [`Folder::title`] / [`Folder::cwd`].
    fn string(&mut self, title: &mut String, cwd: &mut String, b: u8, bel_ends: bool) {
        match b {
            0x1b => {
                if self.osc_active {
                    self.osc_esc_pending = true;
                }
                self.state = State::Esc;
            }
            0x07 if bel_ends => {
                self.finish_osc(title, cwd);
                self.state = State::Ground;
            }
            0x18 | 0x1a => {
                self.clear_osc();
                self.state = State::Ground;
            }
            _ => {
                if self.osc_active && !self.osc_overflow {
                    if self.osc_buf.len() < MAX_OSC_CAPTURE_BYTES {
                        self.osc_buf.push(b);
                    } else {
                        self.osc_overflow = true;
                        self.osc_buf.clear();
                    }
                }
            }
        }
    }

    fn csi(&mut self, screen: &mut Screen, b: u8) {
        match b {
            // ESC anywhere begins a new escape (ECMA-48): an unterminated CSI is
            // abandoned, and the new sequence is parsed rather than painted.
            0x1b => self.state = State::Esc,
            0x18 | 0x1a => self.state = State::Ground, // CAN/SUB abort
            0x00..=0x1f => self.ground(screen, b),     // a C0 control executes inside a CSI
            0x20..=0x2f => self.csi_ignore = true,     // intermediate: outside the subset
            0x3c..=0x3f if self.marker == 0 && self.params.is_empty() && !self.csi_ignore => {
                self.marker = b; // leading private marker: `?`, `>`, `=`, `<`
            }
            0x3c..=0x3f => self.csi_ignore = true, // a marker after parameters: malformed
            0x30..=0x3b => {
                if !self.csi_ignore {
                    if self.params.len() >= CSI_PARAM_MAX {
                        // Longer than any sequence this fold models: ignore the whole
                        // CSI and stop accumulating, so the parser's state stays
                        // bounded no matter what the target emits.
                        self.csi_ignore = true;
                        self.params.clear();
                    } else {
                        self.params.push(b as char); // digits, `;`, `:`
                    }
                }
            }
            0x40..=0x7e => {
                if !self.csi_ignore {
                    self.dispatch_csi(screen, b);
                }
                self.state = State::Ground;
            }
            0x7f => {}
            _ => {
                // An 8-bit byte cannot continue a CSI: abort and reprocess it.
                self.state = State::Ground;
                self.ground(screen, b);
            }
        }
    }

    fn dispatch_csi(&mut self, screen: &mut Screen, final_byte: u8) {
        // Which (marker, final) pairs the fold models: plain sequences (the
        // ANSI modes of SM/RM among them), DEC private modes, and DECSED/DECSEL
        // (`? J`/`? K`, which erase like ED/EL with no protected cells).
        // `>`/`=`/`<`-marked sequences (XTMODKEYS `> Ps m`, tertiary DA, …)
        // are consumed whole.
        match (self.marker, final_byte) {
            (b'?', b'h' | b'l' | b'J' | b'K') | (0, _) => {}
            _ => return,
        }
        // `1;2:3;4` → values plus a per-value "is a `:` sub-parameter" flag. On
        // the stack, not the heap (this runs for every CSI): `params` holds at
        // most CSI_PARAM_MAX bytes, hence at most CSI_PARAM_MAX + 1 values.
        let mut vals = [0u16; CSI_PARAM_MAX + 1];
        let mut sub = [false; CSI_PARAM_MAX + 1];
        let mut n = 0;
        if !self.params.is_empty() {
            let mut cur: u16 = 0;
            let mut cur_sub = false;
            for c in self.params.bytes() {
                match c {
                    b'0'..=b'9' => cur = csi_acc_digit(cur, c),
                    _ => {
                        if let (Some(v_slot), Some(s_slot)) = (vals.get_mut(n), sub.get_mut(n)) {
                            *v_slot = cur;
                            *s_slot = cur_sub;
                            n = n.saturating_add(1);
                        }
                        cur = 0;
                        cur_sub = c == b':';
                    }
                }
            }
            if let (Some(v_slot), Some(s_slot)) = (vals.get_mut(n), sub.get_mut(n)) {
                *v_slot = cur;
                *s_slot = cur_sub;
                n = n.saturating_add(1);
            }
        }
        let vals = vals.get(..n).unwrap_or(&[]);
        let sub = sub.get(..n).unwrap_or(&[]);
        // Outside SGR a sub-parameter carries nothing the fold models.
        let mut nums = [0u16; CSI_PARAM_MAX + 1];
        let mut m = 0;
        for (&v, &s) in vals.iter().zip(sub) {
            if !s {
                if let Some(num_slot) = nums.get_mut(m) {
                    *num_slot = v;
                    m = m.saturating_add(1);
                }
            }
        }
        let nums = nums.get(..m).unwrap_or(&[]);

        match final_byte {
            b'A' => {
                let n = csi_count0(nums);
                screen.cursor_up(n);
                self.rec(ScreenOp::CursorUp(n));
            }
            b'B' => {
                let n = csi_count0(nums);
                screen.cursor_down(n);
                self.rec(ScreenOp::CursorDown(n));
            }
            b'C' => {
                let n = csi_count0(nums);
                screen.cursor_forward(n);
                self.rec(ScreenOp::CursorForward(n));
            }
            b'D' => {
                let n = csi_count0(nums);
                screen.cursor_back(n);
                self.rec(ScreenOp::CursorBack(n));
            }
            b'E' => {
                let n = csi_count0(nums);
                screen.cursor_down(n);
                screen.carriage_return();
                self.rec(ScreenOp::CursorDown(n));
                self.rec(ScreenOp::CarriageReturn);
            }
            b'F' => {
                let n = csi_count0(nums);
                screen.cursor_up(n);
                screen.carriage_return();
                self.rec(ScreenOp::CursorUp(n));
                self.rec(ScreenOp::CarriageReturn);
            }
            // Absolute addressing is xterm's `CursorSet`: rows and columns
            // count from the top and left margins under origin mode (CHA is
            // xterm's `CASE_HPA`), so the op records the absolute position
            // the cursor went to.
            b'G' => {
                let r = screen.addressed_row(screen.cursor_row_addressed());
                let c = screen.addressed_col(csi_coord0(nums));
                screen.move_to(r, c);
                self.rec(ScreenOp::MoveTo(r, c));
            }
            b'd' => {
                let c = screen.addressed_col(screen.cursor_col_addressed());
                let r = screen.addressed_row(csi_coord0(nums));
                screen.move_to(r, c);
                self.rec(ScreenOp::MoveTo(r, c));
            }
            b'H' | b'f' => {
                let r = screen.addressed_row(csi_coord0(nums));
                let c = screen.addressed_col(csi_coord1(nums));
                screen.move_to(r, c);
                self.rec(ScreenOp::MoveTo(r, c));
            }
            b'S' => {
                let n = csi_count0(nums);
                screen.scroll_up_lines(n);
                self.rec(ScreenOp::ScrollUp(n));
            }
            // xterm `CASE_TRACK_MOUSE`: a lone nonzero (or defaulted)
            // parameter is SD; `CSI 0 T` or more than one parameter starts
            // highlight mouse tracking, which paints nothing.
            b'T' if nums.len() <= 1 && !matches!(nums, &[0]) => {
                let n = csi_count0(nums);
                screen.scroll_down_lines(n);
                self.rec(ScreenOp::ScrollDown(n));
            }
            b'J' => {
                let m = csi_mode0(nums);
                screen.erase_display(m);
                self.rec(ScreenOp::EraseDisplay(m));
            }
            b'K' => {
                let m = csi_mode0(nums);
                screen.erase_line(m);
                self.rec(ScreenOp::EraseLine(m));
            }
            b'm' => {
                screen.sgr(vals, sub);
                // Record the RESOLVED pen (after sgr ran), not the raw params —
                // this is what kills the two-party terminfo-disagreement class.
                // The attribute byte says whether the pen underlines; a style past
                // single, or a colour, follows as a `SetUnderline`.
                let pen = screen.pen;
                if pen.fg_rgb.is_none() && pen.bg_rgb.is_none() {
                    self.rec(ScreenOp::SetSgr {
                        fg: pen.fg,
                        bg: pen.bg,
                        attrs: pen.wire_attrs(),
                    });
                } else {
                    self.rec(ScreenOp::SetSgrRgb {
                        fg: pen.fg,
                        fg_rgb: pen.fg_rgb,
                        bg: pen.bg,
                        bg_rgb: pen.bg_rgb,
                        attrs: pen.wire_attrs(),
                    });
                }
                if pen.underline_ext() {
                    self.rec(ScreenOp::SetUnderline {
                        style: pen.underline,
                        ul: pen.ul,
                        ul_rgb: pen.ul_rgb,
                    });
                }
            }
            b'h' | b'l' if self.marker == b'?' => {
                let set = final_byte == b'h';
                screen.set_mode(nums, set);
                if self.recording {
                    self.rec(ScreenOp::SetMode {
                        params: nums.to_vec(),
                        set,
                    });
                }
            }
            b'h' | b'l' => {
                let set = final_byte == b'h';
                screen.set_ansi_mode(nums, set);
                if nums.contains(&4) {
                    self.rec(ScreenOp::SetInsertMode(set));
                }
                if nums.contains(&20) {
                    self.rec(ScreenOp::SetNewlineMode(set));
                }
            }
            b'r' => {
                // DECSTBM: set the scrolling region [top; bottom] (1-based, inclusive).
                // Absent/0 top -> 1; absent/0 bottom -> last row. Converted to 0-based.
                let (_, rows) = screen.dims();
                let top0 = csi_coord0(nums);
                let bottom0 = csi_bottom0(nums, rows);
                screen.set_scroll_region(top0, bottom0);
                self.rec(ScreenOp::SetScrollRegion {
                    top: top0,
                    bottom: bottom0,
                });
            }
            b'@' => {
                let n = csi_count0(nums);
                screen.insert_chars(n);
                self.rec(ScreenOp::InsertChars(n));
            }
            b'P' => {
                let n = csi_count0(nums);
                screen.delete_chars(n);
                self.rec(ScreenOp::DeleteChars(n));
            }
            b'X' => {
                let n = csi_count0(nums);
                screen.erase_chars(n);
                self.rec(ScreenOp::EraseChars(n));
            }
            b'L' => {
                let n = csi_count0(nums);
                screen.insert_lines(n, true);
                self.rec(ScreenOp::InsertLines(n));
            }
            b'M' => {
                let n = csi_count0(nums);
                screen.insert_lines(n, false);
                self.rec(ScreenOp::DeleteLines(n));
            }
            // Under DECLRMM `CSI s` is DECSLRM (xterm `CASE_DECSLRM`): a
            // left of 0 or none is 1; a right that is absent, 0 or past the
            // screen is its last column.
            b's' if screen.lrmm => {
                let last_col = screen.cols.saturating_sub(1);
                let left = csi_coord0(nums);
                let right = match nums {
                    &[_, r, ..] if r != 0 => r.saturating_sub(1).min(last_col),
                    _ => last_col,
                };
                if left < right {
                    screen.set_lr_margins(left, right);
                    self.rec(ScreenOp::SetLeftRightMargins { left, right });
                }
            }
            b's' => {
                screen.save_cursor();
                self.rec(ScreenOp::SaveCursor);
            }
            b'u' => {
                screen.restore_cursor();
                self.rec(ScreenOp::RestoreCursor);
            }
            _ => {}
        }
    }
}

/// Project records into the normalized typed screen-op stream via the **single
/// canonical parser** (the same parse that produces the fold). One parser emits
/// both, so two viewers cannot disagree.
pub fn emit_ops(cols: u16, rows: u16, records: &[Record]) -> Vec<ScreenOp> {
    let mut folder = Folder::new(cols, rows);
    folder.parser.recording = true;
    for rec in records {
        folder.apply(rec);
    }
    folder.parser.ops
}

const fn screen_op_group(op: &ScreenOp) -> u8 {
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
        | ScreenOp::MoveTo(_, _) => 0,
        ScreenOp::EraseDisplay(_)
        | ScreenOp::EraseLine(_)
        | ScreenOp::ReverseIndex
        | ScreenOp::InsertChars(_)
        | ScreenOp::DeleteChars(_)
        | ScreenOp::EraseChars(_)
        | ScreenOp::InsertLines(_)
        | ScreenOp::DeleteLines(_)
        | ScreenOp::ScrollUp(_)
        | ScreenOp::ScrollDown(_) => 1,
        ScreenOp::SetSgr { .. }
        | ScreenOp::SetSgrRgb { .. }
        | ScreenOp::SetUnderline { .. }
        | ScreenOp::SetMode { .. }
        | ScreenOp::SaveCursor
        | ScreenOp::RestoreCursor
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

fn apply_op_cursor(screen: &mut Screen, op: &ScreenOp) {
    match op {
        ScreenOp::Print(ch) => screen.put(*ch),
        ScreenOp::CarriageReturn => screen.carriage_return(),
        ScreenOp::LineFeed => screen.line_feed(),
        ScreenOp::Tab => screen.tab(),
        ScreenOp::Backspace => screen.backspace(),
        ScreenOp::CursorUp(n) => screen.cursor_up(*n),
        ScreenOp::CursorDown(n) => screen.cursor_down(*n),
        ScreenOp::CursorForward(n) => screen.cursor_forward(*n),
        ScreenOp::CursorBack(n) => screen.cursor_back(*n),
        ScreenOp::MoveTo(r, c) => screen.move_to(*r, *c),
        _ => {}
    }
}

fn apply_op_edit(screen: &mut Screen, op: &ScreenOp) {
    match op {
        ScreenOp::EraseDisplay(m) => screen.erase_display(*m),
        ScreenOp::EraseLine(m) => screen.erase_line(*m),
        ScreenOp::ReverseIndex => screen.reverse_index(),
        ScreenOp::InsertChars(n) => screen.insert_chars(*n),
        ScreenOp::DeleteChars(n) => screen.delete_chars(*n),
        ScreenOp::EraseChars(n) => screen.erase_chars(*n),
        ScreenOp::InsertLines(n) => screen.insert_lines(*n, true),
        ScreenOp::DeleteLines(n) => screen.insert_lines(*n, false),
        ScreenOp::ScrollUp(n) => screen.scroll_up_lines(*n),
        ScreenOp::ScrollDown(n) => screen.scroll_down_lines(*n),
        _ => {}
    }
}

fn apply_op_style_or_mode(screen: &mut Screen, op: &ScreenOp) {
    match op {
        ScreenOp::SetSgr { fg, bg, attrs } => {
            screen.pen = Pen::from_wire(*fg, None, *bg, None, *attrs);
        }
        ScreenOp::SetSgrRgb {
            fg,
            fg_rgb,
            bg,
            bg_rgb,
            attrs,
        } => {
            screen.pen = Pen::from_wire(*fg, *fg_rgb, *bg, *bg_rgb, *attrs);
        }
        ScreenOp::SetUnderline { style, ul, ul_rgb } => {
            screen.pen.underline = *style;
            screen.pen.ul = *ul;
            screen.pen.ul_rgb = *ul_rgb;
        }
        ScreenOp::SetMode { params, set } => screen.set_mode(params, *set),
        ScreenOp::SaveCursor => screen.save_cursor(),
        ScreenOp::RestoreCursor => screen.restore_cursor(),
        ScreenOp::SetScrollRegion { top, bottom } => screen.set_scroll_region(*top, *bottom),
        ScreenOp::SetInsertMode(set) => screen.insert = *set,
        ScreenOp::SetNewlineMode(set) => screen.newline = *set,
        ScreenOp::Designate { g1, charset } => screen.designate(*g1, *charset),
        ScreenOp::LockShift { g1 } => screen.charsets.shifted = *g1,
        ScreenOp::SetLeftRightMargins { left, right } => screen.set_lr_margins(*left, *right),
        ScreenOp::Reset => screen.reset(),
        ScreenOp::Resize(c, r) => screen.resize(*c, *r),
        _ => {}
    }
}

fn apply_one_op(screen: &mut Screen, op: &ScreenOp) {
    match screen_op_group(op) {
        0 => apply_op_cursor(screen, op),
        1 => apply_op_edit(screen, op),
        _ => apply_op_style_or_mode(screen, op),
    }
}

/// Re-apply a screen-op slice onto an existing [`Screen`], re-driving the
/// **same** private mutators from typed ops — an independent dispatch path that
/// bypasses only the VT state machine. Enables incremental cross-machine
/// viewers that decode [`ScreenOp`] batches off the bus record-by-record.
pub fn apply_ops_to(screen: &mut Screen, ops: &[ScreenOp]) {
    for op in ops {
        apply_one_op(screen, op);
    }
}

/// Re-apply a screen-op stream to a fresh screen, re-driving the **same** private
/// mutators from typed ops — an independent dispatch path that bypasses only the
/// VT state machine. Reproduces the fold's screen byte-for-byte.
pub fn apply_ops(cols: u16, rows: u16, ops: &[ScreenOp]) -> Screen {
    let mut screen = Screen::new(cols, rows);
    apply_ops_to(&mut screen, ops);
    screen
}

#[cfg(test)]
mod tests {
    use super::*;

    fn out(s: &[u8]) -> Vec<Record> {
        vec![Record::Out(s.to_vec())]
    }

    #[test]
    fn printable_text_lands_in_the_grid() {
        let s = fold(10, 2, &out(b"hi"));
        assert_eq!(s.line_text(0), "hi");
        assert_eq!(s.cursor(), (0, 2));
    }

    #[test]
    fn deferred_wrap_moves_to_next_row_only_on_the_next_glyph() {
        // Three columns, write "abc" then "d": the wrap is deferred until 'd'.
        let s = fold(3, 2, &out(b"abcd"));
        assert_eq!(s.line_text(0), "abc");
        assert_eq!(s.line_text(1), "d");
    }

    #[test]
    fn sgr_color_and_attr_apply_to_subsequent_cells() {
        let s = fold(10, 1, &out(b"\x1b[31;1mX"));
        let cell = s.cell(0, 0).unwrap();
        assert_eq!(cell.fg, Color::Indexed(1));
        assert_ne!(cell.attrs & attr::BOLD, 0);
    }

    #[test]
    fn arbitrary_bytes_never_panic() {
        // Every single byte value, including stray UTF-8 continuations and
        // truncated escapes, must fold without panicking.
        let all: Vec<u8> = (0..=255u8).collect();
        let s = fold(8, 4, &out(&all));
        assert_eq!(s.dims(), (8, 4));
    }

    #[test]
    fn large_cursor_movement_params_do_not_overflow() {
        // A near-u16::MAX CSI param from a non-zero cursor must clamp to the last
        // cell, not overflow u16. Move to (3,3), then CUD 65535 and CUF 65535.
        let s = fold(10, 8, &out(b"\x1b[4;4H\x1b[65535B\x1b[65535C"));
        assert_eq!(s.cursor(), (7, 9)); // clamped to (rows-1, cols-1)
                                        // Tab from the far edge of a max-width screen must not overflow either.
        let wide = fold(MAX_DIM, 1, &out(b"\x1b[1;1000H\t"));
        assert_eq!(wide.cursor().1, MAX_DIM - 1);
        // An over-long parameter saturates rather than collapsing to 0.
        let big = fold(10, 8, &out(b"\x1b[99999999B"));
        assert_eq!(big.cursor(), (7, 0));
    }

    #[test]
    fn a_csi_split_across_records_still_dispatches() {
        let recs = vec![
            Record::Out(b"\x1b[3".to_vec()),
            Record::Out(b";2Hx".to_vec()),
        ];
        let s = fold(10, 4, &recs);
        assert_eq!(s.line_text(2), " x");
    }

    #[test]
    fn a_string_sequence_split_across_records_is_still_swallowed() {
        let recs = vec![
            Record::Out(b"a\x1b]0;half a ".to_vec()),
            Record::Out(b"title\x07b".to_vec()),
        ];
        let s = fold(20, 2, &recs);
        assert_eq!(s.line_text(0), "ab");
    }

    #[test]
    fn an_unterminated_csi_cannot_grow_the_parser_without_bound() {
        // A hostile (or wedged) target emitting `ESC [` and then an endless run of
        // `1;` never terminates the CSI, so its parameter bytes are carried across
        // every record. The buffer must stay capped rather than growing with the
        // stream — the fold is the pump's one piece of per-session state.
        let mut folder = Folder::new(20, 4);
        folder.apply(&Record::Out(b"\x1b[".to_vec()));
        for _ in 0..1000 {
            folder.apply(&Record::Out(b"1;".repeat(64)));
            assert!(
                folder.parser.params.len() <= CSI_PARAM_MAX,
                "params grew to {}",
                folder.parser.params.len()
            );
        }
        // And the over-long CSI is ignored, not dispatched: the next printable
        // byte after its final byte paints normally.
        folder.apply(&Record::Out(b"mX".to_vec()));
        assert_eq!(folder.screen().line_text(0), "X");

        // A sequence of legal length is unaffected — the cap is far above any the
        // fold models (truecolour SGR with a foreground and a background).
        let s = fold(20, 4, &out(b"\x1b[38;2;10;20;30;48;2;40;50;60mA\x1b[3;2Hb"));
        assert_eq!(s.line_text(0), "A");
        assert_eq!(s.line_text(2), " b");
    }

    #[test]
    fn a_csi_at_the_parameter_cap_dispatches() {
        // CSI_PARAM_MAX separators is the most values a dispatch can see
        // (CSI_PARAM_MAX + 1, all zero): an SGR reset, then a CUP home.
        let mut bytes = b"\x1b[31mA\x1b[".to_vec();
        bytes.extend(std::iter::repeat_n(b';', CSI_PARAM_MAX));
        bytes.extend_from_slice(b"mB\x1b[");
        bytes.extend(std::iter::repeat_n(b':', CSI_PARAM_MAX));
        bytes.extend_from_slice(b"H");
        let s = fold(10, 2, &out(&bytes));
        assert_eq!(s.cell(0, 0).unwrap().fg, Color::Indexed(1));
        assert_eq!(s.cell(0, 1).unwrap().fg, Color::Default);
        assert_eq!(s.cursor(), (0, 0));
    }

    #[test]
    fn restore_with_nothing_saved_homes_the_cursor() {
        // DEC STD 070 / xterm: DECRC with no prior DECSC moves to the home position.
        let s = fold(10, 4, &out(b"\x1b[3;3H\x1b8"));
        assert_eq!(s.cursor(), (0, 0));
    }
}
