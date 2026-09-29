//! A pure VT/ECMA-48 screen: the deterministic fold of recorded output.
//!
//! [`fold`] turns an ordered slice of [`Record`]s into a [`Screen`] with no
//! clock, no randomness, and no I/O, so the same records always yield a
//! byte-identical screen ([`Screen::serialize`]). That purity is the spine of
//! the astream-term replay guarantee.
//!
//! ### Scope
//!
//! A deliberately bounded but real VT subset: C0 controls (CR/LF/TAB/BS), CSI
//! cursor motion (CUU/CUD/CUF/CUB/CNL/CPL/CHA/VPA/CUP), erase (ED/EL), SGR (the
//! 16- and 256-colour palettes in both the `;` and the `:` sub-parameter form,
//! plus bold/underline/reverse), the alternate screen (`?1049`/`?47`/`?1047`),
//! cursor visibility (`?25`), save/restore cursor (DECSC/DECRC and `CSI s`/`u`,
//! one slot per screen buffer as in xterm), the DEC scrolling region (`DECSTBM`),
//! RIS, and inline [`Record::Resize`]. The scroll region is cross-validated
//! against the production aterm engine (see `term.fold.scroll-region`).
//!
//! Everything else in the byte stream is **consumed, never painted**, following
//! the ECMA-48 parser: OSC/DCS/APC/PM/SOS string sequences (window titles,
//! OSC-133 shell marks, image payloads) are swallowed up to their terminator
//! (`ESC \`, or BEL for OSC); two-byte escapes (`ESC ( B` charset designations,
//! `ESC =`/`ESC >`, IND/NEL/RI) and CSI sequences outside the subset (any with an
//! intermediate byte, or a private marker other than `?`) are skipped whole;
//! truecolour SGR (`38;2;r;g;b`, `38:2::r:g:b`) is consumed *with* its
//! sub-parameters and leaves the pen unchanged; DEL, and C1 controls arriving
//! as UTF-8 (U+0080..U+009F), are ignored; malformed UTF-8 (overlong,
//! truncated, a stray continuation or 8-bit byte) yields U+FFFD — a control
//! character never lands in a cell. `ESC` anywhere begins a new escape, and a
//! C0 control executes inside an unfinished CSI.
//!
//! Simplifications, documented so they are never mistaken for fidelity — each is
//! deterministic:
//!
//! * **Deferred line wrap** is modelled with xterm's last-column semantics: after
//!   the last column is painted the cursor reports `col == cols`, and the next
//!   glyph wraps. CR/LF/BS/CUB/CUF/CUU/CUD/CUP resolve the pending wrap back
//!   onto the last column first — so BS after a full line lands on the
//!   second-to-last column (`abcde BS X` on 5 columns is `abcXe`) — while TAB
//!   and ED/EL leave it pending (erase-to-end from a pending wrap starts past
//!   the parked glyph, so it survives; erase-to-cursor includes it), and
//!   DECSC/DECRC round-trip it (a restored cursor wraps on its next glyph, as
//!   in aterm/xterm). Scrolling honours the `DECSTBM` region, and CUU/CUD (and
//!   CNL/CPL) stop at its margins as in xterm.
//! * **Erase honours background-colour-erase** (`bce`): `ED`/`EL` fill with the
//!   current SGR background, not a hardcoded default blank (reverse-video bce is
//!   out of scope). Cross-validated structurally against aterm.
//! * **The alternate screen is not persistent**: entering it (any of
//!   `?47`/`?1047`/`?1049`) gives a blank grid, and leaving discards that grid
//!   and its DECSC slot (xterm keeps one alternate buffer across sessions). Only
//!   `?1049` saves/restores the cursor; the cursor is otherwise shared between
//!   the buffers and never moved by the switch, as in xterm.
//! * Character sets, origin mode, insert/delete, VT/FF, IND/NEL/RI and
//!   truecolour are not modelled (consumed and ignored).
//! * **One codepoint per cell**: an East Asian wide character takes one cell,
//!   not two, and a combining (zero-width) mark takes a cell of its own.
//! * DECSC/DECRC save and restore the cursor position (and a pending wrap)
//!   only, not the SGR rendition. There is no scrollback: `ED 3` erases the
//!   display like `ED 2`.
//! * **Resize clips/extends**; it does not reflow wrapped lines.
//! * Grid dimensions are clamped to `1..=`[`MAX_DIM`] so hostile input cannot
//!   trigger an unbounded allocation (panic-free, like `astream-wire`).

use crate::ops::ScreenOp;
use crate::record::Record;

/// Where [`Screen::serialize_into`] writes its encoding: a byte buffer, or a
/// hasher that consumes it without buffering.
pub(crate) trait ByteSink {
    fn extend_from_slice(&mut self, bytes: &[u8]);
    fn push(&mut self, byte: u8) {
        self.extend_from_slice(&[byte]);
    }
}

impl ByteSink for Vec<u8> {
    fn extend_from_slice(&mut self, bytes: &[u8]) {
        Vec::extend_from_slice(self, bytes);
    }
    fn push(&mut self, byte: u8) {
        Vec::push(self, byte);
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

/// Cell attribute bits (a bitset in [`Cell::attrs`]).
pub mod attr {
    /// Bold / increased intensity.
    pub const BOLD: u8 = 1 << 0;
    /// Underline.
    pub const UNDERLINE: u8 = 1 << 1;
    /// Reverse video (swap fg/bg).
    pub const REVERSE: u8 = 1 << 2;
    /// Faint / dim — used to render an unconfirmed speculative echo.
    pub const FAINT: u8 = 1 << 3;
}

/// One character cell of the grid.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Cell {
    /// The displayed character (one `char`; grapheme clustering is a later rung).
    pub ch: char,
    /// Foreground colour.
    pub fg: Color,
    /// Background colour.
    pub bg: Color,
    /// Attribute bits (see [`attr`]).
    pub attrs: u8,
}

impl Cell {
    /// An empty cell: a space with default colours and no attributes.
    pub const BLANK: Cell = Cell {
        ch: ' ',
        fg: Color::Default,
        bg: Color::Default,
        attrs: 0,
    };
}

/// The current drawing pen (SGR state).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Pen {
    fg: Color,
    bg: Color,
    attrs: u8,
}

impl Pen {
    const fn reset() -> Pen {
        Pen {
            fg: Color::Default,
            bg: Color::Default,
            attrs: 0,
        }
    }
}

/// A terminal screen: the foldable state. Build one with [`fold`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Screen {
    cols: u16,
    rows: u16,
    grid: Vec<Cell>,
    row: u16,
    col: u16,
    pen: Pen,
    cursor_visible: bool,
    altscreen: bool,
    saved_main: Option<Vec<Cell>>,
    /// The main screen's DECSC slot (`ESC 7` / `CSI s`, and the `?1049` round
    /// trip). Never consumed by a restore.
    saved_cursor: Option<(u16, u16)>,
    /// The alternate screen's own DECSC slot — `Some` only while the alternate
    /// screen is active; a DECSC issued there never clobbers the main slot.
    alt_saved_cursor: Option<(u16, u16)>,
    /// Top row of the DEC scrolling region (`DECSTBM`), 0-based inclusive.
    scroll_top: u16,
    /// Bottom row of the DEC scrolling region (`DECSTBM`), 0-based inclusive.
    /// `(scroll_top, scroll_bottom) == (0, rows-1)` means the full screen scrolls.
    scroll_bottom: u16,
}

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
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Folder {
    screen: Screen,
    parser: Parser,
}

impl Folder {
    /// A fresh folder over a blank screen of the given size.
    pub fn new(cols: u16, rows: u16) -> Folder {
        Folder {
            screen: Screen::new(cols, rows),
            parser: Parser::new(),
        }
    }

    /// Advance by one record. `In`/`Exit` do not paint (only echoed `Out` does).
    pub fn apply(&mut self, record: &Record) {
        match record {
            Record::Out(bytes) => self.parser.feed(&mut self.screen, bytes),
            Record::Resize { cols, rows } => {
                self.screen.resize(*cols, *rows);
                self.parser.rec(ScreenOp::Resize(*cols, *rows));
            }
            Record::In { .. } | Record::Exit { .. } => {}
        }
    }

    /// The current screen.
    pub fn screen(&self) -> &Screen {
        &self.screen
    }

    /// Consume the folder, returning its screen.
    pub fn into_screen(self) -> Screen {
        self.screen
    }
}

impl Screen {
    /// A blank screen of the given size (each edge clamped to `1..=`[`MAX_DIM`]).
    pub fn new(cols: u16, rows: u16) -> Screen {
        let cols = cols.clamp(1, MAX_DIM);
        let rows = rows.clamp(1, MAX_DIM);
        Screen {
            cols,
            rows,
            grid: vec![Cell::BLANK; cols as usize * rows as usize],
            row: 0,
            col: 0,
            pen: Pen::reset(),
            cursor_visible: true,
            altscreen: false,
            saved_main: None,
            saved_cursor: None,
            alt_saved_cursor: None,
            scroll_top: 0,
            scroll_bottom: rows - 1,
        }
    }

    /// Current `(cols, rows)`.
    pub fn dims(&self) -> (u16, u16) {
        (self.cols, self.rows)
    }

    /// Cursor position as `(row, col)`, 0-based. `col` equals `cols` while a
    /// line-wrap is pending (deferred wrap: the cursor sits past the last
    /// column until the next glyph wraps or cursor motion resolves it).
    pub fn cursor(&self) -> (u16, u16) {
        (self.row, self.col)
    }

    /// Whether the cursor is currently visible (`?25`).
    pub fn cursor_visible(&self) -> bool {
        self.cursor_visible
    }

    /// Whether the alternate screen is active.
    pub fn is_altscreen(&self) -> bool {
        self.altscreen
    }

    /// The cell at `(row, col)`, or `None` if out of bounds.
    pub fn cell(&self, row: u16, col: u16) -> Option<&Cell> {
        if row < self.rows && col < self.cols {
            self.grid.get(self.idx(row, col))
        } else {
            None
        }
    }

    /// Overlay a single cell. Used by speculative echo to paint an unconfirmed
    /// prediction onto a copy of the authoritative screen. No-op if out of bounds.
    pub fn set_cell(&mut self, row: u16, col: u16, cell: Cell) {
        if row < self.rows && col < self.cols {
            let i = self.idx(row, col);
            self.grid[i] = cell;
        }
    }

    /// The text of a row, with trailing blanks trimmed. Empty if out of bounds.
    pub fn line_text(&self, row: u16) -> String {
        if row >= self.rows {
            return String::new();
        }
        let start = self.idx(row, 0);
        let mut line: String = self.grid[start..start + self.cols as usize]
            .iter()
            .map(|c| c.ch)
            .collect();
        line.truncate(line.trim_end().len());
        line
    }

    /// A deterministic byte encoding of the **entire** screen state — the visible
    /// grid, cursor, modes, the current SGR pen, and the saved cursors /
    /// alternate-screen grid. Two screens are equal under the derived `Eq` iff
    /// they serialize to the same bytes (the encoding is self-delimiting, hence
    /// injective); that is what the replay/fork/cut/echo oracles and
    /// [`crate::render::frame_hash`] rely on, and what the replay claim pins.
    pub fn serialize(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(16 + self.grid.len() * 9);
        self.serialize_into(&mut out);
        out
    }

    /// [`serialize`](Self::serialize), streamed into `out` instead of collected, so
    /// a consumer that only hashes the encoding never materializes it.
    pub(crate) fn serialize_into<S: ByteSink>(&self, out: &mut S) {
        out.extend_from_slice(&self.cols.to_le_bytes());
        out.extend_from_slice(&self.rows.to_le_bytes());
        out.extend_from_slice(&self.row.to_le_bytes());
        out.extend_from_slice(&self.col.to_le_bytes());
        out.push(self.cursor_visible as u8);
        out.push(self.altscreen as u8);
        let put_cell = |out: &mut S, cell: &Cell| {
            out.extend_from_slice(&(cell.ch as u32).to_le_bytes());
            let (ft, fv) = enc_color(cell.fg);
            out.push(ft);
            out.push(fv);
            let (bt, bv) = enc_color(cell.bg);
            out.push(bt);
            out.push(bv);
            out.push(cell.attrs);
        };
        for cell in &self.grid {
            put_cell(out, cell);
        }
        // Internal state that derived `Eq` distinguishes but the grid alone does
        // not — without these, two unequal screens could serialize identically
        // (e.g. a pending SGR pen with nothing yet printed). The grid length is
        // fixed by cols*rows above, so what follows is self-delimiting.
        let (pft, pfv) = enc_color(self.pen.fg);
        out.push(pft);
        out.push(pfv);
        let (pbt, pbv) = enc_color(self.pen.bg);
        out.push(pbt);
        out.push(pbv);
        out.push(self.pen.attrs);
        let put_cursor = |out: &mut S, cursor: Option<(u16, u16)>| match cursor {
            Some((r, c)) => {
                out.push(1);
                out.extend_from_slice(&r.to_le_bytes());
                out.extend_from_slice(&c.to_le_bytes());
            }
            None => out.push(0),
        };
        put_cursor(out, self.saved_cursor);
        match &self.saved_main {
            Some(cells) => {
                out.push(1);
                out.extend_from_slice(&(cells.len() as u32).to_le_bytes());
                for cell in cells {
                    put_cell(out, cell);
                }
                // The alternate screen's DECSC slot lives and dies with the
                // alternate grid, so it is encoded exactly when that grid is.
                put_cursor(out, self.alt_saved_cursor);
            }
            None => {
                debug_assert!(self.alt_saved_cursor.is_none());
                out.push(0);
            }
        }
        out.extend_from_slice(&self.scroll_top.to_le_bytes());
        out.extend_from_slice(&self.scroll_bottom.to_le_bytes());
    }

    // --- internal mutators ------------------------------------------------

    fn idx(&self, row: u16, col: u16) -> usize {
        row as usize * self.cols as usize + col as usize
    }

    /// Resolve a pending wrap (`col == cols`) back onto the last column: what
    /// xterm's cursor-motion primitives do to the last-column flag before they
    /// move (CR/LF/BS/CUB/CUU/CUD/CUP, DECRC). TAB and erase deliberately do not.
    fn clear_pending_wrap(&mut self) {
        self.col = self.col.min(self.cols - 1);
    }

    fn put(&mut self, ch: char) {
        // Deferred wrap: a pending wrap (col == cols) resolves on the next glyph.
        if self.col >= self.cols {
            self.col = 0;
            self.line_feed();
        }
        let i = self.idx(self.row, self.col);
        self.grid[i] = Cell {
            ch,
            fg: self.pen.fg,
            bg: self.pen.bg,
            attrs: self.pen.attrs,
        };
        self.col += 1; // may reach `cols`, leaving a wrap pending
    }

    fn carriage_return(&mut self) {
        self.col = 0;
    }

    fn line_feed(&mut self) {
        // LF is a cursor-down: it resolves a pending wrap (xterm CursorDown),
        // so `abcd LF Z` on four columns puts Z on the last column of the next
        // row rather than wrapping a second time.
        self.clear_pending_wrap();
        if self.row == self.scroll_bottom {
            // At the bottom of the scrolling region: scroll the region up.
            self.scroll_up();
        } else if self.row + 1 < self.rows {
            self.row += 1;
        }
    }

    /// Scroll the active region `[scroll_top, scroll_bottom]` up one line: the top
    /// row of the region is discarded and a blank row appears at its bottom. Rows
    /// outside the region are untouched. With the default full-screen region this
    /// is the ordinary full-screen scroll.
    fn scroll_up(&mut self) {
        let w = self.cols as usize;
        let start = self.scroll_top as usize * w;
        let end = (self.scroll_bottom as usize + 1) * w;
        self.grid.copy_within(start + w..end, start);
        self.grid[end - w..end].fill(Cell::BLANK);
    }

    /// `DECSTBM`: set the scrolling region to 0-based inclusive `[top, bottom]`
    /// and home the cursor. As in xterm's `CASE_DECSTBM`, a `bottom` past the
    /// screen means the last row, and a region that is empty after that clamp
    /// (`top >= bottom`) is ignored entirely: neither the margins nor the cursor
    /// change.
    fn set_scroll_region(&mut self, top: u16, bottom: u16) {
        let bottom = bottom.min(self.rows - 1);
        if top < bottom {
            self.scroll_top = top;
            self.scroll_bottom = bottom;
            self.row = 0;
            self.col = 0;
        }
    }

    fn tab(&mut self) {
        // A pending wrap survives a TAB (xterm's TabToNextStop never touches the
        // last-column flag): the next glyph still wraps.
        if self.col >= self.cols {
            return;
        }
        // Advance to the next 8-column tab stop, not past the last column.
        let next = (self.col / 8 + 1).saturating_mul(8);
        self.col = next.min(self.cols - 1);
    }

    fn backspace(&mut self) {
        // From a pending wrap the cursor is ON the last column (xterm), so BS
        // lands on the second-to-last: `abcde BS X` is `abcXe`, never `abcdX`.
        self.clear_pending_wrap();
        self.col = self.col.saturating_sub(1);
    }

    fn move_to(&mut self, row: u16, col: u16) {
        self.row = row.min(self.rows - 1);
        self.col = col.min(self.cols - 1);
    }

    /// CUU. As in xterm's `CursorUp`, a cursor at or below the top margin stops
    /// at it; one above the region may go to row 0.
    fn cursor_up(&mut self, n: u16) {
        self.clear_pending_wrap();
        let min = if self.row >= self.scroll_top {
            self.scroll_top
        } else {
            0
        };
        self.row = self.row.saturating_sub(n).max(min);
    }

    /// CUD. As in xterm's `CursorDown`, a cursor at or above the bottom margin
    /// stops at it; one below the region may go to the last row.
    fn cursor_down(&mut self, n: u16) {
        self.clear_pending_wrap();
        let max = if self.row <= self.scroll_bottom {
            self.scroll_bottom
        } else {
            self.rows - 1
        };
        // saturating_add: a CSI param up to 65535 must not overflow u16.
        self.row = self.row.saturating_add(n).min(max);
    }

    fn cursor_forward(&mut self, n: u16) {
        self.col = self.col.saturating_add(n).min(self.cols - 1);
    }

    fn cursor_back(&mut self, n: u16) {
        // Like BS: resolve a pending wrap onto the last column, then move.
        self.clear_pending_wrap();
        self.col = self.col.saturating_sub(n);
    }

    /// The grid index erase-to-end starts at, and the one erase-to-cursor ends
    /// before. A pending wrap (`col == cols`) sits logically one past the last
    /// cell (xterm/aterm): erase-to-end then leaves the parked glyph — and the
    /// pending wrap — alone, while erase-to-cursor includes that cell.
    fn erase_bounds(&self) -> (usize, usize) {
        let from_cursor = self.idx(self.row, self.col);
        let through_cursor = self.idx(self.row, self.col.min(self.cols - 1)) + 1;
        (from_cursor, through_cursor)
    }

    fn erase_display(&mut self, mode: u16) {
        let (from_cursor, through_cursor) = self.erase_bounds();
        let last = self.grid.len();
        match mode {
            0 => self.fill(from_cursor, last), // cursor to end
            1 => self.fill(0, through_cursor), // start to cursor (inclusive)
            2 | 3 => self.fill(0, last),       // entire display
            _ => {}
        }
    }

    fn erase_line(&mut self, mode: u16) {
        let start = self.idx(self.row, 0);
        let end = start + self.cols as usize;
        let (from_cursor, through_cursor) = self.erase_bounds();
        match mode {
            0 => self.fill(from_cursor, end),      // cursor to end of line
            1 => self.fill(start, through_cursor), // start of line to cursor
            2 => self.fill(start, end),            // whole line
            _ => {}
        }
    }

    /// An erased cell under background-colour-erase (`bce`): a space carrying the
    /// **current SGR background**, so `ED`/`EL` after `\x1b[44m` paints blue, not a
    /// hardcoded default blank. (Reverse-video bce is out of scope.)
    fn bce_blank(&self) -> Cell {
        Cell {
            ch: ' ',
            fg: Color::Default,
            bg: self.pen.bg,
            attrs: 0,
        }
    }

    fn fill(&mut self, from: usize, to: usize) {
        let blank = self.bce_blank();
        let to = to.min(self.grid.len());
        for cell in &mut self.grid[from..to] {
            *cell = blank;
        }
    }

    /// Apply an SGR parameter list. `sub[i]` marks `params[i]` as a `:`
    /// sub-parameter of the preceding parameter (`38:5:196`) rather than a
    /// `;`-separated parameter of its own; a colon group is handled as one unit so
    /// a sub-parameter is never re-dispatched as a top-level code.
    fn sgr(&mut self, params: &[u16], sub: &[bool]) {
        if params.is_empty() {
            self.pen = Pen::reset();
            return;
        }
        let is_sub = |i: usize| sub.get(i).copied().unwrap_or(false);
        let mut i = 0;
        while i < params.len() {
            let mut end = i + 1;
            while end < params.len() && is_sub(end) {
                end += 1;
            }
            if end > i + 1 {
                self.sgr_colon(&params[i..end]);
                i = end;
                continue;
            }
            match params[i] {
                0 => self.pen = Pen::reset(),
                1 => self.pen.attrs |= attr::BOLD,
                4 => self.pen.attrs |= attr::UNDERLINE,
                7 => self.pen.attrs |= attr::REVERSE,
                22 => self.pen.attrs &= !attr::BOLD,
                24 => self.pen.attrs &= !attr::UNDERLINE,
                27 => self.pen.attrs &= !attr::REVERSE,
                30..=37 => self.pen.fg = Color::Indexed((params[i] - 30) as u8),
                39 => self.pen.fg = Color::Default,
                40..=47 => self.pen.bg = Color::Indexed((params[i] - 40) as u8),
                49 => self.pen.bg = Color::Default,
                90..=97 => self.pen.fg = Color::Indexed((params[i] - 90 + 8) as u8),
                100..=107 => self.pen.bg = Color::Indexed((params[i] - 100 + 8) as u8),
                38 => {
                    if let Some(c) = parse_extended(params, &mut i) {
                        self.pen.fg = c;
                    }
                }
                48 => {
                    if let Some(c) = parse_extended(params, &mut i) {
                        self.pen.bg = c;
                    }
                }
                _ => {}
            }
            i += 1;
        }
    }

    /// One colon group: `g[0]` is the code, `g[1..]` its sub-parameters.
    fn sgr_colon(&mut self, g: &[u16]) {
        match g[0] {
            // `4:0` is underline off; `4:n` a styled underline (modelled as plain).
            4 => {
                if g[1] == 0 {
                    self.pen.attrs &= !attr::UNDERLINE;
                } else {
                    self.pen.attrs |= attr::UNDERLINE;
                }
            }
            38 => {
                if let Some(c) = parse_colon_colour(&g[1..]) {
                    self.pen.fg = c;
                }
            }
            48 => {
                if let Some(c) = parse_colon_colour(&g[1..]) {
                    self.pen.bg = c;
                }
            }
            _ => {} // 58 (underline colour) and any other sub-parameterised code
        }
    }

    fn set_mode(&mut self, params: &[u16], set: bool) {
        for &p in params {
            match p {
                25 => self.cursor_visible = set,
                // `?1049` is DECSC + switch on set, switch + DECRC on reset — into
                // the SAME per-buffer slot DECSC uses, so a later bare `ESC 8` on
                // the main screen still restores the position `?1049h` saved.
                1049 => {
                    if set {
                        self.save_cursor();
                        self.enter_alt();
                    } else {
                        self.leave_alt();
                        self.restore_cursor();
                    }
                }
                // `?47`/`?1047` only swap buffers; the cursor is shared and stays.
                47 | 1047 => {
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

    fn enter_alt(&mut self) {
        if self.altscreen {
            return;
        }
        let blank = vec![Cell::BLANK; self.cols as usize * self.rows as usize];
        self.saved_main = Some(std::mem::replace(&mut self.grid, blank));
        self.alt_saved_cursor = None;
        self.altscreen = true;
    }

    fn leave_alt(&mut self) {
        if !self.altscreen {
            return;
        }
        if let Some(main) = self.saved_main.take() {
            self.grid = main;
        }
        self.alt_saved_cursor = None;
        self.altscreen = false;
    }

    /// DECSC: save the cursor into the active buffer's slot (one per buffer, as
    /// xterm) — a save inside the alternate screen never clobbers the main slot.
    fn save_cursor(&mut self) {
        let slot = if self.altscreen {
            &mut self.alt_saved_cursor
        } else {
            &mut self.saved_cursor
        };
        *slot = Some((self.row, self.col));
    }

    /// DECRC: restore from the active buffer's slot without consuming it (a
    /// saved pending wrap is kept). With nothing saved the cursor homes, per
    /// DEC STD 070 and xterm.
    fn restore_cursor(&mut self) {
        let slot = if self.altscreen {
            self.alt_saved_cursor
        } else {
            self.saved_cursor
        };
        let (r, c) = slot.unwrap_or((0, 0));
        self.row = r.min(self.rows - 1);
        self.col = c.min(self.cols);
    }

    fn reset(&mut self) {
        *self = Screen::new(self.cols, self.rows);
    }

    fn resize(&mut self, cols: u16, rows: u16) {
        let cols = cols.clamp(1, MAX_DIM);
        let rows = rows.clamp(1, MAX_DIM);
        self.grid = reflow(&self.grid, self.cols, self.rows, cols, rows);
        if let Some(saved) = &self.saved_main {
            self.saved_main = Some(reflow(saved, self.cols, self.rows, cols, rows));
        }
        self.cols = cols;
        self.rows = rows;
        self.row = self.row.min(rows - 1);
        self.col = self.col.min(cols);
        // A resize invalidates the scrolling region: reset it to the full screen.
        self.scroll_top = 0;
        self.scroll_bottom = rows - 1;
    }
}

fn enc_color(c: Color) -> (u8, u8) {
    match c {
        Color::Default => (0, 0),
        Color::Indexed(n) => (1, n),
    }
}

/// Clip/extend a grid into new dimensions, copying the overlapping top-left
/// region. Does not reflow wrapped lines (a later rung).
fn reflow(old: &[Cell], old_cols: u16, old_rows: u16, new_cols: u16, new_rows: u16) -> Vec<Cell> {
    let mut g = vec![Cell::BLANK; new_cols as usize * new_rows as usize];
    let rows = old_rows.min(new_rows);
    let cols = old_cols.min(new_cols);
    for r in 0..rows {
        for c in 0..cols {
            g[r as usize * new_cols as usize + c as usize] =
                old[r as usize * old_cols as usize + c as usize];
        }
    }
    g
}

/// Parse the `;`-form extended colour selector after a `38`/`48` at `params[*i]`,
/// advancing `i` past everything it consumed. `;5;n` selects a palette colour.
/// Truecolour `;2;r;g;b` (and CMY `;3;c;m;y`, CMYK `;4;c;m;y;k`) are out of scope
/// and select nothing, but are consumed *with* their sub-parameters — otherwise
/// `r`, `g`, `b` would be re-dispatched as top-level codes (`0` resetting the
/// pen, `1` setting bold, `30..37` recolouring). Any other selector consumes
/// itself; a truncated form consumes what is there.
fn parse_extended(params: &[u16], i: &mut usize) -> Option<Color> {
    let last = params.len() - 1;
    let (after_selector, colour) = match params.get(*i + 1) {
        None => return None,
        Some(5) => (
            1,
            params
                .get(*i + 2)
                .map(|n| Color::Indexed((*n).min(255) as u8)),
        ),
        Some(2) | Some(3) => (3, None),
        Some(4) => (4, None),
        Some(_) => (0, None),
    };
    *i = (*i + 1 + after_selector).min(last);
    colour
}

/// The `:`-form colour sub-parameters after `38`/`48`: `5:n` selects a palette
/// colour; `2:r:g:b` / `2:cs:r:g:b` (truecolour) select nothing.
fn parse_colon_colour(sub: &[u16]) -> Option<Color> {
    match sub.first() {
        Some(5) => sub.get(1).map(|n| Color::Indexed((*n).min(255) as u8)),
        _ => None,
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
    /// Mid UTF-8 multibyte sequence: bytes still needed, accumulated codepoint,
    /// and the smallest codepoint this sequence length may legally encode.
    Utf8 {
        needed: u8,
        acc: u32,
        min: u32,
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

/// A persistent byte→action state machine. Persisting it across [`Parser::feed`]
/// calls is what lets an escape sequence (or a multibyte glyph) span two `Out`
/// records without corrupting the fold. Its state is bounded: a small enum, two
/// bytes, and at most [`CSI_PARAM_MAX`] parameter bytes.
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
            recording: false,
            ops: Vec::new(),
        }
    }

    /// Record one top-level op (no-op unless recording). Internal mutator
    /// cascades (deferred-wrap line-feed, line-feed scroll) are deliberately NOT
    /// recorded — they reproduce deterministically when the op is re-applied.
    fn rec(&mut self, op: ScreenOp) {
        if self.recording {
            self.ops.push(op);
        }
    }

    fn feed(&mut self, screen: &mut Screen, bytes: &[u8]) {
        for &b in bytes {
            match self.state {
                State::Ground => self.ground(screen, b),
                State::Esc => self.escape(screen, b),
                State::EscIntermediate => self.esc_intermediate(screen, b),
                State::Csi => self.csi(screen, b),
                State::Str { bel_ends } => self.string(b, bel_ends),
                State::Utf8 { needed, acc, min } => self.utf8_cont(screen, b, needed, acc, min),
            }
        }
    }

    fn ground(&mut self, screen: &mut Screen, b: u8) {
        match b {
            0x1b => self.state = State::Esc,
            b'\n' => {
                screen.line_feed();
                self.rec(ScreenOp::LineFeed);
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
            0x00..=0x1f | 0x7f => {} // other C0 controls and DEL: ignored
            0x20..=0x7e => {
                screen.put(b as char);
                self.rec(ScreenOp::Print(b as char));
            }
            _ => self.begin_utf8(screen, b),
        }
    }

    fn begin_utf8(&mut self, screen: &mut Screen, b: u8) {
        let (needed, acc, min) = match b {
            0xc0..=0xdf => (1u8, (b & 0x1f) as u32, 0x80),
            0xe0..=0xef => (2u8, (b & 0x0f) as u32, 0x800),
            0xf0..=0xf7 => (3u8, (b & 0x07) as u32, 0x1_0000),
            _ => {
                // A stray continuation byte or invalid lead: emit the
                // replacement character and stay in the ground state.
                screen.put('\u{fffd}');
                self.rec(ScreenOp::Print('\u{fffd}'));
                return;
            }
        };
        self.state = State::Utf8 { needed, acc, min };
    }

    fn utf8_cont(&mut self, screen: &mut Screen, b: u8, needed: u8, acc: u32, min: u32) {
        if (0x80..=0xbf).contains(&b) {
            let acc = (acc << 6) | (b & 0x3f) as u32;
            if needed <= 1 {
                self.state = State::Ground;
                if acc < min {
                    // Overlong: `C0 80` or `E0 80 8A` would decode to a control
                    // character — reject it as malformed, never put it in a cell.
                    screen.put('\u{fffd}');
                    self.rec(ScreenOp::Print('\u{fffd}'));
                } else if (0x80..=0x9f).contains(&acc) {
                    // A validly encoded C1 control: not modelled, ignored.
                } else {
                    let ch = char::from_u32(acc).unwrap_or('\u{fffd}');
                    screen.put(ch);
                    self.rec(ScreenOp::Print(ch));
                }
            } else {
                self.state = State::Utf8 {
                    needed: needed - 1,
                    acc,
                    min,
                };
            }
        } else {
            // Truncated sequence: emit replacement, then reprocess `b` fresh.
            self.state = State::Ground;
            screen.put('\u{fffd}');
            self.rec(ScreenOp::Print('\u{fffd}'));
            self.ground(screen, b);
        }
    }

    fn escape(&mut self, screen: &mut Screen, b: u8) {
        match b {
            b'[' => {
                self.params.clear();
                self.marker = 0;
                self.csi_ignore = false;
                self.state = State::Csi;
            }
            b']' => self.state = State::Str { bel_ends: true }, // OSC
            b'P' | b'X' | b'^' | b'_' => self.state = State::Str { bel_ends: false }, // DCS/SOS/PM/APC
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
                self.rec(ScreenOp::Reset);
                self.state = State::Ground;
            }
            0x20..=0x2f => self.state = State::EscIntermediate, // ESC ( B etc.
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
            0x20..=0x2f | 0x7f => {}
            0x30..=0x7e => self.state = State::Ground, // the final byte: consumed
            _ => {
                self.state = State::Ground;
                self.ground(screen, b);
            }
        }
    }

    /// An OSC/DCS/APC/PM/SOS string body: swallowed byte by byte. `ESC` ends it
    /// (as `ESC \`, or as the start of a new escape), BEL ends an OSC, CAN/SUB
    /// abort; nothing is ever painted.
    fn string(&mut self, b: u8, bel_ends: bool) {
        match b {
            0x1b => self.state = State::Esc,
            0x07 if bel_ends => self.state = State::Ground,
            0x18 | 0x1a => self.state = State::Ground,
            _ => {}
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
        // Which (marker, final) pairs the fold models: plain sequences (SM/RM
        // `h`/`l` excepted), DEC private modes, and DECSED/DECSEL (`? J`/`? K`,
        // which erase like ED/EL with no protected cells). `>`/`=`/`<`-marked
        // sequences (XTMODKEYS `> Ps m`, tertiary DA, …) are consumed whole.
        match (self.marker, final_byte) {
            (0, b'h' | b'l') => return,
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
                    b'0'..=b'9' => cur = cur.saturating_mul(10).saturating_add((c - b'0') as u16),
                    _ => {
                        vals[n] = cur;
                        sub[n] = cur_sub;
                        n += 1;
                        cur = 0;
                        cur_sub = c == b':';
                    }
                }
            }
            vals[n] = cur;
            sub[n] = cur_sub;
            n += 1;
        }
        let (vals, sub) = (&vals[..n], &sub[..n]);
        // Outside SGR a sub-parameter carries nothing the fold models.
        let mut nums = [0u16; CSI_PARAM_MAX + 1];
        let mut m = 0;
        for (&v, &s) in vals.iter().zip(sub) {
            if !s {
                nums[m] = v;
                m += 1;
            }
        }
        let nums = &nums[..m];
        // A movement count: the param, treating 0/absent as 1.
        let count = |i: usize| match nums.get(i).copied() {
            Some(0) | None => 1,
            Some(n) => n,
        };
        // A 1-based coordinate → 0-based, treating 0/absent as 1 → 0.
        let coord = |i: usize| count(i) - 1;

        match final_byte {
            b'A' => {
                screen.cursor_up(count(0));
                self.rec(ScreenOp::CursorUp(count(0)));
            }
            b'B' => {
                screen.cursor_down(count(0));
                self.rec(ScreenOp::CursorDown(count(0)));
            }
            b'C' => {
                screen.cursor_forward(count(0));
                self.rec(ScreenOp::CursorForward(count(0)));
            }
            b'D' => {
                screen.cursor_back(count(0));
                self.rec(ScreenOp::CursorBack(count(0)));
            }
            b'E' => {
                screen.cursor_down(count(0));
                screen.carriage_return();
                self.rec(ScreenOp::CursorDown(count(0)));
                self.rec(ScreenOp::CarriageReturn);
            }
            b'F' => {
                screen.cursor_up(count(0));
                screen.carriage_return();
                self.rec(ScreenOp::CursorUp(count(0)));
                self.rec(ScreenOp::CarriageReturn);
            }
            b'G' => {
                let (r, _) = screen.cursor();
                screen.move_to(r, coord(0));
                self.rec(ScreenOp::MoveTo(r, coord(0)));
            }
            b'd' => {
                let (_, c) = screen.cursor();
                screen.move_to(coord(0), c);
                self.rec(ScreenOp::MoveTo(coord(0), c));
            }
            b'H' | b'f' => {
                screen.move_to(coord(0), coord(1));
                self.rec(ScreenOp::MoveTo(coord(0), coord(1)));
            }
            b'J' => {
                let m = nums.first().copied().unwrap_or(0);
                screen.erase_display(m);
                self.rec(ScreenOp::EraseDisplay(m));
            }
            b'K' => {
                let m = nums.first().copied().unwrap_or(0);
                screen.erase_line(m);
                self.rec(ScreenOp::EraseLine(m));
            }
            b'm' => {
                screen.sgr(vals, sub);
                // Record the RESOLVED pen (after sgr ran), not the raw params —
                // this is what kills the two-party terminfo-disagreement class.
                self.rec(ScreenOp::SetSgr {
                    fg: screen.pen.fg,
                    bg: screen.pen.bg,
                    attrs: screen.pen.attrs,
                });
            }
            b'h' | b'l' => {
                let set = final_byte == b'h';
                screen.set_mode(nums, set);
                if self.recording {
                    self.rec(ScreenOp::SetMode {
                        params: nums.to_vec(),
                        set,
                    });
                }
            }
            b'r' => {
                // DECSTBM: set the scrolling region [top; bottom] (1-based, inclusive).
                // Absent/0 top -> 1; absent/0 bottom -> last row. Converted to 0-based.
                let (_, rows) = screen.dims();
                let top0 = count(0) - 1;
                let bottom0 = match nums.get(1).copied() {
                    Some(0) | None => rows - 1,
                    Some(n) => n - 1,
                };
                screen.set_scroll_region(top0, bottom0);
                self.rec(ScreenOp::SetScrollRegion {
                    top: top0,
                    bottom: bottom0,
                });
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

/// Re-apply a screen-op stream to a fresh screen, re-driving the **same** private
/// mutators from typed ops — an independent dispatch path that bypasses only the
/// VT state machine. Reproduces the fold's screen byte-for-byte.
pub fn apply_ops(cols: u16, rows: u16, ops: &[ScreenOp]) -> Screen {
    let mut screen = Screen::new(cols, rows);
    for op in ops {
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
            ScreenOp::EraseDisplay(m) => screen.erase_display(*m),
            ScreenOp::EraseLine(m) => screen.erase_line(*m),
            ScreenOp::SetSgr { fg, bg, attrs } => {
                screen.pen = Pen {
                    fg: *fg,
                    bg: *bg,
                    attrs: *attrs,
                }
            }
            ScreenOp::SetMode { params, set } => screen.set_mode(params, *set),
            ScreenOp::SaveCursor => screen.save_cursor(),
            ScreenOp::RestoreCursor => screen.restore_cursor(),
            ScreenOp::SetScrollRegion { top, bottom } => screen.set_scroll_region(*top, *bottom),
            ScreenOp::Reset => screen.reset(),
            ScreenOp::Resize(c, r) => screen.resize(*c, *r),
        }
    }
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
