//! Semantic session events — the boundaries a driving agent wakes on.
//!
//! [`crate::perceive`] and [`crate::screen`] give the screen *state* at any
//! offset. This module adds the *semantic* layer the drive-pipe pump needs: not
//! "the bytes changed" but "the prompt is ready", "a command started", "a
//! command finished (exit N)", "the screen settled". It is the same
//! program-agnostic, deterministic, I/O-free projection of the recorded `Out`
//! log — the difference between a raw delta stream and a wake signal, so a
//! turn-based agent driving this session sleeps until a real boundary instead of
//! polling every frame.
//!
//! Signals, most to least authoritative:
//!
//! 1. **OSC-133 / OSC-633 shell-integration marks** (FinalTerm / iTerm2 /
//!    VS Code): `A` prompt-start, `C` output-start (a command is running), `D`
//!    command-end with an optional exit code. Program-agnostic and exact — any
//!    integrated shell emits them, and they are already in the byte stream.
//! 2. **A quiescence point** — the offset after which the folded screen never
//!    changes again (`frame_hash`-stable). The fallback "settled" wake for a
//!    program with no shell integration.
//! 3. **Per-program prompt glyphs** (a [`Profile`]) — the settled screen's last
//!    non-empty line ends with a known marker (Claude Code's `❯`, a REPL's
//!    `>>>`, a shell's `$`/`%`/`#`). Prompt-ready for a program that emits no
//!    OSC-133 — and **only** for such a program: once a session has shown a
//!    single OSC-133/633 **`A`, `C` or `D`** mark, signal 1 owns prompt-ready
//!    and the glyph profile is off, so an integrated shell's stalled progress
//!    line ending in `%` or `#` (or a nested program's prompt while a command
//!    is in flight — `C` seen, no `D`) is never read as a prompt. The gate is
//!    those three lifecycle letters, not any mark: a `B`/`E`/`P` (or unknown)
//!    letter is not a wake and does not hand prompt-ready to signal 1, so one
//!    stray mark in the byte stream cannot permanently blind the profile.
//!    Codex's `»` composer is deliberately *not* a marker: it is visible while
//!    Codex works, so its wake is quiescence (DESIGN-drive-pipe.md §5).
//!
//! **Timeline order** (the same for [`classify`] and a fully-fed
//! [`EventClassifier`]): the OSC mark events in record order, then the settle
//! events — `Quiesced` at the settle point and, for a non-integrated target, a
//! glyph `PromptReady` there. Mark events are offset-ascending among themselves;
//! the settle events come last even when a mark landed *after* the settle point
//! (a record that carries a mark but repaints nothing), so a consumer must not
//! assume a global offset sort. This is the only order a stream can produce
//! without buffering, so the batch classifier produces it too.

use crate::record::Record;
use crate::render::frame_hash;
use crate::screen::{Folder, Screen};

/// A classified boundary in a recorded session. `offset` is the record index
/// that produced it (records are position-addressed at this rung).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SessionEvent {
    /// The prompt is ready for input (OSC-133 `A`, or a [`Profile`] glyph at
    /// quiescence).
    PromptReady {
        /// Record index that produced the event.
        offset: usize,
    },
    /// A command began executing (OSC-133 `C`).
    CommandStart {
        /// Record index that produced the event.
        offset: usize,
    },
    /// A command finished (OSC-133 `D`); `exit` is its status when reported.
    CommandEnd {
        /// Record index that produced the event.
        offset: usize,
        /// The reported exit status, if the mark carried one.
        exit: Option<i32>,
    },
    /// The screen settled and stopped changing at this offset.
    Quiesced {
        /// Record index after which `frame_hash` is stable.
        offset: usize,
    },
}

impl SessionEvent {
    /// The record index this event is anchored to.
    #[must_use]
    pub fn offset(&self) -> usize {
        match *self {
            SessionEvent::PromptReady { offset }
            | SessionEvent::CommandStart { offset }
            | SessionEvent::CommandEnd { offset, .. }
            | SessionEvent::Quiesced { offset } => offset,
        }
    }
}

/// Per-program prompt recognition for targets **without** OSC-133 shell
/// integration (an agent TUI, a bare REPL). The settled screen's last non-empty
/// line ending with one of `prompt_markers` is read as prompt-ready.
///
/// This is an end-of-line glyph match at quiescence and nothing more: there is
/// no separate spinner/idle predicate. A spinner keeps `frame_hash` churning, so
/// the screen does not settle — and the glyph is not consulted — until it has
/// cleared. The profile is ignored entirely once the session has emitted an
/// OSC-133/633 `A`, `C` or `D` mark (see the module doc).
#[derive(Debug, Clone, Default)]
pub struct Profile {
    /// End-of-line markers that mean "prompt ready" (matched against the trimmed
    /// last non-empty line).
    pub prompt_markers: Vec<String>,
}

impl Profile {
    /// A profile covering the common interactive agents, REPLs, and shells:
    /// Claude Code's `❯` idle box, a REPL's `>>>`, a shell's `$`/`%`/`#`.
    /// Codex's `»` composer is excluded on purpose — it is visible while Codex
    /// is still working, so a `»` at quiescence would wake the driver
    /// mid-turn; Codex's wake is `Quiesced` (DESIGN-drive-pipe.md §5).
    #[must_use]
    pub fn common() -> Self {
        Profile {
            prompt_markers: ["❯", ">>>", "$", "%", "#"]
                .iter()
                .map(|s| (*s).to_string())
                .collect(),
        }
    }
}

// The index just past the run of ASCII digits starting at `b[i]` — used to read
// the OSC command number before the first `;`.
fn digits_end(b: &[u8], mut i: usize) -> usize {
    while i < b.len() && b[i].is_ascii_digit() {
        i += 1;
    }
    i
}

// A shell-mark introducer (`\x1b]133/633;<letter>;<params><term>`) is short; bound
// the bytes we carry for a split/never-terminated one.
const CARRY_MAX: usize = 32;

// True if `code` (the digits right after `\x1b]`) is a prefix of "133" or "633" — a
// mark code that may still complete once more bytes arrive.
fn is_shell_prefix(code: &[u8]) -> bool {
    b"133".starts_with(code) || b"633".starts_with(code)
}

// Scan `b` for COMPLETE OSC-133/633 marks, appending events at `offset`, and RETURN
// the trailing bytes of an unterminated potential shell-mark to prepend to the next
// record (bounded; empty if none). Threading this carry across records is what makes
// a mark split across two PTY reads (two `Out` records) still recognised — otherwise
// a `\x1b]133;D;0\x07` split as `…\x1b]133;` | `D;0\x07` is silently lost.
// `integrated` is set once a complete 133/633 `A`, `C` or `D` mark has been seen: the
// session's shell integration owns the prompt/command lifecycle, and the glyph profile
// must stay out of its way. A `B`/`E`/`P` or unknown letter does NOT set it.
fn scan_marks(
    b: &[u8],
    offset: usize,
    out: &mut Vec<SessionEvent>,
    integrated: &mut bool,
) -> Vec<u8> {
    let mut i = 0;
    while i < b.len() {
        if b[i] != 0x1b {
            i += 1;
            continue;
        }
        // A lone trailing ESC could begin `\x1b]` on the next record.
        if i + 1 >= b.len() {
            return vec![0x1b];
        }
        if b[i + 1] != b']' {
            i += 1;
            continue;
        }
        let code_start = i + 2;
        let code_end = digits_end(b, code_start);
        let code = &b[code_start..code_end];
        // The numeric code is still being read at end-of-buffer: carry if it could
        // yet become 133/633.
        if code_end == b.len() {
            return if is_shell_prefix(code) && b.len() - i <= CARRY_MAX {
                b[i..].to_vec()
            } else {
                Vec::new()
            };
        }
        if !matches!(code, b"133" | b"633") || b[code_end] != b';' {
            i += 1; // some other OSC (e.g. a title) — skip its introducer
            continue;
        }
        let letter_idx = code_end + 1;
        if letter_idx >= b.len() {
            // `\x1b]133;` with no letter yet → carry.
            return if b.len() - i <= CARRY_MAX {
                b[i..].to_vec()
            } else {
                Vec::new()
            };
        }
        let letter = b[letter_idx];
        // Collect params up to the terminator (BEL 0x07 or ST ESC \). Any other
        // ESC begins a new escape, as in the fold's parser: the mark is abandoned
        // there and the scan resumes AT that ESC, so a later mark is still seen.
        // An ESC as the last byte may be the first half of a split ST: carry it.
        let mut k = letter_idx + 1;
        let mut terminated = false;
        let mut abandoned = false;
        while k < b.len() {
            if b[k] == 0x07 {
                terminated = true;
                break;
            }
            if b[k] == 0x1b && k + 1 < b.len() {
                if b[k + 1] == b'\\' {
                    terminated = true;
                } else {
                    abandoned = true;
                }
                break;
            }
            k += 1;
        }
        if abandoned {
            i = k;
            continue;
        }
        if !terminated {
            // Unterminated shell mark running off the end → carry it.
            return if b.len() - i <= CARRY_MAX {
                b[i..].to_vec()
            } else {
                Vec::new()
            };
        }
        let params = &b[letter_idx + 1..k];
        match letter {
            b'A' => {
                *integrated = true;
                out.push(SessionEvent::PromptReady { offset });
            }
            b'C' => {
                *integrated = true;
                out.push(SessionEvent::CommandStart { offset });
            }
            b'D' => {
                *integrated = true;
                out.push(SessionEvent::CommandEnd {
                    offset,
                    exit: parse_exit(params),
                });
            }
            // B (input boundary), E (command line), P (property) and any unknown
            // letter are neither wakes NOR proof that signal 1 owns prompt-ready:
            // they carry no prompt/command lifecycle, so they must not switch the
            // glyph profile off. Otherwise one such byte sequence anywhere in the
            // output -- a replayed transcript, a `cat` of a log, a letter a future
            // spec adds -- would permanently blind glyph detection for the session.
            _ => {}
        }
        i = k + if b[k] == 0x07 { 1 } else { 2 }; // past BEL (1) or ST (2)
    }
    Vec::new()
}

// Params look like `;0` / `;127` / `` — parse the exit code after a leading `;`.
fn parse_exit(params: &[u8]) -> Option<i32> {
    let s = std::str::from_utf8(params).ok()?;
    let s = s.strip_prefix(';').unwrap_or(s);
    // A D-mark may carry `<exit>;<extra>`; take the first field.
    let field = s.split(';').next().unwrap_or("");
    field.trim().parse::<i32>().ok()
}

// The settle events over the settled `screen` at settle point `q`: `Quiesced{q}`,
// then — only for a target that has emitted no OSC-133/633 A/C/D mark — a glyph
// `PromptReady{q}` when the last non-empty line ends with a profile marker. Shared
// by the batch and streaming paths so the two cannot disagree on WHAT settles;
// the differential tests cover HOW each gets here (order, carry, state).
fn settle_events(
    screen: &Screen,
    q: usize,
    profile: &Profile,
    integrated: bool,
) -> Vec<SessionEvent> {
    let mut ev = vec![SessionEvent::Quiesced { offset: q }];
    if integrated || profile.prompt_markers.is_empty() {
        return ev;
    }
    let (_, nrows) = screen.dims();
    let last_nonempty = (0..nrows)
        .rev()
        .map(|r| screen.line_text(r))
        .find(|l| !l.is_empty());
    if let Some(line) = last_nonempty {
        let tail = line.trim_end();
        if profile
            .prompt_markers
            .iter()
            .any(|m| tail.ends_with(m.trim_end()))
        {
            ev.push(SessionEvent::PromptReady { offset: q });
        }
    }
    ev
}

/// The quiescence offset: the last record index that changed the folded screen.
/// After it, `frame_hash` is stable — the screen has settled. `None` for an
/// empty log. Folds incrementally, so it is O(bytes), not O(n·bytes).
#[must_use]
pub fn quiesced_at(cols: u16, rows: u16, records: &[Record]) -> Option<usize> {
    if records.is_empty() {
        return None;
    }
    let mut folder = Folder::new(cols, rows);
    let mut last_hash: Option<u64> = None;
    let mut last_change = 0usize;
    for (i, r) in records.iter().enumerate() {
        folder.apply(r);
        let h = frame_hash(folder.screen());
        if last_hash != Some(h) {
            last_change = i;
            last_hash = Some(h);
        }
    }
    Some(last_change)
}

/// Classify a recorded session into its timeline of semantic events, in the
/// **streaming order** (see the module doc): every OSC-133/633 mark event in
/// record order, then the settle events — `Quiesced` at the settle point and,
/// for a target that emitted no OSC-133/633 `A`/`C`/`D` mark, a glyph
/// [`Profile`] `PromptReady` there. A mark that lands after the settle point
/// (its record repaints nothing) precedes `Quiesced` despite its higher offset;
/// there is no global sort. Fed the same records and quiesced once, [`EventClassifier`] produces
/// exactly this sequence — the batch/stream equivalence the pump relies on.
#[must_use]
pub fn classify(cols: u16, rows: u16, records: &[Record], profile: &Profile) -> Vec<SessionEvent> {
    let mut ev = Vec::new();
    let mut carry: Vec<u8> = Vec::new();
    let mut integrated = false;
    for (i, r) in records.iter().enumerate() {
        if let Record::Out(bytes) = r {
            let mut input = std::mem::take(&mut carry);
            input.extend_from_slice(bytes);
            carry = scan_marks(&input, i, &mut ev, &mut integrated);
        }
    }
    if !records.is_empty() {
        // One fold tracks the settle point (the last frame_hash change) and
        // leaves the final screen for the glyph check.
        let mut folder = Folder::new(cols, rows);
        let mut last_hash: Option<u64> = None;
        let mut q = 0usize;
        for (i, r) in records.iter().enumerate() {
            folder.apply(r);
            let h = frame_hash(folder.screen());
            if last_hash != Some(h) {
                q = i;
                last_hash = Some(h);
            }
        }
        ev.extend(settle_events(folder.screen(), q, profile, integrated));
    }
    ev
}

/// A streaming, incremental version of [`classify`] for a live pump: feed
/// records as they arrive off the bus and get wake events as they occur, without
/// re-folding the whole history on every frame. OSC marks fire on [`EventClassifier::push`];
/// the settled-screen signals (`Quiesced` and a glyph `PromptReady`) fire on
/// [`EventClassifier::quiesce`], which the pump calls after a debounce window of
/// no new output. Fed every record of a session and then quiesced once, it
/// produces the same event sequence as [`classify`] (marks in record order, then
/// the settle events) — the streaming/batch equivalence the pump relies on.
///
/// The classifier's own state is bounded for the life of the pump: one screen
/// fold, a hash, two offsets, one `integrated` flag, and a carry of at most 32
/// bytes — nothing grows per prompt or per record. (The fold's parser also holds
/// the parameter bytes of one unterminated CSI; that buffer is
/// [`crate::screen`]'s, and it is capped there.)
#[derive(Debug)]
pub struct EventClassifier {
    folder: Folder,
    profile: Profile,
    next_offset: usize,
    last_hash: Option<u64>,
    last_change: usize,
    // Set once a complete OSC-133/633 `A`, `C` or `D` mark has been seen: from then
    // on the shell integration owns prompt-ready and the glyph profile is not
    // consulted. `B`/`E`/`P` and unknown letters do not set it.
    integrated: bool,
    // Trailing bytes of an unterminated OSC mark, carried to the next push so a
    // mark split across two Out records is still recognised.
    carry: Vec<u8>,
}

impl EventClassifier {
    /// A classifier for a `cols`x`rows` session, recognising `profile`'s prompt
    /// glyphs when the target emits no OSC-133.
    #[must_use]
    pub fn new(cols: u16, rows: u16, profile: Profile) -> Self {
        EventClassifier {
            folder: Folder::new(cols, rows),
            profile,
            next_offset: 0,
            last_hash: None,
            last_change: 0,
            integrated: false,
            carry: Vec::new(),
        }
    }

    /// Feed the next record; returns the OSC-derived events it produced (empty
    /// for a record that carries no mark).
    pub fn push(&mut self, record: &Record) -> Vec<SessionEvent> {
        let offset = self.next_offset;
        self.next_offset += 1;
        let mut ev = Vec::new();
        if let Record::Out(bytes) = record {
            let mut input = std::mem::take(&mut self.carry);
            input.extend_from_slice(bytes);
            self.carry = scan_marks(&input, offset, &mut ev, &mut self.integrated);
        }
        self.folder.apply(record);
        let h = frame_hash(self.folder.screen());
        if self.last_hash != Some(h) {
            self.last_hash = Some(h);
            self.last_change = offset;
        }
        ev
    }

    /// Signal that the stream has gone idle (the pump's debounce fired): emit
    /// `Quiesced` at the settle point and, for a target that has emitted no
    /// OSC-133/633 `A`, `C` or `D` mark, a glyph `PromptReady` there. Returns
    /// nothing before any record is seen.
    pub fn quiesce(&mut self) -> Vec<SessionEvent> {
        if self.next_offset == 0 {
            return Vec::new();
        }
        settle_events(
            self.folder.screen(),
            self.last_change,
            &self.profile,
            self.integrated,
        )
    }

    /// Whether the session has emitted an OSC-133/633 `A`, `C` or `D`
    /// shell-integration mark — from then on prompt-ready comes from the `A`
    /// mark, never from a glyph. A `B`/`E`/`P` or unknown letter leaves this
    /// `false`: it carries no prompt/command lifecycle.
    #[must_use]
    pub fn integrated(&self) -> bool {
        self.integrated
    }
}
