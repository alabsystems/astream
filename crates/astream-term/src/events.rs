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

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "events_island.rs"]
mod events_island;
#[cfg(not(clean_islands))]
pub use crate::twins::event_advance_offset_monotone;
#[cfg(clean_islands)]
pub use events_island::event_advance_offset_monotone;

#[cfg(clean_islands)]
#[path = "sync_island.rs"]
mod sync_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{sync_bytes_clamp, sync_hold_ticks_clamp};
#[cfg(clean_islands)]
pub use sync_island::{sync_bytes_clamp, sync_hold_ticks_clamp};

/// Maximum output bytes (`1 MiB`) a single DEC `?2026` synchronized-output frame may
/// hold before [`Folder::in_sync_update`] / [`EventClassifier::in_sync_update`]
/// auto-unlatches so a runaway or crashed TUI cannot suppress settle wakes forever.
pub const MAX_SYNC_OUTPUT_BYTES: usize = 1 << 20;

/// Maximum consecutive debounce intervals (`4`) a live pump holds settle wakes while
/// [`EventClassifier::in_sync_update`] remains active with no new output arriving.
pub const MAX_SYNC_HOLD_TICKS: u8 = 4;

contract_fn! {
    /// Kernel-certified check that accumulated DEC `?2026` synchronized-output bytes
    /// `sync_bytes` remain strictly below `byte_cap` (`sync_bytes < byte_cap`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `sync_within_budget_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn sync_within_budget(sync_bytes: u64, byte_cap: u64) -> bool
    clauses [ensures result == (sync_bytes < byte_cap)]
    {
        sync_bytes < byte_cap
    }
}

contract_fn! {
    /// Kernel-certified check that a trailing split-OSC carry buffer length `len`
    /// lies within `max_carry` (`len <= max_carry`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `event_carry_within_bound_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn event_carry_within_bound(len: u64, max_carry: u64) -> bool
    clauses [ensures result == (len <= max_carry)]
    {
        len <= max_carry
    }
}

/// A classified boundary in a recorded session. `offset` is the record index
/// that produced it (records are position-addressed at this rung).
#[derive(Debug, Clone, Eq)]
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

impl PartialEq for SessionEvent {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::PromptReady { offset: a }, Self::PromptReady { offset: b }) => a == b,
            (Self::CommandStart { offset: a }, Self::CommandStart { offset: b }) => a == b,
            (
                Self::CommandEnd {
                    offset: oa,
                    exit: ea,
                },
                Self::CommandEnd {
                    offset: ob,
                    exit: eb,
                },
            ) => oa == ob && ea == eb,
            (Self::Quiesced { offset: a }, Self::Quiesced { offset: b }) => a == b,
            _ => false,
        }
    }
}

impl SessionEvent {
    /// The record index this event is anchored to.
    #[must_use]
    pub const fn offset(&self) -> usize {
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
#[derive(Debug, Clone, Default, PartialEq, Eq)]
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
            prompt_markers: vec![
                "❯".to_string(),
                ">>>".to_string(),
                "$".to_string(),
                "%".to_string(),
                "#".to_string(),
            ],
        }
    }

    /// Claude Code's `❯` idle composer box only — omits `$`/`%`/`#` so settled
    /// tool output ending in a percentage or hash never false-triggers
    /// [`SessionEvent::PromptReady`].
    #[must_use]
    pub fn claude() -> Self {
        Profile {
            prompt_markers: vec!["❯".to_string()],
        }
    }

    /// Codex CLI profile: no glyph marker (`»` remains visible while Codex works,
    /// so its boundary wake is [`SessionEvent::Quiesced`] alone).
    #[must_use]
    pub const fn codex() -> Self {
        Profile {
            prompt_markers: Vec::new(),
        }
    }

    /// Interactive REPL profile (`>>>`, `...`, `irb>`, `iex>`, `sqlite>`) — omits
    /// `$`/`%`/`#` so settled mid-evaluation progress lines ending in `%` or `#`
    /// never false-trigger [`SessionEvent::PromptReady`] (`DESIGN-drive-pipe.md`
    /// §5, §9 Rung 3).
    #[must_use]
    pub fn repl() -> Self {
        Profile {
            prompt_markers: vec![
                ">>>".to_string(),
                "...".to_string(),
                "irb>".to_string(),
                "iex>".to_string(),
                "sqlite>".to_string(),
            ],
        }
    }

    /// Emacs interactive buffers and minibuffer prompts (`ELISP>` IELM,
    /// `Eval:` `M-:`, `M-x` command prompt, `eshell>` Eshell) — omits `$`/`%`/`#`
    /// so settled buffer lines do not false-trigger [`SessionEvent::PromptReady`]
    /// (`DESIGN-drive-pipe.md` §9 Rung 3).
    #[must_use]
    pub fn emacs() -> Self {
        Profile {
            prompt_markers: vec![
                "ELISP>".to_string(),
                "Eval:".to_string(),
                "M-x".to_string(),
                "eshell>".to_string(),
            ],
        }
    }

    /// Bare POSIX/csh/root shell prompt glyphs (`$`, `%`, `#`) for unintegrated
    /// shells that emit no OSC-133/633 marks.
    #[must_use]
    pub fn shell() -> Self {
        Profile {
            prompt_markers: vec!["$".to_string(), "%".to_string(), "#".to_string()],
        }
    }

    /// Empty profile: disable glyph-based [`SessionEvent::PromptReady`] entirely
    /// (relying solely on OSC-133/633 marks and [`SessionEvent::Quiesced`]).
    #[must_use]
    pub const fn none() -> Self {
        Profile {
            prompt_markers: Vec::new(),
        }
    }

    /// Look up a built-in [`Profile`] by name (`"common"`, `"claude"`, `"codex"`,
    /// `"repl"`, `"emacs"`, `"shell"`, or `"none"`).
    #[must_use]
    pub fn by_name(name: &str) -> Option<Self> {
        match name {
            "common" => Some(Self::common()),
            "claude" => Some(Self::claude()),
            "codex" => Some(Self::codex()),
            "repl" => Some(Self::repl()),
            "emacs" => Some(Self::emacs()),
            "shell" => Some(Self::shell()),
            "none" => Some(Self::none()),
            _ => None,
        }
    }
}

// A shell-mark introducer (`\x1b]133/633;<letter>;<params><term>`) is short; bound
// the bytes we carry for a split/never-terminated one.
const CARRY_MAX: usize = 32;

// True if `code` (the digits right after `\x1b]`) is a prefix of "133" or "633" — a
// mark code that may still complete once more bytes arrive.
const fn is_shell_prefix(code: &[u8]) -> bool {
    matches!(code, b"" | b"1" | b"13" | b"133" | b"6" | b"63" | b"633")
}

#[derive(Clone, Copy)]
enum MarkScan<'a> {
    Terminated {
        after_term: &'a [u8],
        param_len: usize,
    },
    Abandoned {
        at_esc: &'a [u8],
    },
    Unterminated,
}

const fn find_mark_terminator(mut k_rest: &[u8]) -> MarkScan<'_> {
    let mut param_len = 0usize;
    loop {
        match k_rest {
            [] | [0x1b] => return MarkScan::Unterminated,
            &[0x07, ref after_term @ ..] => {
                return MarkScan::Terminated {
                    after_term,
                    param_len,
                };
            }
            &[0x1b, b'\\', ref after_term @ ..] => {
                return MarkScan::Terminated {
                    after_term,
                    param_len,
                };
            }
            &[0x1b, ..] => {
                return MarkScan::Abandoned { at_esc: k_rest };
            }
            &[_, ref tail @ ..] => {
                param_len = param_len.saturating_add(1);
                k_rest = tail;
            }
        }
    }
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
    let mut rest = b;
    while let &[cur, ref after_cur @ ..] = rest {
        if cur != 0x1b {
            rest = after_cur;
            continue;
        }
        // A lone trailing ESC could begin `\x1b]` on the next record.
        let &[after_esc, ref after_intro @ ..] = after_cur else {
            return vec![0x1b];
        };
        if after_esc != b']' {
            rest = after_cur;
            continue;
        }
        let after_semi = match after_intro {
            &[b'1', b'3', b'3', b';', ref tail @ ..] | &[b'6', b'3', b'3', b';', ref tail @ ..] => {
                tail
            }
            _ => {
                if is_shell_prefix(after_intro) {
                    return if event_carry_within_bound(rest.len() as u64, CARRY_MAX as u64) {
                        rest.to_vec()
                    } else {
                        Vec::new()
                    };
                }
                rest = after_cur;
                continue;
            }
        };
        let &[letter, ref after_letter @ ..] = after_semi else {
            // `\x1b]133;` with no letter yet → carry.
            return if event_carry_within_bound(rest.len() as u64, CARRY_MAX as u64) {
                rest.to_vec()
            } else {
                Vec::new()
            };
        };
        let (after_term, param_len) = match find_mark_terminator(after_letter) {
            MarkScan::Abandoned { at_esc } => {
                rest = at_esc;
                continue;
            }
            MarkScan::Unterminated => {
                return if event_carry_within_bound(rest.len() as u64, CARRY_MAX as u64) {
                    rest.to_vec()
                } else {
                    Vec::new()
                };
            }
            MarkScan::Terminated {
                after_term,
                param_len,
            } => (after_term, param_len),
        };
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
                    exit: parse_exit_prefix(after_letter, param_len),
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
        rest = after_term;
    }
    Vec::new()
}

const fn is_valid_utf8_prefix(bytes: &[u8], len: usize) -> bool {
    if len > bytes.len() {
        return false;
    }
    let mut rem = len;
    let mut scan = bytes;
    while rem > 0 {
        let &[b0, ref tail @ ..] = scan else {
            return false;
        };
        if b0 < 0x80 {
            rem = rem.saturating_sub(1);
            scan = tail;
        } else if b0 >= 0xC2 && b0 <= 0xDF {
            if rem < 2 {
                return false;
            }
            let &[b1, ref tail2 @ ..] = tail else {
                return false;
            };
            if (b1 & 0xC0) != 0x80 {
                return false;
            }
            rem = rem.saturating_sub(2);
            scan = tail2;
        } else if b0 >= 0xE0 && b0 <= 0xEF {
            if rem < 3 {
                return false;
            }
            let &[b1, b2, ref tail3 @ ..] = tail else {
                return false;
            };
            if (b1 & 0xC0) != 0x80 || (b2 & 0xC0) != 0x80 {
                return false;
            }
            if (b0 == 0xE0 && b1 < 0xA0) || (b0 == 0xED && b1 >= 0xA0) {
                return false;
            }
            rem = rem.saturating_sub(3);
            scan = tail3;
        } else if b0 >= 0xF0 && b0 <= 0xF4 {
            if rem < 4 {
                return false;
            }
            let &[b1, b2, b3, ref tail4 @ ..] = tail else {
                return false;
            };
            if (b1 & 0xC0) != 0x80 || (b2 & 0xC0) != 0x80 || (b3 & 0xC0) != 0x80 {
                return false;
            }
            if (b0 == 0xF0 && b1 < 0x90) || (b0 == 0xF4 && b1 >= 0x90) {
                return false;
            }
            rem = rem.saturating_sub(4);
            scan = tail4;
        } else {
            return false;
        }
    }
    true
}

// Read only the parameter bytes before the OSC terminator. Keep Rust's UTF-8,
// Unicode whitespace and signed-i32 grammar, including validation of extra fields.
const fn parse_exit_prefix(params: &[u8], param_len: usize) -> Option<i32> {
    if param_len == 0 || !is_valid_utf8_prefix(params, param_len) {
        return None;
    }
    let mut rem = param_len;
    let mut scan = params;
    let mut first = true;
    let mut skip = 0u8;
    let mut phase = 0u8;
    let mut neg = false;
    let mut digits = false;
    let mut acc = 0i64;
    while let &[b0, ref tail @ ..] = scan {
        if rem == 0 {
            break;
        }
        rem = rem.saturating_sub(1);
        if skip > 0 {
            skip = (skip & 3).wrapping_sub(1);
            scan = tail;
            continue;
        }
        if first {
            first = false;
            if b0 == b';' {
                scan = tail;
                continue;
            }
        }
        if b0 == b';' {
            break;
        }
        if matches!(b0, b' ' | b'\t' | b'\n' | b'\r' | 0x0B | 0x0C) {
            if phase == 1 {
                return None;
            }
            if phase == 2 {
                phase = 3;
            }
            scan = tail;
            continue;
        }
        if b0 == 0xC2 {
            if rem >= 1 && matches!(tail, &[0x85 | 0xA0, ..]) {
                if phase == 1 {
                    return None;
                }
                if phase == 2 {
                    phase = 3;
                }
                skip = 1;
                scan = tail;
                continue;
            }
            return None;
        }
        if matches!(b0, 0xE1..=0xE3) {
            if rem >= 2 {
                if let &[b1, b2, ..] = tail {
                    let is_ws = (b0 == 0xE1 && b1 == 0x9A && b2 == 0x80)
                        || (b0 == 0xE2
                            && b1 == 0x80
                            && ((b2 >= 0x80 && b2 <= 0x8A)
                                || b2 == 0xA8
                                || b2 == 0xA9
                                || b2 == 0xAF))
                        || (b0 == 0xE2 && b1 == 0x81 && b2 == 0x9F)
                        || (b0 == 0xE3 && b1 == 0x80 && b2 == 0x80);
                    if is_ws {
                        if phase == 1 {
                            return None;
                        }
                        if phase == 2 {
                            phase = 3;
                        }
                        skip = 2;
                        scan = tail;
                        continue;
                    }
                }
            }
            return None;
        }
        if phase == 3 {
            return None;
        }
        if phase == 0 && (b0 == b'+' || b0 == b'-') {
            neg = b0 == b'-';
            phase = 1;
            scan = tail;
            continue;
        }
        let d: i64 = match b0 {
            b'0' => 0,
            b'1' => 1,
            b'2' => 2,
            b'3' => 3,
            b'4' => 4,
            b'5' => 5,
            b'6' => 6,
            b'7' => 7,
            b'8' => 8,
            b'9' => 9,
            _ => return None,
        };
        acc = acc.saturating_mul(10).saturating_add(d);
        if acc > 2_147_483_648 {
            return None;
        }
        digits = true;
        phase = 2;
        scan = tail;
    }
    if !digits {
        return None;
    }
    if neg {
        if acc == 2_147_483_648 {
            Some(i32::MIN)
        } else if acc <= 2_147_483_647 {
            Some(0i32.saturating_sub(acc as i32))
        } else {
            None
        }
    } else if acc <= 2_147_483_647 {
        Some(acc as i32)
    } else {
        None
    }
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
    let mut last_nonempty = None;
    let mut r = nrows;
    while r > 0 {
        r = r.saturating_sub(1);
        let l = screen.line_text(r);
        if !l.is_empty() {
            last_nonempty = Some(l);
            break;
        }
    }
    if let Some(line) = last_nonempty {
        let tail = line.trim_end();
        for m in &profile.prompt_markers {
            if tail.ends_with(m.trim_end()) {
                ev.push(SessionEvent::PromptReady { offset: q });
                break;
            }
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
        let next = self.next_offset.saturating_add(1);
        self.next_offset = event_advance_offset_monotone(offset as u64, next as u64) as usize;
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

    /// Discard any partial mid-record OSC-133/633 mark carry and reset the
    /// underlying [`Folder`]'s mid-escape VT parser state while preserving the
    /// painted screen, `integrated` latch, and offset counters.
    ///
    /// Call this when a retention `Gap` indicates one or more `Out` records
    /// were skipped between deliveries, so a torn pre-gap OSC/CSI prefix can
    /// neither splice onto post-gap bytes to forge a phantom mark nor trap the
    /// screen fold inside an unterminated OSC string.
    pub fn reset_escape(&mut self) {
        self.carry.clear();
        self.folder.reset_escape();
    }

    /// Whether the target is mid-frame inside DEC `?2026` synchronized output
    /// (`BSU` `\x1b[?2026h` received, `ESU` `\x1b[?2026l` not yet received, and
    /// accumulated frame bytes remain strictly below [`MAX_SYNC_OUTPUT_BYTES`]).
    #[must_use]
    pub const fn in_sync_update(&self) -> bool {
        self.folder.in_sync_update()
    }

    /// Settle the screen if and only if the target is **not** currently inside an
    /// active DEC `?2026` synchronized-output frame (`!self.in_sync_update()`).
    ///
    /// Returns `None` while a synchronized frame is still in flight (holding off
    /// torn mid-redraw `Quiesced` / glyph `PromptReady` wakes), or `Some(events)`
    /// once `\x1b[?2026l` commits the frame (or [`MAX_SYNC_OUTPUT_BYTES`] /
    /// [`Self::reset_escape`] auto-unlatches it).
    pub fn quiesce_if_unsynced(&mut self) -> Option<Vec<SessionEvent>> {
        if self.in_sync_update() {
            None
        } else {
            Some(self.quiesce())
        }
    }

    /// Borrow the underlying [`Folder`].
    #[must_use]
    pub const fn folder(&self) -> &Folder {
        &self.folder
    }

    /// Borrow the folded [`Screen`] accumulated across classified deliveries.
    #[must_use]
    pub const fn screen(&self) -> &Screen {
        self.folder.screen()
    }

    /// Current sanitized window title (`OSC 0` / `OSC 2`) from the underlying [`Folder`].
    #[must_use]
    pub fn title(&self) -> &str {
        self.folder.title()
    }

    /// Current decoded working directory (`OSC 7`) from the underlying [`Folder`].
    #[must_use]
    pub fn cwd(&self) -> &str {
        self.folder.cwd()
    }

    /// Whether the session has emitted an OSC-133/633 `A`, `C` or `D`
    /// shell-integration mark — from then on prompt-ready comes from the `A`
    /// mark, never from a glyph. A `B`/`E`/`P` or unknown letter leaves this
    /// `false`: it carries no prompt/command lifecycle.
    #[must_use]
    pub const fn integrated(&self) -> bool {
        self.integrated
    }
}
