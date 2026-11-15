#![forbid(unsafe_code)]
//! `astream-pump` — the drive-pipe **pump**.
//!
//! The pump owns the block-forever end of the bus so a *turn-based* driving
//! agent does not have to. It holds a broker `SUBSCRIBE` on a target terminal
//! session's `/out` subtree, feeds each delivered `Out` record to
//! [`astream_term`]'s streaming [`EventClassifier`], and surfaces the **semantic
//! wake boundaries** — prompt-ready, command-start, command-end (+exit),
//! screen-quiescence — that the agent acts on.
//!
//! astream deliberately stops at a socket that blocks until an event, and the
//! entity that blocks is a *thread*, not an agent turn (`DESIGN-drive-pipe.md`
//! §5). The pump is that thread: [`Pump::next_wake`] is the no-poll wait (the broker
//! `recv` parks on a `Condvar` tail until a publish); [`Pump::quiesce`] is the
//! debounce boundary; and the events they return are what an outer runner turns
//! into an agent wake (a hook, a resumed turn, a queued task).
//!
//! **Subjects.** [`out_subject`] is the built PTY face
//! (`/a/stream/term/<sid>/out`) and stays the default, but the pump is not
//! bound to it: [`Pump::attach_subject`] takes an arbitrary subject, so a
//! fabric node's `/f/<F>/term/<node>/<sid>/out` face
//! (`DESIGN-aterm-fabric.md` §3.3) pumps through exactly the same code.
//!
//! **Cursors.** Two forms, and the difference is *where the read position
//! lives*:
//!
//! - [`Pump::attach`] / [`Pump::attach_subject`] — a **client-held** cursor. The
//!   broker delivers from `from_offset` **inclusive**, so a restarted pump
//!   resumes gaplessly and without re-delivering its last wake by attaching at
//!   [`Pump::next_offset`], not at [`Pump::offset`]. Get that argument wrong and
//!   you miss or double a boundary; nothing on the broker remembers for you.
//! - [`Pump::attach_group`] — a **broker-durable** cursor. The pump subscribes as
//!   a consumer group and calls [`Pump::commit`] once every wake that delivery
//!   can still produce is out — its marks AND the settle wakes [`Pump::quiesce`]
//!   fires at its offset, a trap [`Pump::commit`] spells out; the next pump for
//!   that group resumes from `committed + 1` with no offset argument at all.
//!   The two contracts agree by construction: `commit()` commits *through*
//!   [`Pump::offset`] (inclusive), so the group's next start is exactly
//!   [`Pump::next_offset`].
//!
//! **Offsets.** [`Pump::offset`] is the broker offset of the most recent
//! delivery — where a woken agent reads the target's screen (today by folding
//! `/out` through it; the designed `/a/state/term/<sid>/screen` snapshot is not
//! yet published by anything on the bus).

// A contracted fn is written once, through `contract_fn!`: under a Trust compiler
// (`cfg(clean_islands)`, build.rs) it carries its `ensures` clause, which no stock rustc can
// parse, and every other compiler gets the plain fn.
#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod nested_drive;
pub mod semantic_wake;
pub mod turn_by;
pub mod wake_dispatch;
pub use nested_drive::{
    nested_prompt_bytes_clamp, nested_turn_ready_to_drive, nested_turn_seq_advance,
    parse_prompt_ready_boffset, NestedTurnState, MAX_NESTED_PROMPT_BYTES,
};
#[cfg(unix)]
pub use wake_dispatch::deliver_hook_unix;
pub use wake_dispatch::{
    deliver_hook_tcp, drain_wake_tasks, task_subject, wake_commit_after_ack,
    wake_dispatch_seq_advance, wake_task_payload_clamp, write_hook_payload, WakeHookFormat,
    WakeTaskItem, WakeTaskQueue, MAX_WAKE_TASK_PAYLOAD, WAKE_TASK_PREFIX,
};
// Plain-Rust twins of the functions this crate's Clean islands compile, for a compiler
// that cannot lex the islands.
#[cfg(any(test, not(clean_islands)))]
mod twins;

use std::io::{self, Read, Write};

pub use astream_broker::Gap;
use astream_broker::{Client, Event, Subscription};
use astream_term::events::{EventClassifier, Profile, SessionEvent};
use astream_term::record::Record;

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
mod pump_island;
#[cfg(not(clean_islands))]
pub use crate::twins::pump_offset_monotone;
#[cfg(clean_islands)]
pub use pump_island::pump_offset_monotone;

contract_fn! {
    /// Verified group-cursor idempotence check linked via `clean-kernel-defeq` to
    /// `cursor_already_committed_isl`.
    #[must_use]
    pub const fn cursor_already_committed(committed: u64, upto: u64) -> bool
    clauses [ensures result == (upto <= committed)]
    {
        upto <= committed
    }
}

/// The subject subtree a target session publishes its PTY output to (the lash's
/// `/out` face). `<sid>` is the session id.
#[must_use]
pub fn out_subject(sid: &str) -> String {
    format!("/a/stream/term/{sid}/out")
}

/// Numeric tag for a [`SessionEvent`] wake boundary:
/// `1` = `PromptReady`, `2` = `CommandStart`, `3` = `CommandEnd` (no exit code),
/// `4` = `CommandEnd` (with exit code), `5` = `Quiesced`.
#[must_use]
pub const fn wake_kind_tag(ev: &SessionEvent) -> u8 {
    match ev {
        SessionEvent::PromptReady { .. } => 1,
        SessionEvent::CommandStart { .. } => 2,
        SessionEvent::CommandEnd { exit: None, .. } => 3,
        SessionEvent::CommandEnd { exit: Some(_), .. } => 4,
        SessionEvent::Quiesced { .. } => 5,
    }
}

/// Encode a compact 13-byte binary wake frame `(kind_tag: u8, boffset: u64, exit_code: i32)`
/// in little-endian byte order using bitwise shifts.
#[must_use]
pub const fn encode_wake_frame(kind_tag: u8, boffset: u64, exit_code: i32) -> [u8; 13] {
    let e = exit_code as u32;
    [
        kind_tag,
        (boffset & 0xFF) as u8,
        ((boffset >> 8) & 0xFF) as u8,
        ((boffset >> 16) & 0xFF) as u8,
        ((boffset >> 24) & 0xFF) as u8,
        ((boffset >> 32) & 0xFF) as u8,
        ((boffset >> 40) & 0xFF) as u8,
        ((boffset >> 48) & 0xFF) as u8,
        ((boffset >> 56) & 0xFF) as u8,
        (e & 0xFF) as u8,
        ((e >> 8) & 0xFF) as u8,
        ((e >> 16) & 0xFF) as u8,
        ((e >> 24) & 0xFF) as u8,
    ]
}

/// Decode a compact 13-byte binary wake frame into `(kind_tag, boffset, exit_code)`
/// using bitwise shifts.
#[must_use]
pub const fn decode_wake_frame(b: [u8; 13]) -> (u8, u64, i32) {
    let boffset = (b[1] as u64)
        | ((b[2] as u64) << 8)
        | ((b[3] as u64) << 16)
        | ((b[4] as u64) << 24)
        | ((b[5] as u64) << 32)
        | ((b[6] as u64) << 40)
        | ((b[7] as u64) << 48)
        | ((b[8] as u64) << 56);
    let e = (b[9] as u32) | ((b[10] as u32) << 8) | ((b[11] as u32) << 16) | ((b[12] as u32) << 24);
    (b[0], boffset, e as i32)
}

/// Encode a pump's cursor state `(from, last, committed)` into a 25-byte little-endian
/// record (`flags: u8 | from: u64 | last: u64 | committed: u64`).
#[must_use]
pub const fn encode_pump_cursor_state(
    from: u64,
    last: Option<u64>,
    committed: Option<u64>,
) -> [u8; 25] {
    let (has_last, last_v) = match last {
        Some(v) => (1u8, v),
        None => (0u8, 0u64),
    };
    let (has_comm, comm_v) = match committed {
        Some(v) => (2u8, v),
        None => (0u8, 0u64),
    };
    let fb = from.to_le_bytes();
    let [l0, l1, l2, l3, l4, l5, l6, l7] = last_v.to_le_bytes();
    let cb = comm_v.to_le_bytes();
    [
        has_last | has_comm,
        fb[0],
        fb[1],
        fb[2],
        fb[3],
        fb[4],
        fb[5],
        fb[6],
        fb[7],
        l0,
        l1,
        l2,
        l3,
        l4,
        l5,
        l6,
        l7,
        cb[0],
        cb[1],
        cb[2],
        cb[3],
        cb[4],
        cb[5],
        cb[6],
        cb[7],
    ]
}

/// Decode a 25-byte little-endian pump cursor record into `(from, last, committed)`.
#[must_use]
pub const fn decode_pump_cursor_state(b: [u8; 25]) -> Option<(u64, Option<u64>, Option<u64>)> {
    let [flags, f0, f1, f2, f3, f4, f5, f6, f7, l0, l1, l2, l3, l4, l5, l6, l7, c0, c1, c2, c3, c4, c5, c6, c7] =
        b;
    let from = (f0 as u64)
        | ((f1 as u64) << 8)
        | ((f2 as u64) << 16)
        | ((f3 as u64) << 24)
        | ((f4 as u64) << 32)
        | ((f5 as u64) << 40)
        | ((f6 as u64) << 48)
        | ((f7 as u64) << 56);
    let last_v = (l0 as u64)
        | ((l1 as u64) << 8)
        | ((l2 as u64) << 16)
        | ((l3 as u64) << 24)
        | ((l4 as u64) << 32)
        | ((l5 as u64) << 40)
        | ((l6 as u64) << 48)
        | ((l7 as u64) << 56);
    let comm_v = (c0 as u64)
        | ((c1 as u64) << 8)
        | ((c2 as u64) << 16)
        | ((c3 as u64) << 24)
        | ((c4 as u64) << 32)
        | ((c5 as u64) << 40)
        | ((c6 as u64) << 48)
        | ((c7 as u64) << 56);
    if (flags & !0x03) != 0 {
        return None;
    }
    let last = if (flags & 1) != 0 {
        Some(last_v)
    } else if last_v == 0 {
        None
    } else {
        return None;
    };
    let committed = if (flags & 2) != 0 {
        Some(comm_v)
    } else if comm_v == 0 {
        None
    } else {
        return None;
    };
    Some((from, last, committed))
}

/// Four-byte magic prefix (`"APAT"`) for a 20-byte pump attach wire header.
pub const PUMP_ATTACH_WIRE_MAGIC: [u8; 4] = *b"APAT";

/// Wire format version for pump attach wire headers.
pub const PUMP_ATTACH_WIRE_VERSION: u8 = 1;

/// Encode a 20-byte pump attach wire header:
/// `[0..4] = b"APAT"`, `[4] = version (1)`, `[5] = mode_tag` (`0 = from`, `1 = group`),
/// `[6..8] = cols (BE)`, `[8..10] = rows (BE)`, `[10..12] = subject_len (BE)`,
/// `[12..20] = from_offset (BE)` (`0` when `mode_tag == 1`).
#[must_use]
pub const fn encode_pump_attach_wire(
    mode_tag: u8,
    cols: u16,
    rows: u16,
    subject_len: u16,
    from_offset: u64,
) -> Option<[u8; 20]> {
    let out = [
        PUMP_ATTACH_WIRE_MAGIC[0],
        PUMP_ATTACH_WIRE_MAGIC[1],
        PUMP_ATTACH_WIRE_MAGIC[2],
        PUMP_ATTACH_WIRE_MAGIC[3],
        PUMP_ATTACH_WIRE_VERSION,
        mode_tag,
        ((cols >> 8) & 0xFF) as u8,
        (cols & 0xFF) as u8,
        ((rows >> 8) & 0xFF) as u8,
        (rows & 0xFF) as u8,
        ((subject_len >> 8) & 0xFF) as u8,
        (subject_len & 0xFF) as u8,
        ((from_offset >> 56) & 0xFF) as u8,
        ((from_offset >> 48) & 0xFF) as u8,
        ((from_offset >> 40) & 0xFF) as u8,
        ((from_offset >> 32) & 0xFF) as u8,
        ((from_offset >> 24) & 0xFF) as u8,
        ((from_offset >> 16) & 0xFF) as u8,
        ((from_offset >> 8) & 0xFF) as u8,
        (from_offset & 0xFF) as u8,
    ];
    if mode_tag > 1
        || cols == 0
        || rows == 0
        || subject_len == 0
        || (mode_tag == 1 && from_offset != 0)
    {
        return None;
    }
    Some(out)
}

/// Decode a 20-byte pump attach wire header into
/// `(mode_tag, cols, rows, subject_len, from_offset)`.
#[must_use]
pub const fn decode_pump_attach_wire(buf: &[u8]) -> Option<(u8, u16, u16, u16, u64)> {
    let [b'A', b'P', b'A', b'T', PUMP_ATTACH_WIRE_VERSION, mode_tag, c0, c1, r0, r1, s0, s1, o0, o1, o2, o3, o4, o5, o6, o7, ..] =
        *buf
    else {
        return None;
    };
    let cols = ((c0 as u16) << 8) | (c1 as u16);
    let rows = ((r0 as u16) << 8) | (r1 as u16);
    let subject_len = ((s0 as u16) << 8) | (s1 as u16);
    let from_offset = ((o0 as u64) << 56)
        | ((o1 as u64) << 48)
        | ((o2 as u64) << 40)
        | ((o3 as u64) << 32)
        | ((o4 as u64) << 24)
        | ((o5 as u64) << 16)
        | ((o6 as u64) << 8)
        | (o7 as u64);
    if mode_tag > 1
        || cols == 0
        || rows == 0
        || subject_len == 0
        || (mode_tag == 1 && from_offset != 0)
    {
        return None;
    }
    Some((mode_tag, cols, rows, subject_len, from_offset))
}

/// Four-byte magic prefix (`"APQS"`) for a 20-byte pump quiesce state wire header.
pub const PUMP_QUIESCE_WIRE_MAGIC: [u8; 4] = *b"APQS";

/// Wire format version for pump quiesce state wire headers.
pub const PUMP_QUIESCE_WIRE_VERSION: u8 = 1;

/// Encode a 20-byte pump quiesce state wire header:
/// `[0..4] = b"APQS"`, `[4] = version (1)`, `[5] = settled (0/1)`, `[6..8] = 0`,
/// `[8..12] = debounce_ms (BE)`, `[12..20] = last_boffset (BE)`.
#[must_use]
pub const fn encode_pump_quiesce_wire(
    settled: bool,
    debounce_ms: u32,
    last_boffset: u64,
) -> Option<[u8; 20]> {
    let settled_tag = settled as u8;
    let out = [
        PUMP_QUIESCE_WIRE_MAGIC[0],
        PUMP_QUIESCE_WIRE_MAGIC[1],
        PUMP_QUIESCE_WIRE_MAGIC[2],
        PUMP_QUIESCE_WIRE_MAGIC[3],
        PUMP_QUIESCE_WIRE_VERSION,
        settled_tag,
        0,
        0,
        ((debounce_ms >> 24) & 0xFF) as u8,
        ((debounce_ms >> 16) & 0xFF) as u8,
        ((debounce_ms >> 8) & 0xFF) as u8,
        (debounce_ms & 0xFF) as u8,
        ((last_boffset >> 56) & 0xFF) as u8,
        ((last_boffset >> 48) & 0xFF) as u8,
        ((last_boffset >> 40) & 0xFF) as u8,
        ((last_boffset >> 32) & 0xFF) as u8,
        ((last_boffset >> 24) & 0xFF) as u8,
        ((last_boffset >> 16) & 0xFF) as u8,
        ((last_boffset >> 8) & 0xFF) as u8,
        (last_boffset & 0xFF) as u8,
    ];
    if debounce_ms == 0 {
        return None;
    }
    Some(out)
}

/// Decode a 20-byte pump quiesce state wire header into `(settled, debounce_ms, last_boffset)`.
#[must_use]
pub const fn decode_pump_quiesce_wire(buf: &[u8]) -> Option<(bool, u32, u64)> {
    let [b'A', b'P', b'Q', b'S', PUMP_QUIESCE_WIRE_VERSION, settled_tag, 0, 0, d0, d1, d2, d3, l0, l1, l2, l3, l4, l5, l6, l7, ..] =
        *buf
    else {
        return None;
    };
    let debounce_ms = ((d0 as u32) << 24) | ((d1 as u32) << 16) | ((d2 as u32) << 8) | (d3 as u32);
    let last_boffset = ((l0 as u64) << 56)
        | ((l1 as u64) << 48)
        | ((l2 as u64) << 40)
        | ((l3 as u64) << 32)
        | ((l4 as u64) << 24)
        | ((l5 as u64) << 16)
        | ((l6 as u64) << 8)
        | (l7 as u64);
    let settled = match settled_tag {
        0 => false,
        1 => true,
        _ => return None,
    };
    if debounce_ms == 0 {
        return None;
    }
    Some((settled, debounce_ms, last_boffset))
}

/// Four-byte magic prefix (`"APGP"`) for a 30-byte pump retention gap wire header.
pub const PUMP_GAP_WIRE_MAGIC: [u8; 4] = *b"APGP";

/// Wire format version for pump retention gap wire headers.
pub const PUMP_GAP_WIRE_VERSION: u8 = 1;

/// Encode a 30-byte pump retention gap wire header:
/// `[0..4] = b"APGP"`, `[4] = version (1)`, `[5] = has_records (0/1)`,
/// `[6..14] = from (BE)`, `[14..22] = to (BE)`, `[22..30] = records_or_zero (BE)`.
/// Returns `None` if `gap.from >= gap.to`.
#[must_use]
pub const fn encode_pump_gap_wire(gap: Gap) -> Option<[u8; 30]> {
    let from = gap.from;
    let to = gap.to;
    let (has_rec, rec_v) = match gap.records {
        Some(r) => (1u8, r),
        None => (0u8, 0u64),
    };
    let out = [
        PUMP_GAP_WIRE_MAGIC[0],
        PUMP_GAP_WIRE_MAGIC[1],
        PUMP_GAP_WIRE_MAGIC[2],
        PUMP_GAP_WIRE_MAGIC[3],
        PUMP_GAP_WIRE_VERSION,
        has_rec,
        ((from >> 56) & 0xFF) as u8,
        ((from >> 48) & 0xFF) as u8,
        ((from >> 40) & 0xFF) as u8,
        ((from >> 32) & 0xFF) as u8,
        ((from >> 24) & 0xFF) as u8,
        ((from >> 16) & 0xFF) as u8,
        ((from >> 8) & 0xFF) as u8,
        (from & 0xFF) as u8,
        ((to >> 56) & 0xFF) as u8,
        ((to >> 48) & 0xFF) as u8,
        ((to >> 40) & 0xFF) as u8,
        ((to >> 32) & 0xFF) as u8,
        ((to >> 24) & 0xFF) as u8,
        ((to >> 16) & 0xFF) as u8,
        ((to >> 8) & 0xFF) as u8,
        (to & 0xFF) as u8,
        ((rec_v >> 56) & 0xFF) as u8,
        ((rec_v >> 48) & 0xFF) as u8,
        ((rec_v >> 40) & 0xFF) as u8,
        ((rec_v >> 32) & 0xFF) as u8,
        ((rec_v >> 24) & 0xFF) as u8,
        ((rec_v >> 16) & 0xFF) as u8,
        ((rec_v >> 8) & 0xFF) as u8,
        (rec_v & 0xFF) as u8,
    ];
    if from >= to {
        return None;
    }
    Some(out)
}

/// Decode a 30-byte pump retention gap wire header into a [`Gap`].
#[must_use]
pub const fn decode_pump_gap_wire(buf: &[u8]) -> Option<Gap> {
    let [b'A', b'P', b'G', b'P', PUMP_GAP_WIRE_VERSION, has_rec, f0, f1, f2, f3, f4, f5, f6, f7, t0, t1, t2, t3, t4, t5, t6, t7, r0, r1, r2, r3, r4, r5, r6, r7, ..] =
        *buf
    else {
        return None;
    };
    let from = ((f0 as u64) << 56)
        | ((f1 as u64) << 48)
        | ((f2 as u64) << 40)
        | ((f3 as u64) << 32)
        | ((f4 as u64) << 24)
        | ((f5 as u64) << 16)
        | ((f6 as u64) << 8)
        | (f7 as u64);
    let to = ((t0 as u64) << 56)
        | ((t1 as u64) << 48)
        | ((t2 as u64) << 40)
        | ((t3 as u64) << 32)
        | ((t4 as u64) << 24)
        | ((t5 as u64) << 16)
        | ((t6 as u64) << 8)
        | (t7 as u64);
    let rec_v = ((r0 as u64) << 56)
        | ((r1 as u64) << 48)
        | ((r2 as u64) << 40)
        | ((r3 as u64) << 32)
        | ((r4 as u64) << 24)
        | ((r5 as u64) << 16)
        | ((r6 as u64) << 8)
        | (r7 as u64);
    let records = match has_rec {
        0 if rec_v == 0 => None,
        1 => Some(rec_v),
        _ => return None,
    };
    if from >= to {
        return None;
    }
    Some(Gap { from, to, records })
}

/// The one-line rendering of a wake — `<KIND> boffset=<broker-offset> [exit=E]`
/// — that `aspump` prints and a shell/bridge parses. `boffset` is the broker
/// offset of the `/out` record that produced the event, i.e. where the woken
/// agent reads the target's screen.
///
/// It lives in the library, not the binary, so a wake rendered by an embedder is
/// byte-identical to the CLI's line.
#[must_use]
pub fn wake_line(ev: &SessionEvent, boffset: u64) -> String {
    match ev {
        SessionEvent::PromptReady { .. } => format!("PROMPT_READY boffset={boffset}"),
        SessionEvent::CommandStart { .. } => format!("COMMAND_START boffset={boffset}"),
        SessionEvent::CommandEnd { exit, .. } => match exit {
            Some(e) => format!("COMMAND_END boffset={boffset} exit={e}"),
            None => format!("COMMAND_END boffset={boffset}"),
        },
        SessionEvent::Quiesced { .. } => format!("QUIESCED boffset={boffset}"),
    }
}

const fn is_meta_token_safe(b: u8) -> bool {
    matches!(
        b,
        b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'.' | b'_' | b'~' | b'/' | b'-' | b':'
    )
}

const fn hex_upper_char(nibble: u8) -> char {
    match nibble & 0x0F {
        0 => '0',
        1 => '1',
        2 => '2',
        3 => '3',
        4 => '4',
        5 => '5',
        6 => '6',
        7 => '7',
        8 => '8',
        9 => '9',
        10 => 'A',
        11 => 'B',
        12 => 'C',
        13 => 'D',
        14 => 'E',
        _ => 'F',
    }
}

fn push_percent_encoded_token(out: &mut String, s: &str) {
    for &b in s.as_bytes() {
        if is_meta_token_safe(b) {
            out.push(b as char);
        } else {
            out.push('%');
            out.push(hex_upper_char(b >> 4));
            out.push(hex_upper_char(b));
        }
    }
}

/// Render [`wake_line`] plus optional percent-encoded `cwd=<path>` and `title=<title>`
/// tokens (used by `aspump --meta`). Safe path characters (`A-Za-z0-9._~/-:`) appear
/// verbatim; whitespace, `=`, `%`, and non-ASCII bytes are `%XX`-encoded so every field
/// remains a single unambiguous whitespace-delimited token.
#[must_use]
pub fn wake_line_with_meta(ev: &SessionEvent, boffset: u64, cwd: &str, title: &str) -> String {
    let mut line = wake_line(ev, boffset);
    if !cwd.is_empty() {
        line.push_str(" cwd=");
        push_percent_encoded_token(&mut line, cwd);
    }
    if !title.is_empty() {
        line.push_str(" title=");
        push_percent_encoded_token(&mut line, title);
    }
    line
}

/// The one-line stderr diagnostic for a retention gap (`REQUIREMENTS-fabric-operations`
/// R4, addendum A9) — `aspump: GAP from=<F> to=<T> records=<N|unknown>` — matching
/// `asb: sub: GAP …`. Never written to stdout, whose framing a wake consumer parses line
/// by line.
#[must_use]
pub fn gap_line(gap: &Gap) -> String {
    let records = match gap.records {
        Some(n) => n.to_string(),
        None => "unknown".to_string(),
    };
    format!(
        "aspump: GAP from={} to={} records={records}",
        gap.from, gap.to
    )
}

// The durable half of a group attach. `SubscribeGroup` consumes its connection
// into a one-way delivery stream — the broker enters its tail loop and never
// reads another request on it — so a commit MUST travel on a second connection.
// That is why `attach_group` takes two clients rather than one.
struct GroupCursor<S: Read + Write> {
    commits: Client<S>,
    group: String,
    committed: Option<u64>,
}

/// A live pump attached to one target session's output stream.
pub struct Pump<S: Read + Write> {
    sub: Subscription<S>,
    classifier: EventClassifier,
    from: u64,
    // The broker offset of the most recent delivery; `None` until the first.
    last: Option<u64>,
    // `Some` only for a group attach: the durable cursor's commit channel.
    cursor: Option<GroupCursor<S>>,
}

impl<S: Read + Write> Pump<S> {
    /// Attach to `sid`'s built `/out` stream ([`out_subject`]) from `from_offset`
    /// **inclusive**. Shorthand for [`Pump::attach_subject`] on that subject.
    ///
    /// # Errors
    /// Propagates the broker's subscribe I/O error.
    pub fn attach(
        client: Client<S>,
        sid: &str,
        from_offset: u64,
        cols: u16,
        rows: u16,
        profile: Profile,
    ) -> io::Result<Self> {
        Self::attach_subject(client, &out_subject(sid), from_offset, cols, rows, profile)
    }

    /// Attach to an ARBITRARY `subject` from `from_offset` **inclusive** — the
    /// broker delivers every record at or after it — classifying it as a
    /// `cols`x`rows` session under `profile`. Consumes `client` into the
    /// subscription (one stream per connection).
    ///
    /// This is the general form. The built PTY face is `/a/stream/term/<sid>/out`
    /// ([`Pump::attach`]); a fabric node's face is
    /// `/f/<F>/term/<node>/<sid>/out`. The pump classifies whatever `Out` bytes
    /// the subject carries — it reads no meaning from the subject's shape, and
    /// `subject` may be any filter the broker accepts.
    ///
    /// **Resume contract.** [`Pump::offset`] names the record most recently
    /// delivered, so re-attaching *at* it delivers that record — and any wake it
    /// carries — a second time. To continue a stream after a pump stopped,
    /// attach at its [`Pump::next_offset`] (`offset() + 1`), or use
    /// [`Pump::attach_group`] and let the broker hold the cursor. The classifier
    /// starts from a blank screen at the attach point: OSC marks are exact from
    /// the first delivery, while the settle/glyph signals describe only what has
    /// been painted since.
    ///
    /// # Errors
    /// Propagates the broker's subscribe I/O error.
    pub fn attach_subject(
        client: Client<S>,
        subject: &str,
        from_offset: u64,
        cols: u16,
        rows: u16,
        profile: Profile,
    ) -> io::Result<Self> {
        let sub = client.subscribe(from_offset, subject)?;
        Ok(Pump {
            sub,
            classifier: EventClassifier::new(cols, rows, profile),
            from: from_offset,
            last: None,
            cursor: None,
        })
    }

    /// Attach to `subject` as consumer **`group`** — the DURABLE cursor. The
    /// broker resumes delivery from the group's committed offset (`committed + 1`,
    /// or 0 for a group that has never committed), so the read position lives on
    /// the broker and survives a pump restart: the replacement pump passes no
    /// offset at all and cannot get it wrong.
    ///
    /// Takes **two** connections because `SubscribeGroup` turns its own
    /// connection into a one-way delivery stream: `client` becomes the
    /// subscription, `commits` carries every [`Pump::commit`]. Under a
    /// capability-guarded broker both must already be attached, and the grant
    /// must cover the group name as a subject as well as the filter.
    ///
    /// **Resume contract**, consistent with the offset form: `commit()` commits
    /// *through* [`Pump::offset`] (the broker's `upto` is inclusive), so the
    /// group's next start is exactly [`Pump::next_offset`]. A wake that is
    /// delivered but not committed before the pump dies is re-delivered — the
    /// group is at-least-once on wakes, and the commit point is the caller's
    /// choice of "acted on".
    ///
    /// # Errors
    /// Propagates the broker's subscribe I/O error.
    pub fn attach_group(
        client: Client<S>,
        commits: Client<S>,
        group: &str,
        subject: &str,
        cols: u16,
        rows: u16,
        profile: Profile,
    ) -> io::Result<Self> {
        let sub = client.subscribe_group(group, subject)?;
        Ok(Pump {
            sub,
            classifier: EventClassifier::new(cols, rows, profile),
            // The start is the broker's to know, not ours; `offset()` before the
            // first delivery therefore reports 0 as a placeholder, NOT the
            // group's committed cursor (see `offset`).
            from: 0,
            last: None,
            cursor: Some(GroupCursor {
                commits,
                group: group.to_string(),
                committed: None,
            }),
        })
    }

    /// Block for the next `Out` delivery and classify it, returning the wake
    /// events it produced (often empty — a delivery that carries no boundary).
    /// `None` at end of stream. This is the pump's **no-poll wait**: the broker
    /// `recv` parks until a publish advances the log.
    ///
    /// An event's `offset` is the classifier's record index (`0` for the first
    /// delivery after attach); the broker offset the delivery sits at — the one
    /// a woken agent uses — is [`Pump::offset`].
    ///
    /// # Errors
    /// Propagates the broker's delivery I/O error — including a broker-side
    /// rejection of the subscription, which arrives as the first result.
    pub fn next_wake(&mut self) -> io::Result<Option<Vec<SessionEvent>>> {
        loop {
            match self.sub.recv_event()? {
                None => return Ok(None),
                Some(Event::Mark { .. }) => continue,
                Some(Event::Gap(_)) => {
                    self.classifier.reset_escape();
                }
                Some(Event::Delivery { offset, body, .. }) => {
                    let next_last = match self.last {
                        Some(prev) => pump_offset_monotone(prev, offset),
                        None => offset,
                    };
                    self.last = Some(next_last);
                    return Ok(Some(self.classifier.push(&Record::Out(body))));
                }
            }
        }
    }

    /// Every retention gap notice this pump's subscription carried since the last call
    /// ([`Gap::and`]): what retention gave up below the tail
    /// (`REQUIREMENTS-fabric-operations` R4, addendum A9). [`Pump::next_wake`]
    /// automatically resets any mid-sequence VT/OSC parser state across each gap so a
    /// torn pre-gap escape cannot forge a wake or swallow post-gap prompt glyphs; callers
    /// read this method to observe that records in `from..to` were skipped. `None` when
    /// none came.
    pub fn take_gap(&mut self) -> Option<Gap> {
        self.sub.take_gap()
    }

    /// Borrow the folded [`astream_term::Screen`] accumulated across deliveries on this pump.
    #[must_use]
    pub const fn screen(&self) -> &astream_term::Screen {
        self.classifier.screen()
    }

    /// Current sanitized window title (`OSC 0` / `OSC 2`) observed on this session's `/out`.
    #[must_use]
    pub fn title(&self) -> &str {
        self.classifier.title()
    }

    /// Current decoded working directory (`OSC 7`) observed on this session's `/out`.
    #[must_use]
    pub fn cwd(&self) -> &str {
        self.classifier.cwd()
    }

    /// Whether the target session is currently mid-frame inside DEC `?2026` synchronized
    /// output (within the [`astream_term::MAX_SYNC_OUTPUT_BYTES`] safety budget).
    #[must_use]
    pub const fn in_sync_update(&self) -> bool {
        self.classifier.in_sync_update()
    }

    /// Signal that the debounce window elapsed with no new output: emit the
    /// settled-screen wakes (`Quiesced`, and a glyph `PromptReady` when the
    /// target has shown no shell integration).
    pub fn quiesce(&mut self) -> Vec<SessionEvent> {
        self.classifier.quiesce()
    }

    /// Settle the screen only when the target is **not** inside an active DEC `?2026`
    /// synchronized-output frame (`None` while latched, `Some(wakes)` once committed
    /// or auto-unlatched).
    pub fn quiesce_if_unsynced(&mut self) -> Option<Vec<SessionEvent>> {
        self.classifier.quiesce_if_unsynced()
    }

    /// Durably advance this pump's group cursor **through** [`Pump::offset`] —
    /// the delivery just acted on. Returns the offset committed through, or
    /// `Ok(None)` when nothing has been delivered yet (there is no record to
    /// commit, and committing 0 would falsely claim record 0 was handled).
    ///
    /// The broker's `upto` is inclusive, so the next pump on this group starts at
    /// [`Pump::next_offset`]. The returned value is the *committed* offset, not
    /// the commit record's own log offset — those live in different spaces and
    /// the latter must never be used to resume.
    ///
    /// **When to call it.** Not merely after [`Pump::next_wake`] has been acted
    /// on: [`Pump::quiesce`] fires its settle wakes (`Quiesced`, and the glyph
    /// `PromptReady` for an unintegrated target) at the offset of the delivery
    /// that ended the burst, out of the classifier's screen state rather than out
    /// of any record. Commit that delivery before its settle window has closed —
    /// before the debounce fires, or before a later delivery supersedes it — and a
    /// pump that dies in between takes the boundary with it: the replacement
    /// resumes past the record, is delivered nothing, and its `quiesce()` (nothing
    /// pushed) yields nothing. `aspump` therefore holds each delivery's commit
    /// until exactly that point.
    ///
    /// # Errors
    /// [`io::ErrorKind::Unsupported`] for a pump attached with
    /// [`Pump::attach`]/[`Pump::attach_subject`]: it has no group, and its cursor
    /// lives in the pump process by construction. Otherwise propagates the
    /// broker's commit I/O error.
    pub fn commit(&mut self) -> io::Result<Option<u64>> {
        let last = self.last;
        let Some(cursor) = self.cursor.as_mut() else {
            return Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "pump has no durable cursor: attach_group is the committing form; attach/attach_subject hold the cursor in the pump process",
            ));
        };
        let Some(upto) = last else {
            return Ok(None);
        };
        if let Some(c) = cursor.committed {
            if cursor_already_committed(c, upto) {
                // Nothing delivered since the last commit: the group is already there,
                // and committing again would only append a redundant commit record.
                return Ok(Some(upto));
            }
        }
        let next_committed = match cursor.committed {
            Some(prev) => pump_offset_monotone(prev, upto),
            None => upto,
        };
        cursor.commits.commit(&cursor.group, next_committed)?;
        cursor.committed = Some(next_committed);
        Ok(Some(next_committed))
    }

    /// The consumer group this pump's durable cursor lives under, or `None` for
    /// the client-held-offset form.
    #[must_use]
    pub fn group(&self) -> Option<&str> {
        match &self.cursor {
            Some(c) => Some(c.group.as_str()),
            None => None,
        }
    }

    /// The offset this pump has durably committed **through**, or `None` if it
    /// has committed nothing (including every non-group pump). This is the
    /// pump's own record of its commits, not a query of the broker's cursor.
    #[must_use]
    pub fn committed(&self) -> Option<u64> {
        match &self.cursor {
            Some(c) => c.committed,
            None => None,
        }
    }

    /// The broker offset of the most recent delivery — where a woken agent reads
    /// the target's screen. Before the first delivery this is the attach offset
    /// `from_offset`, which is not a delivered record; for a group attach, where
    /// the start is the broker's to know, it is `0` as a placeholder — never read
    /// it as the group's committed cursor.
    #[must_use]
    pub const fn offset(&self) -> u64 {
        match self.last {
            Some(o) => o,
            None => self.from,
        }
    }

    /// The offset a restarted pump attaches from to continue this stream with no
    /// gap and no re-delivery: one past the most recent delivery, or
    /// `from_offset` while nothing has been delivered yet (for a group attach, the
    /// same `0` placeholder as [`Pump::offset`]). It is also exactly the offset a
    /// group resumes at once [`Pump::commit`] has run.
    #[must_use]
    pub const fn next_offset(&self) -> u64 {
        match self.last {
            Some(o) => o.saturating_add(1),
            None => self.from,
        }
    }
}

#[cfg(test)]
mod codec_tests {
    use super::*;

    #[test]
    fn wake_frame_and_cursor_state_roundtrip() {
        let ev = SessionEvent::PromptReady { offset: 3 };
        let tag = wake_kind_tag(&ev);
        assert_eq!(tag, 1);
        let frame = encode_wake_frame(tag, 0x0102_0304_0506_0708, -42);
        assert_eq!(decode_wake_frame(frame), (1, 0x0102_0304_0506_0708, -42));

        let c_enc = encode_pump_cursor_state(10, Some(25), Some(20));
        assert_eq!(
            decode_pump_cursor_state(c_enc),
            Some((10, Some(25), Some(20)))
        );
        let c_none = encode_pump_cursor_state(7, None, None);
        assert_eq!(decode_pump_cursor_state(c_none), Some((7, None, None)));

        let gap = Gap {
            from: 12,
            to: 48,
            records: Some(36),
        };
        let g_enc = encode_pump_gap_wire(gap).expect("ordered gap encodes");
        assert_eq!(decode_pump_gap_wire(&g_enc), Some(gap));
        let gap_none = Gap {
            from: 12,
            to: 48,
            records: None,
        };
        let gn_enc = encode_pump_gap_wire(gap_none).expect("uncounted gap encodes");
        assert_eq!(decode_pump_gap_wire(&gn_enc), Some(gap_none));
        assert_eq!(
            encode_pump_gap_wire(Gap {
                from: 48,
                to: 48,
                records: Some(1),
            }),
            None
        );
    }
}
