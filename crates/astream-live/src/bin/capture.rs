//! `capture` — the live-capture CLI: record ONE real Anthropic model completion
//! and replay the session assembled around it through the in-tree substrate.
//!
//! This is the **non-hermetic** record pass of `astream_agent::unified`'s
//! session, so it is a runnable TOOL, never a green evidence claim (the
//! hermetic parse + replay + fork half is the green claim
//! `cognition.live-bridge.parse-and-replay`). It captures over one of
//! two real, `#[ignore]`-gated paths:
//!
//! * `ANTHROPIC_API_KEY` set → `capture_live`: a keyed `curl` to the Messages API
//!   (key via curl's stdin config, never argv);
//! * no key → `capture_via_cli`: the authenticated `claude` CLI (the local Claude
//!   Code session; the model is asked to WRITE a Messages-shaped JSON object, so
//!   its tool_use block is model-authored text in that shape, not an API block).
//!
//! It exits non-zero only when the chosen path fails (no key AND no working
//! `claude` CLI, network/API error, unparseable response) — a no-key run on a
//! machine with an authenticated CLI performs a real model call and exits 0.
//!
//! ### What is real and what is not
//!
//! Only the model's **completion** is captured live. This binary does NOT run the
//! tool the model called and records NO real effect: the tool output
//! (`"BUILD OK: 0 errors"`), its error flag (`false`), and the effect clock
//! (`1_700_000_000`) below are fixed PLACEHOLDERS handed to `unified_from_capture`,
//! whatever the task was. The replay it then proves deterministic is of the real
//! completion plus those placeholders. Running the captured tool call under a
//! recording seam (real stdout/exit, a taped clock) is a documented seed.
//!
//! ```text
//! ANTHROPIC_API_KEY=... targo --unverified run -p astream-live --bin capture -- "<prompt>" [model]
//! targo --unverified run -p astream-live --bin capture -- "<prompt>"       # via the claude CLI
//! ```

#![forbid(unsafe_code)]

// A contracted fn is written once, through `contract_fn!`: under a Trust compiler
// (`cfg(clean_islands)`, build.rs) it carries its `ensures` clause, which no stock rustc can
// parse, and every other compiler gets the plain fn.
#[macro_use]
#[path = "../../../astream-wire/contract_fn.rs"]
mod contract_fn;

// Plain-Rust twins of the functions this binary's Clean island compiles, for a compiler
// that cannot lex the island.
#[cfg(any(test, not(clean_islands)))]
#[path = "islands/capture_twins.rs"]
mod twins;

use astream_agent::replay_session;
use astream_live::{capture_live, capture_via_cli, unified_from_capture};
use std::process::ExitCode;

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "islands/capture_island.rs"]
mod capture_island;
#[cfg(clean_islands)]
use capture_island::capture_clamp_dim;
#[cfg(not(clean_islands))]
use twins::capture_clamp_dim;

contract_fn! {
    /// Verified check that a replayed live-capture session recorded at least one decision,
    /// linked via `clean-kernel-defeq` to `capture_decisions_present_isl`.
    #[must_use]
    pub const fn capture_decisions_present(decisions: usize) -> bool
    clauses [ensures result == (0 < decisions)]
    {
        0 < decisions
    }
}

/// Four-byte magic prefix (`"ALCP"`) for a 24-byte `capture` replay receipt wire header.
pub const CAPTURE_RECEIPT_WIRE_MAGIC: [u8; 4] = *b"ALCP";

/// Wire format version for `capture` replay receipt wire headers.
pub const CAPTURE_RECEIPT_WIRE_VERSION: u8 = 1;

/// Encode a 24-byte `capture` replay receipt wire header:
/// `[0..4] = b"ALCP"`, `[4] = version (1)`, `[5] = path_tag` (`0` = ApiKey, `1` = ClaudeCli),
/// `[6] = deterministic` (`0` or `1`, requires `decisions > 0` when `1`),
/// `[7] = is_error` (`0` or `1`), `[8..12] = decisions (BE)`,
/// `[12..16] = inputs_applied (BE)`, `[16..24] = screen_hash (BE)`.
#[must_use]
pub const fn capture_encode_receipt_wire(
    path_tag: u8,
    deterministic: bool,
    is_error: bool,
    decisions: u32,
    inputs_applied: u32,
    screen_hash: u64,
) -> Option<[u8; 24]> {
    let det_tag = deterministic as u8;
    let err_tag = is_error as u8;
    let out = [
        CAPTURE_RECEIPT_WIRE_MAGIC[0],
        CAPTURE_RECEIPT_WIRE_MAGIC[1],
        CAPTURE_RECEIPT_WIRE_MAGIC[2],
        CAPTURE_RECEIPT_WIRE_MAGIC[3],
        CAPTURE_RECEIPT_WIRE_VERSION,
        path_tag,
        det_tag,
        err_tag,
        ((decisions >> 24) & 0xFF) as u8,
        ((decisions >> 16) & 0xFF) as u8,
        ((decisions >> 8) & 0xFF) as u8,
        (decisions & 0xFF) as u8,
        ((inputs_applied >> 24) & 0xFF) as u8,
        ((inputs_applied >> 16) & 0xFF) as u8,
        ((inputs_applied >> 8) & 0xFF) as u8,
        (inputs_applied & 0xFF) as u8,
        ((screen_hash >> 56) & 0xFF) as u8,
        ((screen_hash >> 48) & 0xFF) as u8,
        ((screen_hash >> 40) & 0xFF) as u8,
        ((screen_hash >> 32) & 0xFF) as u8,
        ((screen_hash >> 24) & 0xFF) as u8,
        ((screen_hash >> 16) & 0xFF) as u8,
        ((screen_hash >> 8) & 0xFF) as u8,
        (screen_hash & 0xFF) as u8,
    ];
    if path_tag > 1 || (deterministic && decisions == 0) {
        return None;
    }
    Some(out)
}

/// Decode a 24-byte `capture` replay receipt wire header into
/// `(path_tag, deterministic, is_error, decisions, inputs_applied, screen_hash)`.
#[must_use]
pub const fn capture_decode_receipt_wire(buf: &[u8]) -> Option<(u8, bool, bool, u32, u32, u64)> {
    let [b'A', b'L', b'C', b'P', CAPTURE_RECEIPT_WIRE_VERSION, path_tag, det_tag, err_tag, d0, d1, d2, d3, i0, i1, i2, i3, h0, h1, h2, h3, h4, h5, h6, h7, ..] =
        *buf
    else {
        return None;
    };
    let decisions = ((d0 as u32) << 24) | ((d1 as u32) << 16) | ((d2 as u32) << 8) | (d3 as u32);
    let inputs_applied =
        ((i0 as u32) << 24) | ((i1 as u32) << 16) | ((i2 as u32) << 8) | (i3 as u32);
    let screen_hash = ((h0 as u64) << 56)
        | ((h1 as u64) << 48)
        | ((h2 as u64) << 40)
        | ((h3 as u64) << 32)
        | ((h4 as u64) << 24)
        | ((h5 as u64) << 16)
        | ((h6 as u64) << 8)
        | (h7 as u64);
    let deterministic = match det_tag {
        0 => false,
        1 => true,
        _ => return None,
    };
    let is_error = match err_tag {
        0 => false,
        1 => true,
        _ => return None,
    };
    if path_tag > 1 || (deterministic && decisions == 0) {
        return None;
    }
    Some((
        path_tag,
        deterministic,
        is_error,
        decisions,
        inputs_applied,
        screen_hash,
    ))
}

/// Four-byte magic prefix (`"ALTR"`) for a 20-byte `capture` turn configuration wire header.
pub const CAPTURE_TURN_WIRE_MAGIC: [u8; 4] = *b"ALTR";

/// Wire format version for `capture` turn configuration wire headers.
pub const CAPTURE_TURN_WIRE_VERSION: u8 = 1;

/// Encode a 20-byte `capture` turn configuration wire header:
/// `[0..4] = b"ALTR"`, `[4] = version (1)`, `[5] = is_error (0/1)`,
/// `[6..8] = cols (BE)`, `[8..10] = rows (BE)`, `[10..12] = tool_out_len (BE)`,
/// `[12..20] = clock_sec (BE)`.
#[must_use]
pub const fn capture_encode_turn_wire(
    clock_sec: u64,
    cols: u16,
    rows: u16,
    tool_out_len: u16,
    is_error: bool,
) -> Option<[u8; 20]> {
    let err_tag = is_error as u8;
    let out = [
        CAPTURE_TURN_WIRE_MAGIC[0],
        CAPTURE_TURN_WIRE_MAGIC[1],
        CAPTURE_TURN_WIRE_MAGIC[2],
        CAPTURE_TURN_WIRE_MAGIC[3],
        CAPTURE_TURN_WIRE_VERSION,
        err_tag,
        ((cols >> 8) & 0xFF) as u8,
        (cols & 0xFF) as u8,
        ((rows >> 8) & 0xFF) as u8,
        (rows & 0xFF) as u8,
        ((tool_out_len >> 8) & 0xFF) as u8,
        (tool_out_len & 0xFF) as u8,
        ((clock_sec >> 56) & 0xFF) as u8,
        ((clock_sec >> 48) & 0xFF) as u8,
        ((clock_sec >> 40) & 0xFF) as u8,
        ((clock_sec >> 32) & 0xFF) as u8,
        ((clock_sec >> 24) & 0xFF) as u8,
        ((clock_sec >> 16) & 0xFF) as u8,
        ((clock_sec >> 8) & 0xFF) as u8,
        (clock_sec & 0xFF) as u8,
    ];
    if cols == 0 || rows == 0 {
        return None;
    }
    Some(out)
}

/// Decode a 20-byte `capture` turn configuration wire header into
/// `(clock_sec, cols, rows, tool_out_len, is_error)`.
#[must_use]
pub const fn capture_decode_turn_wire(buf: &[u8]) -> Option<(u64, u16, u16, u16, bool)> {
    let [b'A', b'L', b'T', b'R', CAPTURE_TURN_WIRE_VERSION, err_tag, c0, c1, r0, r1, t0, t1, k0, k1, k2, k3, k4, k5, k6, k7, ..] =
        *buf
    else {
        return None;
    };
    let cols = ((c0 as u16) << 8) | (c1 as u16);
    let rows = ((r0 as u16) << 8) | (r1 as u16);
    let tool_out_len = ((t0 as u16) << 8) | (t1 as u16);
    let clock_sec = ((k0 as u64) << 56)
        | ((k1 as u64) << 48)
        | ((k2 as u64) << 40)
        | ((k3 as u64) << 32)
        | ((k4 as u64) << 24)
        | ((k5 as u64) << 16)
        | ((k6 as u64) << 8)
        | (k7 as u64);
    let is_error = match err_tag {
        0 => false,
        1 => true,
        _ => return None,
    };
    if cols == 0 || rows == 0 {
        return None;
    }
    Some((clock_sec, cols, rows, tool_out_len, is_error))
}

/// Four-byte magic prefix (`"ALCS"`) for a 20-byte `capture` summary wire header.
pub const CAPTURE_SUMMARY_WIRE_MAGIC: [u8; 4] = *b"ALCS";

/// Wire format version for `capture` summary wire headers.
pub const CAPTURE_SUMMARY_WIRE_VERSION: u8 = 1;

/// Encode a 20-byte `capture` summary wire header:
/// `[0..4] = b"ALCS"`, `[4] = version (1)`, `[5] = exit_code` (`0..=2`), `[6..8] = 0`,
/// `[8..12] = events_len (BE)`, `[12..16] = prompt_bytes (BE)`,
/// `[16..20] = model_bytes (BE)`.
#[must_use]
pub const fn capture_encode_summary_wire(
    exit_code: u8,
    events_len: u32,
    prompt_bytes: u32,
    model_bytes: u32,
) -> Option<[u8; 20]> {
    let out = [
        CAPTURE_SUMMARY_WIRE_MAGIC[0],
        CAPTURE_SUMMARY_WIRE_MAGIC[1],
        CAPTURE_SUMMARY_WIRE_MAGIC[2],
        CAPTURE_SUMMARY_WIRE_MAGIC[3],
        CAPTURE_SUMMARY_WIRE_VERSION,
        exit_code,
        0,
        0,
        ((events_len >> 24) & 0xFF) as u8,
        ((events_len >> 16) & 0xFF) as u8,
        ((events_len >> 8) & 0xFF) as u8,
        (events_len & 0xFF) as u8,
        ((prompt_bytes >> 24) & 0xFF) as u8,
        ((prompt_bytes >> 16) & 0xFF) as u8,
        ((prompt_bytes >> 8) & 0xFF) as u8,
        (prompt_bytes & 0xFF) as u8,
        ((model_bytes >> 24) & 0xFF) as u8,
        ((model_bytes >> 16) & 0xFF) as u8,
        ((model_bytes >> 8) & 0xFF) as u8,
        (model_bytes & 0xFF) as u8,
    ];
    if exit_code > 2 || prompt_bytes == 0 || model_bytes == 0 || (exit_code == 0 && events_len == 0)
    {
        return None;
    }
    Some(out)
}

/// Decode a 20-byte `capture` summary wire header into
/// `(exit_code, events_len, prompt_bytes, model_bytes)`.
#[must_use]
pub const fn capture_decode_summary_wire(buf: &[u8]) -> Option<(u8, u32, u32, u32)> {
    let [b'A', b'L', b'C', b'S', CAPTURE_SUMMARY_WIRE_VERSION, exit_code, 0, 0, e0, e1, e2, e3, p0, p1, p2, p3, m0, m1, m2, m3, ..] =
        *buf
    else {
        return None;
    };
    let events_len = ((e0 as u32) << 24) | ((e1 as u32) << 16) | ((e2 as u32) << 8) | (e3 as u32);
    let prompt_bytes = ((p0 as u32) << 24) | ((p1 as u32) << 16) | ((p2 as u32) << 8) | (p3 as u32);
    let model_bytes = ((m0 as u32) << 24) | ((m1 as u32) << 16) | ((m2 as u32) << 8) | (m3 as u32);
    if exit_code > 2 || prompt_bytes == 0 || model_bytes == 0 || (exit_code == 0 && events_len == 0)
    {
        return None;
    }
    Some((exit_code, events_len, prompt_bytes, model_bytes))
}

/// Four-byte magic prefix (`"ALCC"`) for a 20-byte `capture` CLI config wire header.
pub const CAPTURE_CONFIG_WIRE_MAGIC: [u8; 4] = *b"ALCC";

/// Wire format version for `capture` CLI config wire headers.
pub const CAPTURE_CONFIG_WIRE_VERSION: u8 = 1;

/// Encode a 20-byte `capture` CLI config wire header:
/// `[0..4] = b"ALCC"`, `[4] = version (1)`, `[5] = has_api_key (0/1)`,
/// `[6..8] = clamp_cols (BE)`, `[8..10] = clamp_max (BE)`, `[10..12] = replay_rows (BE)`,
/// `[12..20] = placeholder_clock (BE)`.
#[must_use]
pub const fn capture_encode_config_wire(
    has_api_key: bool,
    clamp_cols: u16,
    clamp_max: u16,
    replay_rows: u16,
    placeholder_clock: u64,
) -> Option<[u8; 20]> {
    let key_tag = has_api_key as u8;
    let out = [
        CAPTURE_CONFIG_WIRE_MAGIC[0],
        CAPTURE_CONFIG_WIRE_MAGIC[1],
        CAPTURE_CONFIG_WIRE_MAGIC[2],
        CAPTURE_CONFIG_WIRE_MAGIC[3],
        CAPTURE_CONFIG_WIRE_VERSION,
        key_tag,
        ((clamp_cols >> 8) & 0xFF) as u8,
        (clamp_cols & 0xFF) as u8,
        ((clamp_max >> 8) & 0xFF) as u8,
        (clamp_max & 0xFF) as u8,
        ((replay_rows >> 8) & 0xFF) as u8,
        (replay_rows & 0xFF) as u8,
        ((placeholder_clock >> 56) & 0xFF) as u8,
        ((placeholder_clock >> 48) & 0xFF) as u8,
        ((placeholder_clock >> 40) & 0xFF) as u8,
        ((placeholder_clock >> 32) & 0xFF) as u8,
        ((placeholder_clock >> 24) & 0xFF) as u8,
        ((placeholder_clock >> 16) & 0xFF) as u8,
        ((placeholder_clock >> 8) & 0xFF) as u8,
        (placeholder_clock & 0xFF) as u8,
    ];
    if clamp_cols == 0 || clamp_max < clamp_cols || replay_rows == 0 || placeholder_clock == 0 {
        return None;
    }
    Some(out)
}

/// Decode a 20-byte `capture` CLI config wire header into
/// `(has_api_key, clamp_cols, clamp_max, replay_rows, placeholder_clock)`.
#[must_use]
pub const fn capture_decode_config_wire(buf: &[u8]) -> Option<(bool, u16, u16, u16, u64)> {
    let [b'A', b'L', b'C', b'C', CAPTURE_CONFIG_WIRE_VERSION, key_tag, c0, c1, m0, m1, r0, r1, k0, k1, k2, k3, k4, k5, k6, k7, ..] =
        *buf
    else {
        return None;
    };
    let clamp_cols = ((c0 as u16) << 8) | (c1 as u16);
    let clamp_max = ((m0 as u16) << 8) | (m1 as u16);
    let replay_rows = ((r0 as u16) << 8) | (r1 as u16);
    let placeholder_clock = ((k0 as u64) << 56)
        | ((k1 as u64) << 48)
        | ((k2 as u64) << 40)
        | ((k3 as u64) << 32)
        | ((k4 as u64) << 24)
        | ((k5 as u64) << 16)
        | ((k6 as u64) << 8)
        | (k7 as u64);
    let has_api_key = match key_tag {
        0 => false,
        1 => true,
        _ => return None,
    };
    if clamp_cols == 0 || clamp_max < clamp_cols || replay_rows == 0 || placeholder_clock == 0 {
        return None;
    }
    Some((
        has_api_key,
        clamp_cols,
        clamp_max,
        replay_rows,
        placeholder_clock,
    ))
}

contract_fn! {
    /// Verified SSE checkpoint byte budget check (`accumulated_bytes <= max_sse_bytes`).
    #[must_use]
    pub const fn capture_sse_budget_within(max_sse_bytes: u64, accumulated_bytes: u64) -> bool
    clauses [ensures result == (accumulated_bytes <= max_sse_bytes)]
    {
        accumulated_bytes <= max_sse_bytes
    }
}

/// Four-byte magic prefix (`"ALSE"`) for a 24-byte `capture` SSE stream checkpoint wire header.
pub const CAPTURE_SSE_WIRE_MAGIC: [u8; 4] = *b"ALSE";

/// Wire format version for `capture` SSE stream checkpoint wire headers.
pub const CAPTURE_SSE_WIRE_VERSION: u8 = 1;

/// Encode a 24-byte `capture` SSE stream checkpoint wire header:
/// `[0..4] = b"ALSE"`, `[4] = version (1)`, `[5] = stop_tag` (`0..=3`),
/// `[6] = has_tool_use` (`0` or `1`), `[7] = complete` (`0` or `1`),
/// `[8..12] = sse_frames (BE)`, `[12..16] = sse_bytes (BE)`,
/// `[16..24] = stream_seq (BE)`.
#[must_use]
pub const fn capture_encode_sse_wire(
    stop_tag: u8,
    has_tool_use: bool,
    complete: bool,
    sse_frames: u32,
    sse_bytes: u32,
    stream_seq: u64,
) -> Option<[u8; 24]> {
    let tool_tag = has_tool_use as u8;
    let done_tag = complete as u8;
    let out = [
        CAPTURE_SSE_WIRE_MAGIC[0],
        CAPTURE_SSE_WIRE_MAGIC[1],
        CAPTURE_SSE_WIRE_MAGIC[2],
        CAPTURE_SSE_WIRE_MAGIC[3],
        CAPTURE_SSE_WIRE_VERSION,
        stop_tag,
        tool_tag,
        done_tag,
        ((sse_frames >> 24) & 0xFF) as u8,
        ((sse_frames >> 16) & 0xFF) as u8,
        ((sse_frames >> 8) & 0xFF) as u8,
        (sse_frames & 0xFF) as u8,
        ((sse_bytes >> 24) & 0xFF) as u8,
        ((sse_bytes >> 16) & 0xFF) as u8,
        ((sse_bytes >> 8) & 0xFF) as u8,
        (sse_bytes & 0xFF) as u8,
        ((stream_seq >> 56) & 0xFF) as u8,
        ((stream_seq >> 48) & 0xFF) as u8,
        ((stream_seq >> 40) & 0xFF) as u8,
        ((stream_seq >> 32) & 0xFF) as u8,
        ((stream_seq >> 24) & 0xFF) as u8,
        ((stream_seq >> 16) & 0xFF) as u8,
        ((stream_seq >> 8) & 0xFF) as u8,
        (stream_seq & 0xFF) as u8,
    ];
    if stop_tag > 3 || (complete && sse_frames == 0) || (has_tool_use && sse_bytes == 0) {
        return None;
    }
    Some(out)
}

/// Decode a 24-byte `capture` SSE stream checkpoint wire header into
/// `(stop_tag, has_tool_use, complete, sse_frames, sse_bytes, stream_seq)`.
#[must_use]
pub const fn capture_decode_sse_wire(buf: &[u8]) -> Option<(u8, bool, bool, u32, u32, u64)> {
    let [b'A', b'L', b'S', b'E', CAPTURE_SSE_WIRE_VERSION, stop_tag, tool_tag, done_tag, f0, f1, f2, f3, b0, b1, b2, b3, s0, s1, s2, s3, s4, s5, s6, s7, ..] =
        *buf
    else {
        return None;
    };
    let sse_frames = ((f0 as u32) << 24) | ((f1 as u32) << 16) | ((f2 as u32) << 8) | (f3 as u32);
    let sse_bytes = ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32);
    let stream_seq = ((s0 as u64) << 56)
        | ((s1 as u64) << 48)
        | ((s2 as u64) << 40)
        | ((s3 as u64) << 32)
        | ((s4 as u64) << 24)
        | ((s5 as u64) << 16)
        | ((s6 as u64) << 8)
        | (s7 as u64);
    let has_tool_use = match tool_tag {
        0 => false,
        1 => true,
        _ => return None,
    };
    let complete = match done_tag {
        0 => false,
        1 => true,
        _ => return None,
    };
    if stop_tag > 3 || (complete && sse_frames == 0) || (has_tool_use && sse_bytes == 0) {
        return None;
    }
    Some((
        stop_tag,
        has_tool_use,
        complete,
        sse_frames,
        sse_bytes,
        stream_seq,
    ))
}

/// The placeholder tool result and clock (see the module doc): NOT a tool run.
const PLACEHOLDER_TOOL_OUTPUT: &str = "BUILD OK: 0 errors";
const PLACEHOLDER_IS_ERROR: bool = false;
const PLACEHOLDER_CLOCK: u64 = 1_700_000_000;

fn main() -> ExitCode {
    let mut args = std::env::args_os().skip(1);
    let prompt = match args.next() {
        Some(raw) => match raw.into_string() {
            Ok(s) => s,
            Err(_) => {
                eprintln!("capture: prompt argument is not valid UTF-8");
                return ExitCode::from(2);
            }
        },
        None => "Build the Rust project and report whether it compiles.".to_string(),
    };
    let model = match args.next() {
        Some(raw) => match raw.into_string() {
            Ok(s) => s,
            Err(_) => {
                eprintln!("capture: model argument is not valid UTF-8");
                return ExitCode::from(2);
            }
        },
        None => "claude-sonnet-4-6".to_string(),
    };

    // Two real, non-hermetic capture paths: a raw keyed Messages call (curl) when
    // ANTHROPIC_API_KEY is set, else the authenticated `claude` CLI (no key needed —
    // it uses the local Claude Code session). Either way the model completion is real.
    let completion = if std::env::var_os("ANTHROPIC_API_KEY").is_some() {
        capture_live(&prompt, &model)
    } else {
        eprintln!("(no ANTHROPIC_API_KEY — capturing via the authenticated `claude` CLI)");
        capture_via_cli(&prompt)
    };
    let completion = match completion {
        Ok(c) => c,
        Err(e) => {
            eprintln!("capture failed: {e}");
            eprintln!(
                "(the live capture is the non-hermetic record pass: it needs \
                 either ANTHROPIC_API_KEY or an authenticated `claude` CLI)"
            );
            return ExitCode::FAILURE;
        }
    };

    // Assemble the unified four-stream turn around the real completion and replay
    // it in-tree, deterministically. The tool result and clock are placeholders:
    // the tool is NOT run here (see the module doc).
    let events = unified_from_capture(
        completion,
        PLACEHOLDER_TOOL_OUTPUT,
        PLACEHOLDER_IS_ERROR,
        PLACEHOLDER_CLOCK,
    );
    let _ = capture_clamp_dim(80, 240);
    let a = replay_session(&events, 80, 12);
    let b = replay_session(&events, 80, 12);
    let deterministic = a == b && capture_decisions_present(a.decisions.len());
    println!(
        "captured a live completion + replayed it with a PLACEHOLDER tool result \
         ({PLACEHOLDER_TOOL_OUTPUT:?}, is_error={PLACEHOLDER_IS_ERROR}) and clock \
         ({PLACEHOLDER_CLOCK}; the tool was NOT run): {} decisions, {} inputs applied, \
         screen_hash={:016x}, deterministic={}",
        a.decisions.len(),
        a.inputs_applied,
        a.screen_hash,
        deterministic
    );
    if deterministic {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
