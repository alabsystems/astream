//! `aspump` — tail a target session's `/out` off the bus and print the semantic
//! WAKE lines a driving agent acts on, one per line. The shell face of
//! [`astream_pump`]: a bridge or an agent runner reads these lines instead of
//! polling the raw byte stream, and reacts only on a real boundary.
//!
//! ```text
//! aspump <endpoint> [<sid>] [--subject SUBJ] [--from N | --group G]
//!        [--cols C] [--rows R] [--debounce MS] [--once] [--tcp]
//!        [--key-file PATH] [--cap-file PATH]...
//! ```
//!
//! Each line is `<KIND> boffset=<broker-offset> [exit=E]` — the broker offset of
//! the record that produced the wake, where a woken agent reads the target's
//! screen. OSC-133 marks fire as they arrive; `QUIESCED` and a glyph
//! `PROMPT_READY` fire after `--debounce` milliseconds (default 300) of no new
//! output. A worker thread forwards raw deliveries so the main thread's
//! `recv_timeout` can drive the debounce (the broker's blocking `recv` has no
//! timeout of its own).
//!
//! **What to tail.** `<sid>` is the built PTY face `/a/stream/term/<sid>/out`;
//! `--subject SUBJ` names any subject instead — a fabric node's
//! `/f/<F>/term/<node>/<sid>/out`, say. Exactly one of the two is required.
//!
//! **Where the cursor lives.** `--from N` is a *client-held* cursor and is
//! **inclusive**: record `N` is delivered (and its wake printed) again. To resume
//! after a run whose last line was `... boffset=N`, pass `--from N+1`.
//! `--group G` is the *broker-durable* alternative: the pump resumes from `G`'s
//! committed offset, so a restart needs no offset at all. It is **at-least-once
//! on wakes, never exactly-once**. What the commit order buys is the *never
//! skipped* half: a delivery's commit is held until every wake that delivery can
//! still produce is out — its own marks as they arrive, and the `QUIESCED` /
//! glyph `PROMPT_READY` the debounce timer fires *at its offset* — and a later
//! delivery, whose output closes the earlier one's settle window, supersedes the
//! held commit. So at most ONE delivery is ever uncommitted, and the cursor never
//! advances past a record whose settle wake was never printed: a kill in that
//! window re-delivers that record, and the replacement prints its marks again and
//! re-derives the settle wake from it. Duplicates are the price — that one
//! record's wakes can appear twice — and the re-derivation is only as good as
//! the resume rule below: the replacement's screen starts blank at that record.
//! The commit travels on a second connection (a group subscription's own
//! connection is one-way), and there is at most one commit record per delivery — the
//! durability is paid for in log writes. `--group` and `--from` are mutually
//! exclusive. In both forms the classifier starts from a blank screen at the
//! resume point.
//!
//! **Transport.** Default is the Unix socket at `<endpoint>`; `--tcp` makes
//! `<endpoint>` a `host:port`; `--key-file PATH` (64 hex chars = a 32-byte PSK,
//! never on argv) selects the XChaCha20-Poly1305-sealed TCP transport and
//! implies `--tcp`. It needs `aspump` built with `--features aead`; without it
//! the flag is a usage error, never a silent plaintext downgrade.
//!
//! **Capabilities.** `--cap-file PATH` (repeatable) reads `<grant> <tag-hex>`
//! capability lines (as `asb mint` prints) and attaches each of them via the
//! broker's `Hello` → `Nonce` → `Attach` proof-of-possession handshake before
//! subscribing (and on the commit connection as well when `--group` is used).
//! It needs `aspump` built with `--features cap`; `--cap-tag` / `--cap-filter`
//! on argv are refused because argv is world-readable via `ps`.
//!
//! **One-wake exit (`--once`).** Exit `0` immediately after emitting (and, under
//! `--group`, committing) the first wake line — whether an immediate OSC-133 mark
//! or a debounced settle wake (`QUIESCED` / glyph `PROMPT_READY`). A turn-based
//! driver whose background command wakes it by exiting runs `aspump --once`
//! instead of `aspump … | head -1` (which after a settle wake would stay alive
//! until the next output write discovered the broken pipe).
//!
//! Exit status: `0` when `--once` emits its wake, the broker closes the stream, or
//! the reader of stdout goes away (a broken pipe ends the pump instead of leaving
//! it holding a subscription); `1` on a connect, delivery, commit, or broker-side error (the
//! reason is on stderr — a rejected subscription is an error, not a silent EOF);
//! `2` on a usage error (a flag value that is missing, itself a flag,
//! non-numeric, or out of range: `--cols`/`--rows` in `1..=65535`, `--debounce`
//! in `1..=4294967295`; a surplus positional, which is almost always a flag whose
//! `--name` was dropped; or a contradictory combination). Argv that is not valid
//! UTF-8 is a usage error too, never a panic — and neither is a STDERR with no
//! reader: `eprintln!` panics on a write error, so every diagnostic goes through a
//! writer that drops what it cannot deliver. The message is the part that can be
//! lost; the status is the part a supervisor reads, and it stays 0, 1 or 2.
//!
//! A closed (as opposed to broken) stdout is not detectable — `std` reports
//! EBADF on fd 1 as a successful write — so a pump launched with fd 1 closed
//! keeps its subscription; a broken pipe does end it (exit 0).
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
#[path = "islands/aspump_twins.rs"]
mod twins;

use astream_broker::{Client, Event};
use astream_pump::{
    deliver_hook_tcp, gap_line, out_subject, wake_line, wake_line_with_meta, Gap, WakeHookFormat,
    WakeTaskQueue,
};
use astream_term::events::{
    sync_hold_ticks_clamp, EventClassifier, Profile, SessionEvent, MAX_SYNC_HOLD_TICKS,
};
use astream_term::record::Record;
use std::io::{self, Read, Write};
use std::process::ExitCode;
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

#[allow(dead_code)]
#[path = "../../../astream-cap/src/capfile.rs"]
mod capfile;

const USAGE: &str = "usage: aspump --help | --version
       aspump <endpoint> [<sid>] [--subject SUBJ] [--from N | --group G] [--cols C] [--rows R] [--debounce MS] [--profile P] [--meta] [--once] [--task-subject SUBJ [--task-producer ID] [--task-seq-start N]] [--hook-unix PATH | --hook-tcp ADDR] [--hook-format FMT] [--tcp] [--key-file PATH] [--cap-file PATH]...
  <sid> tails the built face /a/stream/term/<sid>/out; --subject tails any subject (exactly one of the two)
  --from N is a client-held cursor and INCLUSIVE; --group G is the broker-durable cursor (they are exclusive)
  --profile P: prompt glyph profile for targets without OSC-133 (common|claude|codex|repl|emacs|shell|none; default common)
  --meta: append percent-encoded cwd=<path> (OSC 7) and title=<title> (OSC 0/2) tokens to wake lines when known
  --once: print one wake line (committing its offset under --group) and exit 0
  --task-subject SUBJ: post each wake onto broker task queue SUBJ before committing --group
  --hook-unix PATH / --hook-tcp ADDR: deliver each wake to a Unix or TCP hook listener (--hook-format line|claude-notification|claude-stop|codex-turn)
  --key-file PATH: 64 hex chars (32-byte PSK) for sealed TCP, or with --handshake / --roam (UDP); needs --features aead / handshake
  --host-key-file PATH --client-key-file PATH: mutual Ed25519 identity TCP; needs --features identity
  --cert-file PATH --ca-key-file PATH... (--client-key-file PATH | --ssh-agent-sock PATH) [--host-principal P]: CA-certified SIGMA TCP; needs --features identity
  --cap-file PATH: repeatable `<grant> <tag-hex>` capability file for a guarded broker; needs aspump built --features cap";

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "islands/aspump_island.rs"]
mod aspump_island;
#[cfg(clean_islands)]
use aspump_island::aspump_commit_offset_advance;
#[cfg(not(clean_islands))]
use twins::aspump_commit_offset_advance;

contract_fn! {
    /// Verified check that a `--cols` or `--rows` dimension is strictly positive (`0 < dim`),
    /// linked via `clean-kernel-defeq` to `aspump_dim_in_range_isl`.
    #[must_use]
    pub const fn aspump_dim_in_range(dim: u16) -> bool
    clauses [ensures result == (0 < dim)]
    {
        0 < dim
    }
}

/// Four-byte magic prefix (`"APMP"`) for a 20-byte `aspump` options wire header.
pub const ASPUMP_OPTS_WIRE_MAGIC: [u8; 4] = *b"APMP";

/// Wire format version for `aspump` options wire headers.
pub const ASPUMP_OPTS_WIRE_VERSION: u8 = 1;

/// Encode a 20-byte `aspump` options wire header:
/// `[0..4] = b"APMP"`, `[4] = version (1)`, `[5] = transport_tag` (`0..=2`),
/// `[6] = cursor_tag` (`0..=1`), `[7] = cap_count`, `[8..12] = debounce_ms (BE)`,
/// `[12..14] = cols (BE)`, `[14..16] = rows (BE)`, `[16..20] = 0`.
#[must_use]
pub const fn aspump_encode_opts_wire(
    transport_tag: u8,
    cursor_tag: u8,
    cap_count: u8,
    cols: u16,
    rows: u16,
    debounce_ms: u32,
) -> Option<[u8; 20]> {
    let out = [
        ASPUMP_OPTS_WIRE_MAGIC[0],
        ASPUMP_OPTS_WIRE_MAGIC[1],
        ASPUMP_OPTS_WIRE_MAGIC[2],
        ASPUMP_OPTS_WIRE_MAGIC[3],
        ASPUMP_OPTS_WIRE_VERSION,
        transport_tag,
        cursor_tag,
        cap_count,
        ((debounce_ms >> 24) & 0xFF) as u8,
        ((debounce_ms >> 16) & 0xFF) as u8,
        ((debounce_ms >> 8) & 0xFF) as u8,
        (debounce_ms & 0xFF) as u8,
        ((cols >> 8) & 0xFF) as u8,
        (cols & 0xFF) as u8,
        ((rows >> 8) & 0xFF) as u8,
        (rows & 0xFF) as u8,
        0,
        0,
        0,
        0,
    ];
    if transport_tag > 2
        || cursor_tag > 1
        || !aspump_dim_in_range(cols)
        || !aspump_dim_in_range(rows)
        || debounce_ms == 0
    {
        return None;
    }
    Some(out)
}

/// Decode a 20-byte `aspump` options wire header into
/// `(transport_tag, cursor_tag, cap_count, cols, rows, debounce_ms)`.
#[must_use]
pub const fn aspump_decode_opts_wire(buf: &[u8]) -> Option<(u8, u8, u8, u16, u16, u32)> {
    let [b'A', b'P', b'M', b'P', ASPUMP_OPTS_WIRE_VERSION, transport_tag, cursor_tag, cap_count, d0, d1, d2, d3, c0, c1, r0, r1, 0, 0, 0, 0, ..] =
        *buf
    else {
        return None;
    };
    let debounce_ms = ((d0 as u32) << 24) | ((d1 as u32) << 16) | ((d2 as u32) << 8) | (d3 as u32);
    let cols = ((c0 as u16) << 8) | (c1 as u16);
    let rows = ((r0 as u16) << 8) | (r1 as u16);
    if transport_tag > 2
        || cursor_tag > 1
        || !aspump_dim_in_range(cols)
        || !aspump_dim_in_range(rows)
        || debounce_ms == 0
    {
        return None;
    }
    Some((
        transport_tag,
        cursor_tag,
        cap_count,
        cols,
        rows,
        debounce_ms,
    ))
}

/// Four-byte magic prefix (`"AWKE"`) for a 20-byte `aspump` wake delivery wire header.
pub const ASPUMP_WAKE_WIRE_MAGIC: [u8; 4] = *b"AWKE";

/// Wire format version for `aspump` wake delivery wire headers.
pub const ASPUMP_WAKE_WIRE_VERSION: u8 = 1;

/// Encode a 20-byte `aspump` wake delivery wire header:
/// `[0..4] = b"AWKE"`, `[4] = version (1)`, `[5] = wake_kind` (`0..=4`),
/// `[6] = has_exit` (`0` or `1`, only `1` when `wake_kind == 2`), `[7] = 0`,
/// `[8..16] = boffset (BE)`, `[16..20] = exit_code (i32 BE, 0 when !has_exit)`.
#[must_use]
pub const fn aspump_encode_wake_wire(
    wake_kind: u8,
    has_exit: bool,
    boffset: u64,
    exit_code: u32,
) -> Option<[u8; 20]> {
    let exit_tag = has_exit as u8;
    let out = [
        ASPUMP_WAKE_WIRE_MAGIC[0],
        ASPUMP_WAKE_WIRE_MAGIC[1],
        ASPUMP_WAKE_WIRE_MAGIC[2],
        ASPUMP_WAKE_WIRE_MAGIC[3],
        ASPUMP_WAKE_WIRE_VERSION,
        wake_kind,
        exit_tag,
        0,
        ((boffset >> 56) & 0xFF) as u8,
        ((boffset >> 48) & 0xFF) as u8,
        ((boffset >> 40) & 0xFF) as u8,
        ((boffset >> 32) & 0xFF) as u8,
        ((boffset >> 24) & 0xFF) as u8,
        ((boffset >> 16) & 0xFF) as u8,
        ((boffset >> 8) & 0xFF) as u8,
        (boffset & 0xFF) as u8,
        ((exit_code >> 24) & 0xFF) as u8,
        ((exit_code >> 16) & 0xFF) as u8,
        ((exit_code >> 8) & 0xFF) as u8,
        (exit_code & 0xFF) as u8,
    ];
    if wake_kind > 4 || (has_exit && wake_kind != 2) || (!has_exit && exit_code != 0) {
        return None;
    }
    Some(out)
}

/// Decode a 20-byte `aspump` wake delivery wire header into
/// `(wake_kind, has_exit, boffset, exit_code)`.
#[must_use]
pub const fn aspump_decode_wake_wire(buf: &[u8]) -> Option<(u8, bool, u64, u32)> {
    let [b'A', b'W', b'K', b'E', ASPUMP_WAKE_WIRE_VERSION, wake_kind, exit_tag, 0, o0, o1, o2, o3, o4, o5, o6, o7, e0, e1, e2, e3, ..] =
        *buf
    else {
        return None;
    };
    let boffset = ((o0 as u64) << 56)
        | ((o1 as u64) << 48)
        | ((o2 as u64) << 40)
        | ((o3 as u64) << 32)
        | ((o4 as u64) << 24)
        | ((o5 as u64) << 16)
        | ((o6 as u64) << 8)
        | (o7 as u64);
    let exit_code = ((e0 as u32) << 24) | ((e1 as u32) << 16) | ((e2 as u32) << 8) | (e3 as u32);
    let has_exit = match exit_tag {
        0 => false,
        1 => true,
        _ => return None,
    };
    if wake_kind > 4 || (has_exit && wake_kind != 2) || (!has_exit && exit_code != 0) {
        return None;
    }
    Some((wake_kind, has_exit, boffset, exit_code))
}

/// Where the cursor lives: in this process, or on the broker.
enum Cursor {
    /// A client-held offset, inclusive (`--from`, default 0).
    From(u64),
    /// A broker-durable consumer group (`--group`).
    Group(String),
}

/// How the pump reaches the broker.
enum Transport {
    Unix,
    Tcp,
    /// XChaCha20-Poly1305-sealed TCP on a pre-shared key (`--key-file`). The
    /// variant itself is absent without the feature, so a build that cannot seal
    /// has no code path that pretends it can.
    #[cfg(feature = "aead")]
    Sealed([u8; 32]),
    /// Rung-7 forward-secret ephemeral X25519 + PSK TCP (`--handshake --key-file`).
    #[cfg(feature = "handshake")]
    Handshake([u8; 32]),
    /// Rung-10 zero-gap AEAD-over-UDP Connection-ID migration (`--roam --key-file`).
    #[cfg(feature = "handshake")]
    Roam([u8; 32]),
    /// Rung-8 mutual static Ed25519 signed-DH TCP (`--host-key-file` + `--client-key-file`).
    #[cfg(feature = "identity")]
    Identity {
        client: astream_broker::IdentityKeypair,
        expected_host: [u8; 32],
    },
    /// Rung-9 mutual CA-certified SIGMA TCP (`--cert-file` + `--ca-key-file` + signer).
    #[cfg(feature = "identity")]
    Certified {
        signer: astream_broker::IdentitySigner,
        cert: Box<astream_broker::IdentityCertificate>,
        trust: astream_broker::CertTrustStore,
        expected_host_principal: Option<String>,
    },
}

struct Opts {
    endpoint: String,
    subject: String,
    cursor: Cursor,
    transport: Transport,
    caps: Vec<capfile::Line>,
    cols: u16,
    rows: u16,
    debounce: Duration,
    profile: Profile,
    meta: bool,
    once: bool,
    task_subject: Option<String>,
    task_producer: u64,
    task_seq_start: u64,
    hook_unix: Option<String>,
    hook_tcp: Option<String>,
    hook_format: WakeHookFormat,
}

/// Every diagnostic `aspump` puts on STDERR goes through here.
///
/// `eprintln!` PANICS on a stderr write error (a supervisor that closed both pipes,
/// `aspump ... 2>&1 | head -0`), turning a clean exit 2 or 1 into 101 with a
/// backtrace — outside the exit contract a supervisor classifies by ("2: bad
/// config, do not retry", "1: transient, retry"). So a diagnostic that cannot be
/// delivered is DROPPED: the exit status is the part that always survives.
fn warn(msg: &str) {
    let mut err = io::stderr().lock();
    let _ = err.write_all(msg.as_bytes());
    let _ = err.write_all(b"\n");
    let _ = err.flush();
}

fn usage_error(msg: &str) -> u8 {
    warn(&format!("aspump: {msg}\n{USAGE}"));
    2
}

// A flag's integer value, strictly: non-numeric or out of `lo..=hi` is a usage
// error (exit 2), never a silent fallback to the default.
fn num(flag: &str, v: &str, lo: u64, hi: u64) -> Result<u64, u8> {
    match v.parse::<u64>() {
        Ok(n) if (lo..=hi).contains(&n) => Ok(n),
        _ => {
            warn(&format!(
                "aspump: {flag}: expected an integer in {lo}..={hi}, got {v:?}"
            ));
            Err(2)
        }
    }
}

/// Decode one ASCII hex digit into its 4-bit value (`0..=15`).
#[cfg(feature = "aead")]
const fn hex_nibble(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some((b - b'a').saturating_add(10)),
        b'A'..=b'F' => Some((b - b'A').saturating_add(10)),
        _ => None,
    }
}

/// Decode exactly `out.len()` bytes of hex. Strict: ASCII hex digits only, exact
/// length. Byte-indexed, so a multibyte character cannot hit a char boundary.
#[cfg(feature = "aead")]
fn decode_hex(hex: &[u8], out: &mut [u8]) -> Result<(), String> {
    let Some(expected) = out.len().checked_mul(2) else {
        return Err("hex output length overflow".to_string());
    };
    if hex.len() != expected {
        return Err(format!(
            "expected {expected} hex chars ({} bytes), got {}",
            out.len(),
            hex.len()
        ));
    }
    for (i, (slot, pair)) in out
        .iter_mut()
        .zip(hex.as_chunks::<2>().0.iter())
        .enumerate()
    {
        match (hex_nibble(pair[0]), hex_nibble(pair[1])) {
            (Some(hi), Some(lo)) => *slot = (hi << 4) | lo,
            _ => return Err(format!("not valid hex at char {}", i.saturating_mul(2))),
        }
    }
    Ok(())
}

// Read the PSK from its file, decode it, and scrub the intermediate buffer.
// Whitespace around the hex (a trailing newline in a key file) is fine. The read
// is capped: a path that is not a key file (a device, a log) is refused, not read
// into memory whole.
#[cfg(feature = "aead")]
fn load_key(path: &str) -> Result<[u8; 32], u8> {
    const KEY_FILE_MAX: u64 = 4096;
    let mut raw = Vec::new();
    let read =
        std::fs::File::open(path).and_then(|f| f.take(KEY_FILE_MAX + 1).read_to_end(&mut raw));
    if let Err(e) = read {
        raw.fill(0);
        warn(&format!("aspump: --key-file {path}: {e}"));
        return Err(2);
    }
    if raw.len() as u64 > KEY_FILE_MAX {
        raw.fill(0);
        warn(&format!(
            "aspump: --key-file {path}: larger than {KEY_FILE_MAX} bytes; not a key file"
        ));
        return Err(2);
    }
    let mut key = [0u8; 32];
    let res = decode_hex(raw.trim_ascii(), &mut key);
    raw.fill(0);
    std::hint::black_box(&raw);
    if let Err(e) = res {
        warn(&format!("aspump: --key-file {path}: {e}"));
        return Err(2);
    }
    Ok(key)
}

#[cfg(feature = "identity")]
fn load_hex32_flag(flag: &str, path: &str) -> Result<[u8; 32], u8> {
    const KEY_FILE_MAX: u64 = 4096;
    let mut raw = Vec::new();
    let read =
        std::fs::File::open(path).and_then(|f| f.take(KEY_FILE_MAX + 1).read_to_end(&mut raw));
    if let Err(e) = read {
        raw.fill(0);
        warn(&format!("aspump: {flag} {path}: {e}"));
        return Err(2);
    }
    if raw.len() as u64 > KEY_FILE_MAX {
        raw.fill(0);
        warn(&format!(
            "aspump: {flag} {path}: larger than {KEY_FILE_MAX} bytes; not a key file"
        ));
        return Err(2);
    }
    let mut key = [0u8; 32];
    let res = decode_hex(raw.trim_ascii(), &mut key);
    raw.fill(0);
    std::hint::black_box(&raw);
    if let Err(e) = res {
        warn(&format!("aspump: {flag} {path}: {e}"));
        return Err(2);
    }
    Ok(key)
}

#[cfg(feature = "identity")]
fn load_ca_pubs(paths: &[String]) -> Result<Vec<[u8; 32]>, u8> {
    let mut cas = Vec::new();
    for path in paths {
        let text = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                warn(&format!("aspump: --ca-key-file {path}: {e}"));
                return Err(2);
            }
        };
        let mut line_no = 0usize;
        for line in text.lines() {
            line_no = line_no.saturating_add(1);
            let trimmed = line.trim_ascii();
            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }
            let mut pk = [0u8; 32];
            if let Err(e) = decode_hex(trimmed.as_bytes(), &mut pk) {
                return Err(usage_error(&format!("--ca-key-file {path}:{line_no}: {e}")));
            }
            cas.push(pk);
        }
    }
    if cas.is_empty() {
        return Err(usage_error("--ca-key-file holds no Ed25519 CA public keys"));
    }
    Ok(cas)
}

#[cfg(feature = "identity")]
fn load_cert_bytes(path: &str) -> Result<Vec<u8>, u8> {
    let bytes = match std::fs::read(path) {
        Ok(v) => v,
        Err(e) => {
            warn(&format!("aspump: --cert-file {path}: {e}"));
            return Err(2);
        }
    };
    if bytes.starts_with(b"ACRT") {
        return Ok(bytes);
    }
    let trimmed = bytes.trim_ascii();
    if trimmed.is_empty() || trimmed.len() % 2 != 0 || trimmed.len() > 8192 {
        return Err(usage_error(&format!(
            "--cert-file {path}: expected binary ACRT certificate or bounded even-length hex"
        )));
    }
    let out_len = trimmed.len() / 2;
    if out_len > 4096 {
        return Err(2);
    }
    let mut out = vec![0u8; out_len];
    if let Err(e) = decode_hex(trimmed, &mut out) {
        return Err(usage_error(&format!("--cert-file {path}: {e}")));
    }
    Ok(out)
}

fn load_caps(paths: &[String]) -> Result<Vec<capfile::Line>, u8> {
    let mut caps = Vec::new();
    for path in paths {
        match capfile::read_file(path) {
            Ok(ring) => caps.extend(ring),
            Err(e @ capfile::ReadError::Io { .. }) => {
                warn(&format!("aspump: --cap-file {e}"));
                return Err(2);
            }
            Err(capfile::ReadError::Malformed(m)) => {
                return Err(usage_error(&format!("--cap-file {m}")));
            }
        }
    }
    if !paths.is_empty() && !cfg!(feature = "cap") {
        return Err(usage_error(
            "--cap-file requires aspump built with `--features cap`",
        ));
    }
    Ok(caps)
}

fn parse(args: &[String]) -> Result<Opts, u8> {
    let mut pos: Vec<&String> = Vec::new();
    let (mut cols, mut rows, mut debounce) = (80u64, 24u64, 300u64);
    let (mut from, mut group, mut subject, mut key_file) = (None, None, None, None);
    let mut profile = Profile::common();
    let mut cap_files: Vec<String> = Vec::new();
    let mut tcp = false;
    let mut handshake_mode = false;
    let mut roam_mode = false;
    let mut host_key_file: Option<String> = None;
    let mut client_key_file: Option<String> = None;
    let mut cert_file: Option<String> = None;
    let mut ca_key_files: Vec<String> = Vec::new();
    let mut ssh_agent_sock: Option<String> = None;
    let mut host_principal: Option<String> = None;
    let mut meta = false;
    let mut once = false;
    let mut task_subject: Option<String> = None;
    let mut task_producer = 0x4153_5055_4D50_5451u64;
    let mut task_seq_start = 0u64;
    let mut hook_unix: Option<String> = None;
    let mut hook_tcp: Option<String> = None;
    let mut hook_format = WakeHookFormat::Line;
    let mut it = args.iter().skip(1);
    while let Some(a) = it.next() {
        match a.as_str() {
            "--tcp" => tcp = true,
            "--handshake" => handshake_mode = true,
            "--roam" => roam_mode = true,
            "--meta" => meta = true,
            "--once" => once = true,
            k if k == "--key" || k.starts_with("--key=") => {
                return Err(usage_error(
                    "--key HEX on argv is refused: the key would be visible to every local user via `ps` for the process's lifetime; pass it with --key-file PATH",
                ));
            }
            k if k == "--client-key" || k.starts_with("--client-key=") => {
                return Err(usage_error(
                    "--client-key HEX on argv is refused: secret seeds on argv are visible via `ps`; pass --client-key-file PATH",
                ));
            }
            k if k == "--cap-tag"
                || k.starts_with("--cap-tag=")
                || k == "--cap-filter"
                || k.starts_with("--cap-filter=") =>
            {
                let name = k.split('=').next().unwrap_or(k);
                return Err(usage_error(&format!(
                    "{name} on argv is refused: a capability tag is a secret and argv is visible via `ps`; pass `--cap-file PATH` (`<grant> <tag-hex>` lines)"
                )));
            }
            "--from" | "--cols" | "--rows" | "--debounce" | "--group" | "--subject"
            | "--profile" | "--key-file" | "--cap-file" | "--task-subject" | "--task-producer"
            | "--task-seq-start" | "--hook-unix" | "--hook-tcp" | "--hook-format"
            | "--host-key-file" | "--client-key-file" | "--cert-file" | "--ca-key-file"
            | "--ssh-agent-sock" | "--host-principal" => {
                // A value that is missing or itself a flag is a usage error.
                let v = match it.next() {
                    Some(v) if !v.starts_with("--") => v,
                    _ => {
                        warn(&format!("aspump: {a} expects a value"));
                        return Err(2);
                    }
                };
                match a.as_str() {
                    "--from" => from = Some(num(a, v, 0, u64::MAX)?),
                    "--cols" => cols = num(a, v, 1, u64::from(u16::MAX))?,
                    "--rows" => rows = num(a, v, 1, u64::from(u16::MAX))?,
                    "--debounce" => debounce = num(a, v, 1, u64::from(u32::MAX))?,
                    "--group" => group = Some(v.clone()),
                    "--subject" => subject = Some(v.clone()),
                    "--profile" => match Profile::by_name(v) {
                        Some(p) => profile = p,
                        None => {
                            return Err(usage_error(&format!(
                                "--profile: unknown profile {v:?}; expected common, claude, codex, repl, emacs, shell, or none"
                            )));
                        }
                    },
                    "--task-subject" => task_subject = Some(v.clone()),
                    "--task-producer" => task_producer = num(a, v, 1, u64::MAX)?,
                    "--task-seq-start" => {
                        task_seq_start = num(a, v, 0, u64::MAX.saturating_sub(1))?
                    }
                    "--hook-unix" => hook_unix = Some(v.clone()),
                    "--hook-tcp" => hook_tcp = Some(v.clone()),
                    "--hook-format" => match WakeHookFormat::by_name(v) {
                        Some(f) => hook_format = f,
                        None => {
                            return Err(usage_error(&format!(
                                "--hook-format: unknown format {v:?}; expected line, claude-notification, claude-stop, or codex-turn"
                            )));
                        }
                    },
                    "--host-key-file" => host_key_file = Some(v.clone()),
                    "--client-key-file" => client_key_file = Some(v.clone()),
                    "--cert-file" => cert_file = Some(v.clone()),
                    "--ca-key-file" => ca_key_files.push(v.clone()),
                    "--ssh-agent-sock" => ssh_agent_sock = Some(v.clone()),
                    "--host-principal" => host_principal = Some(v.clone()),
                    "--cap-file" => cap_files.push(v.clone()),
                    _ => key_file = Some(v.clone()),
                }
            }
            // Named without any `=value`: that value is never echoed, since it
            // may be a secret put on the wrong flag.
            flag if flag.starts_with("--") => {
                let name = flag.split('=').next().unwrap_or(flag);
                warn(&format!("aspump: unknown flag {name}\n{USAGE}"));
                return Err(2);
            }
            _ => pos.push(a),
        }
    }

    let Some(endpoint) = pos.first() else {
        return Err(usage_error("missing <endpoint>"));
    };
    // `<sid>` and `--subject` name the same thing two ways; accepting both would
    // silently pick one and tail a stream the caller did not ask for.
    let subject = match (pos.get(1), subject) {
        (Some(_), Some(_)) => {
            return Err(usage_error("<sid> and --subject are mutually exclusive"));
        }
        (Some(sid), None) => out_subject(sid),
        (None, Some(s)) => s,
        (None, None) => return Err(usage_error("missing <sid> (or --subject SUBJ)")),
    };
    // A surplus positional is a mistyped flag (`aspump sock sid 4711` for
    // `--from 4711`), and silently ignoring it would tail from 0 and re-print
    // every historical wake. Refuse it like a bad flag value.
    if let Some(extra) = pos.get(2) {
        return Err(usage_error(&format!("unexpected argument {extra:?}")));
    }
    let cursor = match (group, from) {
        (Some(_), Some(_)) => {
            return Err(usage_error(
                "--group resumes from the group's committed offset; it cannot be combined with --from",
            ));
        }
        (Some(g), None) => Cursor::Group(g),
        (None, f) => Cursor::From(f.unwrap_or(0)),
    };
    let caps = load_caps(&cap_files)?;
    let transport = build_transport(
        tcp,
        handshake_mode,
        roam_mode,
        key_file.as_deref(),
        host_key_file.as_deref(),
        client_key_file.as_deref(),
        cert_file.as_deref(),
        &ca_key_files,
        ssh_agent_sock.as_deref(),
        host_principal,
    )?;
    // Range-checked above: these narrowings cannot truncate.
    let cols = if cols <= u16::MAX as u64 {
        cols as u16
    } else {
        u16::MAX
    };
    let rows = if rows <= u16::MAX as u64 {
        rows as u16
    } else {
        u16::MAX
    };
    if !aspump_dim_in_range(cols) || !aspump_dim_in_range(rows) {
        return Err(2);
    }
    if hook_unix.is_some() && hook_tcp.is_some() {
        return Err(usage_error(
            "--hook-unix and --hook-tcp are mutually exclusive",
        ));
    }
    if hook_unix.is_some() && !cfg!(unix) {
        return Err(usage_error(
            "--hook-unix requires a unix host; use --hook-tcp",
        ));
    }
    Ok(Opts {
        endpoint: (*endpoint).clone(),
        subject,
        cursor,
        transport,
        caps,
        cols,
        rows,
        debounce: Duration::from_millis(debounce),
        profile,
        meta,
        once,
        task_subject,
        task_producer,
        task_seq_start,
        hook_unix,
        hook_tcp,
        hook_format,
    })
}

#[allow(clippy::too_many_arguments)]
fn build_transport(
    tcp: bool,
    handshake_mode: bool,
    roam_mode: bool,
    key_file: Option<&str>,
    host_key_file: Option<&str>,
    client_key_file: Option<&str>,
    cert_file: Option<&str>,
    ca_key_files: &[String],
    ssh_agent_sock: Option<&str>,
    host_principal: Option<String>,
) -> Result<Transport, u8> {
    if handshake_mode && roam_mode {
        return Err(usage_error("--handshake and --roam are mutually exclusive"));
    }
    if (handshake_mode || roam_mode) && key_file.is_none() {
        let f = if handshake_mode {
            "--handshake"
        } else {
            "--roam"
        };
        return Err(usage_error(&format!("{f} requires --key-file PATH")));
    }
    let has_cert_opts = cert_file.is_some()
        || !ca_key_files.is_empty()
        || ssh_agent_sock.is_some()
        || host_principal.is_some();
    if key_file.is_some() && (host_key_file.is_some() || client_key_file.is_some() || has_cert_opts)
    {
        return Err(usage_error(
            "--key-file cannot be combined with identity or certificate flags",
        ));
    }
    if host_key_file.is_some() && has_cert_opts {
        return Err(usage_error(
            "--host-key-file cannot be combined with --cert-file / --ca-key-file / --ssh-agent-sock",
        ));
    }
    if let Some(path) = key_file {
        if handshake_mode {
            return handshake_transport(path);
        }
        if roam_mode {
            return roam_transport(path);
        }
        return sealed_transport(path);
    }
    if let Some(hpath) = host_key_file {
        let Some(cpath) = client_key_file else {
            return Err(usage_error(
                "--host-key-file requires --client-key-file PATH",
            ));
        };
        return identity_transport(hpath, cpath);
    }
    if has_cert_opts {
        let Some(cpath) = cert_file else {
            return Err(usage_error(
                "--ca-key-file / --ssh-agent-sock / --host-principal require --cert-file PATH",
            ));
        };
        if ca_key_files.is_empty() {
            return Err(usage_error("--cert-file requires --ca-key-file PATH"));
        }
        if client_key_file.is_some() == ssh_agent_sock.is_some() {
            return Err(usage_error(
                "--cert-file requires exactly one of --client-key-file PATH or --ssh-agent-sock PATH",
            ));
        }
        return certified_transport(
            cpath,
            ca_key_files,
            client_key_file,
            ssh_agent_sock,
            host_principal,
        );
    }
    if client_key_file.is_some() {
        return Err(usage_error(
            "--client-key-file requires --host-key-file PATH or --cert-file PATH",
        ));
    }
    if tcp {
        Ok(Transport::Tcp)
    } else {
        Ok(Transport::Unix)
    }
}

#[cfg(feature = "aead")]
fn sealed_transport(path: &str) -> Result<Transport, u8> {
    Ok(Transport::Sealed(load_key(path)?))
}
#[cfg(not(feature = "aead"))]
fn sealed_transport(_path: &str) -> Result<Transport, u8> {
    Err(usage_error(
        "--key-file requires aspump built with `--features aead`",
    ))
}

#[cfg(feature = "handshake")]
fn handshake_transport(path: &str) -> Result<Transport, u8> {
    Ok(Transport::Handshake(load_key(path)?))
}
#[cfg(not(feature = "handshake"))]
fn handshake_transport(_path: &str) -> Result<Transport, u8> {
    Err(usage_error(
        "--handshake requires aspump built with `--features handshake`",
    ))
}

#[cfg(feature = "handshake")]
fn roam_transport(path: &str) -> Result<Transport, u8> {
    Ok(Transport::Roam(load_key(path)?))
}
#[cfg(not(feature = "handshake"))]
fn roam_transport(_path: &str) -> Result<Transport, u8> {
    Err(usage_error(
        "--roam requires aspump built with `--features handshake`",
    ))
}

#[cfg(feature = "identity")]
fn identity_transport(host_path: &str, client_path: &str) -> Result<Transport, u8> {
    let expected_host = load_hex32_flag("--host-key-file", host_path)?;
    let seed = load_hex32_flag("--client-key-file", client_path)?;
    Ok(Transport::Identity {
        client: astream_broker::IdentityKeypair::from_seed(seed),
        expected_host,
    })
}
#[cfg(not(feature = "identity"))]
fn identity_transport(_host_path: &str, _client_path: &str) -> Result<Transport, u8> {
    Err(usage_error(
        "--host-key-file / --client-key-file require aspump built with `--features identity`",
    ))
}

#[cfg(feature = "identity")]
fn certified_transport(
    cert_path: &str,
    ca_paths: &[String],
    client_key_path: Option<&str>,
    ssh_agent_sock: Option<&str>,
    expected_host_principal: Option<String>,
) -> Result<Transport, u8> {
    let cert_bytes = load_cert_bytes(cert_path)?;
    let cert = match astream_broker::IdentityCertificate::decode(&cert_bytes) {
        Ok(c) => c,
        Err(e) => return Err(usage_error(&format!("--cert-file {cert_path}: {e}"))),
    };
    let ca_pubs = load_ca_pubs(ca_paths)?;
    let trust = match astream_broker::CertTrustStore::new(ca_pubs, 30 * 86_400_000) {
        Ok(t) => t,
        Err(e) => return Err(usage_error(&format!("--ca-key-file: {e}"))),
    };
    let signer = if let Some(cpath) = client_key_path {
        let seed = load_hex32_flag("--client-key-file", cpath)?;
        let kp = astream_broker::IdentityKeypair::from_seed(seed);
        if kp.public() != cert.subject_pub() {
            return Err(usage_error(
                "--client-key-file public key does not match --cert-file subject_pub",
            ));
        }
        astream_broker::IdentitySigner::from(kp)
    } else if let Some(sock) = ssh_agent_sock {
        if !cfg!(unix) {
            return Err(usage_error("--ssh-agent-sock requires a unix host"));
        }
        match astream_broker::SshAgentSigner::connect_for_key(sock, cert.subject_pub()) {
            Ok(ag) => astream_broker::IdentitySigner::from(ag),
            Err(e) => {
                warn(&format!("aspump: --ssh-agent-sock {sock}: {e}"));
                return Err(1);
            }
        }
    } else {
        return Err(2);
    };
    Ok(Transport::Certified {
        signer,
        cert: Box::new(cert),
        trust,
        expected_host_principal,
    })
}
#[cfg(not(feature = "identity"))]
fn certified_transport(
    _cert_path: &str,
    _ca_paths: &[String],
    _client_key_path: Option<&str>,
    _ssh_agent_sock: Option<&str>,
    _expected_host_principal: Option<String>,
) -> Result<Transport, u8> {
    Err(usage_error(
        "--cert-file requires aspump built with `--features identity`",
    ))
}

// One byte-stream type for every transport, so the pump has ONE code path. The
// worker thread owns the subscription, so the stream must be `Send`.
trait Stream: Read + Write + Send {}
impl<T: Read + Write + Send> Stream for T {}
type AnyClient = Client<Box<dyn Stream>>;

#[cfg(feature = "aead")]
fn connect_sealed(ep: &str, key: &[u8; 32]) -> io::Result<AnyClient> {
    Ok(Client::from_stream(Box::new(
        Client::connect_tcp_sealed(ep, *key)?.into_stream(),
    )))
}

#[cfg(feature = "handshake")]
fn connect_handshake(ep: &str, psk: &[u8; 32]) -> io::Result<AnyClient> {
    Ok(Client::from_stream(Box::new(
        Client::connect_tcp_handshake(ep, *psk)?.into_stream(),
    )))
}

#[cfg(feature = "handshake")]
fn connect_roam(ep: &str, psk: &[u8; 32]) -> io::Result<AnyClient> {
    let (c, _roam) = Client::connect_udp_roaming(ep, *psk)?;
    Ok(Client::from_stream(Box::new(c.into_stream())))
}

#[cfg(feature = "identity")]
fn connect_identity(
    ep: &str,
    client: &astream_broker::IdentityKeypair,
    expected_host: &[u8; 32],
) -> io::Result<AnyClient> {
    Ok(Client::from_stream(Box::new(
        Client::connect_tcp_identity(ep, client.clone(), *expected_host)?.into_stream(),
    )))
}

#[cfg(feature = "identity")]
fn connect_certified(
    ep: &str,
    signer: &astream_broker::IdentitySigner,
    cert: &astream_broker::IdentityCertificate,
    trust: &astream_broker::CertTrustStore,
    expected_host_principal: Option<&str>,
) -> io::Result<AnyClient> {
    Ok(Client::from_stream(Box::new(
        Client::connect_tcp_certified(
            ep,
            signer.clone(),
            cert.clone(),
            trust,
            expected_host_principal,
        )?
        .into_stream(),
    )))
}

fn connect(t: &Transport, ep: &str) -> Result<AnyClient, u8> {
    let res: io::Result<AnyClient> = match t {
        #[cfg(unix)]
        Transport::Unix => match Client::connect(ep) {
            Ok(c) => Ok(Client::from_stream(
                Box::new(c.into_stream()) as Box<dyn Stream>
            )),
            Err(e) => Err(e),
        },
        #[cfg(not(unix))]
        Transport::Unix => {
            return Err(usage_error(
                "Unix-socket endpoints need a unix host; use --tcp",
            ));
        }
        Transport::Tcp => match Client::connect_tcp(ep) {
            Ok(c) => Ok(Client::from_stream(
                Box::new(c.into_stream()) as Box<dyn Stream>
            )),
            Err(e) => Err(e),
        },
        #[cfg(feature = "aead")]
        Transport::Sealed(key) => connect_sealed(ep, key),
        #[cfg(feature = "handshake")]
        Transport::Handshake(psk) => connect_handshake(ep, psk),
        #[cfg(feature = "handshake")]
        Transport::Roam(psk) => connect_roam(ep, psk),
        #[cfg(feature = "identity")]
        Transport::Identity {
            client,
            expected_host,
        } => connect_identity(ep, client, expected_host),
        #[cfg(feature = "identity")]
        Transport::Certified {
            signer,
            cert,
            trust,
            expected_host_principal,
        } => connect_certified(ep, signer, cert, trust, expected_host_principal.as_deref()),
    };
    match res {
        Ok(c) => Ok(c),
        Err(e) => {
            warn(&format!("aspump: connect {ep}: {e}"));
            Err(1)
        }
    }
}

fn connect_or_exit(t: &Transport, ep: &str, caps: &[capfile::Line]) -> Result<AnyClient, u8> {
    let mut c = connect(t, ep)?;
    for cap in caps {
        if let Err(e) = c.attach(&cap.grant, &cap.tag) {
            warn(&format!("aspump: attach {:?}: {e}", cap.grant));
            return Err(1);
        }
    }
    Ok(c)
}

// Print one wake line and flush it. A write error ends the pump: a broken pipe
// (the reader of the wake lines went away) is a clean end, exit 0 — never a
// subscription held open writing wakes nobody can read; anything else is
// reported, exit 1. A stdout that was already CLOSED at launch is invisible to
// this function — `std` reports EBADF on fd 1 as a successful write — which is
// the documented limit at the top of this file, not a case a write error catches.
fn emit(out: &mut io::StdoutLock<'_>, s: &str) -> Result<(), u8> {
    let res = out
        .write_all(s.as_bytes())
        .and_then(|()| out.write_all(b"\n"))
        .and_then(|()| out.flush());
    if let Err(e) = res {
        if e.kind() == io::ErrorKind::BrokenPipe {
            return Err(0);
        }
        warn(&format!("aspump: stdout: {e}"));
        return Err(1);
    }
    Ok(())
}

// Advance the durable cursor over the one delivery whose wakes are now ALL out.
// Held rather than issued at delivery time because the settle wakes (`QUIESCED`,
// and the glyph `PROMPT_READY` for a target with no shell integration) are fired
// by the debounce timer at that delivery's offset, AFTER it was delivered: they
// live in the classifier's screen state, not in any record, so a cursor already
// past that record loses the boundary for good instead of re-delivering it. A
// commit failure is fatal — a cursor that silently stopped advancing would replay
// the same history on every restart.
fn commit_wakes_through(
    commits: &mut Option<AnyClient>,
    cursor: &Cursor,
    pending: &mut Option<u64>,
) -> Result<(), u8> {
    let (Some(c), Cursor::Group(g), Some(offset)) = (commits.as_mut(), cursor, *pending) else {
        return Ok(());
    };
    if let Err(e) = c.commit(g, offset) {
        warn(&format!("aspump: commit {g} upto {offset}: {e}"));
        return Err(1);
    }
    *pending = None;
    Ok(())
}

// Deliveries the worker may read ahead of the main thread. Bounded, so a reader
// that stops draining stdout blocks the main thread, then the worker, then the
// broker socket, instead of the pump queueing the stream in memory (a record can
// be up to 16 MiB, so this caps the read-ahead at a few of them).
const READ_AHEAD: usize = 8;

// What the worker forwards from the broker: each delivery or retention gap notice,
// then exactly one terminal message — the broker closed the stream, or an error.
enum Msg {
    Delivery(u64, Vec<u8>),
    Gap(Gap),
    Eof,
    Error(io::Error),
}

fn format_wake(
    ev: &SessionEvent,
    boffset: u64,
    meta: bool,
    classifier: &EventClassifier,
) -> String {
    if meta {
        wake_line_with_meta(ev, boffset, classifier.cwd(), classifier.title())
    } else {
        wake_line(ev, boffset)
    }
}

fn dispatch_wake_adapters(
    opts: &Opts,
    task_client: &mut Option<AnyClient>,
    task_queue: &mut WakeTaskQueue,
    boffset: u64,
    line: &str,
) -> Result<(), u8> {
    let item = if let Some(ref tc) = task_client {
        let _ = tc;
        let Some(c) = task_client.as_mut() else {
            return Err(1);
        };
        match task_queue.publish_wake(c, boffset, &opts.subject, line) {
            Ok((it, _, _)) => Some(it),
            Err(e) => {
                warn(&format!("aspump: task-subject publish: {e}"));
                return Err(1);
            }
        }
    } else if opts.hook_unix.is_some() || opts.hook_tcp.is_some() {
        Some(task_queue.next_item(boffset, &opts.subject, line))
    } else {
        None
    };

    if let Some(ref it) = item {
        #[cfg(unix)]
        if let Some(ref sock_path) = opts.hook_unix {
            if let Err(e) = astream_pump::deliver_hook_unix(
                std::path::Path::new(sock_path),
                opts.hook_format,
                it,
            ) {
                warn(&format!("aspump: hook-unix {sock_path}: {e}"));
                return Err(1);
            }
            task_queue.mark_acked(it.wake_seq);
        }
        if let Some(ref addr) = opts.hook_tcp {
            if let Err(e) = deliver_hook_tcp(addr, opts.hook_format, it) {
                warn(&format!("aspump: hook-tcp {addr}: {e}"));
                return Err(1);
            }
            task_queue.mark_acked(it.wake_seq);
        }
    }
    Ok(())
}

fn run() -> Result<(), u8> {
    // `args_os`, NOT `args`: `std::env::args()` PANICS (exit 101) on an argument
    // that is not valid Unicode — a plausible `--key-file` path — where the exit
    // contract calls a malformed argument a usage error (2).
    let mut args = Vec::new();
    for a in std::env::args_os() {
        match a.into_string() {
            Ok(s) => args.push(s),
            Err(bad) => {
                return Err(usage_error(&format!(
                    "argument is not valid UTF-8: {bad:?}"
                )));
            }
        }
    }
    // Only lone top-level informational flags bypass connection setup. Mixed
    // commands and malformed arguments retain the ordinary usage-error path.
    if let [_, flag] = args.as_slice() {
        let text = match flag.as_str() {
            "--help" => Some(USAGE),
            "--version" => Some(concat!("aspump ", env!("CARGO_PKG_VERSION"))),
            _ => None,
        };
        if let Some(text) = text {
            let mut out = io::stdout().lock();
            if let Err(error) = writeln!(out, "{text}").and_then(|()| out.flush()) {
                warn(&format!("aspump: stdout: {error}"));
                return Err(1);
            }
            return Ok(());
        }
    }
    let opts = parse(&args)?;

    let client = connect_or_exit(&opts.transport, &opts.endpoint, &opts.caps)?;
    // The durable cursor needs a SECOND connection: a group subscription's own
    // connection becomes a one-way delivery stream the broker never reads again.
    let mut commits = match &opts.cursor {
        Cursor::Group(_) => Some(connect_or_exit(
            &opts.transport,
            &opts.endpoint,
            &opts.caps,
        )?),
        Cursor::From(_) => None,
    };
    let mut task_client = match &opts.task_subject {
        Some(_) => Some(connect_or_exit(
            &opts.transport,
            &opts.endpoint,
            &opts.caps,
        )?),
        None => None,
    };
    let mut task_queue = WakeTaskQueue::new(
        opts.task_subject.clone().unwrap_or_default(),
        opts.task_producer,
        opts.task_seq_start,
    );
    // `last_offset` tags the QUIESCED/glyph wakes the debounce timer fires. Until
    // the first delivery it is the attach point: `--from`, or 0 for a group, whose
    // real resume point is the broker's to know.
    let (sub, mut last_offset) = match &opts.cursor {
        Cursor::From(n) => (client.subscribe(*n, &opts.subject), *n),
        Cursor::Group(g) => (client.subscribe_group(g, &opts.subject), 0),
    };
    let sub = match sub {
        Ok(s) => s,
        Err(e) => {
            warn(&format!("aspump: subscribe: {e}"));
            return Err(1);
        }
    };

    // Worker: block on the broker and forward each raw delivery to main, so main's
    // recv_timeout can fire the debounce without a broker-side read timeout. The
    // broker never acks a Subscribe — a rejection (bad filter, capability denied)
    // arrives as the FIRST recv result, as an Err — so every outcome is forwarded,
    // never collapsed into a silent end of stream.
    let (tx, rx) = mpsc::sync_channel::<Msg>(READ_AHEAD);
    thread::spawn(move || {
        let mut sub = sub;
        loop {
            let msg = match sub.recv_event() {
                Ok(Some(Event::Mark { .. })) => continue,
                Ok(Some(Event::Gap(gap))) => Msg::Gap(gap),
                Ok(Some(Event::Delivery { offset, body, .. })) => Msg::Delivery(offset, body),
                Ok(None) => Msg::Eof,
                Err(e) => Msg::Error(e),
            };
            let terminal = !matches!(msg, Msg::Delivery(..) | Msg::Gap(..));
            if tx.send(msg).is_err() || terminal {
                break;
            }
        }
    });

    let mut classifier = EventClassifier::new(opts.cols, opts.rows, opts.profile.clone());
    let mut quiesced = false;
    let mut sync_hold_ticks: u8 = 0;
    // The one delivery whose durable commit is held until its settle window closes.
    let mut pending: Option<u64> = None;
    let mut out = io::stdout().lock();
    loop {
        // Once the settle wakes are out (and any held commit released), there is
        // nothing left to time: block for the next message rather than waking
        // every debounce period for as long as the target stays idle.
        let next = if quiesced {
            match rx.recv() {
                Ok(m) => Ok(m),
                Err(mpsc::RecvError) => Err(mpsc::RecvTimeoutError::Disconnected),
            }
        } else {
            rx.recv_timeout(opts.debounce)
        };
        match next {
            Ok(Msg::Delivery(offset, body)) => {
                // New output closes the PREVIOUS delivery's settle window — the
                // debounce can no longer fire a wake at that older offset — so its
                // held commit is released here. At most one delivery is ever
                // uncommitted, and only ever one whose wakes are all flushed.
                commit_wakes_through(&mut commits, &opts.cursor, &mut pending)?;
                quiesced = false;
                sync_hold_ticks = 0;
                last_offset = aspump_commit_offset_advance(last_offset, offset);
                let wakes = classifier.push(&Record::Out(body));
                for ev in &wakes {
                    let line = format_wake(ev, last_offset, opts.meta, &classifier);
                    dispatch_wake_adapters(
                        &opts,
                        &mut task_client,
                        &mut task_queue,
                        last_offset,
                        &line,
                    )?;
                    emit(&mut out, &line)?;
                    if opts.once {
                        pending = Some(offset);
                        commit_wakes_through(&mut commits, &opts.cursor, &mut pending)?;
                        return Ok(());
                    }
                }
                // This delivery's own commit waits: the settle wakes it may still
                // produce are printed at ITS offset by the timeout arm below.
                pending = Some(offset);
            }
            // Retention gave up matching records below this subscription's cursor
            // (`REQUIREMENTS-fabric-operations` R4, addendum A9): report it on stderr
            // before any post-gap wake on stdout, and clear any mid-sequence VT/OSC
            // escape left over from pre-gap output so it cannot forge a wake or swallow
            // post-gap prompt glyphs.
            Ok(Msg::Gap(gap)) => {
                warn(&gap_line(&gap));
                classifier.reset_escape();
                sync_hold_ticks = 0;
            }
            // The broker closed the stream (shutdown): a clean end. The held commit
            // stays held — the last burst's settle wake never fired, so a
            // replacement pump must be re-delivered that record rather than resume
            // past a boundary no reader ever saw.
            Ok(Msg::Eof) => break,
            Ok(Msg::Error(e)) => {
                warn(&format!("aspump: {e}"));
                return Err(1);
            }
            // Idle for the debounce window: unless the target is mid-redraw inside DEC
            // `?2026` synchronized output (within `MAX_SYNC_HOLD_TICKS` and
            // `MAX_SYNC_OUTPUT_BYTES`), the screen has settled. Emit the quiescence
            // wakes ONCE per idle period (until new output resets it).
            Err(mpsc::RecvTimeoutError::Timeout) => {
                if !quiesced {
                    if classifier.in_sync_update() && sync_hold_ticks < MAX_SYNC_HOLD_TICKS {
                        sync_hold_ticks = sync_hold_ticks_clamp(
                            (sync_hold_ticks as u64).saturating_add(1),
                            MAX_SYNC_HOLD_TICKS as u64,
                        ) as u8;
                        continue;
                    }
                    quiesced = true;
                    sync_hold_ticks = 0;
                    let wakes = classifier.quiesce();
                    for ev in &wakes {
                        let line = format_wake(ev, last_offset, opts.meta, &classifier);
                        dispatch_wake_adapters(
                            &opts,
                            &mut task_client,
                            &mut task_queue,
                            last_offset,
                            &line,
                        )?;
                        emit(&mut out, &line)?;
                        if opts.once {
                            commit_wakes_through(&mut commits, &opts.cursor, &mut pending)?;
                            return Ok(());
                        }
                    }
                }
                // Every wake the last delivery could produce is now out — its marks
                // when it arrived, its settle wakes just above — so the cursor may
                // finally pass it.
                commit_wakes_through(&mut commits, &opts.cursor, &mut pending)?;
            }
            // The worker always sends Eof/Error before it exits; this is a crash.
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                warn("aspump: delivery thread ended unexpectedly");
                return Err(1);
            }
        }
    }
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(code) => ExitCode::from(code),
    }
}
