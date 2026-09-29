//! `aspump` — tail a target session's `/out` off the bus and print the semantic
//! WAKE lines a driving agent acts on, one per line. The shell face of
//! [`astream_pump`]: a bridge or an agent runner reads these lines instead of
//! polling the raw byte stream, and reacts only on a real boundary.
//!
//! ```text
//! aspump <endpoint> [<sid>] [--subject SUBJ] [--from N | --group G]
//!        [--cols C] [--rows R] [--debounce MS] [--tcp] [--key-file PATH]
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
//! Exit status: `0` when the broker closes the stream or the reader of stdout
//! goes away (a broken pipe ends the pump instead of leaving it holding a
//! subscription); `1` on a connect, delivery, commit, or broker-side error (the
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
//! There is no `--cap` face: against a broker with `cap` enforcement on, the
//! subscription is refused and aspump exits 1 with the broker's reason on
//! stderr. A closed (as opposed to broken) stdout is also not detectable —
//! `std` reports EBADF on fd 1 as a successful write — so a pump launched with
//! fd 1 closed keeps its subscription; a broken pipe does end it (exit 0).
#![forbid(unsafe_code)]

use astream_broker::Client;
use astream_pump::{out_subject, wake_line};
use astream_term::events::{EventClassifier, Profile};
use astream_term::record::Record;
use std::io::{self, Read, Write};
use std::process::exit;
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

const USAGE: &str = "usage: aspump <endpoint> [<sid>] [--subject SUBJ] [--from N | --group G] [--cols C] [--rows R] [--debounce MS] [--tcp] [--key-file PATH]
  <sid> tails the built face /a/stream/term/<sid>/out; --subject tails any subject (exactly one of the two)
  --from N is a client-held cursor and INCLUSIVE; --group G is the broker-durable cursor (they are exclusive)
  --key-file PATH: 64 hex chars (32-byte PSK) for the sealed TCP transport; needs aspump built --features aead";

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
}

struct Opts {
    endpoint: String,
    subject: String,
    cursor: Cursor,
    transport: Transport,
    cols: u16,
    rows: u16,
    debounce: Duration,
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

fn usage_error(msg: &str) -> ! {
    warn(&format!("aspump: {msg}\n{USAGE}"));
    exit(2);
}

// A flag's integer value, strictly: non-numeric or out of `lo..=hi` is a usage
// error (exit 2), never a silent fallback to the default.
fn num(flag: &str, v: &str, lo: u64, hi: u64) -> u64 {
    match v.parse::<u64>() {
        Ok(n) if (lo..=hi).contains(&n) => n,
        _ => {
            warn(&format!(
                "aspump: {flag}: expected an integer in {lo}..={hi}, got {v:?}"
            ));
            exit(2);
        }
    }
}

/// Decode exactly `out.len()` bytes of hex. Strict: ASCII hex digits only, exact
/// length. Byte-indexed, so a multibyte character cannot hit a char boundary.
#[cfg(feature = "aead")]
fn decode_hex(hex: &[u8], out: &mut [u8]) -> Result<(), String> {
    if hex.len() != out.len() * 2 {
        return Err(format!(
            "expected {} hex chars ({} bytes), got {}",
            out.len() * 2,
            out.len(),
            hex.len()
        ));
    }
    fn nibble(b: u8) -> Option<u8> {
        match b {
            b'0'..=b'9' => Some(b - b'0'),
            b'a'..=b'f' => Some(b - b'a' + 10),
            b'A'..=b'F' => Some(b - b'A' + 10),
            _ => None,
        }
    }
    for (i, pair) in hex.chunks_exact(2).enumerate() {
        match (nibble(pair[0]), nibble(pair[1])) {
            (Some(hi), Some(lo)) => out[i] = (hi << 4) | lo,
            _ => return Err(format!("not valid hex at char {}", i * 2)),
        }
    }
    Ok(())
}

// Read the PSK from its file, decode it, and scrub the intermediate buffer.
// Whitespace around the hex (a trailing newline in a key file) is fine. The read
// is capped: a path that is not a key file (a device, a log) is refused, not read
// into memory whole.
#[cfg(feature = "aead")]
fn load_key(path: &str) -> [u8; 32] {
    const KEY_FILE_MAX: u64 = 4096;
    let mut raw = Vec::new();
    let read =
        std::fs::File::open(path).and_then(|f| f.take(KEY_FILE_MAX + 1).read_to_end(&mut raw));
    if let Err(e) = read {
        raw.fill(0);
        warn(&format!("aspump: --key-file {path}: {e}"));
        exit(2);
    }
    if raw.len() as u64 > KEY_FILE_MAX {
        raw.fill(0);
        warn(&format!(
            "aspump: --key-file {path}: larger than {KEY_FILE_MAX} bytes; not a key file"
        ));
        exit(2);
    }
    let mut key = [0u8; 32];
    let res = decode_hex(raw.trim_ascii(), &mut key);
    raw.fill(0);
    std::hint::black_box(&raw);
    if let Err(e) = res {
        warn(&format!("aspump: --key-file {path}: {e}"));
        exit(2);
    }
    key
}

fn parse(args: &[String]) -> Opts {
    let mut pos: Vec<&String> = Vec::new();
    let (mut cols, mut rows, mut debounce) = (80u64, 24u64, 300u64);
    let (mut from, mut group, mut subject, mut key_file) = (None, None, None, None);
    let mut tcp = false;
    let mut it = args.iter().skip(1);
    while let Some(a) = it.next() {
        match a.as_str() {
            "--tcp" => tcp = true,
            k if k == "--key" || k.starts_with("--key=") => usage_error(
                "--key HEX on argv is refused: the key would be visible to every local user via `ps` for the process's lifetime; pass it with --key-file PATH",
            ),
            "--from" | "--cols" | "--rows" | "--debounce" | "--group" | "--subject"
            | "--key-file" => {
                // A value that is missing or itself a flag is a usage error.
                let v = match it.next() {
                    Some(v) if !v.starts_with("--") => v,
                    _ => {
                        warn(&format!("aspump: {a} expects a value"));
                        exit(2);
                    }
                };
                match a.as_str() {
                    "--from" => from = Some(num(a, v, 0, u64::MAX)),
                    "--cols" => cols = num(a, v, 1, u64::from(u16::MAX)),
                    "--rows" => rows = num(a, v, 1, u64::from(u16::MAX)),
                    "--debounce" => debounce = num(a, v, 1, u64::from(u32::MAX)),
                    "--group" => group = Some(v.clone()),
                    "--subject" => subject = Some(v.clone()),
                    _ => key_file = Some(v.clone()),
                }
            }
            // Named without any `=value`: that value is never echoed, since it
            // may be a secret put on the wrong flag.
            flag if flag.starts_with("--") => {
                let name = flag.split('=').next().unwrap_or(flag);
                warn(&format!("aspump: unknown flag {name}\n{USAGE}"));
                exit(2);
            }
            _ => pos.push(a),
        }
    }

    let Some(endpoint) = pos.first() else {
        usage_error("missing <endpoint>");
    };
    // `<sid>` and `--subject` name the same thing two ways; accepting both would
    // silently pick one and tail a stream the caller did not ask for.
    let subject = match (pos.get(1), subject) {
        (Some(_), Some(_)) => usage_error("<sid> and --subject are mutually exclusive"),
        (Some(sid), None) => out_subject(sid),
        (None, Some(s)) => s,
        (None, None) => usage_error("missing <sid> (or --subject SUBJ)"),
    };
    // A surplus positional is a mistyped flag (`aspump sock sid 4711` for
    // `--from 4711`), and silently ignoring it would tail from 0 and re-print
    // every historical wake. Refuse it like a bad flag value.
    if let Some(extra) = pos.get(2) {
        usage_error(&format!("unexpected argument {extra:?}"));
    }
    let cursor = match (group, from) {
        (Some(_), Some(_)) => usage_error(
            "--group resumes from the group's committed offset; it cannot be combined with --from",
        ),
        (Some(g), None) => Cursor::Group(g),
        (None, f) => Cursor::From(f.unwrap_or(0)),
    };
    // A key implies TCP (sealing a local Unix socket is pointless); `--tcp` alone
    // is plaintext, for a trusted network.
    let transport = match key_file {
        Some(path) => sealed_transport(&path),
        None if tcp => Transport::Tcp,
        None => Transport::Unix,
    };
    // Range-checked above: these narrowings cannot truncate.
    let cols = u16::try_from(cols).unwrap_or(u16::MAX);
    let rows = u16::try_from(rows).unwrap_or(u16::MAX);
    Opts {
        endpoint: (*endpoint).clone(),
        subject,
        cursor,
        transport,
        cols,
        rows,
        debounce: Duration::from_millis(debounce),
    }
}

// The sealed transport is gated on the `aead` feature. Built WITHOUT it, aspump
// stays zero-third-party and `--key-file` is a usage error refused BEFORE the key
// file is even read — never a silent plaintext downgrade.
#[cfg(feature = "aead")]
fn sealed_transport(path: &str) -> Transport {
    Transport::Sealed(load_key(path))
}
#[cfg(not(feature = "aead"))]
fn sealed_transport(_path: &str) -> Transport {
    usage_error("--key-file requires aspump built with `--features aead`");
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

fn connect(t: &Transport, ep: &str) -> io::Result<AnyClient> {
    Ok(match t {
        #[cfg(unix)]
        Transport::Unix => Client::from_stream(Box::new(Client::connect(ep)?.into_stream())),
        #[cfg(not(unix))]
        Transport::Unix => usage_error("Unix-socket endpoints need a unix host; use --tcp"),
        Transport::Tcp => Client::from_stream(Box::new(Client::connect_tcp(ep)?.into_stream())),
        #[cfg(feature = "aead")]
        Transport::Sealed(key) => connect_sealed(ep, key)?,
    })
}

fn connect_or_exit(t: &Transport, ep: &str) -> AnyClient {
    connect(t, ep).unwrap_or_else(|e| {
        warn(&format!("aspump: connect {ep}: {e}"));
        exit(1);
    })
}

// Print one wake line and flush it. A write error ends the pump: a broken pipe
// (the reader of the wake lines went away) is a clean end, exit 0 — never a
// subscription held open writing wakes nobody can read; anything else is
// reported, exit 1. A stdout that was already CLOSED at launch is invisible to
// this function — `std` reports EBADF on fd 1 as a successful write — which is
// the documented limit at the top of this file, not a case a write error catches.
fn emit(out: &mut impl Write, s: &str) {
    if let Err(e) = writeln!(out, "{s}").and_then(|()| out.flush()) {
        if e.kind() == io::ErrorKind::BrokenPipe {
            exit(0);
        }
        warn(&format!("aspump: stdout: {e}"));
        exit(1);
    }
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
) {
    let (Some(c), Cursor::Group(g), Some(offset)) = (commits.as_mut(), cursor, *pending) else {
        return;
    };
    if let Err(e) = c.commit(g, offset) {
        warn(&format!("aspump: commit {g} upto {offset}: {e}"));
        exit(1);
    }
    *pending = None;
}

// Deliveries the worker may read ahead of the main thread. Bounded, so a reader
// that stops draining stdout blocks the main thread, then the worker, then the
// broker socket, instead of the pump queueing the stream in memory (a record can
// be up to 16 MiB, so this caps the read-ahead at a few of them).
const READ_AHEAD: usize = 8;

// What the worker forwards from the broker: each delivery, then exactly one
// terminal message — the broker closed the stream, or a delivery/broker error.
enum Msg {
    Delivery(u64, Vec<u8>),
    Eof,
    Error(io::Error),
}

fn main() {
    // `args_os`, NOT `args`: `std::env::args()` PANICS (exit 101) on an argument
    // that is not valid Unicode — a plausible `--key-file` path — where the exit
    // contract calls a malformed argument a usage error (2).
    let args: Vec<String> = std::env::args_os()
        .map(|a| {
            a.into_string()
                .unwrap_or_else(|bad| usage_error(&format!("argument is not valid UTF-8: {bad:?}")))
        })
        .collect();
    let opts = parse(&args);

    let client = connect_or_exit(&opts.transport, &opts.endpoint);
    // The durable cursor needs a SECOND connection: a group subscription's own
    // connection becomes a one-way delivery stream the broker never reads again.
    let mut commits = match &opts.cursor {
        Cursor::Group(_) => Some(connect_or_exit(&opts.transport, &opts.endpoint)),
        Cursor::From(_) => None,
    };
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
            exit(1);
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
            let msg = match sub.recv() {
                Ok(Some((offset, _subject, body))) => Msg::Delivery(offset, body),
                Ok(None) => Msg::Eof,
                Err(e) => Msg::Error(e),
            };
            let terminal = !matches!(msg, Msg::Delivery(..));
            if tx.send(msg).is_err() || terminal {
                break;
            }
        }
    });

    let mut classifier = EventClassifier::new(opts.cols, opts.rows, Profile::common());
    let mut quiesced = false;
    // The one delivery whose durable commit is held until its settle window closes.
    let mut pending: Option<u64> = None;
    let mut out = io::stdout().lock();
    loop {
        // Once the settle wakes are out (and any held commit released), there is
        // nothing left to time: block for the next message rather than waking
        // every debounce period for as long as the target stays idle.
        let next = if quiesced {
            rx.recv()
                .map_err(|mpsc::RecvError| mpsc::RecvTimeoutError::Disconnected)
        } else {
            rx.recv_timeout(opts.debounce)
        };
        match next {
            Ok(Msg::Delivery(offset, body)) => {
                // New output closes the PREVIOUS delivery's settle window — the
                // debounce can no longer fire a wake at that older offset — so its
                // held commit is released here. At most one delivery is ever
                // uncommitted, and only ever one whose wakes are all flushed.
                commit_wakes_through(&mut commits, &opts.cursor, &mut pending);
                quiesced = false;
                last_offset = offset;
                for ev in classifier.push(&Record::Out(body)) {
                    emit(&mut out, &wake_line(&ev, last_offset));
                }
                // This delivery's own commit waits: the settle wakes it may still
                // produce are printed at ITS offset by the timeout arm below.
                pending = Some(offset);
            }
            // The broker closed the stream (shutdown): a clean end. The held commit
            // stays held — the last burst's settle wake never fired, so a
            // replacement pump must be re-delivered that record rather than resume
            // past a boundary no reader ever saw.
            Ok(Msg::Eof) => break,
            Ok(Msg::Error(e)) => {
                warn(&format!("aspump: {e}"));
                exit(1);
            }
            // Idle for the debounce window: the screen settled. Emit the quiescence
            // wakes ONCE per idle period (until new output resets it).
            Err(mpsc::RecvTimeoutError::Timeout) => {
                if !quiesced {
                    quiesced = true;
                    for ev in classifier.quiesce() {
                        emit(&mut out, &wake_line(&ev, last_offset));
                    }
                }
                // Every wake the last delivery could produce is now out — its marks
                // when it arrived, its settle wakes just above — so the cursor may
                // finally pass it.
                commit_wakes_through(&mut commits, &opts.cursor, &mut pending);
            }
            // The worker always sends Eof/Error before it exits; this is a crash.
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                warn("aspump: delivery thread ended unexpectedly");
                exit(1);
            }
        }
    }
}
