//! Claim `broker.cli.pub-sub-roundtrip`: the `asb` CLI puts bytes on the bus and
//! tails them back byte-exactly (through NUL and newline) over a real Unix
//! socket — the shape a lash/bridge uses to move a terminal's /out and /in.
//! Pins the framing exactly (`<offset> <nbytes>\n<body>\n`, offsets matching the
//! ones `pub` printed, two records to prove the boundaries), the strict flag
//! surface (exit 2, never a silent default), the refusal to serve a socket a live
//! broker is answering on, durable consumer-group resume through
//! `sub --group` + `commit`, the `--` end-of-flags terminator, and a non-UTF-8
//! argument as a usage error rather than a panic. Synchronizes on the serve readiness line and on
//! `subscribe from 0` replaying history, so there are no sleeps and no attach race.
#![cfg(unix)]

use std::io::{BufRead, BufReader, Write};
use std::process::{Child, Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);

struct Paths {
    sock: String,
    log: String,
}

fn fresh(tag: &str) -> Paths {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let sock = format!("/tmp/asbcli_{tag}_{pid}_{n}.sock");
    let log = format!("/tmp/asbcli_{tag}_{pid}_{n}.log");
    let _ = std::fs::remove_file(&sock);
    let _ = std::fs::remove_file(&log);
    Paths { sock, log }
}

impl Drop for Paths {
    /// Remove the socket, the log and every `<path>.*` sidecar beside them (the
    /// broker's `.hw`, `.base`, `.replica`, …) on success and on panic alike. A test
    /// binds its `Paths` before serving on them, so this runs after the broker is gone.
    fn drop(&mut self) {
        remove_with_sidecars(&self.sock);
        remove_with_sidecars(&self.log);
    }
}

/// Remove `path` and every `<path>.*` sidecar in its directory.
fn remove_with_sidecars(path: impl AsRef<std::path::Path>) {
    let path = path.as_ref();
    let _ = std::fs::remove_file(path);
    let (Some(dir), Some(name)) = (path.parent(), path.file_name()) else {
        return;
    };
    let prefix = format!("{}.", name.to_string_lossy());
    for entry in std::fs::read_dir(dir).into_iter().flatten().flatten() {
        if entry.file_name().to_string_lossy().starts_with(&prefix) {
            let _ = std::fs::remove_file(entry.path());
        }
    }
}

fn asb() -> Command {
    Command::new(env!("CARGO_BIN_EXE_asb"))
}

/// A serving broker; killed + reaped on drop.
struct Serve(Child);

impl Drop for Serve {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

/// `asb serve`, synchronized on its readiness line (data, not a sleep).
fn serve(p: &Paths) -> Serve {
    let mut serve = asb()
        .args(["serve", &p.sock, &p.log])
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut r = BufReader::new(serve.stdout.take().unwrap());
    let mut line = String::new();
    r.read_line(&mut line).unwrap();
    assert_eq!(line, format!("listening {}\n", p.sock), "serve readiness");
    Serve(serve)
}

/// `asb pub` with stdin = body; returns stdout.
fn publish(p: &Paths, subject: &str, extra: &[&str], body: &[u8]) -> Output {
    let mut c = asb()
        .args(["pub", &p.sock, subject])
        .args(extra)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    c.stdin.take().unwrap().write_all(body).unwrap();
    c.wait_with_output().unwrap()
}

fn stdout(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}
fn stderr(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

/// Write a `--cap-file`: one `<grant> <tag-hex>` line, exactly what `asb mint`
/// prints. Removed with the socket and the log at the end of the test.
#[cfg(feature = "cap")]
fn cap_file(p: &Paths, name: &str, line: &str) -> String {
    let path = format!("{}.{name}.cap", p.log);
    std::fs::write(&path, format!("{line}\n")).unwrap();
    path
}

/// Read one framed delivery, asserting the exact framing: `<offset> <nbytes>\n`,
/// then exactly nbytes of body, then ONE newline.
fn read_record(r: &mut impl BufRead) -> (u64, Vec<u8>) {
    let mut header = String::new();
    r.read_line(&mut header).unwrap();
    assert!(header.ends_with('\n'), "header line: {header:?}");
    let parts: Vec<&str> = header.trim_end_matches('\n').split(' ').collect();
    assert_eq!(parts.len(), 2, "framing header: {header:?}");
    let offset: u64 = parts[0].parse().expect("offset field");
    let nbytes: usize = parts[1].parse().expect("nbytes field");
    let mut body = vec![0u8; nbytes];
    r.read_exact(&mut body).unwrap();
    let mut nl = [0u8; 1];
    r.read_exact(&mut nl).unwrap();
    assert_eq!(nl, [b'\n'], "exactly one newline terminates the body");
    (offset, body)
}

#[test]
fn asb_pub_sub_roundtrip_over_the_socket() {
    let p = fresh("rt");
    let _s = serve(&p);

    // A subscriber tailing from offset 0 (replays history, so no attach race).
    let mut sub = asb()
        .args(["sub", &p.sock, "/a/stream/x"])
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();

    // Two bodies containing NUL and newline, to prove byte-exact framing AND that
    // the record boundary (nbytes + the terminating newline) is honoured.
    let first: &[u8] = b"hello\x00world\nsecond";
    let second: &[u8] = b"\n\x00tail";
    let out = publish(&p, "/a/stream/x", &["--id", "1", "--seq", "1"], first);
    assert_eq!(stdout(&out), "0 new\n", "pub prints `<offset> new`");
    let out = publish(&p, "/a/stream/x", &["--id", "1", "--seq", "2"], second);
    assert_eq!(stdout(&out), "1 new\n");
    // An idempotent retry (explicit --id/--seq; the default --id is the process's
    // pid, unique per invocation) is a dup at the ORIGINAL offset.
    let out = publish(&p, "/a/stream/x", &["--id", "1", "--seq", "2"], b"retry");
    assert_eq!(stdout(&out), "1 dup\n", "same (id, seq) dedups to offset 1");

    let mut r = BufReader::new(sub.stdout.take().unwrap());
    let (off, got) = read_record(&mut r);
    assert_eq!(off, 0, "the header's offset is the one pub printed");
    assert_eq!(got, first, "delivered body byte-exact incl NUL/newline");
    let (off, got) = read_record(&mut r);
    assert_eq!(off, 1);
    assert_eq!(
        got, second,
        "second record parsed from the documented framing"
    );

    let _ = sub.kill();
    let _ = sub.wait();
}

/// Every flag is strict: a present-but-unparsable numeric value, an unknown
/// flag, a key on argv, and a surplus positional are usage errors (exit 2), never a
/// silent default (which would defeat an idempotent retry, replay from 0, or
/// downgrade a sealed transport to plaintext).
#[test]
fn asb_rejects_bad_flags_with_exit_2() {
    let cases: &[(&[&str], &str)] = &[
        (
            &["pub", "x.sock", "/a/x", "--seq", "abc"],
            "--seq expects an unsigned integer",
        ),
        (
            &["pub", "x.sock", "/a/x", "--id", "agent-7"],
            "--id expects an unsigned integer",
        ),
        (
            &["pub", "x.sock", "/a/x", "--seq", "1e3"],
            "--seq expects an unsigned integer",
        ),
        (
            &["pub", "x.sock", "/a/x", "--seq", "-1"],
            "--seq expects an unsigned integer",
        ),
        (&["pub", "x.sock", "/a/x", "--seq"], "--seq expects a value"),
        (
            &["pub", "x.sock", "/a/x", "--seq", "1"],
            "--seq needs a producer id that survives a restart",
        ),
        (
            &["sub", "x.sock", "/a/>", "--from", "1e6"],
            "--from expects an unsigned integer",
        ),
        (
            &["sub", "x.sock", "/a/>", "--from=1_000"],
            "--from expects an unsigned integer",
        ),
        (
            &["sub", "x.sock", "/a/>", "--form", "5"],
            "unknown flag --form",
        ),
        (
            &["pub", "x.sock", "/a/x", "--tcp", "--psk", "00"],
            "unknown flag --psk",
        ),
        (
            &["pub", "x.sock", "/a/x", "--Key", "00"],
            "unknown flag --Key",
        ),
        (
            &["pub", "x.sock", "/a/x", "--key", "00"],
            "--key on argv is refused",
        ),
        (
            &["pub", "x.sock", "/a/x", "--key=00"],
            "--key on argv is refused",
        ),
        (
            &["pub", "x.sock", "/a/x", "extra"],
            "unexpected argument \"extra\"",
        ),
        (
            &["sub", "x.sock", "/a/>", "--from", "1", "--group", "/a/g"],
            "cannot be combined with --from",
        ),
        (
            &["commit", "x.sock", "/a/g", "seven"],
            "<upto> expects an unsigned integer",
        ),
        // A capability tag is a secret, so it may no more ride on argv than a
        // key: both flags are refused with a pointer to --cap-file.
        (
            &["pub", "x.sock", "/a/x", "--cap-tag", "00"],
            "--cap-tag on argv is refused",
        ),
        (
            &["pub", "x.sock", "/a/x", "--cap-filter", "/a/>"],
            "--cap-filter on argv is refused",
        ),
        (
            &["pub", "x.sock", "/a/x", "--cap-filter=/a/>"],
            "pass --cap-file PATH",
        ),
        // A flag that belongs to another verb is as much a mistake as a typo.
        (
            &["pub", "x.sock", "/a/x", "--from", "3"],
            "--from does not apply to pub",
        ),
        (
            &["last", "x.sock", "/a/>", "--group", "/a/g"],
            "--group does not apply to last",
        ),
        (
            &["serve", "x.sock", "--id", "1"],
            "--id does not apply to serve",
        ),
        (&["frobnicate", "x.sock"], "unknown verb"),
    ];
    for (args, want) in cases {
        let out = asb()
            .args(*args)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()
            .unwrap();
        assert_eq!(out.status.code(), Some(2), "{args:?}: {}", stderr(&out));
        assert!(
            stderr(&out).contains(want),
            "{args:?}: stderr {:?} should mention {want:?}",
            stderr(&out)
        );
        assert!(stdout(&out).is_empty(), "{args:?}: nothing on stdout");
    }
}

/// A non-UTF-8 argv byte is a USAGE ERROR, not a panic. `std::env::args()` aborts
/// the process on an argument that is not valid Unicode (exit 101, a backtrace, no
/// message a script can act on) BEFORE any strict-flag handling runs — and a
/// non-UTF-8 `--key-file` path is a plausible real input.
#[test]
fn asb_rejects_a_non_utf8_argument_with_exit_2() {
    use std::ffi::OsStr;
    use std::os::unix::ffi::OsStrExt;

    let out = asb()
        .args(["sub", "x.sock", "/a/>"])
        .arg("--key-file")
        .arg(OsStr::from_bytes(b"/tmp/\xff"))
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .unwrap();
    assert_eq!(
        out.status.code(),
        Some(2),
        "non-UTF-8 argv: {}",
        stderr(&out)
    );
    assert!(
        stderr(&out).contains("not valid UTF-8"),
        "stderr: {}",
        stderr(&out)
    );
    assert!(stdout(&out).is_empty(), "nothing on stdout");
}

/// `--` ends flag parsing, so a positional that begins with `-` is usable at all:
/// the strict unknown-flag check refuses every dash-leading token otherwise, which
/// would leave `asb serve <ep> -journal.log` (and a dash-leading subject) with no
/// escape.
#[test]
fn asb_double_dash_ends_flag_parsing() {
    let p = fresh("dashes");

    // Without the terminator a dash-leading positional is a usage error.
    let out = asb()
        .args(["pub", &p.sock, "-a/dash"])
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(2), "{}", stderr(&out));
    assert!(
        stderr(&out).contains("unknown flag -a/dash"),
        "stderr: {}",
        stderr(&out)
    );

    // With it, the token is the <subject> — parsing gets past the flags and asb
    // fails on the connect instead (exit 1: nothing is listening on that socket).
    let out = asb()
        .args(["pub", &p.sock, "--", "-a/dash"])
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .unwrap();
    assert_eq!(
        out.status.code(),
        Some(1),
        "`--` must not be a usage error: {}",
        stderr(&out)
    );
    assert!(
        !stderr(&out).contains("unknown flag"),
        "stderr: {}",
        stderr(&out)
    );
}

/// A second `asb serve` on a socket a live broker answers on exits 1 with a clear
/// message instead of hijacking the path (and racing the first broker's log).
#[test]
fn asb_serve_refuses_a_socket_a_live_broker_answers_on() {
    let p = fresh("dup");
    let _s = serve(&p);

    let out = asb()
        .args(["serve", &p.sock, &p.log])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(1), "second serve: {}", stderr(&out));
    assert!(
        stderr(&out).contains("already served by another broker"),
        "stderr: {}",
        stderr(&out)
    );
    assert!(
        stdout(&out).is_empty(),
        "no `listening` line from the loser"
    );

    // The first broker is unharmed: its socket still answers a publish.
    let out = publish(
        &p,
        "/a/stream/x",
        &["--id", "1", "--seq", "1"],
        b"still here",
    );
    assert_eq!(stdout(&out), "0 new\n", "{}", stderr(&out));
}

/// Durable consumer-group resume from the shell: `sub --group G` starts at the
/// group's committed offset + 1 (0 when never committed); `commit <ep> G <upto>`
/// advances it durably, so a restarted consumer — even after a broker restart —
/// resumes exactly after the last record it acted on, never re-processing history.
#[test]
fn asb_sub_group_and_commit_resume_durably() {
    let p = fresh("grp");
    let group = "/a/consumer/shell";
    let s = serve(&p);
    for (i, body) in [&b"one"[..], b"two", b"three"].iter().enumerate() {
        let out = publish(
            &p,
            "/a/stream/x",
            &["--id", "7", "--seq", &(i + 1).to_string()],
            body,
        );
        assert_eq!(stdout(&out), format!("{i} new\n"));
    }

    // A never-committed group starts from 0.
    let mut sub = asb()
        .args(["sub", &p.sock, "/a/stream/x", "--group", group])
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut r = BufReader::new(sub.stdout.take().unwrap());
    assert_eq!(read_record(&mut r), (0, b"one".to_vec()));
    assert_eq!(read_record(&mut r), (1, b"two".to_vec()));
    let _ = sub.kill();
    let _ = sub.wait();

    // The consumer acted on offsets 0 and 1: commit upto=1.
    let out = asb()
        .args(["commit", &p.sock, group, "1"])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .unwrap();
    assert_eq!(stdout(&out), "3 committed\n", "{}", stderr(&out));

    // Restart the BROKER (kill + serve the same log): the commit is durable.
    drop(s);
    let _s = serve(&p);

    // A fresh `sub --group` resumes at 2 — history is not re-delivered.
    let mut sub = asb()
        .args(["sub", &p.sock, "/a/stream/x", "--group", group])
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut r = BufReader::new(sub.stdout.take().unwrap());
    assert_eq!(read_record(&mut r), (2, b"three".to_vec()));
    // And it tails live from there.
    let out = publish(&p, "/a/stream/x", &["--id", "7", "--seq", "4"], b"four");
    assert_eq!(stdout(&out), "4 new\n");
    assert_eq!(read_record(&mut r), (4, b"four".to_vec()));
    let _ = sub.kill();
    let _ = sub.wait();

    // A commit is monotone: re-committing an older offset does not regress.
    let out = asb()
        .args(["commit", &p.sock, group, "0"])
        .stdout(Stdio::piped())
        .output()
        .unwrap();
    assert!(stdout(&out).ends_with(" committed\n"));
    let mut sub = asb()
        .args(["sub", &p.sock, "/a/stream/x", "--group", group])
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut r = BufReader::new(sub.stdout.take().unwrap());
    assert_eq!(read_record(&mut r).0, 2, "resume point never regresses");
    let _ = sub.kill();
    let _ = sub.wait();
}

/// The capability face: against a guarded broker (the `cap` feature), a
/// `--cap-file` line presents a minted capability before the verb, so the shell
/// faces run under mint enforcement. Without it, or with a forged (widened)
/// filter, the broker refuses and asb exits 1. The tag reaches asb ONLY through
/// the file: `--cap-filter`/`--cap-tag` on argv are refused, because argv is
/// readable by every same-uid process for the command's whole lifetime.
#[cfg(feature = "cap")]
#[test]
fn asb_presents_a_capability_to_a_guarded_broker() {
    use astream_broker::Broker;
    let p = fresh("cap");
    let secret = b"broker-secret-key";
    let broker = Broker::open_guarded(&p.log, secret.to_vec()).unwrap();
    let _h = broker.serve(&p.sock).unwrap();
    let cap = astream_cap::mint(secret, "/a/stream/s1/>").unwrap();
    let tag_hex: String = cap.tag.iter().map(|b| format!("{b:02x}")).collect();
    let good = cap_file(&p, "good", &format!("{} {tag_hex}", cap.filter));
    // The SAME genuine tag under a widened filter: the grant string is what the
    // HMAC covers, so this verifies as nothing at all.
    let forged = cap_file(&p, "forged", &format!("/a/> {tag_hex}"));

    // No capability -> refused.
    let out = publish(
        &p,
        "/a/stream/s1/out",
        &["--id", "1", "--seq", "1"],
        b"nope",
    );
    assert_eq!(out.status.code(), Some(1));
    assert!(stderr(&out).contains("unauthorized"), "{}", stderr(&out));

    // A forged (widened) filter under the real tag -> refused at the attach.
    let out = publish(
        &p,
        "/a/stream/s1/out",
        &["--id", "1", "--seq", "1", "--cap-file", &forged],
        b"nope",
    );
    assert_eq!(out.status.code(), Some(1));
    assert!(
        stderr(&out).contains("capability") || stderr(&out).contains("unauthorized"),
        "{}",
        stderr(&out)
    );

    // The minted capability -> a publish within the grant lands.
    let out = publish(
        &p,
        "/a/stream/s1/out",
        &["--id", "1", "--seq", "1", "--cap-file", &good],
        b"hi",
    );
    assert_eq!(stdout(&out), "0 new\n", "{}", stderr(&out));

    // ...and a scoped subscribe delivers it.
    let mut sub = asb()
        .args(["sub", &p.sock, "/a/stream/s1/out", "--cap-file", &good])
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut r = BufReader::new(sub.stdout.take().unwrap());
    assert_eq!(read_record(&mut r), (0, b"hi".to_vec()));
    let _ = sub.kill();
    let _ = sub.wait();
}

/// A log with a CORRUPT record is refused by `serve` — the bytes from there on
/// may be acked data — and `asb repair` is the operator's way out. Before this
/// verb existed the refusal named `BrokerLog::open_repair`, a Rust function no
/// operator can call: a dead end at exactly the moment a log is unopenable.
#[test]
fn asb_repair_truncates_a_log_that_serve_refuses_to_open() {
    let p = fresh("repair");
    {
        let _s = serve(&p);
        assert_eq!(stdout(&publish(&p, "/a/x", &[], b"hello")), "0 new\n");
        assert_eq!(stdout(&publish(&p, "/a/x", &[], b"world")), "1 new\n");
    } // the broker is killed here, releasing the log's exclusive lock

    // Damage a byte inside the FIRST record: not a torn tail (which recovery
    // truncates on its own) but a corruption with decodable records after it.
    let mut bytes = std::fs::read(&p.log).unwrap();
    assert!(bytes.len() > 24, "two records were written");
    bytes[20] ^= 0xFF;
    let damaged = bytes.len();
    std::fs::write(&p.log, &bytes).unwrap();

    // serve refuses, naming the offset, the byte, and the command that fixes it.
    let sock2 = format!("{}.2", p.sock);
    let out = asb()
        .args(["serve", &sock2, &p.log])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .unwrap();
    let _ = std::fs::remove_file(&sock2);
    assert_eq!(out.status.code(), Some(1), "stderr {}", stderr(&out));
    let err = stderr(&out);
    assert!(
        err.contains("corrupt record at offset") && err.contains("asb repair"),
        "the refusal names the corruption and the way out: {err:?}"
    );

    // repair truncates and says how much it dropped ...
    let out = asb().args(["repair", &p.log]).output().unwrap();
    assert_eq!(out.status.code(), Some(0), "stderr {}", stderr(&out));
    assert!(
        stdout(&out).contains(&format!("dropped {damaged} byte(s)")),
        "repair reports the discarded bytes: {:?}",
        stdout(&out)
    );
    // ... is idempotent ...
    let out = asb().args(["repair", &p.log]).output().unwrap();
    assert!(
        stdout(&out).contains("nothing to repair"),
        "second repair: {:?}",
        stdout(&out)
    );
    // ... and the log serves again.
    let _s = serve(&p);
    assert_eq!(stdout(&publish(&p, "/a/x", &[], b"after")), "0 new\n");
}
