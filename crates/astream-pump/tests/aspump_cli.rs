//! Claim `pump.cli.wake-lines`: the `aspump` CLI tails a target session's /out
//! off a live broker and prints the semantic WAKE lines a driving agent acts on
//! — `PROMPT_READY boffset=1`, `COMMAND_START boffset=3`,
//! `COMMAND_END boffset=5 exit=0`, `QUIESCED boffset=5` for the fixture, each
//! tagged with the broker offset of the /out record that produced it — so a
//! shell/bridge reacts on boundaries instead of polling raw bytes. Also pinned:
//! `--from N` is inclusive (resume from `boffset+1`), a broker-side rejection
//! exits 1 with the reason on stderr, a BROKEN stdout pipe (its reader went away)
//! ends the pump (exit 0) rather than leaving it holding a subscription, and a
//! missing/malformed/out-of-range flag value exits 2 before connecting.
//! The fabric flags too: `--subject` tails a face `<sid>` cannot name (and is
//! refused alongside a `<sid>`), `--group` is a broker-durable cursor that a
//! restart resumes from with no `--from` (at-least-once, never replaying what it
//! committed, and never advancing past a record whose settle wake was not
//! printed), `--tcp` reaches a TCP endpoint, and `--key-file`/`--key` are
//! refused with the flag named — the first because this build has no `aead`
//! feature, the second because a key on argv is world-readable via `ps`.
//! Synchronizes on subscribe-from-0 replay, known boundaries, a published
//! sentinel and the broker's log head (a commit is a record); QUIESCED and the
//! exit-on-broken-pipe case are driven by the binary's `--debounce` timer, and
//! process exit is awaited with a bounded poll. A stdout that was already CLOSED
//! at launch is NOT covered here or by the pump: `std` reports EBADF on fd 1 as a
//! successful write, so the pump cannot see it (`aspump.rs`'s module doc says so).
#![cfg(unix)]

use astream_broker::{Broker, BrokerHandle, Client};
use std::io::{BufRead, BufReader, Read};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

static CTR: AtomicU64 = AtomicU64::new(0);

/// Removes its paths when dropped, each with every `<path>.*` sidecar beside it (the
/// broker's `.hw`, `.base`, `.replica`, …), so a test leaves nothing behind whether it
/// passes or panics. Bind it before whatever uses the paths, so it drops after that.
struct Cleanup(Vec<std::path::PathBuf>);

impl Cleanup {
    fn new<P: AsRef<std::path::Path>>(paths: &[P]) -> Cleanup {
        Cleanup(paths.iter().map(|p| p.as_ref().to_path_buf()).collect())
    }
}

impl Drop for Cleanup {
    fn drop(&mut self) {
        for path in &self.0 {
            remove_with_sidecars(path);
        }
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

fn fresh(tag: &str) -> (Cleanup, Broker, BrokerHandle, String) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let sock = format!("/tmp/aspump_{pid}_{tag}_{n}.sock");
    let log = format!("/tmp/aspump_{pid}_{tag}_{n}.log");
    let _ = std::fs::remove_file(&log);
    let tmp = Cleanup::new(&[&sock, &log]);
    let broker = Broker::open(&log).unwrap();
    let handle = broker.serve(&sock).unwrap();
    (tmp, broker, handle, sock)
}

fn session() -> Vec<&'static [u8]> {
    vec![
        b"\x1b[2J\x1b[H",
        b"\x1b]133;A\x07$ ",
        b"echo hi\r\n",
        b"\x1b]133;C\x07",
        b"hi\r\n",
        b"\x1b]133;D;0\x07",
    ]
}

// Publish the fixture; on a fresh log its records land at broker offsets 0..=5,
// which the exact `boffset=` assertions below rely on.
fn publish_session(sock: &str, subj: &str) {
    let mut prod = Client::connect(sock).unwrap();
    for (i, body) in session().iter().enumerate() {
        let (off, _) = prod.publish(1, i as u64, subj, body).unwrap();
        assert_eq!(off, i as u64, "fixture offsets are 0..=5");
    }
}

fn spawn(args: &[&str]) -> Child {
    Command::new(env!("CARGO_BIN_EXE_aspump"))
        .args(args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap()
}

// Read exactly `n` lines (fewer at EOF), trimmed.
fn read_lines(r: &mut impl BufRead, n: usize) -> Vec<String> {
    let mut lines = Vec::new();
    for _ in 0..n {
        let mut l = String::new();
        if r.read_line(&mut l).unwrap() == 0 {
            break;
        }
        lines.push(l.trim_end().to_string());
    }
    lines
}

// Wait for the child to exit on its own, polling with a bounded deadline so a
// regression (a pump that lingers) fails the test instead of hanging it.
fn wait_bounded(child: &mut Child, deadline: Duration) -> ExitStatus {
    let start = Instant::now();
    loop {
        if let Some(st) = child.try_wait().unwrap() {
            return st;
        }
        if start.elapsed() > deadline {
            let _ = child.kill();
            let _ = child.wait();
            panic!("aspump did not exit within {deadline:?}");
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}

// The child's wake lines on a channel, so a test can wait for one with a
// DEADLINE: a wake the pump LOST fails the test instead of blocking it forever
// in `read_line`.
fn line_stream(child: &mut Child) -> mpsc::Receiver<String> {
    let out = child.stdout.take().unwrap();
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let mut r = BufReader::new(out);
        loop {
            let mut l = String::new();
            match r.read_line(&mut l) {
                Ok(0) | Err(_) => break,
                Ok(_) => {
                    if tx.send(l.trim_end().to_string()).is_err() {
                        break;
                    }
                }
            }
        }
    });
    rx
}

fn next_line(rx: &mpsc::Receiver<String>, what: &str) -> String {
    rx.recv_timeout(Duration::from_secs(10))
        .unwrap_or_else(|_| panic!("waited 10s for {what}; the pump printed nothing more"))
}

// Every commit a pump has in flight is a record on the broker's reserved commit
// subject, so the log head stops growing once they have all landed. Waiting for
// that before a kill makes "what the cursor had committed" deterministic instead
// of a race with the signal.
fn head_settles(b: &Broker) -> u64 {
    let start = Instant::now();
    let mut last = b.head();
    loop {
        std::thread::sleep(Duration::from_millis(50));
        let now = b.head();
        if now == last {
            return now;
        }
        last = now;
        assert!(
            start.elapsed() < Duration::from_secs(10),
            "the broker's log head never stopped growing"
        );
    }
}

fn stderr_of(child: &mut Child) -> String {
    let mut s = String::new();
    child.stderr.take().unwrap().read_to_string(&mut s).unwrap();
    s
}

#[test]
fn aspump_prints_wake_lines_tagged_with_the_broker_offset() {
    let (_tmp, _b, h, sock) = fresh("wake");
    publish_session(&sock, "/a/stream/term/s1/out");

    let mut child = spawn(&[&sock, "s1"]);
    let mut r = BufReader::new(child.stdout.take().unwrap());
    // The three OSC wake lines, exactly, each at the broker offset of the record
    // that carried its mark (A at 1, C at 3, D;0 at 5).
    assert_eq!(
        read_lines(&mut r, 3),
        vec![
            "PROMPT_READY boffset=1",
            "COMMAND_START boffset=3",
            "COMMAND_END boffset=5 exit=0",
        ]
    );

    // The broker shutting down closes the stream: a clean end, exit 0, no noise.
    drop(h);
    let st = wait_bounded(&mut child, Duration::from_secs(10));
    assert_eq!(st.code(), Some(0), "stderr: {}", stderr_of(&mut child));
}

#[test]
fn aspump_emits_quiesced_after_debounce() {
    let (_tmp, _b, _h, sock) = fresh("quiesce");
    publish_session(&sock, "/a/stream/term/s2/out");

    let mut child = spawn(&[&sock, "s2", "--debounce", "50"]);
    let mut r = BufReader::new(child.stdout.take().unwrap());
    // After the replay goes idle for the debounce window, QUIESCED is tagged with
    // the last delivered offset — and nothing else follows it: the session is
    // integrated (its marks fired), so no glyph PROMPT_READY is invented.
    assert_eq!(
        read_lines(&mut r, 4),
        vec![
            "PROMPT_READY boffset=1",
            "COMMAND_START boffset=3",
            "COMMAND_END boffset=5 exit=0",
            "QUIESCED boffset=5",
        ]
    );
    let _ = child.kill();
    let _ = child.wait();
}

#[test]
fn aspump_settles_again_after_output_resumes_from_idle() {
    // Once settled the pump waits without a timer; new output must re-arm the
    // debounce so the next burst gets its own settle wake, at its own offset.
    let (_tmp, _b, _h, sock) = fresh("resettle");
    let subj = "/a/stream/term/s10/out";
    publish_session(&sock, subj);

    let mut child = spawn(&[&sock, "s10", "--debounce", "50"]);
    let lines = line_stream(&mut child);
    for _ in 0..3 {
        next_line(&lines, "a fixture wake");
    }
    assert_eq!(next_line(&lines, "the first settle"), "QUIESCED boffset=5");
    // Idle well past several debounce windows: nothing more is printed.
    assert!(lines.recv_timeout(Duration::from_millis(300)).is_err());

    let mut prod = Client::connect(&sock).unwrap();
    let (off, _) = prod.publish(2, 0, subj, b"\x1b]133;A\x07$ ").unwrap();
    assert_eq!(off, 6);
    assert_eq!(next_line(&lines, "the new mark"), "PROMPT_READY boffset=6");
    assert_eq!(next_line(&lines, "the second settle"), "QUIESCED boffset=6");
    let _ = child.kill();
    let _ = child.wait();
}

#[test]
fn aspump_from_is_inclusive_so_a_resume_passes_the_next_offset() {
    let (_tmp, _b, _h, sock) = fresh("from");
    let subj = "/a/stream/term/s3/out";
    publish_session(&sock, subj);

    // --from 3 delivers record 3 (the C mark) and onward; the earlier prompt is
    // not replayed.
    let mut child = spawn(&[&sock, "s3", "--from", "3"]);
    let mut r = BufReader::new(child.stdout.take().unwrap());
    assert_eq!(
        read_lines(&mut r, 2),
        vec!["COMMAND_START boffset=3", "COMMAND_END boffset=5 exit=0"]
    );
    // Live: a new prompt lands at offset 6 and wakes immediately.
    let mut prod = Client::connect(&sock).unwrap();
    let (off, _) = prod.publish(2, 0, subj, b"\x1b]133;A\x07$ ").unwrap();
    assert_eq!(off, 6);
    assert_eq!(read_lines(&mut r, 1), vec!["PROMPT_READY boffset=6"]);
    let _ = child.kill();
    let _ = child.wait();

    // Restarting AT the last printed boffset re-delivers that record: the wake is
    // printed twice. The contract is `--from <boffset+1>` to resume.
    let mut dup = spawn(&[&sock, "s3", "--from", "6"]);
    let mut r = BufReader::new(dup.stdout.take().unwrap());
    assert_eq!(read_lines(&mut r, 1), vec!["PROMPT_READY boffset=6"]);
    let _ = dup.kill();
    let _ = dup.wait();

    let mut resumed = spawn(&[&sock, "s3", "--from", "7"]);
    let mut r = BufReader::new(resumed.stdout.take().unwrap());
    let (off, _) = prod.publish(2, 1, subj, b"\x1b]133;A\x07$ ").unwrap();
    assert_eq!(off, 7);
    // The first line is the NEW record — offset 6 was not delivered again.
    assert_eq!(read_lines(&mut r, 1), vec!["PROMPT_READY boffset=7"]);
    let _ = resumed.kill();
    let _ = resumed.wait();
}

#[test]
fn aspump_reports_a_broker_rejection_and_exits_nonzero() {
    let (_tmp, _b, _h, sock) = fresh("reject");
    // The broker never acks a Subscribe; it answers a bad filter (here a partial
    // wildcard in the sid) with an Error frame as the first delivery. That must
    // surface as a failure, not as a silent clean EOF a supervisor never restarts.
    let child = spawn(&[&sock, "no*sid"]);
    let output = child.wait_with_output().unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "stderr: {stderr}");
    assert!(
        stderr.starts_with("aspump: ") && stderr.contains("bad filter"),
        "the broker's reason must reach stderr: {stderr:?}"
    );
    assert!(output.stdout.is_empty());
}

#[test]
fn aspump_exits_when_its_reader_goes_away() {
    let (_tmp, _b, _h, sock) = fresh("epipe");
    let subj = "/a/stream/term/s4/out";
    publish_session(&sock, subj);

    let mut child = spawn(&[&sock, "s4", "--debounce", "50"]);
    let mut r = BufReader::new(child.stdout.take().unwrap());
    assert_eq!(read_lines(&mut r, 1), vec!["PROMPT_READY boffset=1"]);
    // The consumer of the wake lines exits (`aspump ... | head -1`): the pipe's
    // read end closes. The next wake line the pump tries to write hits EPIPE and
    // the pump must end (exit 0) — not linger holding a broker subscription.
    drop(r);
    let mut prod = Client::connect(&sock).unwrap();
    prod.publish(2, 0, subj, b"\x1b]133;A\x07$ ").unwrap();
    let st = wait_bounded(&mut child, Duration::from_secs(10));
    assert_eq!(st.code(), Some(0), "stderr: {}", stderr_of(&mut child));
}

#[test]
fn aspump_rejects_a_missing_or_malformed_flag_value() {
    // Parsing precedes connecting: a bad flag is a usage error (exit 2) even
    // though the socket does not exist (a connect failure would be exit 1).
    let cases: Vec<Vec<&str>> = vec![
        vec!["--from"],
        vec!["--from", "1x"],
        vec!["--from", "--debounce", "50"],
        vec!["--cols", "70000"],
        vec!["--rows", "0"],
        vec!["--debounce", "0"],
        vec!["--bogus"],
    ];
    for extra in cases {
        let mut args = vec!["/nonexistent/aspump.sock", "sid"];
        args.extend(extra.iter().copied());
        let output = spawn(&args).wait_with_output().unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.code(), Some(2), "{extra:?}: stderr {stderr}");
        assert!(
            stderr.starts_with("aspump: ") && stderr.contains(extra[0]),
            "{extra:?}: the offending flag is named: {stderr:?}"
        );
    }
    // And a plain missing positional.
    let output = spawn(&["/nonexistent/aspump.sock"])
        .wait_with_output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));

    // A SURPLUS positional is almost always a flag whose `--name` was dropped
    // (`aspump sock sid 4711` for `--from 4711`). Ignoring it would silently
    // tail from 0 and re-print every historical wake, so it is a usage error.
    let output = spawn(&["/nonexistent/aspump.sock", "sid", "4711"])
        .wait_with_output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "stderr {stderr}");
    assert!(
        stderr.starts_with("aspump: ") && stderr.contains("4711"),
        "the surplus argument is named back: {stderr:?}"
    );
}

// ---------------------------------------------------------------------------
// The fabric flags: --subject, --group, --tcp, --key-file (§11.1, R10).
// ---------------------------------------------------------------------------

/// A fabric node's PTY face (`DESIGN-aterm-fabric.md` §3.3): the subject shape
/// `<sid>` alone cannot name.
const FABRIC_SUBJECT: &str = "/f/F/term/n1/s5/out";

/// The fixture's three OSC wake lines at offsets 0..=5 on a fresh log.
fn fixture_lines() -> Vec<String> {
    [
        "PROMPT_READY boffset=1",
        "COMMAND_START boffset=3",
        "COMMAND_END boffset=5 exit=0",
    ]
    .iter()
    .map(|s| (*s).to_string())
    .collect()
}

#[test]
fn aspump_subject_tails_a_fabric_face_the_sid_form_cannot_name() {
    let (_tmp, _b, _h, sock) = fresh("subject");
    publish_session(&sock, FABRIC_SUBJECT);

    let mut child = spawn(&[&sock, "--subject", FABRIC_SUBJECT]);
    let mut r = BufReader::new(child.stdout.take().unwrap());
    assert_eq!(
        read_lines(&mut r, 3),
        fixture_lines(),
        "an arbitrary subject prints the same wake lines as the built face"
    );
    let _ = child.kill();
    let _ = child.wait();

    // `<sid>` and `--subject` name the same thing two ways; taking both would
    // silently tail a stream the caller did not ask for.
    let output = spawn(&[&sock, "s5", "--subject", FABRIC_SUBJECT])
        .wait_with_output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "stderr {stderr}");
    assert!(
        stderr.contains("mutually exclusive"),
        "stderr names the conflict: {stderr:?}"
    );
}

#[test]
fn aspump_group_is_a_broker_durable_cursor_that_survives_a_restart() {
    let (_tmp, _b, _h, sock) = fresh("group");
    let subj = "/a/stream/term/s6/out";
    publish_session(&sock, subj);
    let group = "/f/F/cur/n1/aspump";
    // A debounce far longer than the test, so no QUIESCED line interleaves with
    // the boundaries being asserted.
    let long = "600000";

    // Run 1 prints all three fixture wakes. By the time the line for offset 5 is
    // out, the commits for every delivery BEFORE it have landed (each is released
    // when the next delivery closes its settle window), so the cursor is at least
    // 4 — the last delivery's own commit is still held (see the settle test).
    let mut first = spawn(&[&sock, "s6", "--group", group, "--debounce", long]);
    let mut r = BufReader::new(first.stdout.take().unwrap());
    assert_eq!(read_lines(&mut r, 3), fixture_lines());
    let _ = first.kill();
    let _ = first.wait();

    // Run 2 is handed NO offset — only the group. Publish a sentinel and read
    // until its wake: everything printed before it is what the restart replayed.
    let mut second = spawn(&[&sock, "s6", "--group", group, "--debounce", long]);
    let mut r = BufReader::new(second.stdout.take().unwrap());
    let mut prod = Client::connect(&sock).unwrap();
    let (sentinel, _) = prod.publish(7, 0, subj, b"\x1b]133;A\x07$ ").unwrap();
    assert!(sentinel > 5, "the commit records took the offsets after 5");
    let sentinel_line = format!("PROMPT_READY boffset={sentinel}");
    let mut replayed = Vec::new();
    loop {
        let line = read_lines(&mut r, 1).pop().expect("the sentinel wake");
        if line == sentinel_line {
            break;
        }
        replayed.push(line);
    }
    // At-least-once, not exactly-once: the delivery whose commit run 1 was still
    // holding may repeat. Nothing older than it may.
    assert!(
        replayed.iter().all(|l| l == "COMMAND_END boffset=5 exit=0"),
        "the durable cursor replayed history it had committed: {replayed:?}"
    );
    assert!(
        replayed.len() <= 1,
        "and replayed it once at most: {replayed:?}"
    );
    let _ = second.kill();
    let _ = second.wait();

    // The control: a group that never committed starts at 0, so `--group` is a
    // real cursor lookup and not "start at the head of the log".
    let mut virgin = spawn(&[
        &sock,
        "s6",
        "--group",
        "/f/F/cur/n1/other",
        "--debounce",
        long,
    ]);
    let mut r = BufReader::new(virgin.stdout.take().unwrap());
    assert_eq!(read_lines(&mut r, 3), fixture_lines());
    let _ = virgin.kill();
    let _ = virgin.wait();
}

/// The settle wakes — `QUIESCED`, and the glyph `PROMPT_READY` for a target with
/// no shell integration — are fired by the debounce timer at the offset of the
/// record that ENDED the burst, after that record was delivered, out of the
/// classifier's screen state rather than out of any record. Committing at
/// delivery time would therefore let a kill in that window take the boundary with
/// it for good: the replacement resumes past the record, is delivered nothing,
/// and its `quiesce()` (nothing pushed) prints nothing — a lost wake, not a
/// re-delivered one. So the commit is HELD until the settle window closes.
#[test]
fn aspump_group_holds_the_commit_until_the_settle_wake_is_out() {
    let (_tmp, b, _h, sock) = fresh("settle");
    let subj = "/a/stream/term/s8/out";
    publish_session(&sock, subj);
    let group = "/f/F/cur/n1/settle";

    // Run 1's debounce is far longer than this test: it prints the three OSC
    // wakes and is killed with the burst's settle wake still unfired.
    let mut first = spawn(&[&sock, "s8", "--group", group, "--debounce", "600000"]);
    let mut r = BufReader::new(first.stdout.take().unwrap());
    assert_eq!(read_lines(&mut r, 3), fixture_lines());
    // Whatever run 1 was going to commit has landed before the kill.
    let committed_head = head_settles(&b);
    let _ = first.kill();
    let _ = first.wait();

    // The replacement is handed NO offset, only the group. Record 5 was delivered
    // but never committed, so the broker delivers it again — and this run's short
    // debounce fires the settle wake run 1 never printed. Read with a deadline:
    // the regression is silence, and silence must fail, not hang.
    let mut second = spawn(&[&sock, "s8", "--group", group, "--debounce", "50"]);
    let lines = line_stream(&mut second);
    assert_eq!(
        next_line(&lines, "the re-delivered COMMAND_END at offset 5"),
        "COMMAND_END boffset=5 exit=0",
        "the cursor advanced past the record that ended the burst"
    );
    assert_eq!(
        next_line(
            &lines,
            "QUIESCED boffset=5 — the settle wake run 1 never printed"
        ),
        "QUIESCED boffset=5"
    );
    // And the hold is a hold, not a stall: once the settle wakes are out, the
    // cursor does pass that record (another commit record on the log).
    assert!(
        head_settles(&b) > committed_head,
        "the settle wake is out, so the held commit must have been released"
    );
    let _ = second.kill();
    let _ = second.wait();
}

#[test]
fn aspump_tcp_tails_the_same_stream_over_a_tcp_endpoint() {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/aspump_{pid}_tcp_{n}.log");
    let _ = std::fs::remove_file(&log);
    let _tmp = Cleanup::new(&[&log]);
    let broker = Broker::open(&log).unwrap();
    let handle = broker.serve_tcp("127.0.0.1:0").unwrap();
    let addr = handle.tcp_addr().unwrap().to_string();

    let subj = "/a/stream/term/s7/out";
    let mut prod = Client::connect_tcp(&addr).unwrap();
    for (i, body) in session().iter().enumerate() {
        prod.publish(1, i as u64, subj, body).unwrap();
    }

    let mut child = spawn(&[&addr, "s7", "--tcp"]);
    let mut r = BufReader::new(child.stdout.take().unwrap());
    assert_eq!(read_lines(&mut r, 3), fixture_lines());
    let _ = child.kill();
    let _ = child.wait();
}

#[test]
fn aspump_rejects_contradictory_and_unsupported_fabric_flags() {
    // Every case is refused at parse time (exit 2) against a socket that does not
    // exist, so none of them is a connect failure in disguise.
    let cases: Vec<(Vec<&str>, &str)> = vec![
        // A missing value is never a silent default.
        (vec!["--group"], "--group"),
        (vec!["--subject"], "--subject"),
        (vec!["--key-file"], "--key-file"),
        // A value that is itself a flag is a dropped value, not a group name.
        (vec!["--group", "--debounce", "50"], "--group"),
        // Two cursors, one pump: which one wins must never be guessed.
        (vec!["--group", "G", "--from", "3"], "--group"),
        // Without `--features aead` there is no sealed transport; the flag must
        // say so rather than fall back to plaintext. (Built WITH the feature this
        // still exits 2 — on the unreadable key file — and still names the flag.)
        (vec!["--key-file", "/nonexistent/aspump.key"], "--key-file"),
        // The key never travels on argv, where `ps` shows it to every local user.
        (vec!["--key", "00"], "--key"),
    ];
    for (extra, named) in cases {
        let mut args = vec!["/nonexistent/aspump.sock", "sid"];
        args.extend(extra.iter().copied());
        let output = spawn(&args).wait_with_output().unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.code(), Some(2), "{extra:?}: stderr {stderr}");
        assert!(
            stderr.starts_with("aspump: ") && stderr.contains(named),
            "{extra:?}: the offending flag is named: {stderr:?}"
        );
        assert!(output.stdout.is_empty(), "{extra:?}: printed a wake line");
    }
}

#[test]
fn aspump_never_echoes_a_key_given_as_flag_equals_value() {
    // `--key=HEX` is the same key-on-argv mistake as `--key HEX`; the refusal
    // must not copy the key into stderr (and whatever log collects it).
    let key = "0123456789abcdef".repeat(4);
    for arg in [format!("--key={key}"), format!("--psk={key}")] {
        let output = spawn(&["/nonexistent/aspump.sock", "sid", &arg])
            .wait_with_output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.code(), Some(2), "{arg}: stderr {stderr}");
        assert!(
            !stderr.contains(&key),
            "{arg}: the value was echoed to stderr: {stderr:?}"
        );
        let flag = arg.split('=').next().unwrap();
        assert!(stderr.contains(flag), "{arg}: flag not named: {stderr:?}");
    }
}

/// A key file is 64 hex chars; a path that is not one — here an endless device —
/// is refused after a bounded read, never read into memory until the process is
/// killed (which would end it outside its documented 0/1/2 statuses). Run under an
/// address-space limit so a regression fails fast instead of eating the machine.
#[cfg(all(target_os = "linux", feature = "aead"))]
#[test]
fn aspump_refuses_an_oversized_key_file_without_reading_it_whole() {
    let output = Command::new("sh")
        .arg("-c")
        .arg("ulimit -v 1048576 && exec \"$0\" \"$@\"")
        .arg(env!("CARGO_BIN_EXE_aspump"))
        .args(["/nonexistent/aspump.sock", "sid", "--key-file", "/dev/zero"])
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "stderr {stderr}");
    assert!(
        stderr.contains("--key-file") && stderr.contains("larger than"),
        "refused for its size, not for running out of memory: {stderr:?}"
    );
}

/// The child's resident set in KiB, from `/proc/<pid>/status`.
#[cfg(target_os = "linux")]
fn rss_kib(pid: u32) -> u64 {
    let status = std::fs::read_to_string(format!("/proc/{pid}/status")).unwrap();
    status
        .lines()
        .find_map(|l| l.strip_prefix("VmRSS:"))
        .and_then(|v| v.trim().trim_end_matches("kB").trim().parse().ok())
        .expect("VmRSS in /proc/<pid>/status")
}

/// A reader that stops reading the wake lines must not make the pump buffer the
/// stream without bound. Once stdout's pipe is full the main thread blocks
/// writing, and the delivery thread must block with it — back-pressure onto the
/// broker socket — instead of queueing every further delivery in memory.
#[cfg(target_os = "linux")]
#[test]
fn aspump_does_not_buffer_the_stream_while_its_reader_stalls() {
    const MIB: usize = 1024 * 1024;
    let (_tmp, _b, _h, sock) = fresh("stall");
    let subj = "/a/stream/term/s9/out";
    let mut prod = Client::connect(&sock).unwrap();
    // One record carrying 8000 prompt marks: 8000 wake lines, ~180 KB, far more
    // than a pipe holds, so the pump's stdout blocks while this record is printed.
    prod.publish(1, 0, subj, &b"\x1b]133;A\x07".repeat(8000))
        .unwrap();

    let mut child = spawn(&[&sock, "s9", "--debounce", "600000"]);
    // Held, never read: the pipe stays open and fills.
    let _stdout = child.stdout.take().unwrap();
    // 64 MiB more output, in 1 MiB records with no marks.
    let body = vec![b'x'; MIB];
    for seq in 1..=64 {
        prod.publish(1, seq, subj, &body).unwrap();
    }

    let pid = child.id();
    let bound_kib = 40 * 1024;
    let start = Instant::now();
    let mut peak = 0;
    while start.elapsed() < Duration::from_secs(2) {
        peak = peak.max(rss_kib(pid));
        if peak > bound_kib {
            break;
        }
        thread::sleep(Duration::from_millis(50));
    }
    let _ = child.kill();
    let _ = child.wait();
    assert!(
        peak <= bound_kib,
        "a stalled reader made aspump hold {peak} KiB (bound {bound_kib} KiB): the \
         delivery thread kept reading into an unbounded queue"
    );
}
