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
fn aspump_once_exits_after_one_wake_and_commits_group_cursor() {
    let (_tmp, _b, _h, sock) = fresh("once");
    let subj = "/a/stream/term/s_once/out";
    publish_session(&sock, subj);
    let group = "/f/F/cur/n1/once";

    // Step through the three OSC-133 mark wakes one at a time via `--group ... --once`.
    for want in [
        "PROMPT_READY boffset=1",
        "COMMAND_START boffset=3",
        "COMMAND_END boffset=5 exit=0",
    ] {
        let mut child = spawn(&[
            &sock,
            "s_once",
            "--group",
            group,
            "--once",
            "--debounce",
            "600000",
        ]);
        let st = wait_bounded(&mut child, Duration::from_secs(10));
        assert_eq!(st.code(), Some(0), "stderr: {}", stderr_of(&mut child));
        let mut r = BufReader::new(child.stdout.take().unwrap());
        assert_eq!(read_lines(&mut r, 10), vec![want]);
    }

    // Publish plain output with no OSC-133 marks: `--once` waits for the debounce
    // settle wake (`QUIESCED`), prints that single line, commits its offset, and
    // exits 0 immediately without waiting for another write to hit EPIPE.
    let mut prod = Client::connect(&sock).unwrap();
    let (plain_off, _) = prod
        .publish(2, 0, subj, b"plain output without osc133\r\n")
        .unwrap();
    let mut settle_child = spawn(&[
        &sock,
        "s_once",
        "--group",
        group,
        "--once",
        "--debounce",
        "50",
    ]);
    let st = wait_bounded(&mut settle_child, Duration::from_secs(10));
    assert_eq!(
        st.code(),
        Some(0),
        "stderr: {}",
        stderr_of(&mut settle_child)
    );
    let mut r = BufReader::new(settle_child.stdout.take().unwrap());
    assert_eq!(
        read_lines(&mut r, 10),
        vec![format!("QUIESCED boffset={plain_off}")]
    );

    // Launched when caught up with no new records yet, `--once` stays parked across
    // idle debounce windows until a new record arrives and produces a wake.
    let mut parked_child = spawn(&[
        &sock,
        "s_once",
        "--group",
        group,
        "--once",
        "--debounce",
        "40",
    ]);
    thread::sleep(Duration::from_millis(150));
    assert!(
        parked_child.try_wait().unwrap().is_none(),
        "aspump --once must not exit on an idle stream before any record arrives"
    );
    let (next_off, _) = prod.publish(2, 1, subj, b"more plain output\r\n").unwrap();
    let st = wait_bounded(&mut parked_child, Duration::from_secs(10));
    assert_eq!(
        st.code(),
        Some(0),
        "stderr: {}",
        stderr_of(&mut parked_child)
    );
    let mut r = BufReader::new(parked_child.stdout.take().unwrap());
    assert_eq!(
        read_lines(&mut r, 10),
        vec![format!("QUIESCED boffset={next_off}")]
    );
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
        (vec!["--cap-file"], "--cap-file"),
        // A value that is itself a flag is a dropped value, not a group name.
        (vec!["--group", "--debounce", "50"], "--group"),
        // Two cursors, one pump: which one wins must never be guessed.
        (vec!["--group", "G", "--from", "3"], "--group"),
        // Without `--features aead` there is no sealed transport; the flag must
        // say so rather than fall back to plaintext. (Built WITH the feature this
        // still exits 2 — on the unreadable key file — and still names the flag.)
        (vec!["--key-file", "/nonexistent/aspump.key"], "--key-file"),
        (vec!["--cap-file", "/nonexistent/aspump.cap"], "--cap-file"),
        // The key/tag never travels on argv, where `ps` shows it to every local user.
        (vec!["--key", "00"], "--key"),
        (vec!["--cap-tag", "00"], "--cap-tag"),
        (vec!["--cap-filter", "ro:/a/>"], "--cap-filter"),
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

#[cfg(feature = "cap")]
#[test]
fn aspump_cap_file_attaches_and_tails_a_guarded_broker() {
    use astream_broker::{mint, producer_id_of};

    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let sock = format!("/tmp/aspump_{pid}_cap_{n}.sock");
    let log = format!("/tmp/aspump_{pid}_cap_{n}.log");
    let cap_path = format!("/tmp/aspump_{pid}_cap_{n}.cap");
    let _ = std::fs::remove_file(&log);
    let _tmp = Cleanup::new(&[&sock, &log, &cap_path]);

    let secret = b"0123456789abcdef0123456789abcdef";
    let broker = Broker::open_guarded(&log, secret.to_vec()).unwrap();
    let _h = broker.serve(&sock).unwrap();

    // Publish fixture under a write capability.
    let subj = "/a/stream/term/s_cap/out";
    let group = "/f/F/cur/n1/aspump_cap";
    let mut prod = Client::connect(&sock).unwrap();
    let w_cap = mint(secret, "rw,p=n-0102030405060708:/a/>").unwrap();
    let r_cap = mint(secret, "ro:/a/stream/term/s_cap/>").unwrap();
    let g_cap = mint(secret, "rw,p=n-0102030405060708:/f/F/cur/>").unwrap();
    prod.attach(&w_cap.filter, &w_cap.tag).unwrap();
    let pid_bound = producer_id_of("n-0102030405060708");
    for (i, body) in session().iter().enumerate() {
        prod.publish(pid_bound, (i + 1) as u64, subj, body).unwrap();
    }

    let hex = |tag: &[u8]| -> String { tag.iter().map(|b| format!("{b:02x}")).collect() };
    std::fs::write(
        &cap_path,
        format!(
            "ro:/a/stream/term/s_cap/> {}\nrw,p=n-0102030405060708:/f/F/cur/> {}\n",
            hex(&r_cap.tag),
            hex(&g_cap.tag),
        ),
    )
    .unwrap();

    let mut child = spawn(&[
        &sock,
        "s_cap",
        "--group",
        group,
        "--cap-file",
        &cap_path,
        "--debounce",
        "50",
    ]);
    let mut r = BufReader::new(child.stdout.take().unwrap());
    assert_eq!(
        read_lines(&mut r, 4),
        vec![
            "PROMPT_READY boffset=2",
            "COMMAND_START boffset=4",
            "COMMAND_END boffset=6 exit=0",
            "QUIESCED boffset=6",
        ]
    );
    let _ = child.kill();
    let _ = child.wait();
}

#[test]
fn aspump_never_echoes_a_key_given_as_flag_equals_value() {
    // `--key=HEX` is the same key-on-argv mistake as `--key HEX`; the refusal
    // must not copy the key into stderr (and whatever log collects it).
    let key: String = std::iter::repeat_n("0123456789abcdef", 4).collect();
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

/// End-to-end drive-pipe composition and crash recovery (`DESIGN-drive-pipe.md` §9 Rung 1,
/// §10):
/// Composes a real PTY child under `astream-host::Driver` (`Pty::spawn`,
/// `Driver::drive_input`, `Driver::read_and_record_chunk`), `astream-engine::Envelope`
/// over a live `astream-broker::Broker` (`/a/stream/term/<sid>/in` and `.../out`), and
/// `aspump` on a durable `--group` cursor:
/// 1. The target PTY emits an initial OSC-133 prompt mark (`PROMPT_READY boffset=0`),
///    which wakes the turn-based driver via `aspump --once --group`.
/// 2. The driver sends command 1 (`(client_id = 7, client_seq = 1, "alpha\n")`) to
///    `.../in`, reads `COMMAND_START boffset=1`, and is killed mid-session before
///    observing `COMMAND_END` or the next `PROMPT_READY`.
/// 3. The replacement driver reattaches with only the broker socket and `--group`:
///    - Re-sending command 1 (`(7, 1, "alpha\n")`) is deduplicated both at broker ingest
///      (`duplicate == true`) and at `Driver::drive_input` (`Ok(false)`), so `"alpha"`
///      reaches the PTY child at most once.
///    - Running `aspump --once --group` resumes at the durable group cursor and surfaces
///      the missed `COMMAND_END boffset=2 exit=0` and `PROMPT_READY boffset=3` in exact
///      order with nothing lost.
/// 4. The replacement driver sends command 2 (`(7, 2, "quit\n")`), observes the final
///    `COMMAND_START boffset=4` and `COMMAND_END boffset=5 exit=0`, and the `Driver`'s
///    recorded `Session` log contains exactly two `Record::In` records and folds to the
///    exact live screen.
#[test]
fn drive_pipe_e2e_crash_recovery_misses_nothing_and_dedups_pty_input() {
    use astream_engine::{Envelope, Log, MemDisk, Offset as EngOffset, Seeded};
    use astream_host::{Driver, Pty};
    use astream_term::{screen, Record as TermRecord};
    use astream_wire::Frame;

    let (_tmp, _b, _h, sock) = fresh("drive_e2e");
    let sid = "s_e2e";
    let in_subj = "/a/stream/term/s_e2e/in";
    let out_subj = "/a/stream/term/s_e2e/out";
    let group = "/f/F/cur/n1/drive_e2e";

    // Spawn the PTY before any `aspump` subprocess so fd creation and fork are serialized.
    let script = "stty -echo; printf '\\033]133;A\\007'; \
        while IFS= read -r line; do \
            if [ \"$line\" = \"quit\" ]; then \
                printf '\\033]133;C\\007BYE\\n\\033]133;D;0\\007'; \
                exit 0; \
            fi; \
            printf '\\033]133;C\\007GOT:%s\\n\\033]133;D;0\\007\\033]133;A\\007' \"$line\"; \
        done";
    let pty = Pty::spawn("/bin/sh", &["-c", script], 80, 24).expect("spawn /bin/sh on pty");
    let mut host_driver = Driver::new(pty, Seeded::new(42));

    let sock_bridge = sock.clone();
    let bridge = thread::spawn(move || {
        let mut out_prod = Client::connect(&sock_bridge).unwrap();
        let in_sub_client = Client::connect(&sock_bridge).unwrap();
        let mut in_sub = in_sub_client.subscribe(0, in_subj).unwrap();
        let mut out_seq = 0u64;
        let mut live_out = Vec::new();
        let mut dup_filtered = 0usize;

        let drain_turn = |drv: &mut Driver<Seeded>,
                          prod: &mut Client<_>,
                          seq: &mut u64,
                          collected: &mut Vec<u8>,
                          until_eof: bool| {
            let mut turn = Vec::new();
            let mut buf = [0u8; 4096];
            loop {
                let n = drv.read_and_record_chunk(&mut buf).expect("pty read");
                if n == 0 {
                    break;
                }
                turn.extend_from_slice(&buf[..n]);
                collected.extend_from_slice(&buf[..n]);
                if !until_eof && turn.ends_with(b"\x1b]133;A\x07") {
                    break;
                }
            }
            for piece in turn.split_inclusive(|&b| b == b'\x07') {
                prod.publish(1, *seq, out_subj, piece).unwrap();
                *seq += 1;
            }
        };

        // Drain initial prompt mark (`\x1b]133;A\x07` -> boffset 0):
        drain_turn(
            &mut host_driver,
            &mut out_prod,
            &mut out_seq,
            &mut live_out,
            false,
        );

        while let Some((_off, _subj, body)) = in_sub.recv().unwrap() {
            let dec = Frame::decode(&body).unwrap().unwrap();
            let env = Envelope::from_payload(&dec.frame.payload).unwrap();
            if let TermRecord::In {
                client_id,
                client_seq,
                bytes,
            } = env.record
            {
                let is_quit = bytes == b"quit\n";
                let applied = host_driver
                    .drive_input(client_id, client_seq, bytes)
                    .expect("drive_input");
                if !applied {
                    dup_filtered += 1;
                    continue;
                }
                drain_turn(
                    &mut host_driver,
                    &mut out_prod,
                    &mut out_seq,
                    &mut live_out,
                    is_quit,
                );
                if is_quit {
                    break;
                }
            }
        }
        let code = host_driver.reap().expect("reap pty child");
        (code, dup_filtered, live_out, host_driver.log_bytes())
    });

    let encode_in = |client_id: u64, client_seq: u64, bytes: &[u8]| -> Vec<u8> {
        Envelope {
            seq: EngOffset(0),
            ts_logical: 0,
            caused_by: None,
            record: TermRecord::In {
                client_id,
                client_seq,
                bytes: bytes.to_vec(),
            },
        }
        .encode()
        .unwrap()
    };

    let next_wake = || -> (String, u64) {
        let mut w = spawn(&[
            &sock,
            sid,
            "--group",
            group,
            "--once",
            "--debounce",
            "600000",
        ]);
        let st = wait_bounded(&mut w, Duration::from_secs(10));
        assert_eq!(st.code(), Some(0), "stderr: {}", stderr_of(&mut w));
        let lines = read_lines(&mut BufReader::new(w.stdout.take().unwrap()), 10);
        assert_eq!(lines.len(), 1, "expected 1 wake line, got: {lines:?}");
        let line = &lines[0];
        let (head, rest) = line.split_once(" boffset=").expect("boffset= in wake line");
        let (off_str, suffix) = match rest.split_once(' ') {
            Some((o, s)) => (o, format!(" {s}")),
            None => (rest, String::new()),
        };
        let boff: u64 = off_str.parse().expect("u64 boffset");
        (format!("{head}{suffix}"), boff)
    };

    // 1. Driver wakes on initial PROMPT_READY (boffset=0) via `aspump --once --group`:
    let (k0, off0) = next_wake();
    assert_eq!((k0.as_str(), off0), ("PROMPT_READY", 0));

    // 2. Driver publishes command 1 `(client_id=7, client_seq=1, "alpha\n")`, reads only
    // `COMMAND_START`, and is killed mid-session before reading `COMMAND_END`
    // or the next `PROMPT_READY`:
    let mut drv1 = Client::connect(&sock).unwrap();
    let in1 = encode_in(7, 1, b"alpha\n");
    let (in1_off, in1_dup) = drv1.publish(7, 1, in_subj, &in1).unwrap();
    assert!(!in1_dup);

    let (k1, off1) = next_wake();
    assert_eq!(k1, "COMMAND_START");
    assert!(off1 > off0);
    drop(drv1); // Driver 1 dies mid-turn before reading COMMAND_END or PROMPT_READY.

    // 3. Replacement driver reattaches after crash:
    // (a) Re-publishing `(producer_id=7, producer_seq=1)` on the broker dedups to `in1_off`:
    let mut drv2 = Client::connect(&sock).unwrap();
    let (retry_off, retry_dup) = drv2.publish(7, 1, in_subj, &in1).unwrap();
    assert_eq!((retry_off, retry_dup), (in1_off, true));
    // (b) Even if a bridge replay delivers the same `(client_id=7, client_seq=1)` proposal
    // in a new broker record, `Driver::drive_input` drops it at the PTY seam (`Ok(false)`):
    drv2.publish(7, 99, in_subj, &in1).unwrap();

    // (c) Replacement driver catches up from the durable `--group` cursor via `--once`,
    // receiving `COMMAND_END exit=0` and `PROMPT_READY` in order with no gap:
    let (k2, off2) = next_wake();
    assert_eq!(k2, "COMMAND_END exit=0");
    assert!(off2 > off1);
    let (k3, off3) = next_wake();
    assert_eq!(k3, "PROMPT_READY");
    assert!(off3 > off2);

    // 4. Replacement driver sends command 2 `(client_id=7, client_seq=2, "quit\n")` and
    // observes the final `COMMAND_START` and `COMMAND_END exit=0`:
    let in2 = encode_in(7, 2, b"quit\n");
    drv2.publish(7, 2, in_subj, &in2).unwrap();
    let (k4, off4) = next_wake();
    assert_eq!(k4, "COMMAND_START");
    assert!(off4 > off3);
    let (k5, off5) = next_wake();
    assert_eq!(k5, "COMMAND_END exit=0");
    assert!(off5 > off4);

    let (exit_code, dup_filtered, live_out, session_log) = bridge.join().expect("bridge panicked");
    assert_eq!(exit_code, 0);
    assert_eq!(
        dup_filtered, 1,
        "Driver::drive_input must filter the re-delivered (client_id=7, client_seq=1) proposal"
    );

    let live_text = String::from_utf8_lossy(&live_out);
    assert_eq!(
        live_text.matches("GOT:alpha").count(),
        1,
        "child executed alpha exactly once: {live_text:?}"
    );
    assert_eq!(
        live_text.matches("BYE").count(),
        1,
        "child executed quit exactly once: {live_text:?}"
    );

    let disk = MemDisk::from_bytes(session_log);
    let records: Vec<TermRecord> = Log::read_from(&disk, EngOffset::ZERO)
        .map(|r| r.unwrap().record)
        .collect();
    let in_count = records
        .iter()
        .filter(|r| matches!(r, TermRecord::In { .. }))
        .count();
    assert_eq!(
        in_count, 2,
        "Session log must record exactly the two distinct In proposals"
    );
    let from_log = screen::fold(80, 24, &records);
    let from_live = screen::fold(80, 24, &[TermRecord::Out(live_out)]);
    assert_eq!(
        from_log.serialize(),
        from_live.serialize(),
        "recorded In+Out session log must fold to the exact live PTY screen"
    );
}

/// Rung 3 (`DESIGN-drive-pipe.md` §9 Rung 3):
/// `--profile repl` and `--profile emacs` drive live non-agent programs over the
/// bus without false-waking on settled intermediate progress lines ending in `%` or `#`.
#[cfg(unix)]
#[test]
fn rung3_repl_and_emacs_profiles_drive_live_non_agent_programs_without_progress_false_wakes() {
    use astream_engine::Seeded;
    use astream_host::{Driver, Pty};
    use astream_pump::out_subject;

    let (_tmp, _b, _h, sock) = fresh("rung3_repl");

    // 1. Unknown `--profile` is rejected with exit 2.
    let mut bad = spawn(&[&sock, "s1", "--profile", "bogus"]);
    assert_eq!(
        wait_bounded(&mut bad, Duration::from_secs(5)).code(),
        Some(2),
        "stderr: {}",
        stderr_of(&mut bad)
    );

    // 2. Spawn a live non-agent REPL child on a real PTY (no OSC-133 marks).
    //    When given `work`, it prints `step 1/2` and `compiling... 50%` and pauses
    //    before printing the final `42` + `>>> ` prompt.
    let repl_script = concat!(
        "stty -echo 2>/dev/null || true; ",
        "printf '>>> '; ",
        "while IFS= read -r line; do ",
        "  case \"$line\" in ",
        "    work) printf 'step 1/2\\r\\ncompiling... 50%%\\r\\n'; sleep 0.25; printf '42\\r\\n>>> ' ;; ",
        "    quit) printf 'bye\\r\\n'; exit 0 ;; ",
        "  esac; ",
        "done"
    );
    let pty = Pty::spawn("/bin/sh", &["-c", repl_script], 80, 24).expect("spawn repl pty");
    let mut driver = Driver::new(pty, Seeded::new(77));
    let mut pub_out = Client::connect(&sock).unwrap();
    let sid = "repl0";
    let out_subj = out_subject(sid);
    let mut out_seq = 0u64;

    // Drain initial `>>> ` prompt from the PTY and publish to the broker.
    let mut buf = [0u8; 4096];
    let mut init_bytes = Vec::new();
    let start = Instant::now();
    while !String::from_utf8_lossy(&init_bytes).contains(">>> ") {
        assert!(
            start.elapsed() < Duration::from_secs(5),
            "init prompt timeout"
        );
        let n = driver.read_and_record_chunk(&mut buf).unwrap();
        if n > 0 {
            init_bytes.extend_from_slice(&buf[..n]);
            out_seq += 1;
            pub_out.publish(1, out_seq, &out_subj, &buf[..n]).unwrap();
        }
    }

    let mut repl_pump = spawn(&[&sock, sid, "--profile", "repl", "--debounce", "40"]);
    let mut repl_out = BufReader::new(repl_pump.stdout.take().unwrap());
    let mut common_pump = spawn(&[&sock, sid, "--profile", "common", "--debounce", "40"]);
    let mut common_out = BufReader::new(common_pump.stdout.take().unwrap());

    // Initial prompt wake: both `repl` and `common` emit QUIESCED + PROMPT_READY.
    let init_repl = read_lines(&mut repl_out, 2);
    let init_common = read_lines(&mut common_out, 2);
    assert!(
        init_repl.iter().any(|l| l.starts_with("PROMPT_READY ")),
        "repl profile must wake on initial >>> prompt: {init_repl:?}"
    );
    assert!(
        init_common.iter().any(|l| l.starts_with("PROMPT_READY ")),
        "common profile wakes on initial >>> prompt: {init_common:?}"
    );

    // Drive `work\n` into the live REPL PTY and forward the intermediate progress
    // (`step 1/2\r\ncompiling... 50%\r\n`) to the broker while the child sleeps.
    assert!(driver.drive_input(7, 1, b"work\n".to_vec()).unwrap());
    let mut prog_bytes = Vec::new();
    let t_prog = Instant::now();
    while !String::from_utf8_lossy(&prog_bytes).contains("compiling... 50%") {
        assert!(
            t_prog.elapsed() < Duration::from_secs(5),
            "progress timeout"
        );
        let n = driver.read_and_record_chunk(&mut buf).unwrap();
        if n > 0 {
            prog_bytes.extend_from_slice(&buf[..n]);
            out_seq += 1;
            pub_out.publish(1, out_seq, &out_subj, &buf[..n]).unwrap();
        }
    }

    // Wait for the mid-evaluation progress settle (`compiling... 50%`):
    // - `--profile common` emits QUIESCED AND a FALSE `PROMPT_READY` (because `50%` ends in `%`).
    // - `--profile repl` emits ONLY `QUIESCED` (no false `PROMPT_READY` during compute!).
    let common_mid = read_lines(&mut common_out, 2);
    assert!(
        common_mid.iter().any(|l| l.starts_with("PROMPT_READY ")),
        "negative control: common profile false-wakes on 50%: {common_mid:?}"
    );
    let repl_mid_quiesced = read_lines(&mut repl_out, 1);
    assert!(
        repl_mid_quiesced[0].starts_with("QUIESCED "),
        "repl profile emits QUIESCED on settled progress: {repl_mid_quiesced:?}"
    );

    // Forward the completion (`42\r\n>>> `) once the REPL finishes evaluating:
    let mut done_bytes = Vec::new();
    let t_done = Instant::now();
    while !String::from_utf8_lossy(&done_bytes).contains(">>> ") {
        assert!(
            t_done.elapsed() < Duration::from_secs(5),
            "completion timeout"
        );
        let n = driver.read_and_record_chunk(&mut buf).unwrap();
        if n > 0 {
            done_bytes.extend_from_slice(&buf[..n]);
            out_seq += 1;
            pub_out.publish(1, out_seq, &out_subj, &buf[..n]).unwrap();
        }
    }

    // Now `--profile repl` emits QUIESCED + PROMPT_READY at the real `>>> ` boundary!
    let repl_done = read_lines(&mut repl_out, 2);
    assert!(
        repl_done.iter().any(|l| l.starts_with("QUIESCED "))
            && repl_done.iter().any(|l| l.starts_with("PROMPT_READY ")),
        "repl profile must emit QUIESCED + PROMPT_READY only at real >>> prompt: {repl_done:?}"
    );

    // Woken driver sends `quit\n` and reaps the REPL child cleanly.
    assert!(driver.drive_input(7, 2, b"quit\n".to_vec()).unwrap());
    let _ = driver.drain_to_eof().unwrap();
    assert_eq!(driver.reap().unwrap(), 0);
    let _ = repl_pump.kill();
    let _ = repl_pump.wait();
    let _ = common_pump.kill();
    let _ = common_pump.wait();

    // 3. Also verify `--profile emacs` on an IELM session (`ELISP> ` after `100%`):
    let emacs_subj = "/a/stream/term/emacs0/out";
    pub_out
        .publish(2, 1, emacs_subj, b"\x1b[2J\x1b[Hloading... 100%")
        .unwrap();
    let mut emacs_pump = spawn(&[
        &sock,
        "--subject",
        emacs_subj,
        "--profile",
        "emacs",
        "--debounce",
        "40",
    ]);
    let mut emacs_out = BufReader::new(emacs_pump.stdout.take().unwrap());
    let emacs_prog = read_lines(&mut emacs_out, 1);
    assert!(
        emacs_prog[0].starts_with("QUIESCED "),
        "emacs profile emits only QUIESCED on 100%: {emacs_prog:?}"
    );
    pub_out.publish(2, 2, emacs_subj, b"\r\nELISP> ").unwrap();
    let emacs_ready = read_lines(&mut emacs_out, 2);
    assert!(
        emacs_ready.iter().any(|l| l.starts_with("PROMPT_READY ")),
        "emacs profile wakes on ELISP> prompt: {emacs_ready:?}"
    );
    let _ = emacs_pump.kill();
    let _ = emacs_pump.wait();
}

#[test]
fn aspump_reports_retention_gap_on_stderr_and_recovers_from_torn_escape() {
    // 1. Real Broker retention cut: records 0..3 compacted away before `aspump` attaches
    // at `--from 0`. `aspump` prints `aspump: GAP from=0 to=3 records=3` on stderr while
    // keeping stdout strictly reserved for wake lines.
    let (_tmp, broker, _handle, sock) = fresh("cli_gap");
    let subj = "/a/stream/term/gapcli/out";
    let mut prod = Client::connect(&sock).unwrap();
    for seq in 0..3u64 {
        prod.publish(1, seq, subj, b"dropped\r\n").unwrap();
    }
    assert_eq!(broker.retain_before(3).unwrap(), 3);
    prod.publish(1, 3, subj, b"\x1b]133;A\x07$ ").unwrap();

    let mut child = Command::new(env!("CARGO_BIN_EXE_aspump"))
        .args([&sock, "gapcli", "--from", "0", "--once", "--debounce", "40"])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let status = wait_bounded(&mut child, Duration::from_secs(5));
    assert!(status.success(), "aspump --once exited {status}");
    let mut stdout = String::new();
    let mut stderr = String::new();
    child
        .stdout
        .take()
        .unwrap()
        .read_to_string(&mut stdout)
        .unwrap();
    child
        .stderr
        .take()
        .unwrap()
        .read_to_string(&mut stderr)
        .unwrap();
    assert_eq!(
        stdout, "PROMPT_READY boffset=3\n",
        "stdout framing must stay pure wake lines (never GAP text): {stdout:?}"
    );
    assert!(
        stderr.contains("aspump: GAP from=0 to=3 records=unknown"),
        "stderr must report R4 addendum A9 gap notice: {stderr:?}"
    );

    // 2. Deterministic mid-stream TCP gap: pre-gap delivery leaves BOTH a torn OSC-133
    // carry (`\x1b]133;D;`) and an unterminated OSC-9 string (`\x1b]9;...`) in `aspump`'s
    // classifier; `Response::Gap(1..4)` arrives, resetting both before post-gap `0\x07>>> `.
    use astream_broker::proto::{
        decode_request, encode_delivery, encode_response, read_frame, write_frame, Gap, Request,
        Response,
    };
    use std::net::TcpListener;

    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let ep = listener.local_addr().unwrap().to_string();
    let server = thread::spawn(move || {
        let (mut conn, _) = listener.accept().unwrap();
        let ack_mark = encode_response(&Response::Mark {
            next: 0,
            head: 0,
            resume: String::new(),
            durable: None,
            oldest: None,
        });
        let f1 = read_frame(&mut conn).unwrap().unwrap();
        assert_eq!(decode_request(&f1), Some(Request::IdleMarks));
        write_frame(&mut conn, &ack_mark).unwrap();
        let f2 = read_frame(&mut conn).unwrap().unwrap();
        assert_eq!(decode_request(&f2), Some(Request::GapNotices));
        write_frame(&mut conn, &ack_mark).unwrap();
        let f3 = read_frame(&mut conn).unwrap().unwrap();
        assert!(matches!(
            decode_request(&f3),
            Some(Request::Subscribe { .. })
        ));

        write_frame(
            &mut conn,
            &encode_delivery(
                0,
                "/a/stream/term/midgap/out",
                b"\x1b[2J\x1b[Hboot\r\n\x1b]9;unterminated\x1b]133;D;",
            ),
        )
        .unwrap();
        write_frame(
            &mut conn,
            &encode_response(&Response::Gap(Gap {
                from: 1,
                to: 4,
                records: Some(3),
            })),
        )
        .unwrap();
        write_frame(
            &mut conn,
            &encode_delivery(4, "/a/stream/term/midgap/out", b"0\x07>>> "),
        )
        .unwrap();
        // Hold connection open long enough for the 40ms debounce to emit PROMPT_READY
        // and `--once` to exit cleanly before EOF.
        thread::sleep(Duration::from_millis(250));
    });

    let mut mid = Command::new(env!("CARGO_BIN_EXE_aspump"))
        .args([
            &ep,
            "midgap",
            "--tcp",
            "--profile",
            "repl",
            "--debounce",
            "40",
        ])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let status = wait_bounded(&mut mid, Duration::from_secs(5));
    assert!(status.success(), "mid-stream aspump exited {status}");
    let mut mid_out = String::new();
    let mut mid_err = String::new();
    mid.stdout
        .take()
        .unwrap()
        .read_to_string(&mut mid_out)
        .unwrap();
    mid.stderr
        .take()
        .unwrap()
        .read_to_string(&mut mid_err)
        .unwrap();
    server.join().unwrap();

    let out_lines: Vec<&str> = mid_out.lines().collect();
    assert!(
        !out_lines.iter().any(|l| l.starts_with("COMMAND_END")),
        "mid-stream gap must clear torn OSC-133 carry (no forged COMMAND_END): {out_lines:?}"
    );
    assert!(
        out_lines.contains(&"QUIESCED boffset=4") && out_lines.contains(&"PROMPT_READY boffset=4"),
        "mid-stream gap must clear State::Str so post-gap >>> wakes cleanly: {out_lines:?}"
    );
    assert!(
        mid_err.contains("aspump: GAP from=1 to=4 records=3"),
        "mid-stream stderr must report GAP from=1 to=4 records=3: {mid_err:?}"
    );
}

#[test]
fn aspump_holds_torn_dec_2026_sync_frames_force_unlatches_wedged_tui_and_emits_meta() {
    let (_tmp, _b, _h, sock) = fresh("sync2026");
    let subj = "/a/stream/term/tui1/out";

    let mut child = spawn(&[
        &sock,
        "tui1",
        "--profile",
        "shell",
        "--debounce",
        "60",
        "--meta",
    ]);
    let rx = line_stream(&mut child);
    let mut prod = Client::connect(&sock).unwrap();

    // Publish chunk 0: sets OSC 7 cwd + OSC 2 title, enters DEC ?2026h synchronized output,
    // and temporarily leaves `$ ` on screen mid-redraw.
    let (off0, _) = prod
        .publish(
            1,
            0,
            subj,
            b"\x1b]7;file://host/fixture-home/my%20proj\x07\x1b]2;claude TUI\x07\x1b[?2026h$ ",
        )
        .unwrap();
    assert_eq!(off0, 0);

    // Wait 110ms (~1.8 debounce windows, < MAX_SYNC_HOLD_TICKS=4): no torn wake may fire!
    assert!(
        rx.recv_timeout(Duration::from_millis(110)).is_err(),
        "aspump must hold settle wakes while DEC ?2026h synchronized frame is mid-flight"
    );

    // Publish chunk 1: finishes redrawing to `$ ` and commits `\x1b[?2026l`.
    let (off1, _) = prod.publish(1, 1, subj, b"\rready $ \x1b[?2026l").unwrap();
    assert_eq!(off1, 1);

    let w1 = next_line(&rx, "QUIESCED after ?2026l commit");
    let w2 = next_line(&rx, "PROMPT_READY after ?2026l commit");
    assert_eq!(
        w1,
        "QUIESCED boffset=1 cwd=/fixture-home/my%20proj title=claude%20TUI"
    );
    assert_eq!(
        w2,
        "PROMPT_READY boffset=1 cwd=/fixture-home/my%20proj title=claude%20TUI"
    );

    // Now simulate a crashed/wedged TUI that sends `\x1b[?2026h` + output and never closes it:
    // after MAX_SYNC_HOLD_TICKS (4 * 60ms = 240ms + 1 settle tick), aspump force-quiesces!
    let (off2, _) = prod
        .publish(1, 2, subj, b"\x1b[?2026h\r\ncrashed $ ")
        .unwrap();
    assert_eq!(off2, 2);
    let w3 = next_line(&rx, "force-unlatched QUIESCED on wedged ?2026h");
    let w4 = next_line(&rx, "force-unlatched PROMPT_READY on wedged ?2026h");
    assert_eq!(
        w3,
        "QUIESCED boffset=2 cwd=/fixture-home/my%20proj title=claude%20TUI"
    );
    assert_eq!(
        w4,
        "PROMPT_READY boffset=2 cwd=/fixture-home/my%20proj title=claude%20TUI"
    );

    let _ = child.kill();
    let _ = child.wait();
}
