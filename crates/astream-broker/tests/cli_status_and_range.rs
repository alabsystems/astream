//! Regressions on the `asb` shell face: the two ways a verb LIED about what
//! it had done, and the sentences that said the opposite of the code.
//!
//! * A stdout write error made `pub`, `ack`, `commit`, `mint` and `repair` PANIC —
//!   exit 101 with a Rust backtrace — where every read verb surfaced the same
//!   failure as a clean exit 1. 101 is none of the three statuses this binary's
//!   contract enumerates, and for `pub` (whose default sequence is a fresh
//!   timestamp) a supervisor that guesses "retry" puts the record on the bus twice.
//!   `eprintln!` panics the same way, so a run whose STDERR was also gone exited 101
//!   out of the code that was reporting the clean status — usage errors included.
//! * `commit <upto>` and `ack <offset>` were passed straight through with no range
//!   check at all. A consumer group's committed offset is monotone by design and no
//!   verb lowers it, so `asb commit <ep> G 999999` exited 0 and durably skipped G
//!   past every record it had not read, with no recovery but a new group name.
//! * The `ack` arm's comment claimed `astream_broker::ack` still keys on the BARE
//!   input offset — the divergence the shared `ACK_SEQ_BASE` key closed, contradicted by this same
//!   file's module header, by `client.rs`, and by the claim built on their
//!   agreement. `last`'s face promised `--max` was the ONLY bound on its answer when
//!   the head pin silently omits a superseded subject and asb makes no paired read.
//!
//! No sleeps. The dead-stdout cases close the pipe's READ end BEFORE the child is
//! spawned, so the write cannot race the close; everything else synchronizes on the
//! serve readiness line and on records the log already holds.
#![cfg(unix)]

use std::io::{BufRead, BufReader, Write};
use std::process::{Child, Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);

/// The mint secret a guarded broker is opened with, and `asb mint` seals with.
#[cfg(feature = "cap")]
const SECRET: &[u8] = b"r4-mint-secret-0123456789abcdef-r4";

struct Paths {
    sock: String,
    log: String,
    dir: std::path::PathBuf,
}

fn fresh(tag: &str) -> Paths {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let dir = std::env::temp_dir().join(format!("asbr4_{tag}_{pid}_{n}"));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    Paths {
        sock: dir.join("b.sock").to_str().unwrap().to_string(),
        log: dir.join("b.log").to_str().unwrap().to_string(),
        dir,
    }
}

impl Paths {
    fn file(&self, name: &str, contents: &str) -> String {
        let p = self.dir.join(name);
        std::fs::write(&p, contents).unwrap();
        // 0600: `asb` refuses a secret file anyone but its owner can read, and
        // nothing in this test needs a wider mode.
        std::fs::set_permissions(&p, std::os::unix::fs::PermissionsExt::from_mode(0o600)).unwrap();
        p.to_str().unwrap().to_string()
    }
}

impl Drop for Paths {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

fn asb() -> Command {
    Command::new(env!("CARGO_BIN_EXE_asb"))
}

fn stdout(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}

fn stderr(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

/// A serving broker; killed and reaped on drop.
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

fn run(args: &[&str]) -> Output {
    asb().args(args).output().unwrap()
}

fn publish(sock: &str, subject: &str, seq: &str, body: &[u8]) -> Output {
    let mut c = asb()
        .args(["pub", sock, subject, "--id", "7", "--seq", seq])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    c.stdin.take().unwrap().write_all(body).unwrap();
    c.wait_with_output().unwrap()
}

/// The broker's visible head, read the way an operator would: `fetch --max 0` is the
/// documented head query, and its `MARK next=<n> head=<h>` is the answer.
fn head(sock: &str) -> u64 {
    let out = run(&["fetch", sock, "/a/>", "--max", "0"]);
    assert_eq!(out.status.code(), Some(0), "{}", stderr(&out));
    let s = stdout(&out);
    let mark = s.lines().last().expect("a MARK line");
    mark.rsplit_once("head=")
        .expect("head= in the MARK")
        .1
        .trim()
        .parse()
        .expect("a numeric head")
}

// ---------------------------------------------------------------------------
// A stdout (or stderr) whose reader is already gone.
// ---------------------------------------------------------------------------

/// A stdio handle whose READ END IS ALREADY CLOSED, so the child's first write to it
/// fails with `EPIPE`.
///
/// This is the determinism the house rules ask for: the reader is dropped BEFORE
/// `spawn`, so there is no window in which the child could write successfully and no
/// sleep anywhere. (`std::io::pipe` is std — no dependency, no `unsafe`.)
fn dead() -> Stdio {
    let (r, w) = std::io::pipe().expect("pipe");
    drop(r);
    Stdio::from(w)
}

/// Run `asb` with a stdout nothing is reading. `stdin_bytes` feeds the verbs that
/// read a body; stderr is captured so the assertion can name what came out.
fn run_dead_stdout(args: &[&str], stdin_bytes: &[u8]) -> Output {
    let mut c = asb()
        .args(args)
        .stdin(Stdio::piped())
        .stdout(dead())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    c.stdin.take().unwrap().write_all(stdin_bytes).unwrap();
    c.wait_with_output().unwrap()
}

/// The same, with NEITHER stream readable — the shape `asb ... 2>&1 | head -0` and a
/// supervisor that closes both pipes produce.
fn run_dead_both(args: &[&str], stdin_bytes: &[u8]) -> Output {
    let mut c = asb()
        .args(args)
        .stdin(Stdio::piped())
        .stdout(dead())
        .stderr(dead())
        .spawn()
        .unwrap();
    c.stdin.take().unwrap().write_all(stdin_bytes).unwrap();
    c.wait_with_output().unwrap()
}

/// EVERY VERB THAT PRINTS ONE LINE SURFACES A STDOUT WRITE ERROR AS EXIT 1.
///
/// `println!` panics on a write error: `asb pub $ep $subj | head -0`, or `> ` a full
/// disk, printed `thread 'main' panicked at ... failed printing to stdout: Broken
/// pipe` and exited 101. The read verbs never did — they write through `writeln!` +
/// `?` — so one binary reported the same failure two ways, and 101 is a status the
/// exit contract does not define. This asserts the write verbs now agree with the
/// read verbs, and that no panic text reaches stderr.
///
/// `pub`'s case is the one with teeth: the record IS durably on the log by the time
/// the print fails, and `pub`'s default sequence is a fresh timestamp, so a supervisor
/// that retries duplicates it. The status alone cannot say that, so the fact is
/// repeated on stderr with the instruction not to retry — asserted here, because a
/// wrapper that has lost stdout has nothing else left to read.
#[test]
fn a_dead_stdout_is_exit_1_on_every_verb_never_a_panic() {
    let p = fresh("deadout");
    let _b = serve(&p);

    // A record to ack, and a group to commit.
    let out = publish(&p.sock, "/a/x", "1", b"one");
    assert_eq!(stdout(&out), "0 new\n", "{}", stderr(&out));

    let cases: Vec<(Vec<String>, &[u8], &str)> = vec![
        (
            ["pub", &p.sock, "/a/x", "--id", "7", "--seq", "2"]
                .iter()
                .map(|s| (*s).to_string())
                .collect(),
            b"two",
            "the record IS on the log",
        ),
        (
            [
                "ack", &p.sock, "/a/g", "0", "/a/back", "handled", "--id", "9",
            ]
            .iter()
            .map(|s| (*s).to_string())
            .collect(),
            b"",
            "the group cursor HAS advanced",
        ),
        (
            ["commit", &p.sock, "/a/g2", "0"]
                .iter()
                .map(|s| (*s).to_string())
                .collect(),
            b"",
            "the group cursor HAS advanced",
        ),
    ];

    for (args, body, note) in &cases {
        let argv: Vec<&str> = args.iter().map(String::as_str).collect();
        let out = run_dead_stdout(&argv, body);
        let err = stderr(&out);
        assert_eq!(
            out.status.code(),
            Some(1),
            "`asb {}` on a dead stdout must exit 1 like the read verbs, not panic: {err}",
            argv[0]
        );
        assert!(
            !err.contains("panicked"),
            "`asb {}` panicked on a stdout write error: {err}",
            argv[0]
        );
        assert!(
            err.contains(note),
            "`asb {}` must repeat the durable fact on stderr, since stdout is gone: {err}",
            argv[0]
        );
        assert!(
            err.contains("Do NOT retry"),
            "`asb {}` must say the effect is already durable: {err}",
            argv[0]
        );
    }

    // `repair` writes no durable change on a clean log, but it still must not panic.
    let clean = p.file("clean.log", "");
    let out = run_dead_stdout(&["repair", &clean], b"");
    assert_eq!(
        out.status.code(),
        Some(1),
        "repair on a dead stdout: {}",
        stderr(&out)
    );
    assert!(!stderr(&out).contains("panicked"), "{}", stderr(&out));
}

/// `asb mint` prints the one line a `--cap-file` holds, and it printed it with
/// `println!` too — so a `asb mint ... | head -0` exited 101 with a backtrace where
/// the operator expected a status. Minting touches no broker and is deterministic, so
/// the failure is a plain exit 1: re-run it.
#[cfg(feature = "cap")]
#[test]
fn mint_on_a_dead_stdout_is_exit_1_never_a_panic() {
    let p = fresh("deadmint");
    let secret = p.file("mint.secret", std::str::from_utf8(SECRET).unwrap());
    let out = run_dead_stdout(&["mint", "ro:/f/F/pub/>", "--secret-file", &secret], b"");
    let err = stderr(&out);
    assert_eq!(out.status.code(), Some(1), "mint on a dead stdout: {err}");
    assert!(!err.contains("panicked"), "mint panicked: {err}");
}

/// A DEAD STDERR IS NOT A PANIC EITHER — including out of `usage_error`.
///
/// `eprintln!` panics on a write error exactly as `println!` does, so the fix above
/// would only have MOVED the panic: a stdout error propagates to `main`, which
/// reports it on stderr, which is also gone. Worse, it was already reachable without
/// any of that — a plain strict-flag refusal with stderr closed exited 101 instead of
/// 2, which is precisely the status confusion `pump.cli.argv-not-utf8` exists to
/// reject. A diagnostic that cannot be delivered is dropped; the status survives.
#[test]
fn a_dead_stderr_keeps_the_status_it_was_reporting() {
    let p = fresh("deaderr");
    let _b = serve(&p);

    // A usage error with nowhere to print it is still exit 2.
    let out = run_dead_both(&["pub", &p.sock, "/a/x", "--seq", "nope"], b"");
    assert_eq!(
        out.status.code(),
        Some(2),
        "a strict-flag refusal with stderr closed must stay exit 2"
    );

    // A read verb whose stdout AND stderr are gone is still exit 1.
    let out = run_dead_both(&["fetch", &p.sock, "/a/>"], b"");
    assert_eq!(
        out.status.code(),
        Some(1),
        "a read verb with both streams closed must stay exit 1"
    );

    // And a write verb: the durable-fact note has nowhere to go, and that is fine —
    // the status is the part that survives. (A record first, so `commit 0` names one:
    // an <upto> at or past the head is a usage error, which is a different test.)
    let out = publish(&p.sock, "/a/x", "1", b"one");
    assert_eq!(stdout(&out), "0 new\n", "{}", stderr(&out));
    let out = run_dead_both(&["commit", &p.sock, "/a/g3", "0"], b"");
    assert_eq!(
        out.status.code(),
        Some(1),
        "a write verb with both streams closed must stay exit 1"
    );
}

/// AN `<upto>` PAST THE HEAD IS REFUSED, AND NOTHING IS COMMITTED.
///
/// `BrokerLog::commit` appends whatever `upto` it is handed and `group_start` is
/// `upto + 1` with no clamp; the cursor is monotone by design and no asb verb and no
/// broker request lowers it. So this used to exit 0 printing `<offset> committed`,
/// and the group was durably skipped past records it had never seen — the drain below
/// came back `n=0` forever while a fresh group over the same filter was handed
/// everything. The only recovery was to abandon the group name.
#[test]
fn commit_past_the_visible_head_is_a_usage_error_and_changes_nothing() {
    let p = fresh("range");
    let _b = serve(&p);
    for (i, body) in [&b"one"[..], b"two", b"three"].iter().enumerate() {
        let out = publish(&p.sock, "/a/x", &(i + 1).to_string(), body);
        assert_eq!(stdout(&out), format!("{i} new\n"), "{}", stderr(&out));
    }
    let before = head(&p.sock);
    assert_eq!(before, 3);

    let group = "/a/g9";
    let out = run(&["commit", &p.sock, group, "999999"]);
    assert_eq!(
        out.status.code(),
        Some(2),
        "an <upto> past the head is a usage error: {}",
        stderr(&out)
    );
    assert_eq!(stdout(&out), "", "nothing on stdout for a refusal");
    assert!(
        stderr(&out).contains("at or past the broker's visible head 3"),
        "the refusal names the head it checked against: {}",
        stderr(&out)
    );

    // NOTHING WAS APPENDED: no commit record, so the head has not moved.
    assert_eq!(head(&p.sock), before, "a refused commit appends nothing");

    // AND THE GROUP IS UNTOUCHED: it still starts at 0 and is handed every record.
    let out = run(&["drain", &p.sock, group, "/a/>", "--idle", "250"]);
    assert_eq!(out.status.code(), Some(0), "{}", stderr(&out));
    assert!(
        stdout(&out).ends_with("DRAIN n=3 upto=2 committed=yes\n"),
        "the group must not have been skipped past its records: {}",
        stdout(&out)
    );

    // The last real offset is still accepted — the check is one-sided, and the happy
    // path is exactly what a fix like this must not break.
    let out = run(&["commit", &p.sock, group, "2"]);
    assert_eq!(out.status.code(), Some(0), "{}", stderr(&out));
    assert!(stdout(&out).ends_with(" committed\n"), "{}", stdout(&out));
}

/// THE SAME OPERAND ON `ack`, WHICH DOES IT IN ONE SHOT.
///
/// `asb ack <ep> G <offset> <subject> handled` advances G past `<offset>` in the same
/// durable append as the answer record, so an out-of-range `<offset>` skipped an inbox
/// AND put an answer on the bus, at exit 0. A wrapper interpolating a stale shell
/// variable was all it took.
#[test]
fn ack_past_the_visible_head_is_a_usage_error_and_appends_nothing() {
    let p = fresh("ackrange");
    let _b = serve(&p);
    for (i, body) in [&b"ask-a"[..], b"ask-b"].iter().enumerate() {
        let out = publish(&p.sock, "/a/in", &(i + 1).to_string(), body);
        assert_eq!(stdout(&out), format!("{i} new\n"), "{}", stderr(&out));
    }
    let before = head(&p.sock);

    let group = "/a/g8";
    let out = run(&[
        "ack", &p.sock, group, "500", "/a/back", "handled", "--id", "5",
    ]);
    assert_eq!(
        out.status.code(),
        Some(2),
        "an <offset> past the head is a usage error: {}",
        stderr(&out)
    );
    assert_eq!(stdout(&out), "", "nothing on stdout for a refusal");
    assert_eq!(head(&p.sock), before, "a refused ack appends nothing");

    // The group never moved: both asks are still delivered.
    let out = run(&["drain", &p.sock, group, "/a/in", "--peek", "--idle", "250"]);
    assert!(
        stdout(&out).ends_with("DRAIN n=2 upto=1 committed=no\n"),
        "the inbox must not have been skipped: {}",
        stdout(&out)
    );

    // A real offset still acks, and its retry still dedups — the head probe must not
    // have disturbed the idempotency this verb exists for.
    let first = run(&[
        "ack", &p.sock, group, "0", "/a/back", "handled", "--id", "5",
    ]);
    assert_eq!(first.status.code(), Some(0), "{}", stderr(&first));
    let at = stdout(&first);
    assert!(at.ends_with(" new\n"), "{at}");
    let retry = run(&[
        "ack", &p.sock, group, "0", "/a/back", "handled", "--id", "5",
    ]);
    assert_eq!(
        stdout(&retry),
        at.replace(" new\n", " dup\n"),
        "a retried ack still dedups to its original offset: {}",
        stderr(&retry)
    );
}

/// A GROUP NAME THAT IS NOT A SUBJECT IS REFUSED BY `commit`, NAMING WHY.
///
/// The head probe reads under the group name, which is what makes it authorized by
/// the same grant the commit is (a guarded broker checks `grants_commit`, which needs
/// the name to parse as a SUBJECT). A name that is not even a valid FILTER can be
/// probed by nothing and committed under no capability, so it is refused here — where
/// the operator can read why — rather than silently dropping the range check.
#[test]
fn commit_refuses_a_group_name_that_is_not_a_subject() {
    let p = fresh("groupshape");
    let _b = serve(&p);
    let out = run(&["commit", &p.sock, "g9", "0"]);
    assert_eq!(out.status.code(), Some(2), "{}", stderr(&out));
    assert!(
        stderr(&out).contains("is not a valid subject"),
        "{}",
        stderr(&out)
    );
}

/// THE HEAD PROBE MUST NOT BREAK A GUARDED BROKER — the way this project's fixes
/// usually break something.
///
/// `commit` and `ack` now ask the broker for its visible head before they act, and a
/// guarded broker authorizes that `Fetch` by `grants_filter` while it authorizes the
/// `Commit`/`ProcessAndProduce` by `grants_commit`/`grants_publish`. Those are the
/// same question for a wildcard-free name, which is exactly why the probe reads under
/// the GROUP (for `commit`) and the OUTPUT SUBJECT (for `ack`) rather than under some
/// wider filter of asb's choosing: a probe on `/>` would have turned every guarded
/// commit into `unauthorized`. Asserted against a real guarded broker with a ring
/// that grants nothing wider than one node's subtree.
#[cfg(feature = "cap")]
#[test]
fn the_head_probe_is_authorized_by_the_same_grant_the_operation_is() {
    use astream_broker::Broker;
    let p = fresh("guardedhead");
    let broker = Broker::open_guarded(&p.log, SECRET.to_vec()).unwrap();
    let _h = broker.serve(&p.sock).unwrap();

    let node = "n-a1b2c3d4e5f60718";
    let grant = format!("rw,p={node}:/f/F/{node}/>");
    let tag: String = astream_cap::mint(SECRET, &grant)
        .unwrap()
        .tag
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    let ring = p.file("node.cap", &format!("{grant} {tag}\n"));

    let inbox = format!("/f/F/{node}/in/ask");
    let back = format!("/f/F/{node}/out/ack");
    let group = format!("/f/F/{node}/cur/inbox");

    // One ask on the node's own lane, published under the bound grant.
    let mut c = asb()
        .args(["pub", &p.sock, &inbox, "--seq", "1", "--cap-file", &ring])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    c.stdin.take().unwrap().write_all(b"v=1 ask").unwrap();
    let out = c.wait_with_output().unwrap();
    let line = stdout(&out);
    assert!(line.ends_with(" new\n"), "{line}{}", stderr(&out));
    // NOT necessarily offset 0: a guarded broker durably records the attach's derived
    // producer binding before it authorizes anything, and that record takes an offset.
    let ask = line.split_whitespace().next().unwrap().to_string();

    // `ack` probes under the OUTPUT SUBJECT, which this ring grants.
    let out = run(&[
        "ack",
        &p.sock,
        &group,
        &ask,
        &back,
        "handled",
        "--cap-file",
        &ring,
    ]);
    assert_eq!(
        out.status.code(),
        Some(0),
        "the ack's head probe must not be refused by the ring that permits the ack: {}",
        stderr(&out)
    );

    // `commit` probes under the GROUP NAME, which this ring grants as a subject.
    let out = run(&["commit", &p.sock, &group, &ask, "--cap-file", &ring]);
    assert_eq!(
        out.status.code(),
        Some(0),
        "the commit's head probe must not be refused by the ring that permits the commit: {}",
        stderr(&out)
    );
}

/// THE HONESTY GATE, on two sentences that once said the opposite of the code.
///
/// Both are first-rank defects here, not typos: one told a maintainer that the two
/// faces of a DURABLE dedup key still disagree (they share one derivation, and a
/// third face written to match the comment would silently double every ack that
/// crossed it), and one told an operator that `--max` was the only thing that could
/// shorten a `last` answer, when a subject superseded past a request's pinned head is
/// omitted from that page and `asb last` makes no paired read to fill it in.
///
/// A comment cannot be exercised, so it is asserted where it lives. The derivation
/// half is checked against `client.rs` in the same breath, so this fails if either
/// face moves away from the shared constant.
#[test]
fn the_asb_face_never_states_the_opposite_of_the_code_it_annotates() {
    let asb = include_str!("../src/bin/asb.rs");
    let client = include_str!("../src/client.rs");

    // ONE derivation, from ONE exported constant, on both faces.
    assert!(
        client.contains("ACK_SEQ_BASE | offset"),
        "the library helper must still derive the ack key from ACK_SEQ_BASE"
    );
    assert!(
        asb.contains("ACK_SEQ_BASE | offset"),
        "asb must still derive the ack key from the SAME exported constant"
    );
    assert!(
        !asb.contains("keys on the BARE input offset"),
        "asb still tells a reader that `astream_broker::ack` keys on the bare offset — \
         it derives from ACK_SEQ_BASE (client.rs), and this file's own module \
         header says so twenty lines above the call site"
    );
    assert!(
        asb.contains("broker.ack-key-is-one-wire-contract"),
        "the ack site should point at the claim that pins the agreement"
    );

    // `last`'s completeness contract is `--max` PLUS a paired read, never `--max`.
    for stale in [
        "`--max` is the only bound on the answer",
        "--max is its only bound",
        "`--max` is the ONLY\n/// limit",
        "a contract with no hidden bound in it",
    ] {
        assert!(
            !asb.contains(stale),
            "asb still promises {stale:?}: the head pin omits a subject superseded past \
             it, and `asb last` performs no paired `sub --from <next>` to fill it in"
        );
    }
    assert!(
        asb.contains("OMITTED"),
        "the asb face must say that a superseded subject is omitted from its page"
    );
    assert!(
        asb.contains("UNION of per-request snapshots"),
        "the asb face must say the printed answer is a union of per-request snapshots \
         reported under the FIRST request's head"
    );
}
