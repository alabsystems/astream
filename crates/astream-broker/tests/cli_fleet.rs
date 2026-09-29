//! Claim `broker.cli.fleet-verbs`: the shell face of the fabric — `asb mint`,
//! `--cap-file`, `last`, `fetch`, `drain`, `ack` and `pub --seq-file`.
//!
//! Everything here is a real `asb` subprocess against a real broker over a real
//! Unix socket, synchronized on the serve readiness line and on the records the
//! log already holds — no sleeps except the explicit `--idle` window `drain` is
//! defined by. Byte-exact stdout is asserted wherever the framing is the point,
//! because a bridge in another language parses these bytes.
#![cfg(unix)]

use std::io::{BufRead, BufReader, Write};
use std::process::{Child, Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);

/// The mint secret a guarded broker is opened with, and `asb mint` seals with.
#[cfg(feature = "cap")]
const SECRET: &[u8] = b"fleet-mint-secret-0123456789abcdef";

struct Paths {
    sock: String,
    log: String,
    dir: std::path::PathBuf,
}

fn fresh(tag: &str) -> Paths {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let dir = std::env::temp_dir().join(format!("asbfleet_{tag}_{pid}_{n}"));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    Paths {
        sock: dir.join("b.sock").to_str().unwrap().to_string(),
        log: dir.join("b.log").to_str().unwrap().to_string(),
        dir,
    }
}

impl Drop for Paths {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

impl Paths {
    /// A path inside this test's own scratch directory.
    fn file(&self, name: &str, contents: &str) -> String {
        let p = self.dir.join(name);
        std::fs::write(&p, contents).unwrap();
        // 0600: `asb` refuses a secret file anyone but its owner can read, and
        // nothing in this test needs a wider mode.
        std::fs::set_permissions(&p, std::os::unix::fs::PermissionsExt::from_mode(0o600)).unwrap();
        p.to_str().unwrap().to_string()
    }
}

fn asb() -> Command {
    Command::new(env!("CARGO_BIN_EXE_asb"))
}

/// Run `asb` with `args` and no stdin.
fn run(args: &[&str]) -> Output {
    asb()
        .args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .unwrap()
}

fn stdout(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}
fn stderr(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

/// Assert a usage error: exit 2, the reason on stderr, nothing on stdout.
fn refused(args: &[&str], want: &str) {
    let out = run(args);
    assert_eq!(out.status.code(), Some(2), "{args:?}: {}", stderr(&out));
    assert!(
        stderr(&out).contains(want),
        "{args:?}: stderr {:?} should mention {want:?}",
        stderr(&out)
    );
    assert!(stdout(&out).is_empty(), "{args:?}: nothing on stdout");
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

/// `asb pub` with stdin = body.
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

/// The log offset an `asb pub` landed at. Offsets are NOT guessable from the
/// publish order alone: a durable commit is itself a record, and so is the hidden
/// `/a/bind` row a bound grant's first attach appends — both take an offset while
/// being invisible to delivery. So every expectation reads the offset back.
fn pub_offset(o: &Output) -> u64 {
    let s = stdout(o);
    let (offset, state) = s.trim_end().split_once(' ').unwrap_or_else(|| {
        panic!("pub printed {s:?} (stderr {:?})", stderr(o));
    });
    assert_eq!(state, "new", "expected a fresh record: {s:?}");
    offset.parse().unwrap()
}

/// The wildcard-read framing `last`/`fetch`/`drain` print, as raw bytes:
/// `<offset> <nbytes> <subject>\n<body>\n`. The COUNT precedes the SUBJECT because
/// the subject is the one header field a publisher chooses byte for byte, and the
/// wire lets it hold a space; with both numbers first the subject is simply the rest
/// of the line and no publisher can spell a header.
fn framed(offset: u64, subject: &str, body: &[u8]) -> Vec<u8> {
    let mut v = format!("{offset} {} {subject}\n", body.len()).into_bytes();
    v.extend_from_slice(body);
    v.push(b'\n');
    v
}

#[cfg(feature = "cap")]
fn tag_hex(grant: &str) -> String {
    astream_cap::mint(SECRET, grant)
        .unwrap()
        .tag
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

// ---------------------------------------------------------------- asb mint

/// `asb mint` will not guess a mode. A bare filter IS a valid grant — the
/// READ-WRITE, UNBOUND god cap, which may publish under any producer id — so the
/// careless spelling is refused and the dangerous one has to be asked for by
/// name. The secret reaches mint through a file or an environment variable and
/// never through argv.
///
/// Every case here is settled BEFORE any MAC is computed, so it holds on a build
/// without the `cap` feature too — which is where a footgun would otherwise hide.
#[test]
fn asb_mint_refuses_a_bare_filter_and_a_secret_on_argv() {
    let p = fresh("mintrefuse");
    let content = "fleet-mint-secret-0123456789abcdef";
    let secret = p.file("secret", content); // a file is the secret, byte for byte

    // A bare filter is refused, and the message spells both safe alternatives.
    let out = run(&["mint", "/f/F/pub/>", "--secret-file", &secret]);
    assert_eq!(out.status.code(), Some(2), "{}", stderr(&out));
    let err = stderr(&out);
    assert!(err.contains("READ-WRITE, UNBOUND grant"), "{err}");
    assert!(
        err.contains("ro:/f/F/pub/>"),
        "names the read-only spelling"
    );
    assert!(
        err.contains("rw,p=<principal>:"),
        "names the bound spelling"
    );
    assert!(err.contains("--legacy-unbound"), "names the opt-in");

    // ...and the opt-in is not a no-op decoration on a grant that binds or reads.
    refused(
        &[
            "mint",
            "ro:/f/F/>",
            "--legacy-unbound",
            "--secret-file",
            &secret,
        ],
        "--legacy-unbound applies only to the READ-WRITE, UNBOUND grant",
    );

    // The secret is required, and it may not ride on argv (where `ps` shows it).
    refused(
        &["mint", "ro:/f/F/>"],
        "mint needs the broker's mint secret",
    );
    refused(
        &[
            "mint",
            "ro:/f/F/>",
            "--secret",
            "fleet-mint-secret-0123456789abcdef",
        ],
        "--secret on argv is refused",
    );
    // A transport flag has no meaning for an offline verb.
    refused(
        &["mint", "ro:/f/F/>", "--secret-file", &secret, "--tcp"],
        "--tcp does not apply to mint",
    );
}

/// What `asb mint` prints IS the `--cap-file` line: `<grant> <tag-hex>`, sealed
/// with exactly the tag `astream_cap::mint` computes. Minting needs the same
/// vetted MAC the broker verifies with, so this half is `cap`-gated.
#[cfg(feature = "cap")]
#[test]
fn asb_mint_prints_the_capability_line_a_cap_file_holds() {
    let p = fresh("mint");
    let content = "fleet-mint-secret-0123456789abcdef";
    let secret = p.file("secret", content);

    for grant in [
        "ro:/f/F/pub/>",
        "rw,p=n-a1b2c3d4e5f60718:/f/F/pub/n-a1b2c3d4e5f60718/>",
    ] {
        let out = run(&["mint", grant, "--secret-file", &secret]);
        assert_eq!(out.status.code(), Some(0), "{}", stderr(&out));
        assert_eq!(stdout(&out), format!("{grant} {}\n", tag_hex(grant)));
    }

    // The god cap is still mintable — deliberately, and only by name.
    let out = run(&[
        "mint",
        "/f/F/>",
        "--legacy-unbound",
        "--secret-file",
        &secret,
    ]);
    assert_eq!(out.status.code(), Some(0), "{}", stderr(&out));
    assert_eq!(stdout(&out), format!("/f/F/> {}\n", tag_hex("/f/F/>")));

    // THE OTHER SPELLING OF THE SAME AUTHORITY. `rw:<filter>` parses to exactly the
    // grant `<filter>` parses to — read-write with NO bound principal, which
    // `grants_publish` lets publish under ANY producer id — so the gate reads the
    // PARSED grant, not the leading character. A gate on the spelling refuses the
    // careless command and mints fleet root for the one-character-different one.
    let out = run(&["mint", "rw:/f/F/>", "--secret-file", &secret]);
    assert_eq!(
        out.status.code(),
        Some(2),
        "rw: with no ,p= is the god cap: {}",
        stdout(&out)
    );
    let err = stderr(&out);
    assert!(err.contains("READ-WRITE, UNBOUND grant"), "{err}");
    assert!(
        err.contains("ro:/f/F/>"),
        "names the read-only spelling: {err}"
    );
    assert!(
        err.contains("rw,p=<principal>:"),
        "names the bound spelling: {err}"
    );
    assert!(err.contains("--legacy-unbound"), "names the opt-in: {err}");

    // ...and the opt-in applies to it, because it IS the unbound grant.
    let out = run(&[
        "mint",
        "rw:/f/F/>",
        "--legacy-unbound",
        "--secret-file",
        &secret,
    ]);
    assert_eq!(out.status.code(), Some(0), "{}", stderr(&out));
    assert_eq!(
        stdout(&out),
        format!("rw:/f/F/> {}\n", tag_hex("rw:/f/F/>"))
    );

    // A grant that BINDS a principal is not the god cap in either direction.
    refused(
        &[
            "mint",
            "rw,p=n-a1b2c3d4e5f60718:/f/F/>",
            "--legacy-unbound",
            "--secret-file",
            &secret,
        ],
        "--legacy-unbound applies only to the READ-WRITE, UNBOUND grant",
    );

    // An unparseable grant is a usage error, not a tag over nonsense.
    refused(
        &[
            "mint",
            "rw,p=NOT_A_PRINCIPAL:/f/F/>",
            "--secret-file",
            &secret,
        ],
        "mint: invalid principal",
    );
    refused(
        &["mint", "ro:not-a-filter", "--secret-file", &secret],
        "mint: invalid filter",
    );

    // The environment form works and matches the file form byte for byte.
    let out = asb()
        .args(["mint", "ro:/f/F/>", "--secret-env", "ASB_TEST_MINT"])
        .env("ASB_TEST_MINT", "fleet-mint-secret-0123456789abcdef")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(0), "{}", stderr(&out));
    assert_eq!(
        stdout(&out),
        format!("ro:/f/F/> {}\n", tag_hex("ro:/f/F/>"))
    );
}

// -------------------------------------------------------- asb last / fetch

/// `last` is retained state and `fetch` is a bounded read, and BOTH print the
/// subject in the header where `sub` does not: they are subtree queries whose
/// answers span subjects, so a wildcard drain that had to guess which subject a
/// record came from could not route it. Each ends with `MARK next= head=`.
#[test]
fn asb_last_and_fetch_print_subject_framed_pages_then_a_mark() {
    let p = fresh("read");
    let _s = serve(&p);

    let a = "/f/F/pub/n-a1/presence";
    let b = "/f/F/pub/n-b2/presence";
    let out_of_filter = "/f/F/fleet/h-andrew/halt";
    // A body with a NUL and a newline, to prove the framing is byte-exact.
    let a2: &[u8] = b"v=1 inc=2\x00state=live\ntail";
    assert_eq!(
        stdout(&publish(&p, a, &["--id", "1", "--seq", "1"], b"v=1 inc=1")),
        "0 new\n"
    );
    assert_eq!(
        stdout(&publish(&p, b, &["--id", "1", "--seq", "2"], b"v=1 inc=1")),
        "1 new\n"
    );
    assert_eq!(
        stdout(&publish(&p, a, &["--id", "1", "--seq", "3"], a2)),
        "2 new\n"
    );
    assert_eq!(
        stdout(&publish(
            &p,
            out_of_filter,
            &["--id", "1", "--seq", "4"],
            b"state=on"
        )),
        "3 new\n"
    );

    // LAST: one record per matching subject, the most recent, ascending by subject,
    // then the Mark — whose `next` for a last-value query IS the head.
    let out = run(&["last", &p.sock, "/f/F/pub/>"]);
    assert_eq!(out.status.code(), Some(0), "{}", stderr(&out));
    let mut want = framed(2, a, a2);
    want.extend(framed(1, b, b"v=1 inc=1"));
    want.extend_from_slice(b"MARK next=4 head=4\n");
    assert_eq!(out.stdout, want, "last framing, byte for byte");

    // ...and paging over it: --max bounds the page, --after resumes past a subject.
    let page1 = run(&["last", &p.sock, "/f/F/pub/>", "--max", "1"]);
    let mut want1 = framed(2, a, a2);
    want1.extend_from_slice(b"MARK next=4 head=4\n");
    assert_eq!(page1.stdout, want1, "one-record page");
    let page2 = run(&["last", &p.sock, "/f/F/pub/>", "--max", "1", "--after", a]);
    let mut want2 = framed(1, b, b"v=1 inc=1");
    want2.extend_from_slice(b"MARK next=4 head=4\n");
    assert_eq!(page2.stdout, want2, "the page after subject a");

    // FETCH: log order, bounded by --max, resumable from the Mark's `next` (the
    // offset after the last record SCANNED, so a sparse filter still advances).
    let f1 = run(&["fetch", &p.sock, "/f/F/pub/>", "--from", "0", "--max", "2"]);
    let mut wf1 = framed(0, a, b"v=1 inc=1");
    wf1.extend(framed(1, b, b"v=1 inc=1"));
    wf1.extend_from_slice(b"MARK next=2 head=4\n");
    assert_eq!(f1.stdout, wf1, "fetch page 1");
    let f2 = run(&["fetch", &p.sock, "/f/F/pub/>", "--from", "2", "--max", "2"]);
    let mut wf2 = framed(2, a, a2);
    wf2.extend_from_slice(b"MARK next=4 head=4\n");
    assert_eq!(f2.stdout, wf2, "fetch page 2 reaches the rest, no dup");

    // `--max 0` is the head query: no records, and the head to page against.
    let head = run(&["fetch", &p.sock, "/f/F/pub/>", "--max", "0"]);
    assert_eq!(stdout(&head), "MARK next=0 head=4\n");

    // A filter matching nothing still answers with a Mark, never with silence.
    let none = run(&["last", &p.sock, "/f/G/>"]);
    assert_eq!(stdout(&none), "MARK next=4 head=4\n");

    // Strictness carries into the new flags.
    refused(
        &["last", &p.sock, "/f/F/>", "--max", "twelve"],
        "--max expects an unsigned integer below 2^32",
    );
    refused(
        &["fetch", &p.sock, "/f/F/>", "--from", "-1"],
        "--from expects an unsigned integer",
    );
    refused(
        &["fetch", &p.sock, "/f/F/>", "--after", "/x"],
        "--after does not apply to fetch",
    );
}

// ------------------------------------------------------------- asb drain

/// `drain` is the batched shell face of a durable consumer group: take a bounded
/// batch, commit through it, print it. `--peek` takes the same batch and commits
/// nothing, so the records come back next time.
#[test]
fn asb_drain_commits_a_batch_and_peek_commits_nothing() {
    let p = fresh("drain");
    let _s = serve(&p);
    let lane = "/f/F/in/n-a1/s-1/h-andrew/ask";
    let filter = "/f/F/in/n-a1/>";
    let group = "/f/F/cur/n-a1/inbox";

    let mut at = Vec::new();
    for (i, body) in [&b"one"[..], b"two", b"three"].iter().enumerate() {
        at.push(pub_offset(&publish(
            &p,
            lane,
            &["--id", "7", "--seq", &(i + 1).to_string()],
            body,
        )));
    }

    // A never-committed group starts at 0. Two records, then the summary line.
    let out = run(&[
        "drain", &p.sock, group, filter, "--max", "2", "--idle", "250",
    ]);
    assert_eq!(out.status.code(), Some(0), "{}", stderr(&out));
    let mut want = framed(at[0], lane, b"one");
    want.extend(framed(at[1], lane, b"two"));
    want.extend_from_slice(format!("DRAIN n=2 upto={} committed=yes\n", at[1]).as_bytes());
    assert_eq!(out.stdout, want, "drain framing, byte for byte");

    // The commit was durable, so the next drain resumes AFTER it: no duplicate.
    let out = run(&[
        "drain", &p.sock, group, filter, "--max", "2", "--idle", "250",
    ]);
    let mut want = framed(at[2], lane, b"three");
    want.extend_from_slice(format!("DRAIN n=1 upto={} committed=yes\n", at[2]).as_bytes());
    assert_eq!(out.stdout, want, "resumes past the committed batch");

    // An empty lane is an empty batch, not a hang and not an error.
    let out = run(&[
        "drain", &p.sock, group, filter, "--max", "2", "--idle", "250",
    ]);
    assert_eq!(stdout(&out), "DRAIN n=0 upto=- committed=no\n");

    // --peek reads without moving the cursor: the same record twice.
    let four = pub_offset(&publish(&p, lane, &["--id", "7", "--seq", "4"], b"four"));
    let mut want = framed(four, lane, b"four");
    want.extend_from_slice(format!("DRAIN n=1 upto={four} committed=no\n").as_bytes());
    for _ in 0..2 {
        let out = run(&[
            "drain", &p.sock, group, filter, "--max", "4", "--idle", "250", "--peek",
        ]);
        assert_eq!(out.stdout, want, "--peek commits nothing");
    }
    // ...and a real drain then takes it exactly once.
    let out = run(&[
        "drain", &p.sock, group, filter, "--max", "4", "--idle", "250",
    ]);
    let mut want = framed(four, lane, b"four");
    want.extend_from_slice(format!("DRAIN n=1 upto={four} committed=yes\n").as_bytes());
    assert_eq!(out.stdout, want);

    refused(
        &["drain", &p.sock, group, filter, "--idle", "soon"],
        "--idle expects an unsigned integer",
    );
    refused(
        &["drain", &p.sock, group, filter, "--from", "0"],
        "--from does not apply to drain",
    );
}

// --------------------------------------------------------------- asb ack

/// `ack` is one atomic read-process-write: the answer record and the group's
/// cursor advance in ONE durable append, deduped by the INPUT OFFSET. So a retried
/// ack appends nothing, returns the original offset, and re-applies no commit —
/// which is exactly why the verb refuses to invent a per-invocation producer id.
#[test]
fn asb_ack_is_one_durable_record_that_a_retry_never_doubles() {
    let p = fresh("ack");
    let _s = serve(&p);
    let lane = "/f/F/in/n-a1/s-1/h-andrew/ask";
    let back = "/f/F/in/p/h-andrew/n-a1/ack";
    let filter = "/f/F/in/n-a1/>";
    let group = "/f/F/cur/n-a1/inbox";

    assert_eq!(
        stdout(&publish(
            &p,
            lane,
            &["--id", "7", "--seq", "1"],
            b"which branch?"
        )),
        "0 new\n"
    );

    // Acknowledge the record at offset 0 and answer on the sender's lane.
    let out = run(&["ack", &p.sock, group, "0", back, "handled", "--id", "77"]);
    assert_eq!(out.status.code(), Some(0), "{}", stderr(&out));
    assert_eq!(stdout(&out), "1 new\n", "the ack record's own offset");

    // The RETRY: same producer id, same input offset -> deduped, nothing appended.
    let out = run(&["ack", &p.sock, group, "0", back, "handled", "--id", "77"]);
    assert_eq!(stdout(&out), "1 dup\n", "a retried ack appends nothing");

    // Exactly one ack record exists, and it carries the correlation and the verdict.
    let page = run(&["fetch", &p.sock, back, "--from", "0"]);
    let text = stdout(&page);
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(
        lines.len(),
        3,
        "one record (header + body) then MARK: {text:?}"
    );
    assert!(
        lines[0].ends_with(" /f/F/in/p/h-andrew/n-a1/ack") && lines[0].starts_with("1 "),
        "{text:?}"
    );
    assert!(
        lines[1].contains("re=0"),
        "correlation by input offset: {text:?}"
    );
    assert!(lines[1].contains("state=handled"), "{text:?}");
    assert_eq!(lines[2], "MARK next=2 head=2");

    // The cursor moved with it — and moved exactly once, so the acked record is
    // not redelivered by a drain of the same group.
    let out = run(&[
        "drain", &p.sock, group, filter, "--max", "4", "--idle", "250",
    ]);
    assert_eq!(stdout(&out), "DRAIN n=0 upto=- committed=no\n");

    // A per-invocation producer id would make every retry a NEW record, so the
    // verb refuses to default one.
    refused(
        &["ack", &p.sock, group, "0", back, "handled"],
        "ack needs a producer id that survives a restart",
    );
    refused(
        &["ack", &p.sock, group, "0", back, "done", "--id", "77"],
        "<verdict> is handled|refused|deferred",
    );
    refused(
        &["ack", &p.sock, group, "no", back, "handled", "--id", "77"],
        "<offset> expects an unsigned integer",
    );
}

// ------------------------------------------------- asb pub --seq-file

/// `pub --seq-file` is a WRITE-AHEAD persisted producer sequence, so a bridge in
/// any language gets safe sequencing across restarts without holding a
/// connection. The file advances and is fsynced BEFORE the publish; the honest
/// consequence is that a crash in between burns that number — never a duplicate,
/// but the record is simply never published.
#[test]
fn asb_pub_seq_file_persists_the_producer_sequence_across_invocations() {
    let p = fresh("seq");
    let _s = serve(&p);
    let subject = "/f/F/pub/n-a1/ev";
    let seq = p.dir.join("n-a1.seq").to_str().unwrap().to_string();

    // Each invocation is a separate process — the "restart" case by construction.
    for i in 0..3u64 {
        let out = publish(&p, subject, &["--id", "9", "--seq-file", &seq], b"ev");
        assert_eq!(stdout(&out), format!("{i} new\n"), "{}", stderr(&out));
        assert_eq!(
            std::fs::read_to_string(&seq).unwrap(),
            (i + 1).to_string(),
            "the file holds the sequence just used"
        );
    }

    // The file IS the dedup key: rewind it and the broker recognises the replay,
    // returning the ORIGINAL offset and appending nothing.
    std::fs::write(&seq, "1").unwrap();
    let out = publish(&p, subject, &["--id", "9", "--seq-file", &seq], b"ev");
    assert_eq!(stdout(&out), "1 dup\n", "seq 2 replayed: {}", stderr(&out));

    // A persisted sequence under a per-invocation producer id would dedup against
    // nothing, so a stable id is required rather than defaulted.
    refused(
        &["pub", &p.sock, subject, "--seq-file", &seq],
        "--seq-file needs a producer id that survives a restart",
    );
    refused(
        &[
            "pub",
            &p.sock,
            subject,
            "--id",
            "9",
            "--seq",
            "1",
            "--seq-file",
            &seq,
        ],
        "both set the producer sequence",
    );
    // A file that does not hold a number is an error, never a silent restart of
    // the sequence (which would let the broker dedup live records away). An EMPTY
    // or whitespace-only file is that same case, and it is the one a truncating
    // wrapper (`: > n-a1.seq`), a torn `tee` or a crashed writer actually leaves:
    // guessing 0 there restarts the producer sequence at 1, and every record until
    // the counter passes the old high-water mark is deduped away while `asb pub`
    // prints `<some old offset> dup` and exits 0. Only an ABSENT file starts one.
    for (name, contents) in [
        ("bad.seq", "seven\n"),
        ("empty.seq", ""),
        ("blank.seq", "   \n\t\n"),
    ] {
        let bad = p.file(name, contents);
        let out = publish(&p, subject, &["--id", "9", "--seq-file", &bad], b"ev");
        assert_eq!(
            out.status.code(),
            Some(1),
            "{name} must not restart the sequence: {}",
            stdout(&out)
        );
        assert!(
            stderr(&out).contains("is not an unsigned integer"),
            "{name}: {}",
            stderr(&out)
        );
        assert!(stdout(&out).is_empty(), "{name}: nothing published");
        assert_eq!(
            std::fs::read_to_string(&bad).unwrap(),
            contents,
            "{name}: the refusal rewrote nothing"
        );
    }
    // The good file is untouched by those refusals, and still counting: the file
    // held 2 (the rewind above re-used it), so the next invocation takes 3 — which
    // the broker recognises as the replay of the third record.
    assert_eq!(std::fs::read_to_string(&seq).unwrap(), "2");
    let out = publish(&p, subject, &["--id", "9", "--seq-file", &seq], b"ev");
    assert_eq!(stdout(&out), "2 dup\n", "seq 3 replayed: {}", stderr(&out));

    // The TOP HALF of the producer-sequence space belongs to `ack` (which publishes
    // under 2^63|<input offset>), so a publish may not reach into it and collide.
    refused(
        &[
            "pub",
            &p.sock,
            subject,
            "--id",
            "9",
            "--seq",
            "9223372036854775808",
        ],
        "--seq must be below 2^63",
    );
}

// ------------------------------------------------------------ --cap-file

/// The capability reaches asb through a FILE, and only through a file. A tag is a
/// secret and argv is world-readable via `ps`, so `--cap-filter`/`--cap-tag` are
/// refused exactly as `--key HEX` is. A ring of several grants attaches in order,
/// and a grant bound to a principal FORCES the producer id — which asb derives, so
/// the operator never retypes it and can never accidentally publish under another.
#[cfg(feature = "cap")]
#[test]
fn asb_cap_file_attaches_a_ring_and_argv_capability_flags_are_refused() {
    use astream_broker::Broker;
    let p = fresh("cap");
    let broker = Broker::open_guarded(&p.log, SECRET.to_vec()).unwrap();
    let _h = broker.serve(&p.sock).unwrap();

    let node = "n-a1b2c3d4e5f60718";
    let read = "ro:/f/F/pub/>".to_string();
    let write = format!("rw,p={node}:/f/F/pub/{node}/>");
    let ring = p.file(
        "node.cap",
        &format!(
            "# node {node}'s ring\n{read} {}\n\n{write} {}\n",
            tag_hex(&read),
            tag_hex(&write)
        ),
    );
    let subject = format!("/f/F/pub/{node}/presence");

    // Nothing attached -> the guarded broker refuses.
    let out = publish(&p, &subject, &["--id", "1", "--seq", "1"], b"v=1 inc=1");
    assert_eq!(out.status.code(), Some(1), "{}", stderr(&out));

    // The ring attaches, and the bound grant supplies the producer id.
    let at = pub_offset(&publish(
        &p,
        &subject,
        &["--seq", "1", "--cap-file", &ring],
        b"v=1 inc=1",
    ));

    // That id is exactly producer_id_of(node) — a retry under the value the design
    // says the broker derives is a DUP at the original offset, which it could only
    // be if asb published under that id.
    let derived = astream_cap::producer_id_of(node).to_string();
    let out = publish(
        &p,
        &subject,
        &["--seq", "1", "--id", &derived, "--cap-file", &ring],
        b"v=1 inc=1",
    );
    assert_eq!(stdout(&out), format!("{at} dup\n"), "{}", stderr(&out));

    // A publish naming any OTHER producer id under that bound grant is refused —
    // the dedup-key-poisoning shape, closed at the broker.
    let out = publish(
        &p,
        &subject,
        &["--seq", "2", "--id", "1", "--cap-file", &ring],
        b"v=1 inc=2",
    );
    assert_eq!(out.status.code(), Some(1), "{}", stderr(&out));
    assert!(stderr(&out).contains("unauthorized"), "{}", stderr(&out));

    // The ro half of the ring reads the whole /pub subtree...
    let out = run(&["last", &p.sock, "/f/F/pub/>", "--cap-file", &ring]);
    let mut want = framed(at, &subject, b"v=1 inc=1");
    want.extend_from_slice(format!("MARK next={0} head={0}\n", at + 1).as_bytes());
    assert_eq!(out.stdout, want, "{}", stderr(&out));

    // ...and grants nothing outside it: the halt lane needs a human's rw cap.
    let out = publish(
        &p,
        "/f/F/fleet/h-andrew/halt",
        &["--seq", "3", "--cap-file", &ring],
        b"state=on",
    );
    assert_eq!(out.status.code(), Some(1), "{}", stderr(&out));
    assert!(stderr(&out).contains("unauthorized"), "{}", stderr(&out));

    // The tag never rides on argv, on any verb.
    for verb in ["pub", "last"] {
        refused(
            &[verb, &p.sock, "/f/F/pub/>", "--cap-tag", &tag_hex(&read)],
            "--cap-tag on argv is refused",
        );
        refused(
            &[verb, &p.sock, "/f/F/pub/>", "--cap-filter", &read],
            "--cap-filter on argv is refused",
        );
    }
    // A malformed cap file is a usage error naming the line, not a silent skip.
    let junk = p.file("junk.cap", &format!("ro:/f/F/> {}\n", "zz".repeat(32)));
    refused(
        &["last", &p.sock, "/f/F/pub/>", "--cap-file", &junk],
        "junk.cap:1: tag: not valid hex",
    );
    let short = p.file("short.cap", "ro:/f/F/>\n");
    refused(
        &["last", &p.sock, "/f/F/pub/>", "--cap-file", &short],
        "short.cap:1: expected `<grant> <tag-hex>`",
    );
}

/// `ack` and `pub` SHARE one producer id under a bound grant — the grant permits no
/// other — and the broker's dedup key is `(producer_id, producer_seq)`. `ack`'s
/// sequence is a function of the input OFFSET (that is what makes a retry
/// idempotent) while `pub --seq-file` counts 1, 2, 3, …, so the two spaces used to
/// overlap exactly where both are dense: acking an ask that landed at offset 2 hit
/// the dedup entry of the second seq-file publish, and the broker appended NO ack
/// record, moved NO cursor, and asb printed `<the publish's offset> dup` and exited
/// 0. The sender waited forever, the ask was redelivered forever, and no error was
/// reported anywhere. asb now publishes an ack under `2^63 | <input offset>` — the
/// reserved top half of the space, disjoint from every sequence `pub` will accept.
#[cfg(feature = "cap")]
#[test]
fn an_ack_and_a_seq_file_publish_never_share_a_dedup_key() {
    use astream_broker::Broker;
    let p = fresh("ackcollide");
    let broker = Broker::open_guarded(&p.log, SECRET.to_vec()).unwrap();
    let _h = broker.serve(&p.sock).unwrap();

    let node = "n-a1b2c3d4e5f60718";
    let grants = [
        format!("rw,p={node}:/f/F/pub/{node}/>"),
        format!("rw,p={node}:/f/F/in/{node}/>"),
        format!("rw,p={node}:/f/F/in/h-andrew/>"),
        format!("rw,p={node}:/f/F/cur/{node}/>"),
    ];
    let mut text = String::new();
    for g in &grants {
        text.push_str(&format!("{g} {}\n", tag_hex(g)));
    }
    let ring = p.file("node.cap", &text);

    let lane = format!("/f/F/in/{node}/s-1/h-andrew/ask");
    // The answer goes on the SENDER's lane — outside the node's own inbox filter,
    // so a drain of that inbox never re-reads the node's own answers.
    let back = format!("/f/F/in/h-andrew/p/{node}/ack");
    let filter = format!("/f/F/in/{node}/>");
    let group = format!("/f/F/cur/{node}/inbox");
    let ev = format!("/f/F/pub/{node}/ev");
    let seq = p.dir.join("node.seq").to_str().unwrap().to_string();

    // The ask lands at some offset O (not guessable: the first attach of a bound
    // grant appends a hidden /a/bind record of its own). Its own sequence is far
    // out of the counter's way, so the only collision under test is the ack's.
    let ask = pub_offset(&publish(
        &p,
        &lane,
        &["--seq", "1000000", "--cap-file", &ring],
        b"v=1 which branch?",
    ));
    assert!(
        ask >= 1,
        "the ask must sit where a seq-file counter reaches"
    );

    // Walk the node's persisted publish counter onto exactly that number — the
    // ordinary case for a node that has published O rows since it started.
    std::fs::write(&seq, (ask - 1).to_string()).unwrap();
    let ev_at = pub_offset(&publish(
        &p,
        &ev,
        &["--seq-file", &seq, "--cap-file", &ring],
        b"v=1 inc=1",
    ));
    assert_eq!(
        std::fs::read_to_string(&seq).unwrap(),
        ask.to_string(),
        "the publish used the sequence that equals the ask's offset"
    );

    // THE COLLISION CASE: ack the ask. Same producer id, and an input offset equal
    // to a producer sequence already published under it.
    let ask_s = ask.to_string();
    let ack_args = [
        "ack",
        &p.sock,
        &group,
        &ask_s,
        &back,
        "handled",
        "--cap-file",
        &ring,
    ];
    let out = run(&ack_args);
    assert_eq!(out.status.code(), Some(0), "{}", stderr(&out));
    let acked = stdout(&out);
    let (at, state) = acked.trim_end().split_once(' ').unwrap();
    assert_eq!(
        state, "new",
        "the ack is a real append, not a collision: {acked}"
    );
    assert_ne!(at, ev_at.to_string(), "and not another record's offset");

    // The ack record really is on the sender's lane, exactly once, correlated.
    let page = run(&["fetch", &p.sock, &back, "--from", "0", "--cap-file", &ring]);
    let text = stdout(&page);
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(lines.len(), 3, "one record then MARK: {text:?}");
    assert!(lines[0].ends_with(&back), "{text:?}");
    assert!(lines[1].contains(&format!("re={ask}")), "{text:?}");
    assert!(lines[1].contains("state=handled"), "{text:?}");

    // The cursor moved with it: the acked ask is not redelivered.
    let out = run(&[
        "drain",
        &p.sock,
        &group,
        &filter,
        "--max",
        "4",
        "--idle",
        "250",
        "--cap-file",
        &ring,
    ]);
    assert_eq!(
        stdout(&out),
        "DRAIN n=0 upto=- committed=no\n",
        "{}",
        stderr(&out)
    );

    // ...and the retry is still idempotent: the sequence is a pure function of the
    // input offset, so a repeated ack appends nothing and returns the same offset.
    let again = run(&ack_args);
    assert_eq!(stdout(&again), format!("{at} dup\n"), "{}", stderr(&again));

    // The publish half is untouched: its own replay still dedups to its offset.
    std::fs::write(&seq, (ask - 1).to_string()).unwrap();
    let out = publish(
        &p,
        &ev,
        &["--seq-file", &seq, "--cap-file", &ring],
        b"v=1 inc=1",
    );
    assert_eq!(stdout(&out), format!("{ev_at} dup\n"), "{}", stderr(&out));
}

/// A READ-ONLY grant binds nothing. `ro,p=<principal>:<filter>` parses, and the
/// broker has an explicit "a read-only grant publishes nothing, so it binds nothing"
/// arm for it — so counting its principal when deriving the producer id was wrong in
/// both directions: a ring holding a human's `ro,p=` grant beside a node's `rw,p=`
/// grant looked AMBIGUOUS and asb refused to publish at all, and a ring holding a
/// `ro,p=` grant beside an unbound `rw` grant silently published under the READ-ONLY
/// principal's id — an id its holder may not write under, in another principal's
/// dedup namespace. Only a writable grant votes.
#[cfg(feature = "cap")]
#[test]
fn only_a_writable_grant_chooses_the_derived_producer_id() {
    use astream_broker::Broker;
    let p = fresh("rovote");
    let broker = Broker::open_guarded(&p.log, SECRET.to_vec()).unwrap();
    let _h = broker.serve(&p.sock).unwrap();

    let node = "n-a1b2c3d4e5f60718";
    let human = "h-andrew";
    let read = format!("ro,p={human}:/f/F/pub/>");
    let write = format!("rw,p={node}:/f/F/pub/{node}/>");
    let ring = p.file(
        "ring.cap",
        &format!("{read} {}\n{write} {}\n", tag_hex(&read), tag_hex(&write)),
    );
    let subject = format!("/f/F/pub/{node}/presence");

    // The ring names two principals but only ONE of them may write, so there is
    // nothing ambiguous about it: the publish goes through with no --id.
    let at = pub_offset(&publish(
        &p,
        &subject,
        &["--seq", "1", "--cap-file", &ring],
        b"v=1 inc=1",
    ));

    // ...and it went out under the WRITABLE grant's principal, not the reader's: a
    // retry naming that id dedups to the same offset (which it could only do if asb
    // published under it), while the read-only principal's id is refused outright.
    let derived = astream_cap::producer_id_of(node).to_string();
    let out = publish(
        &p,
        &subject,
        &["--seq", "1", "--id", &derived, "--cap-file", &ring],
        b"v=1 inc=1",
    );
    assert_eq!(stdout(&out), format!("{at} dup\n"), "{}", stderr(&out));

    let readers = astream_cap::producer_id_of(human).to_string();
    let out = publish(
        &p,
        &subject,
        &["--seq", "2", "--id", &readers, "--cap-file", &ring],
        b"v=1 inc=2",
    );
    assert_eq!(out.status.code(), Some(1), "{}", stdout(&out));
    assert!(stderr(&out).contains("unauthorized"), "{}", stderr(&out));
}
