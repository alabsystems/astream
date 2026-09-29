//! Regression tests for four confirmed `asb` defects, each a real subprocess
//! against a real broker over a real Unix socket:
//!
//! * `pub --seq-file` was an UNLOCKED read-modify-write through one shared temp
//!   path, so concurrent invocations swallowed records (`dup`, exit 0) and failed
//!   others with a bare ENOENT;
//! * `last` printed a page the BROKER's own row bound had cut short as if it were
//!   the whole answer;
//! * `--cap-file` split a line on its FIRST whitespace, so a grant whose filter
//!   holds a space — legal on the wire, and something `asb mint` will happily seal
//!   and print — could not be read back;
//! * `drain --idle 0` reached the OS and died at exit 1 after the group
//!   subscription was already registered, where every other bad flag value is a
//!   parse-time exit 2.
//!
//! Synchronized on the serve readiness line and on the records the log already
//! holds — no sleeps.
#![cfg(unix)]

use std::io::{BufRead, BufReader, Write};
use std::process::{Child, Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);

struct Paths {
    sock: String,
    log: String,
    dir: std::path::PathBuf,
}

fn fresh(tag: &str) -> Paths {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let dir = std::env::temp_dir().join(format!("asbr2_{tag}_{pid}_{n}"));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    Paths {
        sock: dir.join("b.sock").to_str().unwrap().to_string(),
        log: dir.join("b.log").to_str().unwrap().to_string(),
        dir,
    }
}

impl Paths {
    /// Write `contents` to `name` in this test's own directory; returns the path.
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

/// Spawn `asb pub` with `body` on stdin, WITHOUT waiting for it: the whole point of
/// the seq-file test is that several of these overlap.
fn spawn_pub(sock: &str, subject: &str, extra: &[&str], body: &[u8]) -> Child {
    let mut c = asb()
        .args(["pub", sock, subject])
        .args(extra)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    c.stdin.take().unwrap().write_all(body).unwrap();
    c
}

/// CONCURRENT `pub --seq-file` INVOCATIONS ON ONE FILE MUST NOT LOSE A RECORD.
///
/// The counter used to be advanced by an unlocked read-modify-write through one
/// fixed `<path>.new`: two publishes a millisecond apart both read the same value,
/// both published under the same `(producer_id, producer_seq)`, and the broker
/// deduped the second away — `asb pub` printed `<the first record's offset> dup`,
/// exited 0, and the caller's bytes were never on the bus. In the same window others
/// raced on the ONE staging inode and died with a bare `asb: No such file or
/// directory (os error 2)` when a peer's rename moved it away.
///
/// Six at a time, eight rounds — the shape that reproduced it (6 `dup` and 26 ENOENT
/// out of 48). Every invocation must exit 0 and print `new`, the log must hold
/// exactly one record per invocation, and the file must end holding exactly the
/// count. Each round is joined before the next starts, so the assertions name the
/// round that failed; the concurrency is WITHIN a round.
#[test]
fn concurrent_seq_file_publishes_never_dedup_a_record_away() {
    const ROUNDS: usize = 8;
    const WIDTH: usize = 6;

    let p = fresh("seqrace");
    let _b = serve(&p);
    let seq = p.dir.join("n.seq").to_str().unwrap().to_string();
    let subject = "/f/F/pub/n-a1/ev";

    let mut published = 0usize;
    for round in 0..ROUNDS {
        let kids: Vec<Child> = (0..WIDTH)
            .map(|i| {
                spawn_pub(
                    &p.sock,
                    subject,
                    &["--id", "42", "--seq-file", &seq],
                    format!("round={round} w={i}").as_bytes(),
                )
            })
            .collect();
        for (i, k) in kids.into_iter().enumerate() {
            let out = k.wait_with_output().unwrap();
            assert_eq!(
                out.status.code(),
                Some(0),
                "round {round} worker {i}: {}",
                stderr(&out)
            );
            let printed = stdout(&out);
            assert!(
                printed.trim_end().ends_with(" new"),
                "round {round} worker {i} was deduped away: {printed:?}"
            );
            published += 1;
        }
        // The counter is exactly the number of publishes so far: no number was
        // handed out twice and none was skipped.
        assert_eq!(
            std::fs::read_to_string(&seq).unwrap(),
            published.to_string(),
            "after round {round}"
        );
    }

    // ...and the bus really holds every one of them.
    let page = run(&["fetch", &p.sock, subject, "--from", "0", "--max", "4096"]);
    assert_eq!(page.status.code(), Some(0), "{}", stderr(&page));
    let text = stdout(&page);
    let headers = text
        .lines()
        .filter(|l| l.starts_with(char::is_numeric) && l.ends_with(subject))
        .count();
    assert_eq!(
        headers,
        ROUNDS * WIDTH,
        "one record per invocation, none swallowed: {text:?}"
    );
}

/// `asb last` MUST ANSWER PAST THE BROKER'S OWN PAGE BOUND.
///
/// One `Last` request returns at most `LAST_PAGE_MAX` (4096) rows however large a
/// `--max` the operator passed, and the closing `MARK` of a page cut short there is
/// byte-identical to the `MARK` of a complete one. `asb last --max 10000` over 4097
/// subjects therefore used to print 4096 records and look finished. asb now follows
/// the broker's resume cursor until it has `--max` rows or the filter's range is
/// exhausted, so `--max` is the only bound on the answer.
///
/// The records are published through the library on one connection (4097 subprocess
/// publishes would be a minute of fsyncs); the READ is the real `asb` subprocess,
/// which is what is under test.
#[test]
fn last_answers_past_the_brokers_own_page_bound() {
    use astream_broker::{Broker, Client, Durability};

    // One more subject than the broker will put in a single page.
    let subjects = astream_broker::broker::LAST_PAGE_MAX as usize + 1;

    let p = fresh("lastpage");
    // Relaxed: this test is about paging, and 4097 strict fsyncs are minutes.
    let broker = Broker::open_with(&p.log, Durability::Relaxed).unwrap();
    let _h = broker.serve(&p.sock).unwrap();

    let mut c = Client::connect(&p.sock).unwrap();
    for i in 0..subjects {
        // Zero-padded so the ASCENDING SUBJECT order the page is returned in is the
        // numeric one, and the last row is predictable.
        let subject = format!("/f/F/pub/n-{i:06}/ev");
        // Spread over several producer ids: one producer may hold at most
        // MAX_SUBJECTS_PER_PRODUCER (4096) distinct subjects, and this test needs
        // one more subject than that in the index.
        let producer = 1 + (i / 1024) as u64;
        c.publish(producer, i as u64, &subject, b"v=1").unwrap();
    }

    let out = run(&["last", &p.sock, "/f/F/pub/>", "--max", "10000"]);
    assert_eq!(out.status.code(), Some(0), "{}", stderr(&out));

    let text = stdout(&out);
    let headers: Vec<&str> = text
        .lines()
        .filter(|l| l.starts_with(char::is_numeric) && l.ends_with("/ev"))
        .collect();
    assert_eq!(
        headers.len(),
        subjects,
        "every subject's last record, not one broker page of them"
    );
    assert!(
        headers
            .last()
            .unwrap()
            .ends_with(&format!("/f/F/pub/n-{:06}/ev", subjects - 1)),
        "the answer runs to the last subject: {:?}",
        headers.last()
    );
    assert!(text.ends_with("\n"), "the MARK closes the answer");
    assert!(
        text.lines().last().unwrap().starts_with("MARK next="),
        "closing line: {:?}",
        text.lines().last()
    );

    // ...and `--max` is still a real bound, with the last subject printed as its
    // cursor: the page after it continues where it stopped.
    let bounded = run(&["last", &p.sock, "/f/F/pub/>", "--max", "3"]);
    let btext = stdout(&bounded);
    let brows: Vec<&str> = btext
        .lines()
        .filter(|l| l.starts_with(char::is_numeric) && l.ends_with("/ev"))
        .collect();
    assert_eq!(brows.len(), 3, "--max bounds the page: {btext:?}");
    let after = "/f/F/pub/n-000002/ev";
    assert!(brows[2].ends_with(after), "{btext:?}");
    let next = run(&[
        "last",
        &p.sock,
        "/f/F/pub/>",
        "--max",
        "3",
        "--after",
        after,
    ]);
    let ntext = stdout(&next);
    let nrows: Vec<&str> = ntext
        .lines()
        .filter(|l| l.starts_with(char::is_numeric) && l.ends_with("/ev"))
        .collect();
    assert_eq!(nrows.len(), 3, "{ntext:?}");
    assert!(nrows[0].ends_with("/f/F/pub/n-000003/ev"), "{ntext:?}");
}

/// A `--cap-file` LINE WHOSE GRANT HOLDS A SPACE MUST STILL PARSE.
///
/// `Filter::new` rejects bytes below 0x20 and 0x7f, and 0x20 is neither — the same
/// fact the record header's field order is built around — so `ro:/f/F/pub a/>` is a
/// legal grant that `asb mint` seals and prints. Split on the FIRST whitespace, the
/// line read back as the grant `ro:/f/F/pub` with the tag `a/>`, and every verb
/// pointed at that file exited 2 with "expected `<grant> <tag-hex>`" — the whole
/// ring unusable, including its other grants.
///
/// This is the parse, in the default build: the line must no longer be a usage
/// error. (What the broker then makes of the attach is `cap`-feature territory, and
/// the round trip through a real `asb mint` and a guarded broker is the test below.)
#[test]
fn a_cap_file_grant_containing_a_space_is_not_a_usage_error() {
    let p = fresh("capspace");
    let _b = serve(&p);
    let ring = p.file(
        "node.cap",
        &format!("ro:/f/F/pub a/> {}\n", "ab".repeat(32)),
    );

    let out = run(&["last", &p.sock, "/f/F/pub a/>", "--cap-file", &ring]);
    assert_ne!(
        out.status.code(),
        Some(2),
        "the line parses; it is not a usage error: {}",
        stderr(&out)
    );
    assert!(
        !stderr(&out).contains("expected `<grant> <tag-hex>`"),
        "{}",
        stderr(&out)
    );

    // A line with NOTHING but a tag is still the usage error it was, naming the
    // file and the line.
    let short = p.file("short.cap", "ro:/f/F/>\n");
    let out = run(&["last", &p.sock, "/f/F/pub/>", "--cap-file", &short]);
    assert_eq!(out.status.code(), Some(2), "{}", stderr(&out));
    assert!(
        stderr(&out).contains("short.cap:1: expected `<grant> <tag-hex>`"),
        "{}",
        stderr(&out)
    );
}

/// THE ROUND TRIP THE DOC PROMISES: `--cap-file` reads "exactly what `asb mint`
/// prints", for a grant whose filter holds a space.
///
/// The tag seals the grant STRING, so this only passes if the bytes `mint` printed
/// are recovered exactly — a grant split at the wrong space would present
/// `ro:/f/F/pub` with a tag that does not verify over it, and the guarded broker
/// would refuse the attach.
#[cfg(feature = "cap")]
#[test]
fn asb_mint_prints_a_cap_file_line_that_reads_back_when_the_grant_holds_a_space() {
    use astream_broker::Broker;

    let p = fresh("mintspace");
    let secret = b"r2-mint-secret-0123456789abcdef-r2";
    let secret_file = p.file("mint.secret", std::str::from_utf8(secret).unwrap());
    let broker = Broker::open_guarded(&p.log, secret.to_vec()).unwrap();
    let _h = broker.serve(&p.sock).unwrap();

    let grant = "ro:/f/F/pub a/>";
    let minted = run(&["mint", grant, "--secret-file", &secret_file]);
    assert_eq!(minted.status.code(), Some(0), "{}", stderr(&minted));
    let line = stdout(&minted);
    assert!(
        line.starts_with(&format!("{grant} ")),
        "mint prints the grant it was given: {line:?}"
    );

    // The mint's own bytes, verbatim, are the cap file.
    let ring = p.file("node.cap", &line);
    let out = run(&["last", &p.sock, "/f/F/pub a/>", "--cap-file", &ring]);
    assert_eq!(
        out.status.code(),
        Some(0),
        "the minted line attaches: {}",
        stderr(&out)
    );
    assert!(stdout(&out).starts_with("MARK next="), "{}", stdout(&out));

    // ...and the grant really is the whole string: the truncated one the first-space
    // split produced does NOT verify against the same tag.
    let tag = line.trim_end().rsplit(' ').next().unwrap().to_string();
    let mangled = p.file("mangled.cap", &format!("ro:/f/F/pub {tag}\n"));
    let out = run(&["last", &p.sock, "/f/F/pub/>", "--cap-file", &mangled]);
    assert_eq!(
        out.status.code(),
        Some(1),
        "a tag over a different grant is refused: {}",
        stderr(&out)
    );
}

/// `drain --idle 0` IS A USAGE ERROR, NOT AN OS ERROR AFTER THE SUBSCRIPTION IS UP.
///
/// `set_read_timeout(Some(Duration::ZERO))` is `InvalidInput` by std's own contract,
/// and that used to surface only after both connections were open, the ring
/// attached and the consumer group registered on the broker: exit 1 with "cannot set
/// a 0 duration timeout", naming neither the flag nor the verb, so a wrapper whose
/// arithmetic (`--idle $((deadline - elapsed))`) reached 0 saw a status it reads as
/// "transient, retry" and retried forever.
///
/// Checked at parse time now, like every other numeric flag — so it does not even
/// need a broker to be listening, which is what this asserts: the endpoint here is a
/// socket path that does not exist.
#[test]
fn drain_refuses_a_zero_idle_window_before_it_connects() {
    let p = fresh("idle0");
    let nowhere = p.dir.join("no-such.sock").to_str().unwrap().to_string();

    let out = run(&["drain", &nowhere, "/a/g", "/a/>", "--idle", "0"]);
    assert_eq!(
        out.status.code(),
        Some(2),
        "a bad flag value is a usage error: {}",
        stderr(&out)
    );
    assert!(
        stderr(&out).contains("--idle"),
        "the message names the flag: {}",
        stderr(&out)
    );

    // A positive window still reaches the connect (there is nothing listening, so
    // that is exit 1) — the check rejects 0, not `--idle` itself.
    let out = run(&["drain", &nowhere, "/a/g", "/a/>", "--idle", "1"]);
    assert_eq!(out.status.code(), Some(1), "{}", stderr(&out));
}
