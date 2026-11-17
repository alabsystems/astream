//! `asb` shell-face regressions, each a real `asb` subprocess:
//!
//! * a secret must never reach stderr — not from a key/secret environment variable
//!   that is not valid UTF-8, and not from a mistyped `--flag=<value>`;
//! * `drain` must be able to commit a batch whose take outlasted the broker's
//!   first-frame timeout;
//! * an explicit `pub --seq` is a dedup key only under a stable producer id, so
//!   without one it is refused rather than published under the process id;
//! * a body no record can hold is bad input (exit 2), refused before a
//!   `--seq-file` sequence is burned;
//! * `sub` and `drain` say on stderr what retention gave up below the read (R4's
//!   addendum, A9), their stdout framing unchanged;
//! * `fetch` below its filter's oldest reads the mail retention still holds there and says
//!   on stderr what it gave up, where a filter's subjects have different floors (BUS-1).
#![cfg(unix)]

use astream_broker::{Broker, Client};
use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt;
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

static CTR: AtomicU64 = AtomicU64::new(0);

struct Paths {
    sock: String,
    log: String,
    dir: std::path::PathBuf,
}

fn fresh(tag: &str) -> Paths {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let dir = std::env::temp_dir().join(format!("asbclient_{tag}_{pid}_{n}"));
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

fn asb() -> Command {
    Command::new(env!("CARGO_BIN_EXE_asb"))
}

fn stdout(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}

fn stderr(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

/// A recognizable secret, with one byte that makes it invalid UTF-8.
const MARK: &str = "S3CR3T-MATERIAL-7f1c";

fn non_utf8_secret() -> OsString {
    let mut v = MARK.as_bytes().to_vec();
    v.push(0xff);
    OsString::from_vec(v)
}

/// std's `VarError::NotUnicode` renders the variable's VALUE in its `Display`, so an
/// error message built from it prints the secret the variable holds. A key or mint
/// secret whose bytes are not UTF-8 must be refused without its bytes on stderr.
#[test]
fn a_non_utf8_secret_in_the_environment_is_refused_without_being_echoed() {
    let p = fresh("envleak");
    for (verb, flag) in [
        (vec!["pub", p.sock.as_str(), "/a/x"], "--key-env"),
        (vec!["mint", "ro:/a/>"], "--secret-env"),
    ] {
        let out = asb()
            .args(&verb)
            .args([flag, "ASB_TEST_SECRET"])
            .env("ASB_TEST_SECRET", non_utf8_secret())
            .stdin(Stdio::null())
            .output()
            .unwrap();
        let err = stderr(&out);
        assert_eq!(out.status.code(), Some(2), "{verb:?}: {err}");
        assert!(!err.contains(MARK), "{verb:?} echoed the secret: {err}");
        assert!(
            err.contains("ASB_TEST_SECRET"),
            "{verb:?}: the message names the variable: {err}"
        );
    }
}

/// An unknown flag is a usage error that names the flag — but in the `--flag=value`
/// spelling the token also carries a VALUE, and a mistyped secret flag
/// (`--psk=<key>`, `--Key=<key>`) puts the key there. The refusal names the flag and
/// leaves the value out, so a supervisor's log does not keep what argv exposed.
#[test]
fn an_unknown_flag_is_named_without_its_inline_value() {
    let p = fresh("flagleak");
    let out = asb()
        .args(["pub", &p.sock, "/a/x", &format!("--psk={MARK}")])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let err = stderr(&out);
    assert_eq!(out.status.code(), Some(2), "{err}");
    assert!(err.contains("--psk"), "the flag is named: {err}");
    assert!(!err.contains(MARK), "the inline value was echoed: {err}");
}

/// `drain` opens its commit connection BEFORE the take and uses it only after. The
/// broker reaps a connection that sends no first frame within its first-frame
/// timeout (30 s by default), so a take that outlasted it — a long `--idle`, or
/// records trickling in — found its committer gone: exit 1 after the batch had been
/// taken, nothing committed, nothing printed. The timeout is shortened here so the
/// take outlasts it by a wide margin without the test taking 30 s.
#[test]
fn drain_commits_after_a_take_longer_than_the_first_frame_timeout() {
    let p = fresh("drainreap");
    let broker = Broker::open(&p.log).unwrap();
    broker.set_first_frame_timeout(Duration::from_millis(100));
    let _h = broker.serve(&p.sock).unwrap();
    let (at, _) = Client::connect(&p.sock)
        .unwrap()
        .publish(1, 1, "/f/F/in/x", b"hello")
        .unwrap();

    let group = "/f/F/cur/g";
    let out = asb()
        .args(["drain", &p.sock, group, "/f/F/in/>", "--idle", "1500"])
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(0), "{}", stderr(&out));
    assert_eq!(
        stdout(&out),
        format!("{at} 5 /f/F/in/x\nhello\nDRAIN n=1 upto={at} committed=yes\n")
    );

    // The commit is durable: the group resumes past the record.
    let out = asb()
        .args(["drain", &p.sock, group, "/f/F/in/>", "--idle", "200"])
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(0), "{}", stderr(&out));
    assert_eq!(stdout(&out), "DRAIN n=0 upto=- committed=no\n");
}

/// `--seq` exists so a retry of the same `(id, seq)` is deduped. Under the
/// per-invocation default id a retry from a new process is a NEW producer, so
/// the "retry" would append the record twice. Without `--id` (or one bound
/// grant) the flag is a usage error, like `--seq-file`; with `--id` a retry of
/// the same pair is deduped.
#[test]
fn an_explicit_seq_without_a_stable_producer_id_is_refused() {
    let p = fresh("seq_id");
    let broker = Broker::open(&p.log).unwrap();
    let _h = broker.serve(&p.sock).unwrap();
    let publish = |extra: &[&str]| {
        let mut c = asb()
            .args(["pub", &p.sock, "/a/x"])
            .args(extra)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        drop(c.stdin.take());
        c.wait_with_output().unwrap()
    };

    let out = publish(&["--seq", "1"]);
    assert_eq!(out.status.code(), Some(2), "{}", stderr(&out));
    assert!(
        stderr(&out).contains("--seq needs a producer id"),
        "{}",
        stderr(&out)
    );
    let mut c = Client::connect(&p.sock).unwrap();
    let (rows, _) = c.fetch(0, "/a/>", 10).unwrap();
    assert!(rows.is_empty(), "the refused publish appended nothing");

    let first = publish(&["--id", "9", "--seq", "1"]);
    assert_eq!(stdout(&first), "0 new\n", "{}", stderr(&first));
    let retry = publish(&["--id", "9", "--seq", "1"]);
    assert_eq!(stdout(&retry), "0 dup\n", "{}", stderr(&retry));
}

/// A body over the record cap can never be stored, so it is a usage error (exit
/// 2, "do not retry") refused before connecting, and `--seq-file` is not advanced.
#[test]
fn a_body_no_record_can_hold_is_refused_before_a_sequence_is_burned() {
    let p = fresh("too_big");
    let seq_file = p.dir.join("seq");
    let mut c = asb()
        .args(["pub", &p.sock, "/a/x", "--id", "3", "--seq-file"])
        .arg(&seq_file)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let body = vec![b'x'; astream_broker::MAX_RECORD_PAYLOAD + 1];
    let mut stdin = c.stdin.take().unwrap();
    std::thread::spawn(move || {
        use std::io::Write;
        let _ = stdin.write_all(&body);
    });
    let out = c.wait_with_output().unwrap();
    assert_eq!(out.status.code(), Some(2), "{}", stderr(&out));
    assert!(
        stderr(&out).contains("a record holds at most"),
        "{}",
        stderr(&out)
    );
    assert!(!seq_file.exists(), "no sequence was burned");
}

/// The log the gap test serves, made with the library and closed: five unread mails and
/// three stream records, under rules that keep the stream's newest two by their bytes and
/// mail for a week within three mails' bytes, so a tick gives up the two oldest mails. The
/// broker that serves it reads the rules back, and knows no count of what was given up
/// before it opened.
#[cfg(feature = "retention")]
fn gapped_log(path: &str) {
    use astream_broker::{record_bytes, BrokerLog, BrokerRecord, Retention, Rule};
    let bytes = |subject: &str| {
        record_bytes(&BrokerRecord {
            seq: astream_wire::Offset(0),
            producer_id: 1,
            producer_seq: 1,
            subject: subject.to_string(),
            body: b"body".to_vec(),
            commit: None,
        })
    };
    let rules = Retention::new(
        vec![
            Rule::prefix("/f/F/pub/*/*/ev")
                .unwrap()
                .max_bytes(2 * bytes("/f/F/pub/n1/s1/ev")),
            Rule::hold("/f/F/in/>")
                .unwrap()
                .max_bytes(3 * bytes("/f/F/in/n1/from/a"))
                .max_age(Duration::from_secs(7 * 86_400)),
        ],
        Rule::default_hold(),
    )
    .unwrap();
    let mut log = BrokerLog::open(path).unwrap();
    log.set_retention(rules).unwrap();
    let subjects = ["/f/F/in/n1/from/a"; 5]
        .into_iter()
        .chain(["/f/F/pub/n1/s1/ev"; 3]);
    for (seq, subject) in subjects.enumerate() {
        log.publish(1, seq as u64 + 1, subject.into(), b"body".to_vec())
            .unwrap();
    }
    let tick = log.retain_by_rules(1_800_000_000_000).unwrap();
    assert_eq!((tick.base, tick.carried), (6, 3));
}

/// `sub` AND `drain` SAY WHAT RETENTION GAVE UP below the read, on stderr (R4's addendum,
/// A9): of mail whose two oldest were given up, a tail from 0 is told `GAP from=0 to=2
/// records=unknown` while its stdout carries the three held mails in the framing it always
/// had; a group's drain is told the same and prints and commits its batch as before. NC: a
/// `sub` that reads records alone (`recv`), and a drain that never takes the notice its take
/// passed, say nothing on stderr.
#[cfg(feature = "retention")]
#[test]
fn sub_and_drain_say_on_stderr_what_retention_gave_up() {
    use std::io::Read;
    let p = fresh("gap");
    gapped_log(&p.log);
    let broker = Broker::open(&p.log).unwrap();
    let _h = broker.serve(&p.sock).unwrap();

    let mut sub = asb()
        .args(["sub", &p.sock, "/f/F/in/>"])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let mut out = sub.stdout.take().unwrap();
    let want = "2 4\nbody\n3 4\nbody\n4 4\nbody\n";
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let mut got = vec![0u8; want.len()];
        let _ = tx.send(out.read_exact(&mut got).map(|()| got));
    });
    // A hang detector, never a budget.
    let got = rx.recv_timeout(Duration::from_secs(60));
    let _ = sub.kill();
    let o = sub.wait_with_output().unwrap();
    let got = got
        .expect("sub delivered its records within a minute")
        .unwrap();
    assert_eq!(String::from_utf8_lossy(&got), want);
    assert_eq!(stderr(&o), "asb: sub: GAP from=0 to=2 records=unknown\n");

    let out = asb()
        .args([
            "drain",
            &p.sock,
            "/f/F/cur/n1/node/inbox",
            "/f/F/in/>",
            "--idle",
            "300",
        ])
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(0), "{}", stderr(&out));
    let mail = "/f/F/in/n1/from/a";
    assert_eq!(
        stdout(&out),
        format!(
            "2 4 {mail}\nbody\n3 4 {mail}\nbody\n4 4 {mail}\nbody\nDRAIN n=3 upto=4 committed=yes\n"
        )
    );
    assert_eq!(
        stderr(&out),
        "asb: drain: GAP from=0 to=2 records=unknown\n"
    );
}

/// `fetch` IS TOLD WHAT RETENTION GAVE UP BELOW ITS FILTER'S OLDEST, AND READS WHAT IT STILL
/// HOLDS THERE (BUS-1; R4's addendum, A9, on the fetch path). n2's mail at 1 and n1's at 2 are
/// carried below the base, 4, then n1's inbox group reads its own and a tick releases it: the
/// mail filter's oldest is n1's floor, 3, above n2's unread mail. `asb fetch` of all mail from 0
/// prints n2's mail in the framing it always had, with `GAP from=0 to=3 records=1` on stderr;
/// from 2, where the filter holds nothing below 3, it is refused `retained-from=3`, exit 1;
/// from 3 it reads on with nothing said. NC: a `fetch` that does not ask for notices
/// (`Client::fetch`) is refused from 0 and never prints n2's mail.
#[cfg(feature = "retention")]
#[test]
fn fetch_reads_what_retention_still_holds_below_its_oldest_and_says_what_it_gave_up() {
    use astream_broker::{record_bytes, BrokerRecord, Retention, Rule};
    let p = fresh("fetchgap");
    let ev = "/f/F/pub/n1/s1/ev";
    let n1 = "/f/F/in/n1/from/a";
    let n2 = "/f/F/in/n2/from/a";
    let rules = Retention::new(
        vec![
            Rule::prefix("/f/F/pub/*/*/ev")
                .unwrap()
                .max_bytes(record_bytes(&BrokerRecord {
                    seq: astream_wire::Offset(0),
                    producer_id: 1,
                    producer_seq: 1,
                    subject: ev.to_string(),
                    body: b"body".to_vec(),
                    commit: None,
                })),
            Rule::hold("/f/F/in/>")
                .unwrap()
                .max_age(Duration::from_secs(7 * 86_400))
                .until_read("/f/{2}/cur/{4}/node/inbox")
                .unwrap(),
        ],
        Rule::default_hold(),
    )
    .unwrap();
    let broker = Broker::open(&p.log).unwrap();
    broker.set_retention_interval(Duration::from_secs(3600));
    let _h = broker.serve(&p.sock).unwrap();
    let mut c = Client::connect(&p.sock).unwrap();
    for (seq, subject) in [ev, n2, n1, ev, ev].into_iter().enumerate() {
        let (at, _) = c.publish(1, seq as u64 + 1, subject, b"body").unwrap();
        assert_eq!(at, seq as u64);
    }
    broker.set_retention(rules).unwrap();
    // `set_retention` asks the broker's own ticker for a tick at once, and the commit's batch
    // may ask again, so each step below is that tick's or this one's, whichever runs first:
    // the test reads what the ticks left (the base and the held store), not one tick's count.
    let now = broker.now_ms();
    let tick = broker.retention_tick_at(now).unwrap();
    assert_eq!(
        (tick.base, broker.stats().log.held_records),
        (4, 2),
        "both mails carried"
    );
    c.commit("/f/F/cur/n1/node/inbox", 2).unwrap();
    broker.retention_tick_at(now + 60_000).unwrap();
    assert_eq!(
        broker.stats().log.held_records,
        1,
        "n1's group read its mail"
    );
    drop(c);

    let fetch = |from: &str| {
        asb()
            .args(["fetch", &p.sock, "/f/F/in/>", "--from", from])
            .output()
            .unwrap()
    };
    let o = fetch("0");
    assert_eq!(o.status.code(), Some(0), "{}", stderr(&o));
    // n1's group commit is the log's record at 5, so the head is 6.
    assert_eq!(stdout(&o), format!("1 4 {n2}\nbody\nMARK next=6 head=6\n"));
    assert_eq!(stderr(&o), "asb: fetch: GAP from=0 to=3 records=1\n");
    let o = fetch("2");
    assert_eq!(o.status.code(), Some(1), "{}", stderr(&o));
    assert!(stdout(&o).is_empty(), "{}", stdout(&o));
    assert!(stderr(&o).contains("retained-from=3"), "{}", stderr(&o));
    let o = fetch("3");
    assert_eq!(o.status.code(), Some(0), "{}", stderr(&o));
    assert_eq!(stdout(&o), "MARK next=6 head=6\n");
    assert_eq!(stderr(&o), "");
}
