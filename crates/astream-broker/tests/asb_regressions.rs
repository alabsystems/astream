//! `asb` shell-face regressions, each a real `asb` subprocess:
//!
//! * a secret must never reach stderr — not from a key/secret environment variable
//!   that is not valid UTF-8, and not from a mistyped `--flag=<value>`;
//! * `drain` must be able to commit a batch whose take outlasted the broker's
//!   first-frame timeout;
//! * an explicit `pub --seq` is a dedup key only under a stable producer id, so
//!   without one it is refused rather than published under the process id;
//! * a body no record can hold is bad input (exit 2), refused before a
//!   `--seq-file` sequence is burned.
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
