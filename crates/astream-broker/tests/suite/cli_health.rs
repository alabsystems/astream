// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! `asb serve` keeps the health sidecar `<log>.health` (`--health-ms`, default 2 s), and
//! `asb stats` reads it for a LIVE log — one a running broker holds locked, which
//! `stats` cannot open — saying whether the broker that wrote it still serves the log.
//! Real `asb` subprocesses, synchronized on the serve readiness line and on what `stats`
//! prints (a one-minute hang detector), never on a sleep.
#![cfg(unix)]

use astream_broker::{Broker, Client};
use std::io::{BufRead, BufReader};
use std::process::{Child, Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

static CTR: AtomicU64 = AtomicU64::new(0);

/// A scratch directory, removed on drop.
struct Dir(std::path::PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        let n = CTR.fetch_add(1, Ordering::Relaxed);
        let dir = std::env::temp_dir().join(format!("asbhl_{tag}_{}_{n}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        Dir(dir)
    }

    fn path(&self, name: &str) -> String {
        self.0.join(name).to_str().unwrap().to_string()
    }
}

impl Drop for Dir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn run(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_asb"))
        .args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .unwrap()
}

/// A serving `asb`; SIGKILLed and reaped on drop — no clean close, so the kernel is
/// what lets the sidecar's lock go.
struct Serve(Child);

impl Drop for Serve {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

/// `asb serve <sock> <log> <args>`, synchronized on its readiness line.
fn serve(sock: &str, log: &str, args: &[&str]) -> Serve {
    let mut child = Command::new(env!("CARGO_BIN_EXE_asb"))
        .args(["serve", sock, log])
        .args(args)
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    let mut line = String::new();
    BufReader::new(child.stdout.take().unwrap())
        .read_line(&mut line)
        .unwrap();
    assert_eq!(line, format!("listening {sock}\n"), "serve readiness");
    Serve(child)
}

/// `asb stats <log>`, again until `done` accepts what it printed — a one-minute HANG
/// DETECTOR, never a latency budget.
fn stats_until(log: &str, what: &str, done: impl Fn(&str) -> bool) -> String {
    let deadline = Instant::now() + Duration::from_secs(60);
    loop {
        let out = run(&["stats", log]);
        let line = String::from_utf8_lossy(&out.stdout).into_owned();
        if out.status.code() == Some(0) && done(&line) {
            return line;
        }
        assert!(
            Instant::now() < deadline,
            "{what}: never printed (last: {line:?}, stderr {:?})",
            String::from_utf8_lossy(&out.stderr)
        );
        std::thread::yield_now();
    }
}

/// A served log: `stats` cannot open it, and reads the serving broker's sidecar — the
/// offline line's counts first, then the broker's own: its heads, one connection, the
/// tier served, no failed flush, the serve process's full flushes (`process_flush_full`),
/// both records resident (no `--resident-budget`), `writer=serving` with the serve
/// process's pid, and `poisoned=no` last. Once that process is gone (SIGKILL: no clean
/// close), the log is no one's and `stats` opens it again, printing the offline line.
#[test]
fn stats_reads_a_served_log_from_its_health_sidecar() {
    let d = Dir::new("live");
    let (sock, log) = (d.path("b.sock"), d.path("b.log"));
    let s = serve(&sock, &log, &["--health-ms", "20"]);
    let pid = s.0.id();
    let mut c = Client::connect(&sock).unwrap();
    c.publish(1, 1, "/o/a", b"one").unwrap();
    c.publish(1, 2, "/o/b", b"two").unwrap();

    let line = stats_until(&log, "the served log's two records", |l| {
        l.starts_with("base=0 head=2 records=2 ")
    });
    for want in [
        " subjects=2 ",
        " replica=no ",
        " visible=2 ",
        " durable=2 ",
        " connections=1 ",
        " served=strict ",
        " flush_failed=0 ",
        " resident_records=2 ",
        " writer=serving ",
        &format!(" pid={pid} "),
    ] {
        assert!(line.contains(want), "{want:?} in {line:?}");
    }
    assert!(line.ends_with(" poisoned=no\n"), "{line:?}");
    // The serve process's own tally rides the snapshot: the line says durable=2, so its
    // Strict publishes had already been flushed in full when the snapshot was taken.
    let full = line
        .split(" process_flush_full=")
        .nth(1)
        .and_then(|rest| rest.split(' ').next())
        .and_then(|n| n.parse::<u64>().ok());
    assert!(
        full.is_some_and(|n| n > 0),
        "the serve process's full flushes in {line:?}"
    );

    drop(c);
    drop(s);
    let out = run(&["stats", &log]);
    let line = String::from_utf8_lossy(&out.stdout);
    assert_eq!(out.status.code(), Some(0), "{line}");
    assert!(line.starts_with("base=0 head=2 records=2 "), "{line}");
    assert!(!line.contains("writer="), "the offline line: {line}");
}

/// NEGATIVE CONTROLS: a live log whose sidecar is NOT current prints nothing. A serve
/// killed leaves a sidecar no one holds; with the log then held by a broker that keeps
/// none, `stats` exits 1 naming the dead writer's pid, stdout empty — never the dead
/// broker's counts as the live one's. With no sidecar at all, it exits 1 saying the
/// serving broker keeps none.
#[test]
fn stats_prints_no_snapshot_whose_writer_is_gone_or_absent() {
    let d = Dir::new("gone");
    let (sock, log) = (d.path("b.sock"), d.path("b.log"));
    let s = serve(&sock, &log, &["--health-ms", "20"]);
    let pid = s.0.id();
    stats_until(&log, "the serve's sidecar", |l| {
        l.contains(" writer=serving ")
    });
    drop(s);

    let held = Broker::open(&log).unwrap();
    let out = run(&["stats", &log]);
    let err = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(1), "{err}");
    assert!(out.stdout.is_empty(), "nothing printed");
    assert!(
        err.contains("no longer serves it") && err.contains(&format!("pid {pid}")),
        "{err}"
    );
    drop(held);

    std::fs::remove_file(format!("{log}.health")).unwrap();
    let held = Broker::open(&log).unwrap();
    let out = run(&["stats", &log]);
    let err = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(1), "{err}");
    assert!(out.stdout.is_empty());
    assert!(err.contains("keeps no health sidecar"), "{err}");
    drop(held);
}

/// `--health-ms` is as strict as every other flag: zero, a word, or the flag on
/// another verb are usage errors (exit 2), decided before any log is opened.
#[test]
fn a_bad_health_period_is_a_usage_error_and_opens_nothing() {
    let d = Dir::new("usage");
    let (sock, log) = (d.path("b.sock"), d.path("b.log"));
    for (args, says) in [
        (
            &["serve", &sock, &log, "--health-ms", "0"][..],
            "at least 1 ms",
        ),
        (
            &["serve", &sock, &log, "--health-ms", "soon"][..],
            "--health-ms",
        ),
        (&["stats", &log, "--health-ms", "5"][..], "--health-ms"),
    ] {
        let out = run(args);
        let err = String::from_utf8_lossy(&out.stderr);
        assert_eq!(out.status.code(), Some(2), "{args:?}: {err}");
        assert!(err.contains(says), "{args:?}: {err}");
        assert!(out.stdout.is_empty(), "{args:?}");
        assert!(!std::path::Path::new(&log).exists(), "{args:?}: no log");
    }
}
