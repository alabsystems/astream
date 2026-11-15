// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! `asb serve --durability strict|ordered|relaxed [--horizon-ms N]`: the tier from the
//! command line, as strict as every other flag, and what the broker SERVES told to a
//! client in `Hello` (never inferred from the flag). Real `asb` subprocesses,
//! synchronized on the serve readiness line — no sleeps.
#![cfg(unix)]

use astream_broker::{Client, ServedReason, Tier};
use std::io::{BufRead, BufReader};
use std::process::{Child, Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);

/// A scratch directory, removed on drop.
struct Dir(std::path::PathBuf);

impl Dir {
    fn new(tag: &str) -> Dir {
        let n = CTR.fetch_add(1, Ordering::Relaxed);
        let dir = std::env::temp_dir().join(format!("asbdur_{tag}_{}_{n}", std::process::id()));
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

fn asb() -> Command {
    Command::new(env!("CARGO_BIN_EXE_asb"))
}

fn run(args: &[&str]) -> Output {
    asb()
        .args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .unwrap()
}

/// A serving broker; killed and reaped on drop.
struct Serve(Child);

impl Drop for Serve {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

/// `asb serve <args>`, synchronized on its readiness line.
fn serve(args: &[&str]) -> Serve {
    let mut child = asb()
        .arg("serve")
        .args(args)
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    let mut line = String::new();
    BufReader::new(child.stdout.take().unwrap())
        .read_line(&mut line)
        .unwrap();
    assert!(line.starts_with("listening "), "serve {args:?}: {line:?}");
    Serve(child)
}

/// An unknown tier, a horizon for a tier that keeps none, and a horizon that is not a
/// number are usage errors (exit 2), decided before any log is opened.
#[test]
fn a_bad_durability_or_horizon_is_a_usage_error_and_opens_nothing() {
    let d = Dir::new("usage");
    let sock = d.path("b.sock");
    let log = d.path("b.log");
    for (args, says) in [
        (
            &["--durability", "eventual"][..],
            "expected strict, ordered or relaxed",
        ),
        (
            &["--durability", "strict", "--horizon-ms", "5"][..],
            "ordered alone",
        ),
        (&["--horizon-ms", "5"][..], "ordered alone"),
        (
            &["--durability", "ordered", "--horizon-ms", "soon"][..],
            "--horizon-ms",
        ),
    ] {
        let mut all = vec!["serve", sock.as_str(), log.as_str()];
        all.extend_from_slice(args);
        let out = run(&all);
        let err = String::from_utf8_lossy(&out.stderr);
        assert_eq!(out.status.code(), Some(2), "{args:?}: {err}");
        assert!(err.contains(says), "{args:?}: {err}");
        assert!(out.stdout.is_empty(), "{args:?}");
        assert!(
            !std::path::Path::new(&log).exists(),
            "{args:?}: no log opened"
        );
    }
}

/// Each tier asked for on the command line is what the broker reports in `Hello`:
/// requested, served (ordered is served strict off Apple), and the horizon asked for
/// (none for a tier that keeps none; zero is a horizon, not none).
#[test]
fn the_tier_asked_on_the_command_line_is_the_tier_hello_reports() {
    for (args, requested, horizon_ms) in [
        (&[][..], Tier::Strict, None),
        (&["--durability", "relaxed"][..], Tier::Relaxed, None),
        (&["--durability", "ordered"][..], Tier::Ordered, Some(1000)),
        (
            &["--durability", "ordered", "--horizon-ms", "250"][..],
            Tier::Ordered,
            Some(250),
        ),
        // A full flush after every batch: zero, never read as "no horizon".
        (
            &["--durability", "ordered", "--horizon-ms", "0"][..],
            Tier::Ordered,
            Some(0),
        ),
    ] {
        let d = Dir::new("tier");
        let sock = d.path("b.sock");
        let log = d.path("b.log");
        let mut all = vec![sock.as_str(), log.as_str()];
        all.extend_from_slice(args);
        let _broker = serve(&all);
        let mut c = Client::connect(&sock).unwrap();
        c.hello().unwrap();
        let told = c
            .served_durability()
            .expect("the Hello block carries the tier");
        assert_eq!(
            (told.requested, told.horizon_ms, told.rules),
            (requested, horizon_ms, 0)
        );
        if requested == Tier::Ordered && !cfg!(target_vendor = "apple") {
            assert_eq!(
                (told.served, told.reason),
                (Tier::Strict, ServedReason::NotApple)
            );
        } else {
            assert_eq!((told.served, told.reason), (requested, ServedReason::None));
        }
        // It serves: a publish is acked.
        c.publish(1, 1, "/a/x", b"one").unwrap();
    }
}
