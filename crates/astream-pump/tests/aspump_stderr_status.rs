//! Regression test: `aspump` must not PANIC when its STDERR has no reader.
//!
//! The same hazard as `aspump_argv`, one stream over. `eprintln!` panics on a
//! write error, so any diagnostic path — `usage_error` included — would exit 101
//! with a Rust backtrace whenever stderr is gone (`aspump ... 2>&1 | head -0`, a
//! supervisor that closes both pipes, a full disk on a redirected log). 101 is none
//! of the three statuses `aspump`'s module doc enumerates (`0` clean end, `1` broker
//! error, `2` usage error). The message is what is lost when stderr is gone; the
//! status is what is left, so it must be the right one.
//!
//! Deterministic: the pipe's READ end is dropped BEFORE the child is spawned, so the
//! child's first write to stderr cannot race the close. No sleeps.
#![cfg(unix)]

use std::process::{Command, Stdio};

fn aspump() -> Command {
    Command::new(env!("CARGO_BIN_EXE_aspump"))
}

/// A stdio handle whose read end is already closed: writing to it fails with EPIPE.
/// `std::io::pipe` is std — no dependency, no `unsafe`.
fn dead() -> Stdio {
    let (r, w) = std::io::pipe().expect("pipe");
    drop(r);
    Stdio::from(w)
}

/// A USAGE ERROR WITH NOWHERE TO PRINT IT IS STILL EXIT 2.
#[test]
fn a_usage_error_with_a_dead_stderr_is_still_exit_2() {
    // No endpoint at all: a run that got past argv parsing would exit 1 on the
    // connect, so reaching 2 proves the refusal happened and did not panic.
    let out = aspump()
        .stdout(Stdio::null())
        .stderr(dead())
        .output()
        .unwrap();
    assert_eq!(
        out.status.code(),
        Some(2),
        "a usage error with stderr closed must stay exit 2, not 101"
    );

    // A strict flag value, the other shape of exit 2.
    let out = aspump()
        .args(["/tmp/r4-aspump-no-such.sock", "s1", "--cols", "0"])
        .stdout(Stdio::null())
        .stderr(dead())
        .output()
        .unwrap();
    assert_eq!(
        out.status.code(),
        Some(2),
        "a rejected flag value with stderr closed must stay exit 2, not 101"
    );
}

/// A BROKER-SIDE FAILURE WITH NOWHERE TO PRINT IT IS STILL EXIT 1.
#[test]
fn a_connect_failure_with_a_dead_stderr_is_still_exit_1() {
    let out = aspump()
        .args(["/tmp/r4-aspump-no-such.sock", "s1"])
        .stdout(Stdio::null())
        .stderr(dead())
        .output()
        .unwrap();
    assert_eq!(
        out.status.code(),
        Some(1),
        "a connect failure with stderr closed must stay exit 1, not 101"
    );
}

/// AND THE STATUSES ARE UNCHANGED WHEN STDERR IS READABLE — the message is still
/// written, so dropping an undeliverable diagnostic did not become dropping every
/// diagnostic.
#[test]
fn a_readable_stderr_still_gets_the_message() {
    let out = aspump().output().unwrap();
    let err = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(2), "{err}");
    assert!(err.contains("missing <endpoint>"), "{err}");
    assert!(!err.contains("panicked"), "{err}");

    let out = aspump()
        .args(["/tmp/r4-aspump-no-such.sock", "s1"])
        .output()
        .unwrap();
    let err = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(1), "{err}");
    assert!(err.contains("aspump: connect"), "{err}");
}
