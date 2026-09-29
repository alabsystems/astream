//! Regression test: `aspump` must not PANIC on an argument that is not valid
//! Unicode.
//!
//! `std::env::args()` panics on such an argument — exit 101 with a Rust backtrace,
//! none of the three statuses `aspump`'s module doc enumerates (`0` clean end, `1`
//! broker error, `2` usage error), so a supervisor that distinguishes 2 ("bad
//! config, do not retry") from 1 ("transient, retry") could classify neither.
//! `--key-file /mnt/keys/<a name with a non-UTF-8 byte>` is a plausible real path,
//! and a malformed argument is a usage error.
#![cfg(unix)]

use std::os::unix::ffi::OsStrExt;
use std::process::Command;

fn aspump() -> Command {
    Command::new(env!("CARGO_BIN_EXE_aspump"))
}

/// A path holding byte 0xFF, which is not valid UTF-8 anywhere in it.
fn non_utf8_path() -> std::ffi::OsString {
    std::ffi::OsString::from(std::ffi::OsStr::from_bytes(b"/tmp/r2-key\xff"))
}

#[test]
fn a_non_utf8_argument_is_a_usage_error_not_a_panic() {
    // The endpoint does not exist, so a run that got past argv parsing would exit 1
    // on the connect — never 2. Reaching 2 therefore proves the argument itself was
    // rejected, and reaching it without a panic proves `args_os`.
    let out = aspump()
        .arg("/tmp/r2-aspump-no-such.sock")
        .arg("s1")
        .arg("--key-file")
        .arg(non_utf8_path())
        .output()
        .unwrap();

    let err = String::from_utf8_lossy(&out.stderr);
    assert_eq!(
        out.status.code(),
        Some(2),
        "a malformed argument is a usage error, not a panic (stderr: {err})"
    );
    assert!(!err.contains("panicked"), "no panic, no backtrace: {err}");
    assert!(
        err.contains("not valid UTF-8"),
        "the message says what is wrong: {err}"
    );
}

/// A non-UTF-8 POSITIONAL is the same usage error — the panic was in collecting
/// argv, so it never depended on which argument carried the bad bytes.
#[test]
fn a_non_utf8_positional_is_a_usage_error_too() {
    let out = aspump().arg(non_utf8_path()).arg("s1").output().unwrap();
    let err = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(2), "stderr: {err}");
    assert!(!err.contains("panicked"), "{err}");
}
