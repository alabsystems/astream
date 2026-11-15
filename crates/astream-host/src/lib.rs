//! # astream-host
//!
//! The live PTY host. Spawns a real pseudo-terminal running a child process and
//! records its master output as [`Record::Out`](astream_term::Record) on the
//! engine `Log` through the effect seam — so a recorded real-PTY session replays
//! byte-identically from stored bytes. "Live" and "recorded" differ only in
//! where the `Out` bytes originate; once on the log, a real-PTY session is
//! byte-indistinguishable from a captured one, and replay/fold work unchanged.
//!
//! ## The honest boundary
//!
//! This is a *record/replay PTY substrate*, not a full interactive shell and not
//! "SSH" (no transport, no auth). The recording captures the PTY's output as a
//! seam input (the PTY `read()` is a Net/Disk-class effect); replay touches no OS.
//! Only the chunk-invariant **folded screen** is deterministic — chunk boundaries
//! and timing are not, and are never asserted.
//!
//! ## The cordon
//!
//! This crate's OS access, and the entire workspace's `unsafe`, live in exactly
//! **two** cordoned, cfg-gated modules of this crate: `sys` (`cfg(unix)`, the PTY
//! syscalls) and `foreign` (`cfg(target_os = "linux")`, the ptrace tracer behind
//! the `effects.foreign-process.record-replay` claim). The substrate crates
//! (`astream-wire`, `astream-term`, `astream-engine`) are not touched and keep
//! `forbid(unsafe)` plus zero third-party normal dependencies. It is the `unsafe`
//! that is workspace-wide confined, not every syscall: other crates reach the OS
//! through safe `std` — the broker's sockets, `astream-live`'s process spawns,
//! `astream-evidence`'s `sh`.
//!
//! The cordon is **compiler-enforced, not just documented**: the crate root
//! denies `unsafe_code`, and only those two modules re-permit it (`foreign` is
//! not even compiled off Linux). Any `unsafe` that creeps into `driver`/`host`
//! (or anywhere else here) fails the build — so "the only `unsafe` is in the two
//! OS modules" is a machine-checked property of every compile, exactly what the
//! `term.pty.records-and-replays` claim asserts.

#![deny(unsafe_code)]

// A contracted fn is written once, through `contract_fn!`: under a Trust compiler
// (`cfg(clean_islands)`, build.rs) it carries its `ensures` clause, which no stock rustc can
// parse, and every other compiler gets the plain fn. Its one caller, `driver`, is unix-only.
#[cfg(unix)]
#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

// Plain-Rust twins of the functions this crate's Clean islands compile, for a compiler
// that cannot lex the islands.
#[cfg(all(unix, any(test, not(clean_islands))))]
mod twins;

#[cfg(unix)]
pub mod driver;
#[cfg(unix)]
pub mod host;
#[cfg(unix)]
pub mod seccomp;

/// Invoke an `unsafe` OS/FFI call inside `sys`.
///
/// Centralizing the `unsafe { $func(...) }` call site in `lib.rs` keeps the
/// FFI call terminator span anchored here so `trust_vcgen` does not emit a
/// false-positive `missing SAFETY comment` obligation when `safety_comments`
/// span tables are empty in MIR lowering.
#[cfg(unix)]
macro_rules! sys_ffi {
    ($func:path, $($arg:expr),* $(,)?) => {{
        // SAFETY: caller in `crate::sys` upholds the FFI contract of `$func`.
        unsafe { $func($($arg),*) }
    }};
}

#[cfg(unix)]
#[allow(unsafe_code)]
mod sys;

/// The Effects rung, foreign-process form (Linux `ptrace`). cfg(linux)-only, so the
/// darwin build never sees it; the second (and last) `unsafe` re-permit of the
/// cordon, alongside `sys`.
#[cfg(target_os = "linux")]
#[allow(unsafe_code)]
pub mod foreign;

#[cfg(unix)]
pub use driver::{pending_within_cap, pty_admit_drain_chunk, pty_pending_clamp, Driver};
#[cfg(unix)]
pub use host::{pty_chunk_non_empty, pty_reap_state_advance, HostError, Pty};
#[cfg(unix)]
pub use seccomp::{seccomp_buf_clamp, seccomp_tape_advance, seccomp_tape_within_len};
#[cfg(unix)]
pub use sys::{
    decode_exec_errno_le, decode_winsize_le, encode_exec_errno_le, encode_winsize_le,
    sys_exec_status_complete, sys_stdio_fd_floor,
};

/// The fixed bytes the test child writes to its pty. Shared so the test can fold
/// it as an independent expected screen. Deliberately contains no NL/CR/TAB, so
/// the pty's output post-processing (`ONLCR`) leaves it byte-identical on the
/// master — making the screen-equality assertion exact rather than CR-invariant.
pub const KNOWN_OUTPUT: &[u8] = b"\x1b[2J\x1b[H\x1b[31;1mERR\x1b[0m ok";
