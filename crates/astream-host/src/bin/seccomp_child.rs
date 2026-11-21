// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Standalone unmodified foreign target binary for `seccomp_record_replay`.
//!
//! Performs zero `PTRACE_TRACEME`, zero `SIGSTOP`, and zero cooperation with any recorder:
//! on Linux it reads `argv[1]` via one `clock_gettime`, one 8-byte `getrandom`, and one
//! `openat` + `read` + `close`, folds `(clock, rand, bytes)` non-commutatively into an 8-byte
//! little-endian digest written to stdout, and exits `0`. Spawned via `fork` + `PTRACE_TRACEME`
//! + `seccomp(SECCOMP_SET_MODE_FILTER)` + `execve` by `astream_host::foreign::{record_exec, replay_exec}`.

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../../astream-wire/contract_fn.rs"]
mod contract_fn;

#[cfg(any(test, not(clean_islands)))]
#[path = "islands/seccomp_child_twins.rs"]
mod twins;

#[cfg(clean_islands)]
#[path = "islands/seccomp_child_island.rs"]
mod seccomp_child_island;
#[cfg(clean_islands)]
use seccomp_child_island::seccomp_child_clamp_read;
#[cfg(not(clean_islands))]
use twins::seccomp_child_clamp_read;

contract_fn! {
    /// Verified check that the emitted digest frame is 8 bytes.
    pub const fn seccomp_child_digest_len_valid(len: u64) -> bool
    clauses [ensures result == (len == 8)]
    {
        len == 8
    }
}

/// Clamp a raw byte read count to `cap` (`256`).
#[must_use]
pub const fn clamp_probe_bytes(got: u64) -> u64 {
    seccomp_child_clamp_read(got, 256)
}

fn main() -> std::process::ExitCode {
    let clamped = clamp_probe_bytes(8);
    if !seccomp_child_digest_len_valid(clamped) {
        return std::process::ExitCode::from(2);
    }
    #[cfg(target_os = "linux")]
    {
        let mut args = std::env::args();
        let _ = args.next();
        let Some(path) = args.next() else {
            return std::process::ExitCode::from(2);
        };
        let code = astream_host::foreign::run_unmodified_probe(&path);
        return std::process::ExitCode::from(code as u8);
    }
    #[cfg(not(target_os = "linux"))]
    {
        std::process::ExitCode::SUCCESS
    }
}
