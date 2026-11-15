//! The deterministic child for the `pty_record_replay` test. Writes the fixed
//! `KNOWN_OUTPUT` byte string to stdout and exits 0. Its output is a pure
//! function of its (empty) argv — no clock, randomness, network, or environment
//! — so the recorded session is reproducible. Spawned by the test via
//! `CARGO_BIN_EXE_pty_child`, never via a PATH-dependent name.

#![forbid(unsafe_code)]

// A contracted fn is written once, through `contract_fn!`: under a Trust compiler
// (`cfg(clean_islands)`, build.rs) it carries its `ensures` clause, which no stock rustc can
// parse, and every other compiler gets the plain fn.
#[macro_use]
#[path = "../../../astream-wire/contract_fn.rs"]
mod contract_fn;

// Plain-Rust twins of the functions this binary's Clean island compiles, for a compiler
// that cannot lex the island.
#[cfg(any(test, not(clean_islands)))]
#[path = "islands/pty_child_twins.rs"]
mod twins;

use std::io::Write;

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "islands/pty_child_island.rs"]
mod pty_child_island;
#[cfg(clean_islands)]
use pty_child_island::pty_child_clamp_len;
#[cfg(not(clean_islands))]
use twins::pty_child_clamp_len;

contract_fn! {
    /// Verified guard checking that the payload to write is non-empty.
    pub const fn pty_child_payload_nonempty(len: u64) -> bool
    clauses [ensures result == (len > 0)]
    {
        len > 0
    }
}

/// Four-byte magic prefix (`"APTY"`) for a 16-byte `pty_child` banner wire header.
pub const PTY_CHILD_BANNER_WIRE_MAGIC: [u8; 4] = *b"APTY";

/// Wire format version for `pty_child` banner wire headers.
pub const PTY_CHILD_BANNER_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `pty_child` banner wire header:
/// `[0..4] = b"APTY"`, `[4] = version (1)`, `[5] = exit_code` (`0..=1`),
/// `[6..8] = payload_len (BE)`, `[8..16] = clamped_len (BE)`.
#[must_use]
pub const fn pty_child_encode_banner_wire(
    exit_code: u8,
    payload_len: u16,
    clamped_len: u64,
) -> Option<[u8; 16]> {
    if exit_code > 1
        || !pty_child_payload_nonempty(payload_len as u64)
        || clamped_len > payload_len as u64
    {
        return None;
    }
    Some([
        PTY_CHILD_BANNER_WIRE_MAGIC[0],
        PTY_CHILD_BANNER_WIRE_MAGIC[1],
        PTY_CHILD_BANNER_WIRE_MAGIC[2],
        PTY_CHILD_BANNER_WIRE_MAGIC[3],
        PTY_CHILD_BANNER_WIRE_VERSION,
        exit_code,
        ((payload_len >> 8) & 0xFF) as u8,
        (payload_len & 0xFF) as u8,
        ((clamped_len >> 56) & 0xFF) as u8,
        ((clamped_len >> 48) & 0xFF) as u8,
        ((clamped_len >> 40) & 0xFF) as u8,
        ((clamped_len >> 32) & 0xFF) as u8,
        ((clamped_len >> 24) & 0xFF) as u8,
        ((clamped_len >> 16) & 0xFF) as u8,
        ((clamped_len >> 8) & 0xFF) as u8,
        (clamped_len & 0xFF) as u8,
    ])
}

/// Decode a 16-byte `pty_child` banner wire header into `(exit_code, payload_len, clamped_len)`.
#[must_use]
pub const fn pty_child_decode_banner_wire(buf: &[u8]) -> Option<(u8, u16, u64)> {
    let [b'A', b'P', b'T', b'Y', PTY_CHILD_BANNER_WIRE_VERSION, exit_code, p0, p1, c0, c1, c2, c3, c4, c5, c6, c7, ..] =
        *buf
    else {
        return None;
    };
    let payload_len = ((p0 as u16) << 8) | (p1 as u16);
    let clamped_len = ((c0 as u64) << 56)
        | ((c1 as u64) << 48)
        | ((c2 as u64) << 40)
        | ((c3 as u64) << 32)
        | ((c4 as u64) << 24)
        | ((c5 as u64) << 16)
        | ((c6 as u64) << 8)
        | (c7 as u64);
    if exit_code > 1
        || !pty_child_payload_nonempty(payload_len as u64)
        || clamped_len > payload_len as u64
    {
        return None;
    }
    Some((exit_code, payload_len, clamped_len))
}

fn main() -> std::process::ExitCode {
    let payload = astream_host::KNOWN_OUTPUT;
    let _clamped = pty_child_clamp_len(payload.len() as u64, 4096);
    if !pty_child_payload_nonempty(payload.len() as u64) {
        return std::process::ExitCode::from(1);
    }
    let stdout = std::io::stdout();
    let mut handle = stdout.lock();
    if handle.write_all(payload).is_err() || handle.flush().is_err() {
        return std::process::ExitCode::from(1);
    }
    std::process::ExitCode::SUCCESS
}
