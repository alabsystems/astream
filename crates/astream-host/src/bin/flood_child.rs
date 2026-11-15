//! The pathological child for the `drive` test's drain-bound case: it consumes
//! its input **one byte at a time** and answers every byte with 8 KiB of output.
//!
//! That is the shape that grows the orchestrator's drain buffer: while the pty's
//! kernel input queue is full, `Pty::write_input` waits and drains the master to
//! keep it from wedging, so the output this child produces per accepted input
//! byte piles up in the pending buffer — without a cap, until the orchestrator is
//! OOM-killed. Deterministic: no clock, randomness, or environment; it exits at
//! EOF, on any I/O error, or when it is killed.

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
#[path = "islands/flood_child_twins.rs"]
mod twins;

use std::io::{Read, Write};

const BURST_BLOCKS: u64 = 8;

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "islands/flood_child_island.rs"]
mod flood_child_island;
#[cfg(clean_islands)]
use flood_child_island::flood_child_advance_step;
#[cfg(not(clean_islands))]
use twins::flood_child_advance_step;

contract_fn! {
    /// Verified guard checking that the current burst step is strictly below `BURST_BLOCKS` (8).
    pub const fn flood_child_within_burst(step: u64) -> bool
    clauses [ensures result == (step < 8)]
    {
        step < BURST_BLOCKS
    }
}

/// Four-byte magic prefix (`"AFLD"`) for a 16-byte `flood_child` burst wire header.
pub const FLOOD_CHILD_BURST_WIRE_MAGIC: [u8; 4] = *b"AFLD";

/// Wire format version for `flood_child` burst wire headers.
pub const FLOOD_CHILD_BURST_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `flood_child` burst wire header:
/// `[0..4] = b"AFLD"`, `[4] = version (1)`, `[5] = fill_byte (b'F')`,
/// `[6..8] = block_len (BE)`, `[8..16] = step (BE)` (requires `step < BURST_BLOCKS` and `block_len > 0`).
#[must_use]
pub const fn flood_child_encode_burst_wire(
    fill_byte: u8,
    block_len: u16,
    step: u64,
) -> Option<[u8; 16]> {
    if !flood_child_within_burst(step) || block_len == 0 || fill_byte == b'\n' || fill_byte == b'\r'
    {
        return None;
    }
    Some([
        FLOOD_CHILD_BURST_WIRE_MAGIC[0],
        FLOOD_CHILD_BURST_WIRE_MAGIC[1],
        FLOOD_CHILD_BURST_WIRE_MAGIC[2],
        FLOOD_CHILD_BURST_WIRE_MAGIC[3],
        FLOOD_CHILD_BURST_WIRE_VERSION,
        fill_byte,
        ((block_len >> 8) & 0xFF) as u8,
        (block_len & 0xFF) as u8,
        ((step >> 56) & 0xFF) as u8,
        ((step >> 48) & 0xFF) as u8,
        ((step >> 40) & 0xFF) as u8,
        ((step >> 32) & 0xFF) as u8,
        ((step >> 24) & 0xFF) as u8,
        ((step >> 16) & 0xFF) as u8,
        ((step >> 8) & 0xFF) as u8,
        (step & 0xFF) as u8,
    ])
}

/// Decode a 16-byte `flood_child` burst wire header into `(fill_byte, block_len, step)`.
#[must_use]
pub const fn flood_child_decode_burst_wire(buf: &[u8]) -> Option<(u8, u16, u64)> {
    let [b'A', b'F', b'L', b'D', FLOOD_CHILD_BURST_WIRE_VERSION, fill_byte, b0, b1, s0, s1, s2, s3, s4, s5, s6, s7, ..] =
        *buf
    else {
        return None;
    };
    let block_len = ((b0 as u16) << 8) | (b1 as u16);
    let step = ((s0 as u64) << 56)
        | ((s1 as u64) << 48)
        | ((s2 as u64) << 40)
        | ((s3 as u64) << 32)
        | ((s4 as u64) << 24)
        | ((s5 as u64) << 16)
        | ((s6 as u64) << 8)
        | (s7 as u64);
    if !flood_child_within_burst(step) || block_len == 0 || fill_byte == b'\n' || fill_byte == b'\r'
    {
        return None;
    }
    Some((fill_byte, block_len, step))
}

fn main() {
    let stdin = std::io::stdin();
    let mut input = stdin.lock();
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    // No NL/CR in the output, so the pty's ONLCR post-processing leaves it
    // byte-identical on the master.
    let block = [b'F'; 1024];
    let mut byte = [0u8; 1];
    loop {
        let mut step = 0u64;
        while flood_child_within_burst(step) {
            if out.write_all(&block).is_err() || out.flush().is_err() {
                return;
            }
            step = flood_child_advance_step(step, step.saturating_add(1));
        }
        match input.read(&mut byte) {
            Ok(0) | Err(_) => return,
            Ok(_) => {}
        }
    }
}
