//! The pathological child for the `drive` test's drain-bound case: it consumes
//! its input **one byte at a time** and answers every byte with 8 KiB of output.
//!
//! That is the shape that grows the orchestrator's drain buffer: while the pty's
//! kernel input queue is full, `Pty::write_input` waits and drains the master to
//! keep it from wedging, so the output this child produces per accepted input
//! byte piles up in the pending buffer — without a cap, until the orchestrator is
//! OOM-killed. Deterministic: no clock, randomness, or environment; it exits at
//! EOF, on any I/O error, or when it is killed.

use std::io::{Read, Write};

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
        for _ in 0..8 {
            if out.write_all(&block).is_err() || out.flush().is_err() {
                return;
            }
        }
        match input.read(&mut byte) {
            Ok(0) | Err(_) => return,
            Ok(_) => {}
        }
    }
}
