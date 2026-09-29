//! The deterministic child for the `pty_record_replay` test. Writes the fixed
//! `KNOWN_OUTPUT` byte string to stdout and exits 0. Its output is a pure
//! function of its (empty) argv — no clock, randomness, network, or environment
//! — so the recorded session is reproducible. Spawned by the test via
//! `CARGO_BIN_EXE_pty_child`, never via a PATH-dependent name.

use std::io::Write;

fn main() {
    let stdout = std::io::stdout();
    let mut handle = stdout.lock();
    handle
        .write_all(astream_host::KNOWN_OUTPUT)
        .expect("write KNOWN_OUTPUT");
    handle.flush().expect("flush");
}
