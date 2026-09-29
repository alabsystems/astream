//! Term-layer microbenchmark for the regression gate.
//!
//! Prints `METRIC <name> <ops_per_sec>` that `astream-evidence` checks against a
//! floor. This guards the screen FOLD — the pure VT projection every perception
//! modality and every replay depends on — against a catastrophic slowdown. It is
//! a regression gate, not a cross-system comparison.
//!
//! Run with `--release` for representative numbers:
//!   cargo run --release -p astream-term --example term_microbench

use astream_term::{screen, Record};
use std::hint::black_box;
use std::time::Instant;

fn main() {
    // A representative output stream: cursor addressing + SGR colour/bold + printable
    // text across a full 80x24 screen (the common interactive shape).
    let mut chunk = Vec::new();
    for row in 0..24u16 {
        chunk.extend_from_slice(format!("\x1b[{};1H", row + 1).as_bytes());
        chunk.extend_from_slice(b"\x1b[32mhello \x1b[1mworld\x1b[0m the quick brown fox jumps");
    }
    let records = vec![Record::Out(chunk)];

    let iters: u64 = 50_000;
    let start = Instant::now();
    let mut acc = 0usize;
    for _ in 0..iters {
        let s = screen::fold(80, 24, &records);
        acc += s.line_text(0).len();
    }
    black_box(acc);
    let ops = iters as f64 / start.elapsed().as_secs_f64();
    println!("METRIC term_fold_ops_per_sec {ops:.0}");
}
