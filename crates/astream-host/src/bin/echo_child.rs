//! Interactive child for the drive test: reads stdin line by line and echoes each
//! line back as `GOT:<line>`, exiting on the line `quit`. Its output is a
//! deterministic function of its input — no clock, randomness, or environment.

use std::io::{BufRead, Write};

fn main() {
    let stdin = std::io::stdin();
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    for line in stdin.lock().lines() {
        let line = match line {
            Ok(l) => l,
            Err(_) => break,
        };
        if line == "quit" {
            break;
        }
        let _ = writeln!(out, "GOT:{line}");
        let _ = out.flush();
    }
}
