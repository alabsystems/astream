//! Interactive child for the drive test: reads stdin line by line and echoes each
//! line back as `GOT:<line>`, exiting on the line `quit`. Its output is a
//! deterministic function of its input and argv — no clock, randomness, or
//! environment.
//!
//! `--tally` adds one line on `quit`: `SAW:` and the first four bytes of every line
//! read, comma-separated, in order. A `GOT:` line can reach the master split by the
//! tty's echo of input that arrives while the child's write is blocked on a full
//! output queue; the tally is written after the last input was read, when nothing is
//! left to echo, so it arrives whole.

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
#[path = "islands/echo_child_twins.rs"]
mod twins;

use std::io::{BufRead, Write};

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "islands/echo_child_island.rs"]
mod echo_child_island;
#[cfg(clean_islands)]
use echo_child_island::echo_child_advance_lines;
#[cfg(not(clean_islands))]
use twins::echo_child_advance_lines;

contract_fn! {
    /// Verified guard checking whether a line's byte length matches `"quit"` (4 bytes).
    pub const fn echo_child_is_quit_len(len: u64) -> bool
    clauses [ensures result == (len == 4)]
    {
        len == 4
    }
}

/// Four-byte magic prefix (`"AECH"`) for a 16-byte `echo_child` frame wire header.
pub const ECHO_CHILD_FRAME_WIRE_MAGIC: [u8; 4] = *b"AECH";

/// Wire format version for `echo_child` frame wire headers.
pub const ECHO_CHILD_FRAME_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `echo_child` frame wire header:
/// `[0..4] = b"AECH"`, `[4] = version (1)`, `[5] = tally (0/1)`,
/// `[6] = is_quit (0/1)`, `[7] = 0`, `[8..16] = lines_seen (BE)`.
#[must_use]
pub const fn echo_child_encode_frame_wire(
    tally: bool,
    is_quit: bool,
    lines_seen: u64,
) -> Option<[u8; 16]> {
    let [m0, m1, m2, m3] = ECHO_CHILD_FRAME_WIRE_MAGIC;
    let tb = if tally { 1u8 } else { 0u8 };
    let qb = if is_quit { 1u8 } else { 0u8 };
    Some([
        m0,
        m1,
        m2,
        m3,
        ECHO_CHILD_FRAME_WIRE_VERSION,
        tb,
        qb,
        0,
        ((lines_seen >> 56) & 0xFF) as u8,
        ((lines_seen >> 48) & 0xFF) as u8,
        ((lines_seen >> 40) & 0xFF) as u8,
        ((lines_seen >> 32) & 0xFF) as u8,
        ((lines_seen >> 24) & 0xFF) as u8,
        ((lines_seen >> 16) & 0xFF) as u8,
        ((lines_seen >> 8) & 0xFF) as u8,
        (lines_seen & 0xFF) as u8,
    ])
}

/// Decode a 16-byte `echo_child` frame wire header into `(tally, is_quit, lines_seen)`.
#[must_use]
pub const fn echo_child_decode_frame_wire(buf: &[u8]) -> Option<(bool, bool, u64)> {
    let [b'A', b'E', b'C', b'H', ECHO_CHILD_FRAME_WIRE_VERSION, tb, qb, 0, l0, l1, l2, l3, l4, l5, l6, l7, ..] =
        *buf
    else {
        return None;
    };
    let tally = match tb {
        0 => false,
        1 => true,
        _ => return None,
    };
    let is_quit = match qb {
        0 => false,
        1 => true,
        _ => return None,
    };
    let lines_seen = ((l0 as u64) << 56)
        | ((l1 as u64) << 48)
        | ((l2 as u64) << 40)
        | ((l3 as u64) << 32)
        | ((l4 as u64) << 24)
        | ((l5 as u64) << 16)
        | ((l6 as u64) << 8)
        | (l7 as u64);
    Some((tally, is_quit, lines_seen))
}

/// Return whether `arg` is the exact ASCII flag `"--tally"`.
#[must_use]
pub const fn echo_child_is_tally_flag(arg: &[u8]) -> bool {
    matches!(arg, [b'-', b'-', b't', b'a', b'l', b'l', b'y'])
}

/// Pack up to four leading bytes of `prefix` into a big-endian `u32` tally word
/// (zero-padding shorter slices on the right).
#[must_use]
pub const fn echo_child_pack_prefix4(prefix: &[u8]) -> u32 {
    let b0 = match prefix {
        [x, ..] => *x,
        [] => 0,
    };
    let b1 = match prefix {
        [_, x, ..] => *x,
        _ => 0,
    };
    let b2 = match prefix {
        [_, _, x, ..] => *x,
        _ => 0,
    };
    let b3 = match prefix {
        [_, _, _, x, ..] => *x,
        _ => 0,
    };
    ((b0 as u32) << 24) | ((b1 as u32) << 16) | ((b2 as u32) << 8) | (b3 as u32)
}

/// Unpack a big-endian `u32` tally word produced by [`echo_child_pack_prefix4`].
#[must_use]
pub const fn echo_child_unpack_prefix4(word: u32) -> [u8; 4] {
    [
        ((word >> 24) & 0xFF) as u8,
        ((word >> 16) & 0xFF) as u8,
        ((word >> 8) & 0xFF) as u8,
        (word & 0xFF) as u8,
    ]
}

/// Return the prefix of `line` spanning at most the first four UTF-8 scalar values.
#[allow(clippy::manual_unwrap_or_default)]
#[must_use]
pub fn echo_child_tally_prefix(line: &str) -> &str {
    let bytes = line.as_bytes();
    let mut idx = 0usize;
    let mut chars = 0u8;
    while idx < bytes.len() && chars < 4 {
        if let Some(&b) = bytes.get(idx) {
            let step = if b < 0x80 {
                1usize
            } else if b < 0xE0 {
                2usize
            } else if b < 0xF0 {
                3usize
            } else {
                4usize
            };
            match idx.checked_add(step) {
                Some(next) if next <= bytes.len() => idx = next,
                _ => break,
            }
            chars += 1;
        } else {
            break;
        }
    }
    match line.get(..idx) {
        Some(prefix) => prefix,
        None => "",
    }
}

fn main() {
    let stdin = std::io::stdin();
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    let mut args = std::env::args_os();
    let _ = args.next();
    let mut tally = false;
    for arg in args {
        if let Ok(s) = arg.into_string() {
            if echo_child_is_tally_flag(s.as_bytes()) {
                tally = true;
                break;
            }
        }
    }
    let mut seen: Vec<String> = Vec::new();
    let mut lines_seen = 0u64;
    for line in stdin.lock().lines() {
        let line = match line {
            Ok(l) => l,
            Err(_) => break,
        };
        if echo_child_is_quit_len(line.len() as u64) && line == "quit" {
            break;
        }
        lines_seen = echo_child_advance_lines(lines_seen, lines_seen.saturating_add(1));
        if tally {
            let mut prefix = String::new();
            prefix.push_str(echo_child_tally_prefix(&line));
            seen.push(prefix);
        }
        let _ = writeln!(out, "GOT:{line}");
        let _ = out.flush();
    }
    if tally {
        let _ = writeln!(out, "SAW:{}", seen.join(","));
        let _ = out.flush();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tally_flag_matches_exact_bytes() {
        assert!(echo_child_is_tally_flag(b"--tally"));
        assert!(!echo_child_is_tally_flag(b"--tally="));
        assert!(!echo_child_is_tally_flag(b"-tally"));
        assert!(!echo_child_is_tally_flag(b""));
    }

    #[test]
    fn tally_prefix_respects_utf8_scalar_boundaries() {
        assert_eq!(echo_child_tally_prefix(""), "");
        assert_eq!(echo_child_tally_prefix("abc"), "abc");
        assert_eq!(echo_child_tally_prefix("abcdef"), "abcd");
        assert_eq!(echo_child_tally_prefix("αβγδε"), "αβγδ");
        assert_eq!(echo_child_tally_prefix("🦀🔥🚀✨🎉"), "🦀🔥🚀✨");
    }

    #[test]
    fn frame_wire_roundtrip() {
        let wire = echo_child_encode_frame_wire(true, false, 42).expect("encodes");
        assert_eq!(echo_child_decode_frame_wire(&wire), Some((true, false, 42)));
        assert_eq!(echo_child_decode_frame_wire(b"short"), None);
    }

    #[test]
    fn prefix4_pack_roundtrip() {
        let packed = echo_child_pack_prefix4(b"abcdxyz");
        assert_eq!(echo_child_unpack_prefix4(packed), *b"abcd");
        let short = echo_child_pack_prefix4(b"hi");
        assert_eq!(echo_child_unpack_prefix4(short), [b'h', b'i', 0, 0]);
    }
}
