// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! 1..3-byte trailing incomplete UTF-8 carry across PTY `read()` chunk boundaries so split
//! multi-byte scalars never emit false `U+FFFD` (`Astream.PtyMux.TlaUtf8BoundaryHold`).

#[cfg(clean_islands)]
#[path = "utf8_boundary_hold_island.rs"]
mod utf8_boundary_hold_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn utf8_carry_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn utf8_emitted_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use utf8_boundary_hold_island::{utf8_carry_clamp, utf8_emitted_advance};

/// At most 3 trailing bytes can belong to an unfinished valid 4-byte UTF-8 scalar.
pub const MAX_UTF8_CARRY_BYTES: u64 = 3;

contract_fn! {
    /// Verified completeness check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `utf8_seq_complete_isl`.
    #[must_use]
    pub const fn utf8_seq_complete(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Stateful streaming UTF-8 chunk splitter holding incomplete trailing multi-byte prefixes.
#[derive(Debug, Clone, Default)]
pub struct Utf8BoundaryCarry {
    carry: [u8; 3],
    carry_len: usize,
    emitted_bytes: u64,
}

impl Utf8BoundaryCarry {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            carry: [0; 3],
            carry_len: 0,
            emitted_bytes: 0,
        }
    }

    pub fn push_chunk(&mut self, incoming: &[u8]) -> Vec<u8> {
        let mut combined = Vec::new();
        if let Some(c) = self.carry.get(..self.carry_len) {
            combined.extend_from_slice(c);
        }
        self.carry_len = 0;
        combined.extend_from_slice(incoming);

        let mut pos = 0usize;
        let mut hold = 0usize;
        while pos < combined.len() {
            let Some(tail) = combined.get(pos..) else {
                break;
            };
            match core::str::from_utf8(tail) {
                Ok(_) => break,
                Err(e) => match e.error_len() {
                    None => {
                        let rem = tail.len().saturating_sub(e.valid_up_to());
                        hold = utf8_carry_clamp(rem as u64, MAX_UTF8_CARRY_BYTES) as usize;
                        break;
                    }
                    Some(bad_len) => {
                        let skip = if bad_len == 0 { 1 } else { bad_len };
                        let step = e.valid_up_to().saturating_add(skip);
                        pos = pos.saturating_add(step);
                    }
                },
            }
        }
        let emit_len = combined.len().saturating_sub(hold);
        if hold > 0 && !utf8_seq_complete(0, hold as u64) {
            if let (Some(src), Some(dst)) = (combined.get(emit_len..), self.carry.get_mut(..hold)) {
                dst.copy_from_slice(src);
                self.carry_len = hold;
            }
        }
        combined.truncate(emit_len);
        self.emitted_bytes = utf8_emitted_advance(
            self.emitted_bytes,
            self.emitted_bytes.saturating_add(combined.len() as u64),
        );
        combined
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn split_four_byte_emoji_across_three_pty_reads_reassembles_without_replacement_char() {
        let mut u = Utf8BoundaryCarry::new();
        let crab = "🦀".as_bytes(); // [0xF0, 0x9F, 0xA6, 0x80]
        assert!(u.push_chunk(&crab[0..1]).is_empty());
        assert!(u.push_chunk(&crab[1..3]).is_empty());
        let done = u.push_chunk(&crab[3..4]);
        assert_eq!(core::str::from_utf8(&done).unwrap(), "🦀");
    }
}
