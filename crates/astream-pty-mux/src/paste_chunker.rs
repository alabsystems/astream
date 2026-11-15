// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bracketed-paste (`\x1b[200~` .. `\x1b[201~`) sanitizer stripping embedded paste-end
//! command-injection sequences and pacing chunks (`<= 1024` B) (`Astream.PtyMux.TlaPasteChunker`).

#[cfg(clean_islands)]
#[path = "paste_chunker_island.rs"]
mod paste_chunker_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn paste_chunk_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn paste_sent_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use paste_chunker_island::{paste_chunk_clamp, paste_sent_advance};

/// POSIX PTY `MAX_CANON`-safe per-write chunk cap (`1024` bytes).
pub const MAX_PASTE_CHUNK_BYTES: u64 = 1_024;

contract_fn! {
    /// Verified drain completion (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `paste_drained_isl`.
    #[must_use]
    pub const fn paste_drained(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

fn utf8_multibyte_len(b0: u8) -> usize {
    if (0xC2..=0xDF).contains(&b0) {
        2
    } else if (0xE0..=0xEF).contains(&b0) {
        3
    } else if (0xF0..=0xF4).contains(&b0) {
        4
    } else {
        0
    }
}

/// Strips hostile `\x1b[201~` / `\x1b[200~` and CSI `~` escapes from untrusted clipboard text
/// before wrapping in DEC `?2004` bracketed-paste markers.
#[must_use]
pub fn sanitize_bracketed_paste(raw: &[u8], bracketed_enabled: bool) -> Vec<u8> {
    let mut clean = Vec::new();
    if bracketed_enabled {
        clean.extend_from_slice(b"\x1b[200~");
    }
    let mut i = 0usize;
    while let Some(&b) = raw.get(i) {
        // Strip ESC (0x1B) and NUL (0x00) inside paste body so pasted text can never close `[201~`!
        if b == 0x1B || b == 0x00 {
            i = i.saturating_add(1);
            continue;
        }
        // Strip UTF-8 encoded C1 controls U+0080..=U+009F (`0xC2 0x80..=0x9F`, including U+009B CSI).
        if b == 0xC2 {
            if let Some(&b1) = raw.get(i.saturating_add(1)) {
                if (0x80..=0x9F).contains(&b1) {
                    i = i.saturating_add(2);
                    continue;
                }
            }
        }
        let mlen = utf8_multibyte_len(b);
        if mlen >= 2 {
            if let Some(seq) = raw.get(i..i.saturating_add(mlen)) {
                if core::str::from_utf8(seq).is_ok() {
                    clean.extend_from_slice(seq);
                    i = i.saturating_add(mlen);
                    continue;
                }
            }
        }
        // Strip standalone 8-bit C1 CSI (0x9B) when not part of a valid UTF-8 scalar.
        if b == 0x9B {
            i = i.saturating_add(1);
            continue;
        }
        clean.push(b);
        i = i.saturating_add(1);
    }
    if bracketed_enabled {
        clean.extend_from_slice(b"\x1b[201~");
    }
    clean
}

/// Stateful PTY paste chunker.
#[derive(Debug, Clone)]
pub struct PasteStreamChunker {
    buf: Vec<u8>,
    cursor: usize,
    chunk_cap: usize,
}

impl PasteStreamChunker {
    #[must_use]
    pub fn new(raw: &[u8], bracketed_enabled: bool, chunk_cap: u64) -> Self {
        let c = paste_chunk_clamp(chunk_cap, MAX_PASTE_CHUNK_BYTES) as usize;
        Self {
            buf: sanitize_bracketed_paste(raw, bracketed_enabled),
            cursor: 0,
            chunk_cap: if c == 0 { 256 } else { c },
        }
    }

    pub fn next_chunk(&mut self) -> Option<&[u8]> {
        if paste_drained(self.cursor as u64, self.buf.len() as u64) {
            return None;
        }
        let rem = self.buf.len().saturating_sub(self.cursor);
        let take = if rem < self.chunk_cap {
            rem
        } else {
            self.chunk_cap
        };
        let start = self.cursor;
        let end = start.saturating_add(take);
        self.cursor = paste_sent_advance(self.cursor as u64, end as u64) as usize;
        self.buf.get(start..end)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn paste_sanitizer_neutralizes_embedded_201_escape_injection_and_chunks_cleanly() {
        let evil = b"echo safe\x1b[201~\nrm -rf /\x1b[200~";
        let mut p = PasteStreamChunker::new(evil, true, 16);
        let mut out = Vec::new();
        while let Some(c) = p.next_chunk() {
            assert!(c.len() <= 16);
            out.extend_from_slice(c);
        }
        assert_eq!(out, b"\x1b[200~echo safe[201~\nrm -rf /[200~\x1b[201~");
    }
}
