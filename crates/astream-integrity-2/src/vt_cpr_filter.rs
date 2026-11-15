// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Terminal Reply-Soliciting Escape Query Sanitizer (`Astream.Pump.TlaTerminalReplySanitizer`).
//!
//! Untrusted output rendered onto a live terminal (`curl`, build logs, peer mail excerpts, or
//! replayed foreign transcripts) can embed reply-soliciting VT queries (`ENQ`, `ESC Z`,
//! `CSI 5 n` / `CSI 6 n` DSR, `CSI c` / `CSI > c` / `CSI = c` DA, `CSI ... t` XTWINOPS queries,
//! or `OSC 4/10/11/12/52 ; ?` color/clipboard queries) that cause a terminal emulator to write
//! synthetic keyboard bytes back onto the PTY master — risking stdin echo injection at an
//! interactive shell prompt.
//!
//! [`TerminalQuerySanitizer`] streams arbitrary byte chunks, passing ordinary SGR/cursor/UTF-8
//! output verbatim while stripping reply-soliciting queries across chunk splits, clamping
//! stripped-query telemetry via Clean-origin [`vt_query_strip_clamp`] and advancing
//! `sanitize_epoch` monotonically via Clean-origin [`vt_sanitize_epoch_advance`].

#[cfg(clean_islands)]
#[path = "vt_cpr_filter_island.rs"]
mod vt_cpr_filter_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn vt_query_strip_clamp(cand_stripped: u64, strip_cap: u64) -> u64 {
    if cand_stripped < strip_cap {
        cand_stripped
    } else {
        strip_cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn vt_sanitize_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}
#[cfg(clean_islands)]
pub use vt_cpr_filter_island::{vt_query_strip_clamp, vt_sanitize_epoch_advance};

/// Default cap on counted stripped terminal queries.
pub const DEFAULT_VT_QUERY_STRIP_CAP: u64 = 100_000;

/// Maximum buffered escape sequence bytes before flushing/resetting (`512` bytes).
pub const MAX_SANITIZER_SEQ_BUF: usize = 512;

contract_fn! {
    /// Kernel-certified check that `stripped <= strip_cap`, linked via
    /// `clean-kernel-defeq` to `vt_stripped_within_cap_isl`.
    #[must_use]
    pub const fn vt_stripped_within_cap(stripped: u64, strip_cap: u64) -> bool
    clauses [ensures result == (stripped <= strip_cap)]
    {
        stripped <= strip_cap
    }
}

fn is_csi_reply_query(params: &[u8], final_byte: u8) -> bool {
    // Device Status Report (`CSI 5 n`, `CSI 6 n`, `CSI ? 6 n`, etc.) and Device Attributes (`CSI ... c`).
    if final_byte == b'n' || final_byte == b'c' {
        return true;
    }
    // DECRQM (`CSI ? Ps $ p` / `CSI Ps $ p`): ends with `$` intermediate + `p`.
    if final_byte == b'p' && params.ends_with(b"$") {
        return true;
    }
    // XTWINOPS report queries (`CSI 11 t`, `CSI 13 t`, `CSI 14 t`, `CSI 18 t`, `CSI 19 t`, `CSI 20 t`, `CSI 21 t`).
    if final_byte == b't' {
        return params == b"11"
            || params == b"13"
            || params == b"14"
            || params == b"18"
            || params == b"19"
            || params == b"20"
            || params == b"21";
    }
    false
}

fn is_osc_reply_query(payload: &[u8]) -> bool {
    // Any OSC ending with `;?` (such as `OSC 10;?`, `OSC 11;?`, `OSC 4;0;?`, `OSC 52;c;?`)
    // solicits a terminal report or clipboard readback!
    payload.ends_with(b";?")
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SanitizeState {
    Ground,
    Esc,
    Csi,
    Osc,
    OscEsc,
}

/// Streaming VT query sanitizer backed by `Astream.Pump.TlaTerminalReplySanitizer`.
#[derive(Debug, Clone)]
pub struct TerminalQuerySanitizer {
    state: SanitizeState,
    seq_buf: Vec<u8>,
    stripped_queries: u64,
    strip_cap: u64,
    sanitize_epoch: u64,
}

impl TerminalQuerySanitizer {
    /// Construct a sanitizer with `strip_cap` (`>= 1`).
    #[must_use]
    pub fn new(strip_cap: u64) -> Self {
        let cap = if strip_cap == 0 { 1 } else { strip_cap };
        Self {
            state: SanitizeState::Ground,
            seq_buf: Vec::new(),
            stripped_queries: 0,
            strip_cap: cap,
            sanitize_epoch: 0,
        }
    }

    /// Construct a sanitizer with [`DEFAULT_VT_QUERY_STRIP_CAP`].
    #[must_use]
    pub fn with_defaults() -> Self {
        Self::new(DEFAULT_VT_QUERY_STRIP_CAP)
    }

    /// Clamped count of stripped reply-soliciting queries (`<= strip_cap`).
    #[must_use]
    pub const fn stripped_queries(&self) -> u64 {
        self.stripped_queries
    }

    /// Monotone sanitization epoch.
    #[must_use]
    pub const fn sanitize_epoch(&self) -> u64 {
        self.sanitize_epoch
    }

    fn record_strip(&mut self) {
        let cand = self.stripped_queries.saturating_add(1);
        self.stripped_queries = vt_query_strip_clamp(cand, self.strip_cap);
    }

    /// Sanitize one chunk of untrusted terminal output, returning safe pass-through bytes.
    pub fn sanitize_chunk(&mut self, chunk: &[u8]) -> Vec<u8> {
        let cand_ep = self.sanitize_epoch.saturating_add(1);
        self.sanitize_epoch = vt_sanitize_epoch_advance(self.sanitize_epoch, cand_ep);

        let out_cap = if chunk.len() < 65_536 {
            chunk.len()
        } else {
            65_536
        };
        let mut out = {
            let _ = out_cap;
            Vec::new()
        };
        let mut cur = chunk;
        while let &[b, ref rest @ ..] = cur {
            cur = rest;
            match self.state {
                SanitizeState::Ground => {
                    if b == 0x05 {
                        // Strip C0 ENQ answerback query (`0x05`).
                        self.record_strip();
                    } else if b == 0x1B {
                        self.seq_buf.clear();
                        self.state = SanitizeState::Esc;
                    } else {
                        out.push(b);
                    }
                }
                SanitizeState::Esc => {
                    if b == b'[' {
                        self.seq_buf.clear();
                        self.state = SanitizeState::Csi;
                    } else if b == b']' {
                        self.seq_buf.clear();
                        self.state = SanitizeState::Osc;
                    } else if b == b'Z' {
                        // Strip legacy DECID `ESC Z` query.
                        self.record_strip();
                        self.state = SanitizeState::Ground;
                    } else {
                        out.push(0x1B);
                        out.push(b);
                        self.state = SanitizeState::Ground;
                    }
                }
                SanitizeState::Csi => {
                    if matches!(b, 0x40..=0x7E) {
                        if is_csi_reply_query(&self.seq_buf, b) {
                            self.record_strip();
                        } else {
                            out.extend_from_slice(b"\x1b[");
                            out.extend_from_slice(&self.seq_buf);
                            out.push(b);
                        }
                        self.seq_buf.clear();
                        self.state = SanitizeState::Ground;
                    } else if self.seq_buf.len() < MAX_SANITIZER_SEQ_BUF {
                        self.seq_buf.push(b);
                    } else {
                        // Malformed/overlong CSI: drop buffer rather than forwarding partial query.
                        self.record_strip();
                        self.seq_buf.clear();
                        self.state = SanitizeState::Ground;
                    }
                }
                SanitizeState::Osc => {
                    if b == 0x07 {
                        if is_osc_reply_query(&self.seq_buf) {
                            self.record_strip();
                        } else {
                            out.extend_from_slice(b"\x1b]");
                            out.extend_from_slice(&self.seq_buf);
                            out.push(0x07);
                        }
                        self.seq_buf.clear();
                        self.state = SanitizeState::Ground;
                    } else if b == 0x1B {
                        self.state = SanitizeState::OscEsc;
                    } else if self.seq_buf.len() < MAX_SANITIZER_SEQ_BUF {
                        self.seq_buf.push(b);
                    } else {
                        self.record_strip();
                        self.seq_buf.clear();
                        self.state = SanitizeState::Ground;
                    }
                }
                SanitizeState::OscEsc => {
                    if b == b'\\' {
                        if is_osc_reply_query(&self.seq_buf) {
                            self.record_strip();
                        } else {
                            out.extend_from_slice(b"\x1b]");
                            out.extend_from_slice(&self.seq_buf);
                            out.extend_from_slice(b"\x1b\\");
                        }
                        self.seq_buf.clear();
                        self.state = SanitizeState::Ground;
                    } else {
                        self.record_strip();
                        self.seq_buf.clear();
                        self.state = SanitizeState::Ground;
                    }
                }
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strips_split_cpr_da_osc_color_and_clipboard_queries_preserving_sgr() {
        let mut s = TerminalQuerySanitizer::new(10);
        let p1 = s.sanitize_chunk(b"\x1b[32mok\x1b[0m\x1b[6");
        let p2 = s.sanitize_chunk(b"n!\x1b]52;c;?\x07\x1b]11;?\x1b\\\x1b[>cDONE");
        let mut combined = p1;
        combined.extend_from_slice(&p2);

        assert_eq!(combined, b"\x1b[32mok\x1b[0m!DONE");
        assert_eq!(s.stripped_queries(), 4);
        assert!(vt_stripped_within_cap(s.stripped_queries(), 10));
        assert_eq!(s.sanitize_epoch(), 2);
    }
}
