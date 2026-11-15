// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! CVE-2021-42574 ("Trojan Source") bidirectional override/isolate sanitizer replacing raw
//! `RLO`/`LRO`/`LRI`/`RLI`/`FSI`/`PDI` (`U+202A..=U+202E`, `U+2066..=U+2069`) in terminal output
//! with visible `<U+HEX>` badges when unclosed or disallowed (`Astream.Grapheme.TlaBidiIsolateGuard`).

#[cfg(clean_islands)]
#[path = "bidi_isolate_guard_island.rs"]
mod bidi_isolate_guard_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn gr_bidi_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn gr_sanitized_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use bidi_isolate_guard_island::{gr_bidi_clamp, gr_sanitized_advance};

/// Maximum characters scanned per line by the Trojan-Source sanitizer.
pub const MAX_BIDI_LINE_CHARS: u64 = 16_384;

contract_fn! {
    /// Verified zero-bidi-leak check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `gr_bidi_balanced_isl`.
    #[must_use]
    pub const fn gr_bidi_balanced(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[must_use]
pub const fn is_bidi_control(ch: char) -> bool {
    matches!(ch, '\u{202A}'..='\u{202E}' | '\u{2066}'..='\u{2069}' | '\u{061C}')
}

/// Neutralizes hidden Trojan-Source bidi control characters into visible `<U+HEX>` escapes.
#[derive(Debug, Clone, Default)]
pub struct TrojanSourceBidiGuard {
    neutralized: u64,
}

fn push_bidi_badge(out: &mut String, cp: u32) {
    const HEX: &[u8; 16] = b"0123456789ABCDEF";
    out.push_str("<U+");
    let mut shift = if cp > 0xFFFF { 20u32 } else { 12u32 };
    loop {
        let nib = ((cp >> (shift & 31)) & 0xF) as usize;
        if let Some(&b) = HEX.get(nib) {
            out.push(b as char);
        }
        if shift == 0 {
            break;
        }
        shift = shift.saturating_sub(4);
    }
    out.push('>');
}

impl TrojanSourceBidiGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self { neutralized: 0 }
    }

    pub fn sanitize_line(&mut self, line: &str) -> (String, bool) {
        let lim = gr_bidi_clamp(MAX_BIDI_LINE_CHARS, MAX_BIDI_LINE_CHARS) as usize;
        let mut out = String::new();
        let mut found = 0u64;
        let mut seen = 0usize;
        for ch in line.chars() {
            if seen >= lim {
                break;
            }
            seen = seen.saturating_add(1);
            if is_bidi_control(ch) {
                found = found.saturating_add(1);
                push_bidi_badge(&mut out, ch as u32);
            } else {
                out.push(ch);
            }
        }
        self.neutralized =
            gr_sanitized_advance(self.neutralized, self.neutralized.saturating_add(found));
        let clean = gr_bidi_balanced(0, found);
        (out, clean)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bidi_guard_exposes_rlo_trojan_source_override_as_visible_codepoint_badge() {
        let mut g = TrojanSourceBidiGuard::new();
        let (rendered, clean) = g.sanitize_line("if is_admin\u{202E} { return; }");
        assert!(!clean);
        assert_eq!(rendered, "if is_admin<U+202E> { return; }");
    }
}
