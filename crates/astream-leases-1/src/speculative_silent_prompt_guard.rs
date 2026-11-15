// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `SpeculativeTerminal` credential / silent-prompt local-echo suppressor
//! (`Astream.Term.TlaSpeculativeSilentPromptGuard`, Island #286).

#![allow(clippy::explicit_auto_deref, clippy::manual_range_contains)]

#[cfg(clean_islands)]
#[path = "speculative_silent_prompt_guard_island.rs"]
mod speculative_silent_prompt_guard_island;
#[cfg(clean_islands)]
pub use speculative_silent_prompt_guard_island::{
    silent_suppressed_advance, silent_tail_len_clamp,
};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn silent_tail_len_clamp(tail_len: u64, max_tail: u64) -> u64 {
    if tail_len < max_tail {
        tail_len
    } else {
        max_tail
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn silent_suppressed_advance(prev: u64, next: u64) -> u64 {
    if prev < next {
        next
    } else {
        prev
    }
}

/// Maximum trailing ASCII bytes inspected on the active prompt line (`128`).
pub const MAX_PROMPT_TAIL_BYTES: usize = 128;

const SILENT_MARKERS: &[&[u8]] = &[
    b"password:",
    b"password for ",
    b"passphrase",
    b"passcode:",
    b"pin:",
    b"secret:",
    b"token:",
    b"api key:",
    b"verification code:",
];

contract_fn! {
    /// Verified check `latched_silent == 0`, linked via `clean-kernel-defeq` to
    /// `silent_echo_permitted_isl`.
    #[must_use]
    pub const fn silent_echo_permitted(latched_silent: u64) -> bool
    clauses [ensures result == (latched_silent == 0)]
    {
        latched_silent == 0
    }
}

#[inline]
const fn ascii_lower(b: u8) -> u8 {
    if b >= b'A' && b <= b'Z' {
        b.saturating_add(32)
    } else {
        b
    }
}

const fn is_ascii_ws(b: u8) -> bool {
    matches!(b, b' ' | b'\t' | b'\r' | b'\n' | 0x0C)
}

const fn trim_end_ascii_ws(mut s: &[u8]) -> &[u8] {
    while let [rest @ .., last] = s {
        if is_ascii_ws(*last) {
            s = rest;
        } else {
            break;
        }
    }
    s
}

const fn starts_with_ascii_ci(mut hay: &[u8], mut needle_lower: &[u8]) -> bool {
    while let [nb, ntail @ ..] = needle_lower {
        let [hb, htail @ ..] = hay else {
            return false;
        };
        if ascii_lower(*hb) != *nb {
            return false;
        }
        hay = htail;
        needle_lower = ntail;
    }
    true
}

const fn contains_ascii_case_insensitive(mut haystack: &[u8], needle_lower: &[u8]) -> bool {
    if needle_lower.is_empty() {
        return false;
    }
    while haystack.len() >= needle_lower.len() {
        if starts_with_ascii_ci(haystack, needle_lower) {
            return true;
        }
        let [_, rest @ ..] = haystack else {
            break;
        };
        haystack = rest;
    }
    false
}

/// Detect whether `prompt_line` looks like a no-echo credential prompt.
#[must_use]
pub const fn is_credential_prompt_line(prompt_line: &str) -> bool {
    let mut tail = trim_end_ascii_ws(prompt_line.as_bytes());
    let keep = silent_tail_len_clamp(tail.len() as u64, MAX_PROMPT_TAIL_BYTES as u64) as usize;
    while tail.len() > keep {
        let [_, rest @ ..] = tail else {
            break;
        };
        tail = rest;
    }
    let mut markers = SILENT_MARKERS;
    while let [marker, mtail @ ..] = markers {
        if contains_ascii_case_insensitive(tail, *marker) {
            return true;
        }
        markers = mtail;
    }
    false
}

/// Stateful per-line silent-prompt local-echo guard.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SilentPromptGuard {
    latched_silent: u64,
    suppressed_keystrokes: u64,
}

impl SilentPromptGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            latched_silent: 0,
            suppressed_keystrokes: 0,
        }
    }

    #[must_use]
    pub const fn is_latched(&self) -> bool {
        !silent_echo_permitted(self.latched_silent)
    }

    #[must_use]
    pub const fn suppressed_keystrokes(&self) -> u64 {
        self.suppressed_keystrokes
    }

    /// Observe authoritative output on the current cursor line before predicting input.
    pub fn observe_prompt_line(&mut self, line: &str) {
        if is_credential_prompt_line(line) {
            self.latched_silent = 1;
        }
    }

    /// Filter an input byte: returns `true` when speculative echo is allowed, `false` when suppressed.
    pub fn allow_speculative_byte(&mut self, b: u8) -> bool {
        if b == b'\r' || b == b'\n' || b == 0x03 || b == 0x04 {
            self.latched_silent = 0;
            return false;
        }
        if silent_echo_permitted(self.latched_silent) {
            b >= 0x20 && b < 0x7f
        } else {
            self.suppressed_keystrokes = silent_suppressed_advance(
                self.suppressed_keystrokes,
                self.suppressed_keystrokes.saturating_add(1),
            );
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn suppresses_entire_password_entry_until_newline_then_resumes_normal_echo() {
        let mut g = SilentPromptGuard::new();
        g.observe_prompt_line("user@host $ ");
        assert!(g.allow_speculative_byte(b'l'));
        assert!(g.allow_speculative_byte(b's'));
        assert!(!g.allow_speculative_byte(b'\n'));

        g.observe_prompt_line("[sudo] Password for user: ");
        assert!(g.is_latched());
        for &ch in b"hunter2!" {
            assert!(!g.allow_speculative_byte(ch));
        }
        assert_eq!(g.suppressed_keystrokes(), 8);

        assert!(!g.allow_speculative_byte(b'\r'));
        assert!(!g.is_latched());
        g.observe_prompt_line("user@host $ ");
        assert!(g.allow_speculative_byte(b'w'));
    }
}
