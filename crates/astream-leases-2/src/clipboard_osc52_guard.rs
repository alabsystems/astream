// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Write-only `OSC 52 ; <selection> ; <base64-or-query> ST` terminal clipboard security guard
//! (`Astream.Term.TlaClipboardOsc52Guard`, Island #291).

#![allow(clippy::collapsible_if)]

#[cfg(clean_islands)]
#[path = "clipboard_osc52_guard_island.rs"]
mod clipboard_osc52_guard_island;
#[cfg(clean_islands)]
pub use clipboard_osc52_guard_island::{clip_osc52_payload_clamp, clip_osc52_writes_clamp};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn clip_osc52_payload_clamp(len: u64, max_len: u64) -> u64 {
    if len < max_len {
        len
    } else {
        max_len
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn clip_osc52_writes_clamp(writes: u64, max_writes: u64) -> u64 {
    if writes < max_writes {
        writes
    } else {
        max_writes
    }
}

/// Default maximum `OSC 52` base64 payload bytes (`131_072` = 128 KiB, ~96 KiB decoded).
pub const MAX_OSC52_BASE64_BYTES: u64 = 131_072;

/// Default maximum `OSC 52` clipboard writes admitted per turn window (`32`).
pub const MAX_OSC52_WINDOW_WRITES: u64 = 32;

contract_fn! {
    /// Verified check whether an `OSC 52` base64 payload fits within `max_len`
    /// (`payload_len <= max_len`), linked via `clean-kernel-defeq` to
    /// `clip_osc52_within_cap_isl`.
    #[must_use]
    pub const fn clip_osc52_within_cap(payload_len: u64, max_len: u64) -> bool
    clauses [ensures result == (payload_len <= max_len)]
    {
        payload_len <= max_len
    }
}

/// Decision returned by [`ClipboardOsc52Guard::evaluate`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Osc52Verdict {
    /// Valid write-only clipboard copy admitted.
    AdmitWrite {
        clear_clipboard: bool,
        base64_len: usize,
    },
    /// Rejected `OSC 52 ; ... ; ?` read query (exfiltration attempt).
    RejectReadQuery,
    /// Rejected malformed syntax, disallowed selection target, or invalid base64 byte.
    RejectMalformed,
    /// Rejected payload exceeding `max_payload_bytes`.
    RejectOversize { len: u64, max_len: u64 },
    /// Rejected write exceeding per-window rate cap.
    RejectRateLimited { writes: u64, max_writes: u64 },
}

const fn is_allowed_selection_byte(b: u8) -> bool {
    matches!(
        b,
        b'c' | b'p' | b'q' | b's' | b'0' | b'1' | b'2' | b'3' | b'4' | b'5' | b'6' | b'7'
    )
}

const fn is_base64_char(b: u8) -> bool {
    (b >= b'A' && b <= b'Z')
        || (b >= b'a' && b <= b'z')
        || (b >= b'0' && b <= b'9')
        || b == b'+'
        || b == b'/'
        || b == b'='
}

const fn all_base64_chars(mut s: &[u8]) -> bool {
    while let [b, rest @ ..] = s {
        if !is_base64_char(*b) {
            return false;
        }
        s = rest;
    }
    true
}

/// Stateful `OSC 52` clipboard policy guard.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClipboardOsc52Guard {
    max_payload_bytes: u64,
    max_window_writes: u64,
    window_writes: u64,
    last_payload_bytes: u64,
    allow_read_query: bool,
}

impl Default for ClipboardOsc52Guard {
    fn default() -> Self {
        Self::new()
    }
}

impl ClipboardOsc52Guard {
    /// Create a strict write-only `OSC 52` guard (`allow_read_query = false`).
    #[must_use]
    pub const fn new() -> Self {
        Self {
            max_payload_bytes: MAX_OSC52_BASE64_BYTES,
            max_window_writes: MAX_OSC52_WINDOW_WRITES,
            window_writes: 0,
            last_payload_bytes: 0,
            allow_read_query: false,
        }
    }

    /// Override payload and window write caps.
    #[must_use]
    pub const fn with_limits(mut self, max_payload_bytes: u64, max_window_writes: u64) -> Self {
        self.max_payload_bytes =
            clip_osc52_payload_clamp(max_payload_bytes, MAX_OSC52_BASE64_BYTES);
        self.max_window_writes =
            clip_osc52_writes_clamp(max_window_writes, MAX_OSC52_WINDOW_WRITES);
        self
    }

    #[must_use]
    pub const fn max_payload_bytes(&self) -> u64 {
        self.max_payload_bytes
    }

    #[must_use]
    pub const fn max_window_writes(&self) -> u64 {
        self.max_window_writes
    }

    #[must_use]
    pub const fn last_payload_bytes(&self) -> u64 {
        self.last_payload_bytes
    }

    #[must_use]
    pub const fn allow_read_query(&self) -> bool {
        self.allow_read_query
    }

    /// Reset the per-turn write counter on a fresh human/operator turn.
    pub fn reset_window(&mut self) {
        self.window_writes = 0;
    }

    /// Number of admitted clipboard writes in the active window.
    #[must_use]
    pub const fn window_writes(&self) -> u64 {
        self.window_writes
    }

    /// Evaluate the body after `OSC 52 ;` (i.e. `<selection>;<payload>`).
    pub fn evaluate(&mut self, body: &[u8]) -> Osc52Verdict {
        let mut cur = body;
        let payload = loop {
            let [b, rest @ ..] = cur else {
                return Osc52Verdict::RejectMalformed;
            };
            if *b == b';' {
                break rest;
            }
            if !is_allowed_selection_byte(*b) {
                return Osc52Verdict::RejectMalformed;
            }
            cur = rest;
        };

        if matches!(payload, b"?") {
            if !self.allow_read_query {
                return Osc52Verdict::RejectReadQuery;
            }
        }

        let payload_len = payload.len() as u64;
        if !clip_osc52_within_cap(payload_len, self.max_payload_bytes) {
            return Osc52Verdict::RejectOversize {
                len: payload_len,
                max_len: self.max_payload_bytes,
            };
        }

        if !all_base64_chars(payload) || (payload.len() & 3) != 0 {
            return Osc52Verdict::RejectMalformed;
        }

        if self.window_writes >= self.max_window_writes {
            return Osc52Verdict::RejectRateLimited {
                writes: self.window_writes,
                max_writes: self.max_window_writes,
            };
        }

        self.window_writes =
            clip_osc52_writes_clamp(self.window_writes.saturating_add(1), self.max_window_writes);
        self.last_payload_bytes = clip_osc52_payload_clamp(payload_len, self.max_payload_bytes);

        Osc52Verdict::AdmitWrite {
            clear_clipboard: payload.is_empty(),
            base64_len: payload.len(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_read_queries_and_admits_bounded_base64_writes() {
        let mut g = ClipboardOsc52Guard::new().with_limits(16, 2);
        assert!(!g.allow_read_query());
        assert_eq!(g.evaluate(b"c;?"), Osc52Verdict::RejectReadQuery);
        assert_eq!(
            g.evaluate(b"c;SGVsbG8="),
            Osc52Verdict::AdmitWrite {
                clear_clipboard: false,
                base64_len: 8,
            }
        );
        assert_eq!(g.last_payload_bytes(), 8);
        assert_eq!(
            g.evaluate(b"c;"),
            Osc52Verdict::AdmitWrite {
                clear_clipboard: true,
                base64_len: 0,
            }
        );
        assert_eq!(
            g.evaluate(b"c;SGVsbG8="),
            Osc52Verdict::RejectRateLimited {
                writes: 2,
                max_writes: 2,
            }
        );
        g.reset_window();
        assert_eq!(
            g.evaluate(b"c;AAAAAAAAAAAAAAAAAAAA"),
            Osc52Verdict::RejectOversize {
                len: 20,
                max_len: 16,
            }
        );
    }
}
