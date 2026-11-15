// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! DEC `?2004` bracketed paste breakout-sequence & C0/C1 injection sanitizer
//! (`Astream.Term.TlaBracketedPasteSanitizer`, Island #294).

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "bracketed_paste_sanitizer_island.rs"]
mod bracketed_paste_sanitizer_island;
#[cfg(clean_islands)]
pub use bracketed_paste_sanitizer_island::{
    sanitize_paste_bytes_clamp, sanitize_paste_stripped_clamp,
};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn sanitize_paste_bytes_clamp(len: u64, max_len: u64) -> u64 {
    if len < max_len {
        len
    } else {
        max_len
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn sanitize_paste_stripped_clamp(stripped: u64, max_len: u64) -> u64 {
    if stripped < max_len {
        stripped
    } else {
        max_len
    }
}

/// Default maximum sanitized paste payload bytes (`1_048_576` = 1 MiB).
pub const MAX_BRACKETED_PASTE_BYTES: u64 = 1_048_576;

/// DEC `?2004` bracketed paste open marker (`ESC [ 200 ~`).
pub const BRACKETED_PASTE_START: &[u8; 6] = b"\x1b[200~";

/// DEC `?2004` bracketed paste close marker (`ESC [ 201 ~`).
pub const BRACKETED_PASTE_END: &[u8; 6] = b"\x1b[201~";

contract_fn! {
    /// Verified check whether a paste payload fits within `max_len` (`paste_len <= max_len`),
    /// linked via `clean-kernel-defeq` to `sanitize_paste_within_budget_isl`.
    #[must_use]
    pub const fn sanitize_paste_within_budget(paste_len: u64, max_len: u64) -> bool
    clauses [ensures result == (paste_len <= max_len)]
    {
        paste_len <= max_len
    }
}

/// Result of [`BracketedPasteSanitizer::encode_paste`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SanitizedPaste {
    /// Bytes ready to write to the PTY (wrapped in `ESC [ 200 ~ ... ESC [ 201 ~` if `bracketed`).
    pub wire_bytes: Vec<u8>,
    /// Sanitized payload byte count (excluding open/close markers).
    pub payload_bytes: u64,
    /// Number of dangerous breakout/control sequences stripped.
    pub stripped_sequences: u64,
    /// True if input exceeded `max_paste_bytes` and was clamped.
    pub truncated: bool,
}

/// Deterministic DEC `?2004` bracketed paste sanitizer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BracketedPasteSanitizer {
    max_paste_bytes: u64,
}

impl Default for BracketedPasteSanitizer {
    fn default() -> Self {
        Self::new()
    }
}

impl BracketedPasteSanitizer {
    /// Create a sanitizer with [`MAX_BRACKETED_PASTE_BYTES`] (`1 MiB`).
    #[must_use]
    pub const fn new() -> Self {
        Self {
            max_paste_bytes: MAX_BRACKETED_PASTE_BYTES,
        }
    }

    /// Create a sanitizer with a custom byte cap (`<= MAX_BRACKETED_PASTE_BYTES`).
    #[must_use]
    pub const fn with_max_bytes(max_paste_bytes: u64) -> Self {
        Self {
            max_paste_bytes: sanitize_paste_bytes_clamp(max_paste_bytes, MAX_BRACKETED_PASTE_BYTES),
        }
    }

    #[must_use]
    pub const fn max_paste_bytes(&self) -> u64 {
        self.max_paste_bytes
    }

    /// Sanitize `raw` and wrap in `ESC [ 200 ~ ... ESC [ 201 ~` when `bracketed_mode` is active.
    #[must_use]
    pub fn encode_paste(&self, raw: &[u8], bracketed_mode: bool) -> SanitizedPaste {
        let cap = self.max_paste_bytes as usize;
        let mut wire = Vec::new();
        if bracketed_mode {
            wire.extend_from_slice(BRACKETED_PASTE_START);
        }

        let mut payload_len = 0usize;
        let mut stripped = 0u64;
        let mut truncated = false;
        let mut cur = raw;

        while !cur.is_empty() {
            if !sanitize_paste_within_budget(
                payload_len.saturating_add(1) as u64,
                self.max_paste_bytes,
            ) || payload_len >= cap
            {
                truncated = true;
                break;
            }
            let Some((&first, after_first)) = cur.split_first() else {
                break;
            };
            if let Some(rest) = strip_paste_escape_prefix(cur) {
                stripped = stripped.saturating_add(1);
                cur = rest;
            } else if first == 0x1b || first == 0x00 || first == 0x9b {
                stripped = stripped.saturating_add(1);
                cur = after_first;
            } else {
                wire.push(first);
                payload_len = payload_len.saturating_add(1);
                cur = after_first;
            }
        }

        if bracketed_mode {
            wire.extend_from_slice(BRACKETED_PASTE_END);
        }

        SanitizedPaste {
            wire_bytes: wire,
            payload_bytes: sanitize_paste_bytes_clamp(payload_len as u64, self.max_paste_bytes),
            stripped_sequences: sanitize_paste_stripped_clamp(stripped, self.max_paste_bytes),
            truncated,
        }
    }
}

fn strip_paste_escape_prefix(cur: &[u8]) -> Option<&[u8]> {
    if let Some(r) = cur.strip_prefix(b"\x1b[200~") {
        Some(r)
    } else if let Some(r) = cur.strip_prefix(b"\x1b[201~") {
        Some(r)
    } else if let Some(r) = cur.strip_prefix(b"\x9b200~") {
        Some(r)
    } else if let Some(r) = cur.strip_prefix(b"\x9b201~") {
        Some(r)
    } else if let Some(r) = cur.strip_prefix(b"\xc2\x9b200~") {
        Some(r)
    } else if let Some(r) = cur.strip_prefix(b"\xc2\x9b201~") {
        Some(r)
    } else {
        cur.strip_prefix(b"\xc2\x9b")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn neutralizes_embedded_201_breakout_and_c1_csi() {
        let san = BracketedPasteSanitizer::new();
        assert_eq!(san.max_paste_bytes(), MAX_BRACKETED_PASTE_BYTES);
        let attack = b"safe\x1b[201~; rm -rf /\r\xc2\x9b201~done";
        let res = san.encode_paste(attack, true);
        assert_eq!(res.wire_bytes, b"\x1b[200~safe; rm -rf /\rdone\x1b[201~");
        assert_eq!(res.stripped_sequences, 2);
        assert!(!res.truncated);
    }
}
