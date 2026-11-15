// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Outbound log/transcript secret-prefix scanner blocking accidental emission of live bearer
//! credentials (`cap1_`, `ghp_`, `github_pat_`, `sk-ant-`, `AIza`) onto shared fabric bus subjects
//! (`Astream.SecVault.TlaRedactedDebugFormatter`).

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
#[path = "redacted_debug_formatter_island.rs"]
mod redacted_debug_formatter_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sv_tok_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sv_red_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use redacted_debug_formatter_island::{sv_red_advance, sv_tok_clamp};

/// Maximum leaked token prefixes counted per diagnostic line (`32`).
pub const MAX_TOKEN_LEAKS: u64 = 32;

contract_fn! {
    /// Verified zero-unredacted-token check (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `sv_line_scrubbed_isl`.
    #[must_use]
    pub const fn sv_line_scrubbed(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct SecretLogScanner {
    lines_scanned: u64,
}

impl SecretLogScanner {
    #[must_use]
    pub const fn new() -> Self {
        Self { lines_scanned: 0 }
    }

    pub fn is_safe_for_bus(&mut self, line: &str) -> bool {
        let bytes = line.as_bytes();
        let mut leaks = 0u64;
        for prefix in [
            b"cap1_".as_slice(),
            b"ghp_".as_slice(),
            b"github_pat_".as_slice(),
            b"sk-ant-".as_slice(),
            b"sk-proj-".as_slice(),
            b"xoxb-".as_slice(),
            b"AIzaSy".as_slice(),
        ] {
            if bytes_contains_exact(bytes, prefix) {
                leaks = leaks.saturating_add(1);
            }
        }
        if bytes_contains_ascii_ci(bytes, b"bearer ") {
            leaks = leaks.saturating_add(1);
        }
        let clamped = sv_tok_clamp(leaks, MAX_TOKEN_LEAKS);
        self.lines_scanned =
            sv_red_advance(self.lines_scanned, self.lines_scanned.saturating_add(1));
        sv_line_scrubbed(0, clamped)
    }
}

fn bytes_contains_exact(haystack: &[u8], needle: &[u8]) -> bool {
    if needle.is_empty() || haystack.len() < needle.len() {
        return false;
    }
    let limit = haystack.len().saturating_sub(needle.len());
    let mut start = 0usize;
    while start <= limit {
        let mut j = 0usize;
        let mut matched = true;
        while j < needle.len() {
            let Some(&hb) = haystack.get(start.saturating_add(j)) else {
                matched = false;
                break;
            };
            let Some(&nb) = needle.get(j) else {
                matched = false;
                break;
            };
            if hb != nb {
                matched = false;
                break;
            };
            j = j.saturating_add(1);
        }
        if matched {
            return true;
        }
        start = start.saturating_add(1);
    }
    false
}

fn bytes_contains_ascii_ci(haystack: &[u8], needle_lower: &[u8]) -> bool {
    if needle_lower.is_empty() || haystack.len() < needle_lower.len() {
        return false;
    }
    let limit = haystack.len().saturating_sub(needle_lower.len());
    let mut start = 0usize;
    while start <= limit {
        let mut j = 0usize;
        let mut matched = true;
        while j < needle_lower.len() {
            let Some(&hb) = haystack.get(start.saturating_add(j)) else {
                matched = false;
                break;
            };
            let Some(&nb) = needle_lower.get(j) else {
                matched = false;
                break;
            };
            if hb.to_ascii_lowercase() != nb {
                matched = false;
                break;
            }
            j = j.saturating_add(1);
        }
        if matched {
            return true;
        }
        start = start.saturating_add(1);
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_log_lines_containing_unredacted_capability_or_api_tokens() {
        let mut s = SecretLogScanner::new();
        assert!(s.is_safe_for_bus("Attach principal=n-8a91c0ffee01 ok"));
        assert!(!s.is_safe_for_bus("Attach token=cap1_deadbeefcafe"));
        assert!(!s.is_safe_for_bus("Authorization: Bearer ghp_1234567890"));
    }
}
