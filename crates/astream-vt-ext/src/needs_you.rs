// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Streaming `NEEDS YOU:` report-line detector & menu-bar / window-border banner ledger
//! (`aterm` primer v45, `Astream.Term.TlaNeedsYouLedger`).
//!
//! Implements `aterm`'s exact `NEEDS YOU:` protocol with `0 mandated` obligations:
//! - Strips CSI/OSC ANSI formatting from output lines before matching `NEEDS YOU:` at the
//!   start of a line.
//! - Records distinct actionable items (`<= MAX_NEEDS_YOU_ITEMS`, each clamped to
//!   `<= MAX_NEEDS_YOU_ITEM_BYTES` via Clean-origin [`needs_you_len_clamp`]).
//! - Immediately clears all active items for the session when `NEEDS YOU: nothing` arrives!

#![allow(clippy::question_mark)]

#[cfg(clean_islands)]
#[path = "needs_you_island.rs"]
mod needs_you_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn needs_you_items_clamp(items: u64, max_items: u64) -> u64 {
    if items < max_items {
        items
    } else {
        max_items
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn needs_you_len_clamp(item_len: u64, max_len: u64) -> u64 {
    if item_len < max_len {
        item_len
    } else {
        max_len
    }
}
#[cfg(clean_islands)]
pub use needs_you_island::{needs_you_items_clamp, needs_you_len_clamp};

/// Maximum concurrent distinct `NEEDS YOU:` items retained per session.
pub const MAX_NEEDS_YOU_ITEMS: usize = 16;

/// Maximum UTF-8 byte length of a single `NEEDS YOU:` reason string.
pub const MAX_NEEDS_YOU_ITEM_BYTES: usize = 160;

/// Maximum buffered bytes in an unfinished line before flushing/truncating.
pub const MAX_LINE_ACCUM_BYTES: usize = 2048;

contract_fn! {
    /// Verified check whether a session's menu-bar / window-border `NEEDS YOU` indicator
    /// should be lit (`active_items > 0`), linked via `clean-kernel-defeq` to
    /// `needs_you_banner_active_isl`.
    #[must_use]
    pub const fn needs_you_banner_active(active_items: usize) -> bool
    clauses [ensures result == (0 < active_items)]
    {
        0 < active_items
    }
}

/// Transition returned when a completed line modifies or confirms a session's `NEEDS YOU` ledger.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NeedsYouEvent {
    /// A new `NEEDS YOU: <item>` was added to the active banner.
    Raised(String),
    /// `NEEDS YOU: nothing` cleared the active banner (`cleared_count` items removed).
    Cleared { cleared_count: usize },
}

/// Per-session streaming `NEEDS YOU:` detector & active banner ledger.
#[derive(Debug, Clone, Default)]
pub struct NeedsYouLedger {
    line_buf: Vec<u8>,
    items: Vec<String>,
}

impl NeedsYouLedger {
    /// Create an empty `NEEDS YOU:` ledger with banner off.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// True when the menu-bar and window-border alert is active (`!items.is_empty()`).
    #[must_use]
    pub fn banner_active(&self) -> bool {
        let clamped = needs_you_items_clamp(self.items.len() as u64, MAX_NEEDS_YOU_ITEMS as u64);
        needs_you_banner_active(clamped as usize)
    }

    /// Active `NEEDS YOU:` items in insertion order (`<= MAX_NEEDS_YOU_ITEMS`).
    #[must_use]
    pub fn items(&self) -> &[String] {
        &self.items
    }

    /// Feed raw PTY / agent output bytes, returning all `NeedsYouEvent` transitions triggered
    /// by newline-terminated lines in `chunk`.
    pub fn feed_bytes(&mut self, chunk: &[u8]) -> Vec<NeedsYouEvent> {
        let mut events = Vec::new();
        let mut rest = chunk;
        while let &[b, ref tail @ ..] = rest {
            rest = tail;
            if b == b'\n' {
                if let Some(ev) = self.process_line_buf() {
                    events.push(ev);
                }
                self.line_buf.clear();
            } else if b != b'\r' && self.line_buf.len() < MAX_LINE_ACCUM_BYTES {
                self.line_buf.push(b);
            }
        }
        events
    }

    /// Inspect a single complete line directly.
    pub fn observe_line(&mut self, raw_line: &[u8]) -> Option<NeedsYouEvent> {
        let plain = strip_ansi_line(raw_line);
        let text = decode_utf8_or_ascii(&plain);
        let trimmed = text.trim();
        let Some(after) = trimmed.strip_prefix("NEEDS YOU:") else {
            return None;
        };
        let body = after.trim();
        if body.is_empty() {
            return None;
        }
        if body.eq_ignore_ascii_case("nothing") || body.eq_ignore_ascii_case("none") {
            let cleared_count = self.items.len();
            self.items.clear();
            return Some(NeedsYouEvent::Cleared { cleared_count });
        }

        let clamped_item = clamp_utf8_prefix(body);
        // Deduplicate against already-raised items.
        let mut k = 0usize;
        while let Some(existing) = self.items.get(k) {
            if existing == &clamped_item {
                return None;
            }
            k = k.saturating_add(1);
        }
        if self.items.len() >= MAX_NEEDS_YOU_ITEMS {
            let mut shifted = Vec::new();
            let mut j = 1usize;
            while let Some(it) = self.items.get(j) {
                shifted.push(it.clone());
                j = j.saturating_add(1);
            }
            self.items = shifted;
        }
        self.items.push(clamped_item.clone());
        Some(NeedsYouEvent::Raised(clamped_item))
    }

    fn process_line_buf(&mut self) -> Option<NeedsYouEvent> {
        let buf = core::mem::take(&mut self.line_buf);
        self.observe_line(&buf)
    }
}

fn clamp_utf8_prefix(s: &str) -> String {
    let max_b = needs_you_len_clamp(s.len() as u64, MAX_NEEDS_YOU_ITEM_BYTES as u64) as usize;
    let bytes = s.as_bytes();
    let end = if bytes.len() > max_b {
        let mut e = max_b;
        while let Some(&b) = bytes.get(e) {
            if e == 0 || (b & 0b1100_0000) != 0b1000_0000 {
                break;
            }
            e = e.saturating_sub(1);
        }
        e
    } else {
        bytes.len()
    };
    let mut out = String::new();
    if let Some(sub_bytes) = bytes.get(..end) {
        if let Ok(sub) = core::str::from_utf8(sub_bytes) {
            out.push_str(sub);
        }
    }
    out
}

fn decode_utf8_or_ascii(bytes: &[u8]) -> String {
    if let Ok(valid) = core::str::from_utf8(bytes) {
        let cap = if valid.len() < MAX_LINE_ACCUM_BYTES {
            valid.len()
        } else {
            MAX_LINE_ACCUM_BYTES
        };
        let mut out = {
            let _ = cap;
            String::new()
        };
        out.push_str(valid);
        return out;
    }
    let cap = if bytes.len() < MAX_LINE_ACCUM_BYTES {
        bytes.len()
    } else {
        MAX_LINE_ACCUM_BYTES
    };
    let mut out = {
        let _ = cap;
        String::new()
    };
    let mut rest = bytes;
    while let &[b, ref tail @ ..] = rest {
        if b.is_ascii() {
            out.push(b as char);
        } else {
            out.push('?');
        }
        rest = tail;
    }
    out
}

/// Strip ECMA-48 CSI, OSC/DCS/SOS/PM/APC, 2-byte ESC, UTF-8 C1, and non-tab C0/DEL controls.
fn strip_ansi_line(raw: &[u8]) -> Vec<u8> {
    let raw_cap = if raw.len() < MAX_LINE_ACCUM_BYTES {
        raw.len()
    } else {
        MAX_LINE_ACCUM_BYTES
    };
    let mut out = {
        let _ = raw_cap;
        Vec::new()
    };
    let mut i = 0usize;
    while let Some(&b) = raw.get(i) {
        if b == 0x1B {
            match raw.get(i.saturating_add(1)) {
                Some(&b'[') => {
                    i = skip_csi_body(raw, i.saturating_add(2));
                    continue;
                }
                Some(&(b']' | b'P' | b'X' | b'^' | b'_')) => {
                    i = skip_string_body(raw, i.saturating_add(2));
                    continue;
                }
                _ => {
                    let mut p = i.saturating_add(1);
                    while matches!(raw.get(p), Some(&(0x20..=0x2F))) {
                        p = p.saturating_add(1);
                    }
                    if matches!(raw.get(p), Some(&(0x30..=0x7E))) {
                        p = p.saturating_add(1);
                    }
                    i = p;
                    continue;
                }
            }
        }
        if b == 0xC2 {
            match raw.get(i.saturating_add(1)) {
                Some(&0x9B) => {
                    i = skip_csi_body(raw, i.saturating_add(2));
                    continue;
                }
                Some(&(0x9D | 0x90 | 0x98 | 0x9E | 0x9F)) => {
                    i = skip_string_body(raw, i.saturating_add(2));
                    continue;
                }
                Some(&(0x80..=0x9F)) => {
                    i = i.saturating_add(2);
                    continue;
                }
                _ => {}
            }
        }
        if (b < 0x20 && b != b'\t') || b == 0x7F {
            i = i.saturating_add(1);
            continue;
        }
        out.push(b);
        i = i.saturating_add(1);
    }
    out
}

fn skip_csi_body(raw: &[u8], mut i: usize) -> usize {
    while let Some(&c) = raw.get(i) {
        if matches!(c, 0x40..=0x7E) {
            return i.saturating_add(1);
        }
        if matches!(c, 0x20..=0x3F) {
            i = i.saturating_add(1);
        } else {
            return i;
        }
    }
    i
}

fn skip_string_body(raw: &[u8], mut i: usize) -> usize {
    while let Some(&c) = raw.get(i) {
        if c == 0x07 {
            return i.saturating_add(1);
        }
        if c == 0x1B {
            if matches!(raw.get(i.saturating_add(1)), Some(&b'\\')) {
                return i.saturating_add(2);
            }
            return i;
        }
        if c == 0xC2 && matches!(raw.get(i.saturating_add(1)), Some(&0x9C)) {
            return i.saturating_add(2);
        }
        i = i.saturating_add(1);
    }
    i
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn raises_ansi_decorated_needs_you_dedups_and_clears_on_nothing() {
        let mut ledger = NeedsYouLedger::new();
        assert!(!ledger.banner_active());

        // Split across chunks with bold red SGR around the line.
        let e1 = ledger.feed_bytes(b"working...\n\x1b[1;31mNEEDS YOU:");
        assert!(e1.is_empty());
        let e2 = ledger.feed_bytes(b" restart the Mac\x1b[0m\n");
        assert_eq!(
            e2,
            vec![NeedsYouEvent::Raised("restart the Mac".to_string())]
        );
        assert!(ledger.banner_active());
        assert_eq!(ledger.items(), &["restart the Mac".to_string()]);

        // Duplicate item does not re-emit.
        assert!(ledger
            .feed_bytes(b"NEEDS YOU: restart the Mac\n")
            .is_empty());

        // `NEEDS YOU: nothing` takes the banner down immediately!
        let e3 = ledger.feed_bytes(b"  NEEDS YOU: nothing  \n");
        assert_eq!(e3, vec![NeedsYouEvent::Cleared { cleared_count: 1 }]);
        assert!(!ledger.banner_active());
        assert!(ledger.items().is_empty());
    }

    #[test]
    fn strips_dcs_apc_two_byte_esc_c1_and_c0_around_needs_you() {
        let mut ledger = NeedsYouLedger::new();
        let line = b"\x1bP+q\x1b\\\x1b7\xc2\x9b31m\x00NEEDS YOU: grant FDA\x7f\x1b_ignored\x07\n";
        let ev = ledger.feed_bytes(line);
        assert_eq!(ev, vec![NeedsYouEvent::Raised("grant FDA".to_string())]);
    }
}
