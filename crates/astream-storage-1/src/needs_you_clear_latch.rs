// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `NEEDS YOU:` menu-bar escalation & `NEEDS YOU: nothing` clear latch
//! (`Astream.Agent.TlaNeedsYouClearLatch`).
//!
//! Enforces `aterm`'s operator-attention banner protocol:
//! - Each line starting `NEEDS YOU: <item>` raises/retains a menu-bar and window-border
//!   escalation (`1` item per line, bounded to `max_items`).
//! - A line `NEEDS YOU: nothing` takes the banner down (`active_items == 0`).

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
#[path = "needs_you_clear_latch_island.rs"]
mod needs_you_clear_latch_island;
#[cfg(clean_islands)]
pub use needs_you_clear_latch_island::{banner_items_clamp, banner_rev_advance};

/// Default maximum simultaneous `NEEDS YOU:` items displayed per session.
pub const DEFAULT_MAX_BANNER_ITEMS: usize = 8;

/// Maximum bytes retained per single `NEEDS YOU:` line payload.
pub const MAX_BANNER_LINE_BYTES: usize = 160;

const NEEDS_YOU_PREFIX: &[u8] = b"NEEDS YOU:";

#[cfg(not(clean_islands))]
/// Monotonically advance the session's `NEEDS YOU` banner revision.
#[must_use]
pub const fn banner_rev_advance(cur_rev: u64, cand_rev: u64) -> u64 {
    if cur_rev < cand_rev {
        cand_rev
    } else {
        cur_rev
    }
}

#[cfg(not(clean_islands))]
/// Clamp active `NEEDS YOU:` item count to `max_items`.
#[must_use]
pub const fn banner_items_clamp(cand_items: u64, max_items: u64) -> u64 {
    if cand_items < max_items {
        cand_items
    } else {
        max_items
    }
}

contract_fn! {
    /// True iff `active_items == zero_expected` (`0`, border & menu-bar banner down).
    #[must_use]
    pub const fn banner_clear_active(active_items: u64, zero_expected: u64) -> bool
    clauses [ensures result == (active_items == zero_expected)]
    {
        active_items == zero_expected
    }
}

fn trim_ascii(mut s: &[u8]) -> &[u8] {
    while let &[b, ref tail @ ..] = s {
        if b == b' ' || b == b'\t' || b == b'\r' {
            s = tail;
        } else {
            break;
        }
    }
    while let &[ref head @ .., b] = s {
        if b == b' ' || b == b'\t' || b == b'\r' {
            s = head;
        } else {
            break;
        }
    }
    s
}

fn eq_ascii_nothing(s: &[u8]) -> bool {
    let &[c0, c1, c2, c3, c4, c5, c6] = s else {
        return false;
    };
    c0.eq_ignore_ascii_case(&b'n')
        && c1.eq_ignore_ascii_case(&b'o')
        && c2.eq_ignore_ascii_case(&b't')
        && c3.eq_ignore_ascii_case(&b'h')
        && c4.eq_ignore_ascii_case(&b'i')
        && c5.eq_ignore_ascii_case(&b'n')
        && c6.eq_ignore_ascii_case(&b'g')
}

/// Stateful `NEEDS YOU:` banner latch for a single supervised session.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NeedsYouClearLatch {
    banner_rev: u64,
    max_items: usize,
    items: Vec<Vec<u8>>,
}

impl Default for NeedsYouClearLatch {
    fn default() -> Self {
        Self::new(DEFAULT_MAX_BANNER_ITEMS)
    }
}

impl NeedsYouClearLatch {
    #[must_use]
    pub const fn new(max_items: usize) -> Self {
        let cap = if max_items == 0 {
            DEFAULT_MAX_BANNER_ITEMS
        } else {
            max_items
        };
        Self {
            banner_rev: 0,
            max_items: cap,
            items: Vec::new(),
        }
    }

    #[must_use]
    pub const fn banner_rev(&self) -> u64 {
        self.banner_rev
    }

    #[must_use]
    pub fn active_count(&self) -> usize {
        banner_items_clamp(self.items.len() as u64, self.max_items as u64) as usize
    }

    #[must_use]
    pub fn is_banner_down(&self) -> bool {
        banner_clear_active(self.active_count() as u64, 0)
    }

    #[must_use]
    pub fn items(&self) -> &[Vec<u8>] {
        &self.items
    }

    /// Scan an agent turn reply line-by-line for `NEEDS YOU:` directives.
    #[allow(clippy::manual_unwrap_or, clippy::manual_unwrap_or_default)]
    pub fn ingest_reply(&mut self, reply: &[u8]) -> u64 {
        let mut mutated = false;
        let mut rem = reply;
        while !rem.is_empty() {
            let mut nl_pos = None;
            let mut idx = 0usize;
            let mut scan = rem;
            while let &[b, ref tail @ ..] = scan {
                if b == b'\n' {
                    nl_pos = Some(idx);
                    break;
                }
                idx = idx.saturating_add(1);
                scan = tail;
            }
            let (line, next_rem) = match nl_pos {
                Some(p) => (
                    match rem.get(..p) {
                        Some(s) => s,
                        None => &[],
                    },
                    match rem.get(p.saturating_add(1)..) {
                        Some(s) => s,
                        None => &[],
                    },
                ),
                None => (rem, &[][..]),
            };
            rem = next_rem;

            if line.starts_with(NEEDS_YOU_PREFIX) {
                let after_prefix = match line.get(NEEDS_YOU_PREFIX.len()..) {
                    Some(s) => s,
                    None => &[],
                };
                let raw_item = trim_ascii(after_prefix);
                if eq_ascii_nothing(raw_item) {
                    if !self.items.is_empty() {
                        self.items.clear();
                        mutated = true;
                    }
                } else if !raw_item.is_empty() && self.items.len() < self.max_items {
                    let mut take = if raw_item.len() < MAX_BANNER_LINE_BYTES {
                        raw_item.len()
                    } else {
                        MAX_BANNER_LINE_BYTES
                    };
                    if take < raw_item.len() {
                        while take > 0 {
                            match raw_item.get(take) {
                                Some(&b) if (b & 0xC0) == 0x80 => take = take.saturating_sub(1),
                                _ => break,
                            }
                        }
                    }
                    let clipped = match raw_item.get(..take) {
                        Some(s) => s,
                        None => raw_item,
                    };
                    let mut already = false;
                    let mut k = 0usize;
                    while k < self.items.len() {
                        if let Some(existing) = self.items.get(k) {
                            if existing.as_slice() == clipped {
                                already = true;
                                break;
                            }
                        }
                        k = k.saturating_add(1);
                    }
                    if !already {
                        let mut v = Vec::new();
                        v.extend_from_slice(clipped);
                        self.items.push(v);
                        mutated = true;
                    }
                }
            }
        }

        if mutated {
            let cand = self.banner_rev.saturating_add(1);
            self.banner_rev = banner_rev_advance(self.banner_rev, cand);
        }
        self.banner_rev
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn raises_one_item_per_line_and_takes_banner_down_on_needs_you_nothing() {
        let mut latch = NeedsYouClearLatch::new(4);
        assert!(latch.is_banner_down());

        latch.ingest_reply(
            b"Working on build.\nNEEDS YOU: grant Full Disk Access\nNEEDS YOU: YubiKey touch\n",
        );
        assert!(!latch.is_banner_down());
        assert_eq!(latch.active_count(), 2);
        assert_eq!(latch.banner_rev(), 1);

        // Indented or inline mention is NOT a line-initial NEEDS YOU: directive
        latch.ingest_reply(b"  NEEDS YOU: nothing\n");
        assert_eq!(latch.active_count(), 2);

        // Exact line-initial NEEDS YOU: nothing clears all active items!
        latch.ingest_reply(b"Resolved!\nNEEDS YOU: nothing\n");
        assert!(latch.is_banner_down());
        assert_eq!(latch.active_count(), 0);
        assert_eq!(latch.banner_rev(), 2);
    }
}
