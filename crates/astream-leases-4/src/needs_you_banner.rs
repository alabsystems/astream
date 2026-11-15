// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `NEEDS YOU:` operator-escalation line parser and menu-bar / window-border banner ledger
//! (`Astream.Agent.TlaNeedsYouBanner`).
//!
//! Per the `aterm` protocol:
//! - A report line starting `NEEDS YOU:` names something only a person can give (a credential,
//!   a decision, physical access), one per line.
//! - `NEEDS YOU: nothing` takes down the active escalation banner for the session.
//!
//! Written using total slice-pattern destructuring (`0` `runtime_checked`, zero dependencies,
//! zero closures).

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
#[path = "needs_you_banner_island.rs"]
mod needs_you_banner_island;
#[cfg(clean_islands)]
pub use needs_you_banner_island::{needs_you_count_clamp, needs_you_seq_advance};

/// Mirror of Clean's `needs_you_count_clamp` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn needs_you_count_clamp(active_items: u64, max_items: u64) -> u64 {
    if active_items < max_items {
        active_items
    } else {
        max_items
    }
}

/// Mirror of Clean's `needs_you_seq_advance` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn needs_you_seq_advance(cur_seq: u64, next_seq: u64) -> u64 {
    if cur_seq < next_seq {
        next_seq
    } else {
        cur_seq
    }
}

contract_fn! {
    /// Kernel-certified check that zero active `NEEDS YOU:` items remain (`active_items == 0`),
    /// linked via `clean-kernel-defeq` to `needs_you_is_cleared_isl`.
    #[must_use]
    pub const fn needs_you_is_cleared(active_items: u64) -> bool
    clauses [ensures result == (active_items == 0)]
    {
        active_items == 0
    }
}

/// Maximum number of concurrent `NEEDS YOU:` items retained per session banner.
pub const MAX_NEEDS_YOU_ITEMS: usize = 16;

/// Parsed directive from a single line of agent output.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NeedsYouDirective<'a> {
    /// Line is not a `NEEDS YOU:` directive.
    Ignore,
    /// `NEEDS YOU: nothing` — clears all active items on the session's banner.
    ClearNothing,
    /// `NEEDS YOU: <item>` — adds or refreshes an operator-required item.
    Raise(&'a str),
}

#[must_use]
const fn trim_ascii_bytes(mut s: &[u8]) -> &[u8] {
    while let &[first, ref rest @ ..] = s {
        if first == b' ' || first == b'\t' || first == b'\r' {
            s = rest;
        } else {
            break;
        }
    }
    while let &[ref head @ .., last] = s {
        if last == b' ' || last == b'\t' || last == b'\r' {
            s = head;
        } else {
            break;
        }
    }
    s
}

#[must_use]
const fn eq_ascii_nothing(s: &[u8]) -> bool {
    let &[b0, b1, b2, b3, b4, b5, b6] = s else {
        return false;
    };
    (b0 | 0x20) == b'n'
        && (b1 | 0x20) == b'o'
        && (b2 | 0x20) == b't'
        && (b3 | 0x20) == b'h'
        && (b4 | 0x20) == b'i'
        && (b5 | 0x20) == b'n'
        && (b6 | 0x20) == b'g'
}

/// Parse one line of agent report text for a leading `NEEDS YOU:` directive.
#[must_use]
pub fn parse_needs_you_line(line: &str) -> NeedsYouDirective<'_> {
    let trimmed = trim_ascii_bytes(line.as_bytes());
    let Some(rest) = trimmed.strip_prefix(b"NEEDS YOU:") else {
        return NeedsYouDirective::Ignore;
    };
    let item_bytes = trim_ascii_bytes(rest);
    if item_bytes.is_empty() {
        return NeedsYouDirective::Ignore;
    }
    if eq_ascii_nothing(item_bytes) {
        return NeedsYouDirective::ClearNothing;
    }
    match std::str::from_utf8(item_bytes) {
        Ok(item) => NeedsYouDirective::Raise(item),
        Err(_) => NeedsYouDirective::Ignore,
    }
}

/// Bounded per-session `NEEDS YOU:` banner state (`Astream.Agent.TlaNeedsYouBanner`).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct NeedsYouLedger {
    seq: u64,
    items: Vec<String>,
    banner_visible: bool,
}

impl NeedsYouLedger {
    /// Construct an empty, cleared ledger.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            seq: 0,
            items: Vec::new(),
            banner_visible: false,
        }
    }

    /// Monotone update sequence number.
    #[must_use]
    pub const fn seq(&self) -> u64 {
        self.seq
    }

    /// Whether the menu-bar / window-border `NEEDS YOU` indicator is visible.
    #[must_use]
    pub const fn is_banner_visible(&self) -> bool {
        self.banner_visible
    }

    /// Active operator-escalation items (`<= MAX_NEEDS_YOU_ITEMS`).
    #[must_use]
    pub fn items(&self) -> &[String] {
        &self.items
    }

    /// Scan all lines of `report` and apply every `NEEDS YOU:` directive in order.
    pub fn ingest_report(&mut self, report: &str) -> bool {
        let mut changed = false;
        for line in report.split('\n') {
            match parse_needs_you_line(line) {
                NeedsYouDirective::Ignore => {}
                NeedsYouDirective::ClearNothing => {
                    self.seq = needs_you_seq_advance(self.seq, self.seq.saturating_add(1));
                    self.items.clear();
                    self.banner_visible = false;
                    let _ = needs_you_is_cleared(self.items.len() as u64);
                    changed = true;
                }
                NeedsYouDirective::Raise(item) => {
                    self.seq = needs_you_seq_advance(self.seq, self.seq.saturating_add(1));
                    let mut exists = false;
                    let mut cur_slice = self.items.as_slice();
                    while let [cur, tail @ ..] = cur_slice {
                        if cur.as_str() == item {
                            exists = true;
                            break;
                        }
                        cur_slice = tail;
                    }
                    if !exists {
                        let allowed = needs_you_count_clamp(
                            (self.items.len() as u64).saturating_add(1),
                            MAX_NEEDS_YOU_ITEMS as u64,
                        ) as usize;
                        if self.items.len() < allowed {
                            let mut owned = String::new();
                            owned.push_str(item);
                            self.items.push(owned);
                        }
                    }
                    self.banner_visible = !self.items.is_empty();
                    changed = true;
                }
            }
        }
        changed
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn raises_dedups_and_clears_needs_you_banner() {
        let mut ledger = NeedsYouLedger::new();
        assert!(!ledger.is_banner_visible());

        assert!(ledger.ingest_report(
            "Working on remaining items.\nNEEDS YOU: restart the Mac\nNEEDS YOU: grant Full Disk Access\nNEEDS YOU: restart the Mac\n"
        ));
        assert!(ledger.is_banner_visible());
        assert_eq!(
            ledger.items(),
            &[
                "restart the Mac".to_string(),
                "grant Full Disk Access".to_string()
            ]
        );

        assert!(ledger.ingest_report("NEEDS YOU: nothing\n"));
        assert!(!ledger.is_banner_visible());
        assert!(ledger.items().is_empty());
        assert!(ledger.seq() >= 4);
    }
}
