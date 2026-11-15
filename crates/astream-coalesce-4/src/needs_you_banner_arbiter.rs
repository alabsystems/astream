// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm` `NEEDS YOU:` Menu-Bar & Window-Border Escalation Arbiter.
//!
//! Enforces the exact `aterm` human-escalation protocol:
//! - A report line starting `NEEDS YOU:` names something ONLY a person can give (a credential,
//!   a decision, physical access, or a Mac restart), one per line, shown on the menu bar and
//!   window border while Autopilot keeps independent work going.
//! - `NEEDS YOU: nothing` clears all active escalations and takes the banner down.
//! - Self-servicing agent restarts (`"restart the agent"`, `"agent restart"`,
//!   `"aterm ctl @self restart"`) are **rejected** because an agent restart is NEVER a
//!   `NEEDS YOU` item (unlike `"restart the Mac"`, which IS a valid `NEEDS YOU` item!).
//!
//! Backed by Clean TLA+ Island `Astream.Agent.TlaNeedsYouArbiter`
//! (`needs_you_banner_arbiter_island.rs`), proving `activeItems <= maxItemsCap` and
//! `bannerBytes <= maxBannerBytes`.

#![allow(
    clippy::absurd_extreme_comparisons,
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
#[path = "needs_you_banner_arbiter_island.rs"]
mod island;
#[cfg(clean_islands)]
pub use island::{arbiter_needs_you_bytes_clamp, arbiter_needs_you_items_clamp};

#[cfg(not(clean_islands))]
#[inline]
pub const fn arbiter_needs_you_items_clamp(items: u64, max_items: u64) -> u64 {
    if items < max_items {
        items
    } else {
        max_items
    }
}

#[cfg(not(clean_islands))]
#[inline]
pub const fn arbiter_needs_you_bytes_clamp(bytes: u64, max_bytes: u64) -> u64 {
    if bytes < max_bytes {
        bytes
    } else {
        max_bytes
    }
}

contract_fn! {
    /// Kernel-certified check whether the `NEEDS YOU:` banner has zero active items.
    #[must_use]
    #[inline]
    pub const fn needs_you_banner_clear(active_items: u64) -> bool
    clauses [ensures result == (active_items <= 0)]
    {
        active_items <= 0
    }
}

/// Maximum concurrent `NEEDS YOU:` items displayed per session (`8`).
pub const MAX_NEEDS_YOU_ITEMS: usize = 8;

/// Maximum rendered menu-bar/border summary byte length (`256` bytes).
pub const DEFAULT_MAX_BANNER_BYTES: usize = 256;

/// Outcome of scanning a single agent report line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NeedsYouLineEffect {
    /// Line does not start with `NEEDS YOU:`.
    NotNeedsYouLine,
    /// `NEEDS YOU: nothing` cleared all active items.
    ClearedAll,
    /// Rejected because an agent restart must be performed directly via `aterm ctl @self restart`.
    RejectedSelfAgentRestart,
    /// Duplicate of an already active escalation item.
    DuplicateIgnored,
    /// Added a new human-only escalation item (`active_items <= MAX_NEEDS_YOU_ITEMS`).
    Added(String),
    /// Dropped because `MAX_NEEDS_YOU_ITEMS` or `max_banner_bytes` is full.
    DroppedOverBudget,
}

const fn trim_ascii_bytes(mut bytes: &[u8]) -> &[u8] {
    while let &[b' ' | b'\t' | b'\r', ref tail @ ..] = bytes {
        bytes = tail;
    }
    while let &[ref head @ .., b' ' | b'\t' | b'\r'] = bytes {
        bytes = head;
    }
    bytes
}

const fn strip_exact_prefix<'a>(mut bytes: &'a [u8], mut prefix: &[u8]) -> Option<&'a [u8]> {
    if bytes.len() < prefix.len() {
        return None;
    }
    while let &[pb, ref ptail @ ..] = prefix {
        let &[bb, ref btail @ ..] = bytes else {
            return None;
        };
        if bb != pb {
            return None;
        }
        prefix = ptail;
        bytes = btail;
    }
    Some(bytes)
}

const fn ascii_lower(b: u8) -> u8 {
    if b >= b'A' && b <= b'Z' {
        b.wrapping_add(32)
    } else {
        b
    }
}

const fn eq_ascii_ignore_case(mut a: &[u8], mut b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    while let (&[ba, ref at @ ..], &[bb, ref bt @ ..]) = (a, b) {
        if ascii_lower(ba) != ascii_lower(bb) {
            return false;
        }
        a = at;
        b = bt;
    }
    true
}

const fn starts_with_ascii_ignore_case(mut hay: &[u8], mut needle: &[u8]) -> bool {
    if hay.len() < needle.len() {
        return false;
    }
    while let &[nb, ref ntail @ ..] = needle {
        let &[hb, ref htail @ ..] = hay else {
            return false;
        };
        if ascii_lower(hb) != ascii_lower(nb) {
            return false;
        }
        needle = ntail;
        hay = htail;
    }
    true
}

const fn contains_ascii_ignore_case(mut hay: &[u8], needle: &[u8]) -> bool {
    if needle.is_empty() {
        return true;
    }
    while hay.len() >= needle.len() {
        if starts_with_ascii_ignore_case(hay, needle) {
            return true;
        }
        let &[_, ref tail @ ..] = hay else {
            break;
        };
        hay = tail;
    }
    false
}

fn is_self_agent_restart(body: &str) -> bool {
    let raw = body.as_bytes();
    // Mac restart IS a valid person-only escalation (`syspolicyd=stuck`), never reject it!
    if contains_ascii_ignore_case(raw, b"restart the mac")
        || contains_ascii_ignore_case(raw, b"mac restart")
        || contains_ascii_ignore_case(raw, b"reboot")
    {
        return false;
    }
    contains_ascii_ignore_case(raw, b"agent restart")
        || contains_ascii_ignore_case(raw, b"restart the agent")
        || contains_ascii_ignore_case(raw, b"restart agent")
        || contains_ascii_ignore_case(raw, b"@self restart")
}

/// Stateful `NEEDS YOU:` menu-bar/window-border arbiter certified by `TlaNeedsYouArbiter`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NeedsYouBannerArbiter {
    items: Vec<String>,
    max_items_cap: u64,
    banner_bytes: u64,
    max_banner_bytes: u64,
}

impl Default for NeedsYouBannerArbiter {
    fn default() -> Self {
        Self::new(MAX_NEEDS_YOU_ITEMS, DEFAULT_MAX_BANNER_BYTES)
    }
}

impl NeedsYouBannerArbiter {
    #[must_use]
    pub fn new(max_items: usize, max_banner_bytes: usize) -> Self {
        let cap_items = if max_items == 0 || max_items > MAX_NEEDS_YOU_ITEMS {
            MAX_NEEDS_YOU_ITEMS as u64
        } else {
            max_items as u64
        };
        let cap_bytes = if max_banner_bytes == 0 {
            DEFAULT_MAX_BANNER_BYTES as u64
        } else {
            max_banner_bytes as u64
        };
        Self {
            items: Vec::new(),
            max_items_cap: cap_items,
            banner_bytes: 0,
            max_banner_bytes: cap_bytes,
        }
    }

    #[inline]
    pub fn active_items(&self) -> u64 {
        arbiter_needs_you_items_clamp(self.items.len() as u64, self.max_items_cap)
    }

    #[inline]
    pub const fn banner_bytes(&self) -> u64 {
        self.banner_bytes
    }

    #[inline]
    pub fn is_clear(&self) -> bool {
        needs_you_banner_clear(self.active_items())
    }

    #[inline]
    pub fn items(&self) -> &[String] {
        &self.items
    }

    /// Evaluates one line of agent output (`ApplyReportLine` in `TlaNeedsYouArbiter`).
    pub fn ingest_line(&mut self, line: &str) -> NeedsYouLineEffect {
        let trimmed_bytes = trim_ascii_bytes(line.as_bytes());
        let Some(after_prefix) = strip_exact_prefix(trimmed_bytes, b"NEEDS YOU:") else {
            return NeedsYouLineEffect::NotNeedsYouLine;
        };
        let body_bytes = trim_ascii_bytes(after_prefix);
        if body_bytes.is_empty() || eq_ascii_ignore_case(body_bytes, b"nothing") {
            self.items.clear();
            self.banner_bytes = 0;
            return NeedsYouLineEffect::ClearedAll;
        }
        let Ok(body) = core::str::from_utf8(body_bytes) else {
            return NeedsYouLineEffect::NotNeedsYouLine;
        };
        if is_self_agent_restart(body) {
            return NeedsYouLineEffect::RejectedSelfAgentRestart;
        }

        let mut rest = self.items.as_slice();
        while let [existing, tail @ ..] = rest {
            if existing.as_bytes() == body_bytes {
                return NeedsYouLineEffect::DuplicateIgnored;
            }
            rest = tail;
        }

        let sep_cost = if self.items.is_empty() { 0u64 } else { 3u64 }; // " | "
        let proposed_bytes = self
            .banner_bytes
            .saturating_add(sep_cost)
            .saturating_add(body.len() as u64);
        let clamped_bytes = arbiter_needs_you_bytes_clamp(proposed_bytes, self.max_banner_bytes);
        let proposed_items = (self.items.len() as u64).saturating_add(1);
        let clamped_items = arbiter_needs_you_items_clamp(proposed_items, self.max_items_cap);

        if clamped_bytes < proposed_bytes || clamped_items < proposed_items {
            return NeedsYouLineEffect::DroppedOverBudget;
        }

        let mut owned = String::new();
        owned.push_str(body);
        self.items.push(owned.clone());
        self.banner_bytes = clamped_bytes;
        NeedsYouLineEffect::Added(owned)
    }

    /// Renders the compact menu-bar summary (`<= max_banner_bytes`).
    #[must_use]
    pub fn render_banner(&self) -> String {
        let cap = if self.banner_bytes < 4096 {
            self.banner_bytes as usize
        } else {
            4096
        };
        let mut out = {
            let _ = cap;
            String::new()
        };
        let mut rest = self.items.as_slice();
        let mut first = true;
        while let [item, tail @ ..] = rest {
            if !first {
                out.push_str(" | ");
            }
            first = false;
            out.push_str(item);
            rest = tail;
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_mac_vs_agent_restart_rule_and_clears_on_nothing() {
        let mut arb = NeedsYouBannerArbiter::default();
        assert!(arb.is_clear());

        // Self agent restart is rejected!
        assert_eq!(
            arb.ingest_line("NEEDS YOU: restart the agent to pick up binary"),
            NeedsYouLineEffect::RejectedSelfAgentRestart
        );
        assert!(arb.is_clear());

        // Mac restart IS accepted (`syspolicyd=stuck`)!
        assert_eq!(
            arb.ingest_line("NEEDS YOU: restart the Mac"),
            NeedsYouLineEffect::Added(String::from("restart the Mac"))
        );
        assert_eq!(
            arb.ingest_line("NEEDS YOU: grant Full Disk Access in System Settings"),
            NeedsYouLineEffect::Added(String::from("grant Full Disk Access in System Settings"))
        );
        assert!(!arb.is_clear());
        assert_eq!(
            arb.render_banner(),
            "restart the Mac | grant Full Disk Access in System Settings"
        );

        // `NEEDS YOU: nothing` takes the banner down cleanly.
        assert_eq!(
            arb.ingest_line("  NEEDS YOU: Nothing  "),
            NeedsYouLineEffect::ClearedAll
        );
        assert!(arb.is_clear());
        assert_eq!(arb.banner_bytes(), 0);
    }
}
