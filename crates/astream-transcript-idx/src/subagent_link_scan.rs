// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Subagent invocation scanner extracting `invoke_subagent` conversation IDs and formatting
//! `[<label>](conversation://<conversation-id>)` links (`Astream.Transcript.TlaSubagentLinkScan`).

#[cfg(clean_islands)]
#[path = "subagent_link_scan_island.rs"]
mod subagent_link_scan_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tr_links_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tr_scan_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use subagent_link_scan_island::{tr_links_clamp, tr_scan_advance};

/// Maximum distinct `conversation://` subagent links indexed per transcript.
pub const MAX_SUBAGENT_LINKS: u64 = 256;

contract_fn! {
    /// Verified link-cap check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `tr_links_bounded_isl`.
    #[must_use]
    pub const fn tr_links_bounded(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

fn copy_str(s: &str) -> String {
    let mut out = String::new();
    out.push_str(s);
    out
}

fn valid_conv_id(conv_id: &str) -> bool {
    if conv_id.is_empty() {
        return false;
    }
    let bytes = conv_id.as_bytes();
    let mut idx = 0usize;
    while idx < bytes.len() {
        let Some(&b) = bytes.get(idx) else {
            break;
        };
        if b <= 0x20 || b == 0x7F || b == b')' || b == b']' {
            return false;
        }
        idx = idx.saturating_add(1);
    }
    true
}

#[must_use]
pub fn format_conversation_link(label: &str, conv_id: &str) -> String {
    let mut out = String::new();
    out.push('[');
    out.push_str(label);
    out.push_str("](conversation://");
    out.push_str(conv_id);
    out.push(')');
    out
}

/// Collects spawned subagent `(role, conversation_id)` pairs from `transcript.jsonl` steps.
#[derive(Debug, Clone, Default)]
pub struct SubagentLinkIndex {
    links: Vec<(String, String)>,
    scanned_steps: u64,
}

impl SubagentLinkIndex {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            links: Vec::new(),
            scanned_steps: 0,
        }
    }

    pub fn record_spawn(&mut self, role: &str, conv_id: &str) -> bool {
        self.scanned_steps =
            tr_scan_advance(self.scanned_steps, self.scanned_steps.saturating_add(1));
        if !valid_conv_id(conv_id) {
            return false;
        }
        let mut idx = 0usize;
        while idx < self.links.len() {
            if let Some((_, existing_id)) = self.links.get(idx) {
                if existing_id == conv_id {
                    return true;
                }
            }
            idx = idx.saturating_add(1);
        }
        let cap = tr_links_clamp(MAX_SUBAGENT_LINKS, MAX_SUBAGENT_LINKS);
        let next_len = (self.links.len() as u64).saturating_add(1);
        if !tr_links_bounded(cap, next_len) {
            return false;
        }
        self.links.push((copy_str(role), copy_str(conv_id)));
        true
    }

    #[must_use]
    pub fn render_markdown_links(&self) -> Vec<String> {
        let mut out = Vec::new();
        let mut idx = 0usize;
        while idx < self.links.len() {
            if let Some((role, id)) = self.links.get(idx) {
                out.push(format_conversation_link(role, id));
            }
            idx = idx.saturating_add(1);
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn subagent_scanner_deduplicates_conversation_ids_and_formats_links() {
        let mut idx = SubagentLinkIndex::new();
        assert!(idx.record_spawn("Broker Auditor", "6e5181aa-c34c"));
        assert!(idx.record_spawn("Broker Auditor", "6e5181aa-c34c"));
        assert_eq!(
            idx.render_markdown_links(),
            vec!["[Broker Auditor](conversation://6e5181aa-c34c)".to_owned()]
        );
    }
}
