// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Unicode UAX #29 Zero-Width-Joiner (`U+200D`) & combining-mark per-cell UTF-8 byte cap (`<= 64`
//! bytes) preventing adversarial Zalgo/ZWJ bombs from exploding `Screen` cell memory
//! (`Astream.Grapheme.TlaZwjClusterBudget`).

#[cfg(clean_islands)]
#[path = "zwj_cluster_budget_island.rs"]
mod zwj_cluster_budget_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn gr_bytes_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn gr_clusters_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use zwj_cluster_budget_island::{gr_bytes_clamp, gr_clusters_advance};

/// Hard per-cell UTF-8 grapheme cluster byte budget (`64` bytes).
pub const MAX_CELL_CLUSTER_BYTES: u64 = 64;

contract_fn! {
    /// Verified cluster byte bound (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `gr_cluster_bounded_isl`.
    #[must_use]
    pub const fn gr_cluster_bounded(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Appends ZWJ / combining scalar continuation codepoints to a terminal cell up to `64` bytes.
#[derive(Debug, Clone, Default)]
pub struct CellGraphemeBuilder {
    buf: String,
    truncated_extends: u64,
}

impl CellGraphemeBuilder {
    #[must_use]
    pub fn with_base(base: char) -> Self {
        let mut buf = String::new();
        buf.push(base);
        Self {
            buf,
            truncated_extends: 0,
        }
    }

    pub fn try_push_extend(&mut self, ch: char) -> bool {
        let cap = gr_bytes_clamp(MAX_CELL_CLUSTER_BYTES, MAX_CELL_CLUSTER_BYTES);
        let next_len = (self.buf.len() as u64).saturating_add(ch.len_utf8() as u64);
        if !gr_cluster_bounded(cap, next_len) {
            self.truncated_extends = gr_clusters_advance(
                self.truncated_extends,
                self.truncated_extends.saturating_add(1),
            );
            return false;
        }
        self.buf.push(ch);
        true
    }

    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.buf
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zwj_builder_admits_family_emoji_sequence_and_caps_zalgo_combiner_flood() {
        let mut c = CellGraphemeBuilder::with_base('\u{1F468}');
        assert!(c.try_push_extend('\u{200D}'));
        assert!(c.try_push_extend('\u{1F4BB}'));
        for _ in 0..40 {
            let _ = c.try_push_extend('\u{0301}');
        }
        assert!(c.as_str().len() <= MAX_CELL_CLUSTER_BYTES as usize);
    }
}
