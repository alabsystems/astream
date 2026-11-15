// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `NEEDS YOU:` menu-bar & window-border banner multiplexer with `NEEDS YOU: nothing` clear
//! semantics (`aterm` primer: one human-only blocker per line; `NEEDS YOU: nothing` takes it down;
//! `Astream.EnvScrub.TlaNeedsYouBannerMux`).

#[cfg(clean_islands)]
#[path = "needs_you_banner_mux_island.rs"]
mod needs_you_banner_mux_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ny_items_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ny_rev_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use needs_you_banner_mux_island::{ny_items_clamp, ny_rev_advance};

/// Maximum active `NEEDS YOU:` items displayed per session border.
pub const MAX_NEEDS_YOU_ITEMS: u64 = 16;

contract_fn! {
    /// Verified clear-state check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ny_cleared_isl`.
    #[must_use]
    pub const fn ny_cleared(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Parses report lines starting with `NEEDS YOU:` and updates the live menu-bar state.
#[derive(Debug, Clone, Default)]
pub struct NeedsYouBannerState {
    items: Vec<String>,
    revision: u64,
}

impl NeedsYouBannerState {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            items: Vec::new(),
            revision: 0,
        }
    }

    pub fn ingest_report(&mut self, report_text: &str) {
        let cap = ny_items_clamp(MAX_NEEDS_YOU_ITEMS, MAX_NEEDS_YOU_ITEMS) as usize;
        for line in report_text.lines() {
            let trimmed = line.trim();
            if let Some(rest) = trimmed.strip_prefix("NEEDS YOU:") {
                let item = rest.trim();
                self.revision = ny_rev_advance(self.revision, self.revision.saturating_add(1));
                if item.eq_ignore_ascii_case("nothing") {
                    self.items.clear();
                } else if !item.is_empty() && self.items.len() < cap {
                    let mut dup = false;
                    for existing in &self.items {
                        if existing.as_str() == item {
                            dup = true;
                            break;
                        }
                    }
                    if !dup {
                        let mut owned = String::new();
                        owned.push_str(item);
                        self.items.push(owned);
                    }
                }
            }
        }
    }

    #[must_use]
    pub fn is_clear(&self) -> bool {
        ny_cleared(0, self.items.len() as u64)
    }

    #[must_use]
    pub fn active_items(&self) -> &[String] {
        &self.items
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn needs_you_mux_collects_blockers_and_takes_banner_down_on_nothing() {
        let mut b = NeedsYouBannerState::new();
        b.ingest_report("Working on wave 15.\nNEEDS YOU: grant Full Disk Access\n");
        assert_eq!(b.active_items(), &["grant Full Disk Access".to_owned()]);
        assert!(!b.is_clear());
        b.ingest_report("NEEDS YOU: nothing\n");
        assert!(b.is_clear());
    }
}
