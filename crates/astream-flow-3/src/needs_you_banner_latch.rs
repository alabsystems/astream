//! `aterm` `NEEDS YOU:` menu-bar & window-border human escalation latch.

#[cfg(clean_islands)]
#[path = "needs_you_banner_latch_island.rs"]
mod needs_you_banner_latch_island;
#[cfg(clean_islands)]
pub use needs_you_banner_latch_island::{needs_you_active_clamp, needs_you_revision_advance};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn needs_you_active_clamp(count: u64) -> u64 {
    if count < 8 {
        count
    } else {
        8
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn needs_you_revision_advance(prev_rev: u64, next_rev: u64) -> u64 {
    if prev_rev < next_rev {
        next_rev
    } else {
        prev_rev
    }
}

contract_fn! {
    #[must_use]
    pub const fn needs_you_banner_visible(active_count: u64) -> bool
    clauses [ensures result == (1 <= active_count)]
    {
        1 <= active_count
    }
}

pub const MAX_NEEDS_YOU_ITEMS: usize = 8;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NeedsYouCategory {
    Credential,
    HumanDecision,
    PhysicalAccessOrPrivacyGrant,
    MacRestart,
    AgentRestartSelfHandled,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NeedsYouBannerLatch {
    item_hashes: [u64; MAX_NEEDS_YOU_ITEMS],
    active_len: usize,
    revision: u64,
}

impl NeedsYouBannerLatch {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            item_hashes: [0; MAX_NEEDS_YOU_ITEMS],
            active_len: 0,
            revision: 0,
        }
    }

    #[must_use]
    pub const fn is_visible(&self) -> bool {
        needs_you_banner_visible(self.active_len as u64)
    }

    #[must_use]
    pub const fn active_count(&self) -> usize {
        self.active_len
    }

    #[must_use]
    pub const fn revision(&self) -> u64 {
        self.revision
    }

    #[must_use]
    pub fn active_item_hashes(&self) -> &[u64] {
        let cap = if self.active_len < MAX_NEEDS_YOU_ITEMS {
            self.active_len
        } else {
            MAX_NEEDS_YOU_ITEMS
        };
        match self.item_hashes.get(..cap) {
            Some(s) => s,
            None => &[],
        }
    }

    pub fn report_item(&mut self, category: NeedsYouCategory, item_hash: u64) -> bool {
        if matches!(category, NeedsYouCategory::AgentRestartSelfHandled) {
            // Agent restarts are handled via `aterm ctl @self restart`, never `NEEDS YOU:`.
            return false;
        }
        let mut rest = self.active_item_hashes();
        while let &[h, ref tail @ ..] = rest {
            if h == item_hash {
                return false;
            }
            rest = tail;
        }
        let next_len = needs_you_active_clamp((self.active_len as u64).saturating_add(1)) as usize;
        if next_len > self.active_len {
            if let Some(slot) = self.item_hashes.get_mut(self.active_len) {
                *slot = item_hash;
                self.active_len = next_len;
                self.revision =
                    needs_you_revision_advance(self.revision, self.revision.saturating_add(1));
                return true;
            }
        }
        false
    }

    pub fn clear_nothing(&mut self) {
        if self.active_len > 0 {
            self.active_len = 0;
            self.item_hashes = [0; MAX_NEEDS_YOU_ITEMS];
            self.revision =
                needs_you_revision_advance(self.revision, self.revision.saturating_add(1));
        }
    }
}

impl Default for NeedsYouBannerLatch {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_agent_restart_deduplicates_items_and_clears_on_nothing() {
        let mut l = NeedsYouBannerLatch::new();
        assert!(!l.is_visible());
        assert!(!l.report_item(NeedsYouCategory::AgentRestartSelfHandled, 1));
        assert!(!l.is_visible());

        assert!(l.report_item(NeedsYouCategory::Credential, 100));
        assert!(!l.report_item(NeedsYouCategory::Credential, 100));
        assert!(l.is_visible());
        assert_eq!(l.active_count(), 1);
        assert_eq!(l.active_item_hashes(), &[100]);

        l.clear_nothing();
        assert!(!l.is_visible());
        assert_eq!(l.active_count(), 0);
        assert_eq!(l.revision(), 2);
        assert_eq!(needs_you_active_clamp(99), 8);
    }
}
