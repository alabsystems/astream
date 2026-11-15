// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm` `NEEDS YOU:` menu-bar / window-border human-blocker fence
//! (`Astream.Agent.TlaAtermNeedsYouBannerFence`).
//!
//! Enforces `aterm` `NEEDS YOU:` discipline:
//! - Only human-only blockers (`Credential`, `Decision`, `PhysicalAccess`, `MacRestartSyspolicydStuck`)
//!   may raise a `NEEDS YOU:` banner; `AgentSelfRestart` is rejected (agents must run `aterm ctl @self restart`).
//! - Bounds active banner slots to `MAX_NEEDS_YOU_ITEMS` (`needs_you_active_clamp_b106`).
//! - `clear_all_nothing()` (`NEEDS YOU: nothing`) atomically clears all active banners while
//!   advancing `banner_epoch` monotonically (`needs_you_epoch_advance`).

#[cfg(clean_islands)]
#[path = "aterm_needs_you_banner_fence_island.rs"]
mod aterm_needs_you_banner_fence_island;
#[cfg(clean_islands)]
pub use aterm_needs_you_banner_fence_island::{
    needs_you_active_clamp_b106, needs_you_epoch_advance,
};

#[cfg(not(clean_islands))]
/// Clamp active `NEEDS YOU:` item count to `max_items`.
#[must_use]
pub const fn needs_you_active_clamp_b106(cand_active: u64, max_items: u64) -> u64 {
    if cand_active < max_items {
        cand_active
    } else {
        max_items
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the `NEEDS YOU:` banner state epoch.
#[must_use]
pub const fn needs_you_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff active `NEEDS YOU:` slots remain strictly below `max_items`.
    #[must_use]
    pub const fn needs_you_has_slot(active: u64, max_items: u64) -> bool
    clauses [ensures result == (active < max_items)]
    {
        active < max_items
    }
}

/// Maximum concurrent `NEEDS YOU:` lines displayed per session border.
pub const MAX_NEEDS_YOU_ITEMS: usize = 8;

/// Category of blocker proposed for `NEEDS YOU:`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NeedsYouCategory {
    Credential,
    HumanDecision,
    PhysicalAccess,
    MacRestartSyspolicydStuck,
    /// Disallowed: agents must self-restart via `aterm ctl @self restart`.
    AgentSelfRestart,
}

/// Outcome of raising a `NEEDS YOU:` item.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NeedsYouOutcome {
    Posted {
        active_count: u64,
        banner_epoch: u64,
    },
    Deduplicated {
        banner_epoch: u64,
    },
    RejectedSelfRestart,
    BannerSlotsFull,
}

/// Bounded `NEEDS YOU:` banner tracker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AtermNeedsYouBannerFence {
    item_digests: [u64; MAX_NEEDS_YOU_ITEMS],
    active_count: u64,
    banner_epoch: u64,
}

impl Default for AtermNeedsYouBannerFence {
    fn default() -> Self {
        Self::new()
    }
}

impl AtermNeedsYouBannerFence {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            item_digests: [0; MAX_NEEDS_YOU_ITEMS],
            active_count: 0,
            banner_epoch: 0,
        }
    }

    #[must_use]
    pub const fn active_count(&self) -> u64 {
        self.active_count
    }

    #[must_use]
    pub const fn banner_epoch(&self) -> u64 {
        self.banner_epoch
    }

    /// Post a `NEEDS YOU:` blocker item identified by `digest`.
    pub fn post_item(&mut self, category: NeedsYouCategory, digest: u64) -> NeedsYouOutcome {
        if category == NeedsYouCategory::AgentSelfRestart {
            return NeedsYouOutcome::RejectedSelfRestart;
        }
        let mut idx = 0usize;
        let len = self.active_count as usize;
        while idx < len {
            let Some(&existing) = self.item_digests.get(idx) else {
                break;
            };
            if existing == digest {
                return NeedsYouOutcome::Deduplicated {
                    banner_epoch: self.banner_epoch,
                };
            }
            idx = idx.saturating_add(1);
        }
        let cap = MAX_NEEDS_YOU_ITEMS as u64;
        if !needs_you_has_slot(self.active_count, cap) {
            return NeedsYouOutcome::BannerSlotsFull;
        }
        if let Some(dst) = self.item_digests.get_mut(self.active_count as usize) {
            *dst = digest;
        }
        let next_cnt = self.active_count.saturating_add(1);
        self.active_count = needs_you_active_clamp_b106(next_cnt, cap);
        let next_ep = self.banner_epoch.saturating_add(1);
        self.banner_epoch = needs_you_epoch_advance(self.banner_epoch, next_ep);
        NeedsYouOutcome::Posted {
            active_count: self.active_count,
            banner_epoch: self.banner_epoch,
        }
    }

    /// Handle `NEEDS YOU: nothing`, taking down all active banners for this session.
    pub fn clear_all_nothing(&mut self) -> u64 {
        self.active_count = 0;
        self.item_digests = [0; MAX_NEEDS_YOU_ITEMS];
        let next_ep = self.banner_epoch.saturating_add(1);
        self.banner_epoch = needs_you_epoch_advance(self.banner_epoch, next_ep);
        self.banner_epoch
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_agent_self_restart_and_clears_on_needs_you_nothing() {
        let mut fence = AtermNeedsYouBannerFence::new();
        assert_eq!(
            fence.post_item(NeedsYouCategory::AgentSelfRestart, 0x11),
            NeedsYouOutcome::RejectedSelfRestart
        );
        assert_eq!(
            fence.post_item(NeedsYouCategory::MacRestartSyspolicydStuck, 0x22),
            NeedsYouOutcome::Posted {
                active_count: 1,
                banner_epoch: 1,
            }
        );
        assert_eq!(fence.clear_all_nothing(), 2);
        assert_eq!(fence.active_count(), 0);
    }
}
