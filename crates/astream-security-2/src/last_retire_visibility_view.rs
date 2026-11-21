// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Checked owned-view & bounded-step retirement-history visibility coordinator
//! (last-value retirement-history lifetime;
//! `Astream.Broker.TlaLastRetireVisibilityView`).
//!
//! Models the visibility-owner retirement discipline:
//! - [`LastRetireVisibilityCoord::publish_last_visible`] advances the visible head monotonically as
//!   an explicit visibility-owner action (never as a query-side side effect).
//! - [`LastRetireVisibilityCoord::release_store_prefix`] advances the store's released prefix while
//!   clamping it at `<= visible_head`, allowing already-opened [`CheckedLastView`] handles whose
//!   forward-history anchor was captured before release to keep reading pre-retire payloads without
//!   a global active-reader registry.
//! - [`LastStep::Pending`] charges retirement preparation and index work to one bounded step
//!   (`<= max_step_budget`), and typed [`LastViewError`] variants replace silent historical fallback.

#[cfg(clean_islands)]
#[path = "last_retire_visibility_view_island.rs"]
mod last_retire_visibility_view_island;
#[cfg(clean_islands)]
pub use last_retire_visibility_view_island::{
    last_retire_head_advance_b124, last_retire_prefix_clamp_b124, last_retire_step_clamp_b124,
};

#[cfg(not(clean_islands))]
/// Monotonically advance the visibility-owner `Last` head.
#[must_use]
pub const fn last_retire_head_advance_b124(cur_head: u64, cand_head: u64) -> u64 {
    if cur_head < cand_head {
        cand_head
    } else {
        cur_head
    }
}

#[cfg(not(clean_islands))]
/// Clamp the store's released retirement prefix to `<= visible_head`.
#[must_use]
pub const fn last_retire_prefix_clamp_b124(cand_prefix: u64, visible_head: u64) -> u64 {
    if cand_prefix < visible_head {
        cand_prefix
    } else {
        visible_head
    }
}

#[cfg(not(clean_islands))]
/// Clamp one `LastStep::Pending` preparation step's work to `max_step_budget`.
#[must_use]
pub const fn last_retire_step_clamp_b124(requested_work: u64, max_step_budget: u64) -> u64 {
    if requested_work < max_step_budget {
        requested_work
    } else {
        max_step_budget
    }
}

contract_fn! {
    /// True iff `store_released_prefix <= visible_head`.
    #[must_use]
    pub const fn last_retire_prefix_within_head_b124(
        store_released_prefix: u64,
        visible_head: u64,
    ) -> bool
    clauses [ensures result == (store_released_prefix <= visible_head)]
    {
        store_released_prefix <= visible_head
    }
}

/// Open mode of the backing log for `Last` retirement-history queries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LastOpenMode {
    /// State-carrying retention mode: retirement history and charges are intact.
    StateCarryingOwned,
    /// Uncarried `retain_before` cut tainted historical `Last` visibility.
    UncarriedCutTainted,
    /// Read-only replica open without retirement-owner authority.
    ReplicaReadOnly,
}

/// Typed errors replacing silent historical fallback on `Last` retirement views.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LastViewError {
    /// Log was opened in a mode that cannot serve checked retirement-history views.
    WrongOpenMode { mode: LastOpenMode },
    /// Requested anchor lies strictly below the store's already-released prefix.
    HistoryReleasedBeforeView {
        requested_anchor: u64,
        released_prefix: u64,
    },
    /// Requested view head exceeds the published visible head.
    BeyondVisibleHead {
        requested_head: u64,
        visible_head: u64,
    },
}

/// Bounded incremental progress of a checked `Last` view scan.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LastStep {
    /// One bounded retirement-prep / index step consumed `charged_work` units, with `remaining_work` left.
    Pending {
        charged_work: u64,
        remaining_work: u64,
    },
    /// View scan reached `snapshot_head` cleanly.
    Ready {
        anchor_offset: u64,
        snapshot_head: u64,
    },
}

/// Checked owned view holding a forward-history link captured while `anchor_offset` was still retained.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CheckedLastView {
    anchor_offset: u64,
    snapshot_head: u64,
    remaining_prep_work: u64,
}

impl CheckedLastView {
    #[must_use]
    pub const fn anchor_offset(&self) -> u64 {
        self.anchor_offset
    }

    #[must_use]
    pub const fn snapshot_head(&self) -> u64 {
        self.snapshot_head
    }

    /// Drive at most one bounded step (`max_step_budget`) of retirement preparation and index work.
    pub fn drive_step(&mut self, max_step_budget: u64) -> LastStep {
        if self.remaining_prep_work == 0 {
            return LastStep::Ready {
                anchor_offset: self.anchor_offset,
                snapshot_head: self.snapshot_head,
            };
        }
        let budget = if max_step_budget == 0 {
            1
        } else {
            max_step_budget
        };
        let charged = last_retire_step_clamp_b124(self.remaining_prep_work, budget);
        self.remaining_prep_work = self.remaining_prep_work.saturating_sub(charged);
        if self.remaining_prep_work == 0 {
            LastStep::Ready {
                anchor_offset: self.anchor_offset,
                snapshot_head: self.snapshot_head,
            }
        } else {
            LastStep::Pending {
                charged_work: charged,
                remaining_work: self.remaining_prep_work,
            }
        }
    }
}

/// Visibility-owner coordinator for `Last` retirement-history views.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LastRetireVisibilityCoord {
    open_mode: LastOpenMode,
    visible_head: u64,
    store_released_prefix: u64,
    max_step_budget: u64,
}

impl LastRetireVisibilityCoord {
    #[must_use]
    pub const fn new(open_mode: LastOpenMode, initial_head: u64, max_step_budget: u64) -> Self {
        Self {
            open_mode,
            visible_head: initial_head,
            store_released_prefix: 0,
            max_step_budget,
        }
    }

    #[must_use]
    pub const fn visible_head(&self) -> u64 {
        self.visible_head
    }

    #[must_use]
    pub const fn store_released_prefix(&self) -> u64 {
        self.store_released_prefix
    }

    /// Visibility-owner operation: monotonically publish a new visible head.
    pub fn publish_last_visible(&mut self, candidate_head: u64) -> Result<u64, LastViewError> {
        if self.open_mode != LastOpenMode::StateCarryingOwned {
            return Err(LastViewError::WrongOpenMode {
                mode: self.open_mode,
            });
        }
        self.visible_head = last_retire_head_advance_b124(self.visible_head, candidate_head);
        Ok(self.visible_head)
    }

    /// Release the store's own historical prefix up to `min(candidate_prefix, visible_head)`.
    /// Existing [`CheckedLastView`] values retain their forward-history chain without a reader registry.
    pub fn release_store_prefix(&mut self, candidate_prefix: u64) -> Result<u64, LastViewError> {
        if self.open_mode != LastOpenMode::StateCarryingOwned {
            return Err(LastViewError::WrongOpenMode {
                mode: self.open_mode,
            });
        }
        let raised = last_retire_head_advance_b124(self.store_released_prefix, candidate_prefix);
        self.store_released_prefix = last_retire_prefix_clamp_b124(raised, self.visible_head);
        let _within =
            last_retire_prefix_within_head_b124(self.store_released_prefix, self.visible_head);
        Ok(self.store_released_prefix)
    }

    /// Acquire a checked owned view at `[anchor_offset, requested_head]`, failing with a typed error
    /// rather than silently falling back when the open mode is wrong or history was already released.
    pub fn open_checked_view(
        &self,
        anchor_offset: u64,
        requested_head: u64,
        prep_work: u64,
    ) -> Result<CheckedLastView, LastViewError> {
        if self.open_mode != LastOpenMode::StateCarryingOwned {
            return Err(LastViewError::WrongOpenMode {
                mode: self.open_mode,
            });
        }
        if anchor_offset < self.store_released_prefix {
            return Err(LastViewError::HistoryReleasedBeforeView {
                requested_anchor: anchor_offset,
                released_prefix: self.store_released_prefix,
            });
        }
        if requested_head > self.visible_head {
            return Err(LastViewError::BeyondVisibleHead {
                requested_head,
                visible_head: self.visible_head,
            });
        }
        Ok(CheckedLastView {
            anchor_offset,
            snapshot_head: requested_head,
            remaining_prep_work: prep_work,
        })
    }

    #[must_use]
    pub const fn max_step_budget(&self) -> u64 {
        self.max_step_budget
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn owned_view_survives_later_prefix_release_and_charges_bounded_pending_steps() {
        let mut coord = LastRetireVisibilityCoord::new(LastOpenMode::StateCarryingOwned, 100, 16);
        assert_eq!(coord.publish_last_visible(250), Ok(250));

        // Open view anchored at 40 before prefix release, requiring 35 units of prep work.
        let mut view = coord.open_checked_view(40, 220, 35).expect("view opens");

        // Store releases its own visible prefix to 180; already-opened `view` keeps working!
        assert_eq!(coord.release_store_prefix(180), Ok(180));
        // A new view below 180 fails with a typed error instead of silent fallback.
        assert_eq!(
            coord.open_checked_view(120, 220, 0),
            Err(LastViewError::HistoryReleasedBeforeView {
                requested_anchor: 120,
                released_prefix: 180,
            })
        );

        let budget = coord.max_step_budget();
        assert_eq!(
            view.drive_step(budget),
            LastStep::Pending {
                charged_work: 16,
                remaining_work: 19,
            }
        );
        assert_eq!(
            view.drive_step(budget),
            LastStep::Pending {
                charged_work: 16,
                remaining_work: 3,
            }
        );
        assert_eq!(
            view.drive_step(budget),
            LastStep::Ready {
                anchor_offset: 40,
                snapshot_head: 220,
            }
        );

        let tainted = LastRetireVisibilityCoord::new(LastOpenMode::UncarriedCutTainted, 50, 8);
        assert_eq!(
            tainted.open_checked_view(0, 50, 0),
            Err(LastViewError::WrongOpenMode {
                mode: LastOpenMode::UncarriedCutTainted,
            })
        );
    }
}
