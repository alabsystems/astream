// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `/a/bind` & `/a/will` Anchor Copy-Forward Compaction Planner
//! (`Astream.Broker.TlaWillBindCompaction`).
//!
//! Long-lived fabric sessions register `/a/bind` principal bindings and `/a/will` last-will
//! tombstones near the beginning of a broker log. Naive prefix retention (`retain_before`)
//! either stalls `base_offset` at the oldest live anchor (pinning multi-gigabyte historical
//! segments on disk and in RAM) or risks dropping a live anchor across restart.
//!
//! [`plan_anchor_rollover`] computes a deterministic, crash-safe copy-forward schedule:
//! 1. Identifies all live `/a/bind` and pending `/a/will` anchors below `effective_cut` via
//!    contract-verified [`anchor_pinned_below_cut`], ordered ascending by `(log_offset, key_id)`.
//! 2. Bounds per-pass synthetic re-appends via Clean-origin [`anchor_copy_clamp`]`(count, copy_cap)`,
//!    assigning fresh tail offsets `hw_offset, hw_offset + 1, ...` that must be fsynced *before*
//!    advancing `base_offset`.
//! 3. Advances `base_offset` via Clean-origin [`retain_base_advance`]: either all the way to
//!    `effective_cut` (when all pinned anchors fit within `copy_cap`) or up to the first
//!    un-copied live anchor's `log_offset` (so zero live anchors are ever truncated).

#[cfg(clean_islands)]
#[path = "will_compaction_island.rs"]
mod will_compaction_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn anchor_copy_clamp(proposed_copies: u64, copy_cap: u64) -> u64 {
    if proposed_copies < copy_cap {
        proposed_copies
    } else {
        copy_cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn retain_base_advance(cur_base: u64, cand_base: u64) -> u64 {
    if cur_base < cand_base {
        cand_base
    } else {
        cur_base
    }
}
#[cfg(clean_islands)]
pub use will_compaction_island::{anchor_copy_clamp, retain_base_advance};

/// Default maximum number of live `/a/bind` + `/a/will` anchors copied forward in one pass.
pub const DEFAULT_ANCHOR_COPY_CAP: u64 = 256;

contract_fn! {
    /// Kernel-certified check whether a live anchor at `anchor_offset` sits strictly below
    /// `cut_offset` (`anchor_offset < cut_offset`), linked via `clean-kernel-defeq` to
    /// `anchor_pinned_below_cut_isl`.
    #[must_use]
    pub const fn anchor_pinned_below_cut(anchor_offset: u64, cut_offset: u64) -> bool
    clauses [ensures result == (anchor_offset < cut_offset)]
    {
        anchor_offset < cut_offset
    }
}

/// Kind of broker control record pinning a historical log offset.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AnchorKind {
    /// Principal identity-to-capability binding (`/a/bind`).
    IdentityBind,
    /// Armed connection last-will record (`/a/will`).
    PendingWill,
}

/// Descriptor for a single live `/a/bind` or pending `/a/will` record currently residing at
/// `log_offset`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LiveLogAnchor {
    pub kind: AnchorKind,
    pub key_id: u64,
    pub log_offset: u64,
}

/// Planned copy-forward re-append mapping an old anchor offset to its new tail offset.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AnchorCopyEntry {
    pub kind: AnchorKind,
    pub key_id: u64,
    pub old_offset: u64,
    pub new_tail_offset: u64,
}

/// Deterministic compaction plan produced by [`plan_anchor_rollover`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AnchorRolloverPlan {
    /// Ordered synthetic re-appends that must be committed to the tail before truncating to
    /// `new_base_offset`.
    pub copies: Vec<AnchorCopyEntry>,
    /// Safe monotone `base_offset` (`>= cur_base` and `<= hw_offset`).
    pub new_base_offset: u64,
    /// Post-copy high-water offset (`hw_offset + copies.len()`).
    pub projected_hw_offset: u64,
    /// Number of pinned anchors still below `target_cut` if `copy_cap` capped this pass.
    pub deferred_anchors: u64,
}

fn anchor_precedes(a: LiveLogAnchor, b: LiveLogAnchor) -> bool {
    if a.log_offset != b.log_offset {
        return a.log_offset < b.log_offset;
    }
    a.key_id < b.key_id
}

fn sort_anchors_in_place(items: &mut [LiveLogAnchor]) {
    let mut i = 1usize;
    while i < items.len() {
        let Some(&cur) = items.get(i) else {
            break;
        };
        let mut j = i;
        while j > 0 {
            let prev_idx = j.saturating_sub(1);
            let Some(&prev_item) = items.get(prev_idx) else {
                break;
            };
            if !anchor_precedes(cur, prev_item) {
                break;
            }
            if let Some(dst) = items.get_mut(j) {
                *dst = prev_item;
            }
            j = prev_idx;
        }
        if let Some(dst) = items.get_mut(j) {
            *dst = cur;
        }
        i = i.saturating_add(1);
    }
}

/// Plan a crash-safe `/a/bind` + `/a/will` copy-forward pass and compute the resulting safe
/// `new_base_offset`.
#[must_use]
pub fn plan_anchor_rollover(
    anchors: &[LiveLogAnchor],
    cur_base: u64,
    hw_offset: u64,
    target_cut: u64,
    copy_cap: u64,
) -> AnchorRolloverPlan {
    let safe_hw = if hw_offset < cur_base {
        cur_base
    } else {
        hw_offset
    };
    let effective_cut = if target_cut < safe_hw {
        target_cut
    } else {
        safe_hw
    };
    if effective_cut <= cur_base {
        return AnchorRolloverPlan {
            copies: Vec::new(),
            new_base_offset: cur_base,
            projected_hw_offset: safe_hw,
            deferred_anchors: 0,
        };
    }

    let mut pinned = Vec::new();
    let mut cur_anchors = anchors;
    while let &[a, ref rest @ ..] = cur_anchors {
        if anchor_pinned_below_cut(a.log_offset, effective_cut) {
            pinned.push(a);
        }
        cur_anchors = rest;
    }
    sort_anchors_in_place(&mut pinned);

    let total_pinned = pinned.len() as u64;
    let allowed_copies = anchor_copy_clamp(total_pinned, copy_cap);
    let mut take_count = if allowed_copies < (usize::MAX as u64) {
        allowed_copies as usize
    } else {
        usize::MAX
    };
    if take_count > pinned.len() {
        take_count = pinned.len();
    }

    // If `copy_cap` splits a tie where multiple anchors share the exact same `log_offset`,
    // never copy a partial offset group that we still cannot advance `base_offset` past!
    if let Some(boundary_item) = pinned.get(take_count) {
        let boundary_offset = boundary_item.log_offset;
        while take_count > 0 {
            let prev_idx = take_count.saturating_sub(1);
            let same = match pinned.get(prev_idx) {
                Some(prev) => prev.log_offset == boundary_offset,
                None => false,
            };
            if !same {
                break;
            }
            take_count = prev_idx;
        }
    }

    let mut copies = Vec::new();
    let mut k = 0usize;
    let mut next_tail = safe_hw;
    while k < take_count {
        if let Some(&a) = pinned.get(k) {
            let assigned = next_tail;
            next_tail = next_tail.saturating_add(1);
            copies.push(AnchorCopyEntry {
                kind: a.kind,
                key_id: a.key_id,
                old_offset: a.log_offset,
                new_tail_offset: assigned,
            });
        }
        k = k.saturating_add(1);
    }

    let cand_base = match pinned.get(take_count) {
        Some(rem_first) => rem_first.log_offset,
        None => effective_cut,
    };
    let new_base_offset = retain_base_advance(cur_base, cand_base);
    let deferred_anchors = pinned.len().saturating_sub(take_count) as u64;

    AnchorRolloverPlan {
        copies,
        new_base_offset,
        projected_hw_offset: next_tail,
        deferred_anchors,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn copies_all_pinned_anchors_and_advances_base_to_target_cut() {
        let anchors = [
            LiveLogAnchor {
                kind: AnchorKind::PendingWill,
                key_id: 22,
                log_offset: 15,
            },
            LiveLogAnchor {
                kind: AnchorKind::IdentityBind,
                key_id: 7,
                log_offset: 3,
            },
            LiveLogAnchor {
                kind: AnchorKind::PendingWill,
                key_id: 99,
                log_offset: 140,
            },
        ];

        let plan = plan_anchor_rollover(&anchors, 0, 200, 100, DEFAULT_ANCHOR_COPY_CAP);
        assert_eq!(plan.copies.len(), 2);
        assert_eq!(
            plan.copies[0],
            AnchorCopyEntry {
                kind: AnchorKind::IdentityBind,
                key_id: 7,
                old_offset: 3,
                new_tail_offset: 200,
            }
        );
        assert_eq!(
            plan.copies[1],
            AnchorCopyEntry {
                kind: AnchorKind::PendingWill,
                key_id: 22,
                old_offset: 15,
                new_tail_offset: 201,
            }
        );
        assert_eq!(plan.new_base_offset, 100);
        assert_eq!(plan.projected_hw_offset, 202);
        assert_eq!(plan.deferred_anchors, 0);
    }

    #[test]
    fn copy_cap_bounds_batch_and_halts_base_at_first_uncopied_anchor() {
        let anchors = [
            LiveLogAnchor {
                kind: AnchorKind::IdentityBind,
                key_id: 1,
                log_offset: 10,
            },
            LiveLogAnchor {
                kind: AnchorKind::PendingWill,
                key_id: 2,
                log_offset: 25,
            },
            LiveLogAnchor {
                kind: AnchorKind::PendingWill,
                key_id: 3,
                log_offset: 40,
            },
        ];

        let plan1 = plan_anchor_rollover(&anchors, 5, 500, 100, 2);
        assert_eq!(plan1.copies.len(), 2);
        assert_eq!(plan1.new_base_offset, 40);
        assert_eq!(plan1.projected_hw_offset, 502);
        assert_eq!(plan1.deferred_anchors, 1);

        // Next pass with updated anchor offsets completes rollover to 100.
        let updated = [
            LiveLogAnchor {
                kind: AnchorKind::IdentityBind,
                key_id: 1,
                log_offset: 500,
            },
            LiveLogAnchor {
                kind: AnchorKind::PendingWill,
                key_id: 2,
                log_offset: 501,
            },
            LiveLogAnchor {
                kind: AnchorKind::PendingWill,
                key_id: 3,
                log_offset: 40,
            },
        ];
        let plan2 = plan_anchor_rollover(&updated, plan1.new_base_offset, 502, 100, 2);
        assert_eq!(plan2.copies.len(), 1);
        assert_eq!(plan2.copies[0].old_offset, 40);
        assert_eq!(plan2.copies[0].new_tail_offset, 502);
        assert_eq!(plan2.new_base_offset, 100);
        assert_eq!(plan2.deferred_anchors, 0);
    }

    #[test]
    fn zero_copy_cap_never_truncates_live_anchor_and_never_regresses_base() {
        let anchors = [LiveLogAnchor {
            kind: AnchorKind::IdentityBind,
            key_id: 9,
            log_offset: 18,
        }];
        let plan = plan_anchor_rollover(&anchors, 12, 100, 80, 0);
        assert!(plan.copies.is_empty());
        assert_eq!(plan.new_base_offset, 18);
        assert_eq!(plan.deferred_anchors, 1);

        let noop = plan_anchor_rollover(&anchors, 50, 100, 30, 10);
        assert!(noop.copies.is_empty());
        assert_eq!(noop.new_base_offset, 50);
    }
}
