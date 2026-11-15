// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm-broker.retain` person-vs-node inbox hold evaluator keeping unread person-lane mail for
//! its full 7-day window regardless of node commits while releasing node-lane mail once its inbox
//! group commits past `record_offset` (`Astream.HeldComp.TlaPersonVsNodeMail`).

#[cfg(clean_islands)]
#[path = "person_vs_node_mail_island.rs"]
mod person_vs_node_mail_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn hc_lane_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn hc_rel_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use person_vs_node_mail_island::{hc_lane_clamp, hc_rel_advance};

/// Lane code (`0 = NodeInbox`, `1 = PersonInbox`).
pub const PERSON_LANE_CODE: u64 = 1;

contract_fn! {
    /// Verified unread hold requirement (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `hc_mail_retained_isl`.
    #[must_use]
    pub const fn hc_mail_retained(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct MailHoldPolicy {
    evaluated: u64,
}

impl MailHoldPolicy {
    #[must_use]
    pub const fn new() -> Self {
        Self { evaluated: 0 }
    }

    pub fn must_hold_mail(
        &mut self,
        is_person_lane: bool,
        record_offset: u64,
        lane_group_committed_exclusive: u64,
        within_seven_days: bool,
    ) -> bool {
        let _ = hc_lane_clamp(if is_person_lane { 1 } else { 0 }, PERSON_LANE_CODE);
        self.evaluated = hc_rel_advance(self.evaluated, self.evaluated.saturating_add(1));
        if !within_seven_days {
            return false;
        }
        let unread_by_own_group = record_offset >= lane_group_committed_exclusive;
        hc_mail_retained(if unread_by_own_group { 1 } else { 0 }, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn holds_unread_person_mail_and_releases_node_mail_once_group_commits_past_it() {
        let mut p = MailHoldPolicy::new();
        assert!(p.must_hold_mail(true, 10, 0, true));
        assert!(!p.must_hold_mail(false, 10, 11, true));
        assert!(!p.must_hold_mail(true, 10, 0, false));
    }
}
