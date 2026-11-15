// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Same-batch `/a/bind` -> `Escalate::PrincipalPrefix` matcher (`broker.ordered-tier`: matching a
//! producer bound by a `/a/bind` record staged earlier inside the same uncommitted batch;
//! `Astream.OrdBar.TlaPreBindBatchMatch`).

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
#[path = "pre_bind_batch_match_island.rs"]
mod pre_bind_batch_match_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ob_bnd_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ob_stg_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use pre_bind_batch_match_island::{ob_bnd_clamp, ob_stg_advance};

/// Maximum staged `/a/bind` entries per single batch (`256`).
pub const MAX_STAGED_BINDS: u64 = 256;

contract_fn! {
    /// Verified principal-escalation match (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `ob_principal_escalated_isl`.
    #[must_use]
    pub const fn ob_principal_escalated(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct StagedBindEscalator {
    staged_binds: u64,
    entries: Vec<(u64, bool)>,
    overflowed: bool,
}

impl StagedBindEscalator {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            staged_binds: 0,
            entries: Vec::new(),
            overflowed: false,
        }
    }

    pub fn stage_bind(&mut self, producer_id: u64, principal: &str, rule_prefix: &str) {
        if producer_id == 0 {
            return;
        }
        let matches_rule =
            !principal.is_empty() && !rule_prefix.is_empty() && principal.starts_with(rule_prefix);
        let mut idx = 0usize;
        while idx < self.entries.len() {
            if let Some(entry) = self.entries.get_mut(idx) {
                if entry.0 == producer_id {
                    entry.1 = matches_rule;
                    return;
                }
            }
            idx = idx.saturating_add(1);
        }
        let next = ob_bnd_clamp(self.staged_binds.saturating_add(1), MAX_STAGED_BINDS);
        if next <= self.staged_binds {
            self.overflowed = true;
            return;
        }
        self.staged_binds = next;
        self.entries.push((producer_id, matches_rule));
    }

    pub fn check_publish_escalated(&mut self, producer_id: u64, subject: &str) -> bool {
        let _ = ob_stg_advance(0, self.staged_binds);
        if subject.is_empty() || subject.starts_with("/a/") || producer_id == 0 {
            return false;
        }
        if self.overflowed {
            return ob_principal_escalated(1, 1);
        }
        let mut hit = false;
        let mut idx = 0usize;
        while idx < self.entries.len() {
            if let Some(&(pid, matches_rule)) = self.entries.get(idx) {
                if pid == producer_id && matches_rule {
                    hit = true;
                    break;
                }
            }
            idx = idx.saturating_add(1);
        }
        ob_principal_escalated(if hit { 1 } else { 0 }, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn escalates_non_hidden_publish_bound_by_earlier_bind_in_same_batch() {
        let mut e = StagedBindEscalator::new();
        e.stage_bind(77, "person/alice", "person/");
        assert!(!e.check_publish_escalated(77, "/a/bind"));
        assert!(e.check_publish_escalated(77, "/f/main/in/n1"));
        assert!(!e.check_publish_escalated(88, "/f/main/in/n1"));
    }
}
