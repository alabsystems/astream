// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `last_owner` subject-charge authorization guard (`is_retire_charged()`): a retire authorizes
//! against the producer the subject is charged to (`last_owner`, refusing an updater that did not
//! introduce the `Last` entry) (`Astream.SubjRet.TlaLastOwnerChargeAuth`).

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
#[path = "last_owner_charge_auth_island.rs"]
mod last_owner_charge_auth_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn srb_chg_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn srb_auth_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use last_owner_charge_auth_island::{srb_auth_advance, srb_chg_clamp};

/// Maximum tracked `last_owner` entries in shard table (`65_536`).
pub const MAX_LAST_OWNERS: u64 = 65_536;

contract_fn! {
    /// Verified exact `last_owner` match (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `srb_is_charged_owner_isl`.
    #[must_use]
    pub const fn srb_is_charged_owner(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct LastOwnerTable {
    owners: Vec<(String, u64)>,
    authorized_retires: u64,
}

impl LastOwnerTable {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            owners: Vec::new(),
            authorized_retires: 0,
        }
    }

    /// Charges only the introducing producer; subsequent updates by other producers do not steal ownership.
    pub fn on_publish(&mut self, subject: &str, producer_id: u64) -> bool {
        if subject.is_empty() || producer_id == 0 {
            return false;
        }
        let mut idx = 0usize;
        while idx < self.owners.len() {
            if let Some((s, _)) = self.owners.get(idx) {
                if s == subject {
                    return true;
                }
            }
            idx = idx.saturating_add(1);
        }
        let next = srb_chg_clamp(
            (self.owners.len() as u64).saturating_add(1),
            MAX_LAST_OWNERS,
        );
        if next as usize <= self.owners.len() {
            return false;
        }
        let mut owned = String::new();
        owned.push_str(subject);
        self.owners.push((owned, producer_id));
        true
    }

    pub fn authorize_retire(&mut self, subject: &str, caller_producer: u64) -> bool {
        if subject.is_empty() || caller_producer == 0 {
            return false;
        }
        for &b in subject.as_bytes() {
            if b == b'*' || b == b'>' {
                return false;
            }
        }
        let mut authorized = false;
        for (s, owner) in core::mem::take(&mut self.owners) {
            if !authorized && s == subject {
                let matched = u64::from(owner == caller_producer);
                if srb_is_charged_owner(matched, 1) {
                    authorized = true;
                } else {
                    self.owners.push((s, owner));
                }
            } else {
                self.owners.push((s, owner));
            }
        }
        if authorized {
            self.authorized_retires = srb_auth_advance(
                self.authorized_retires,
                self.authorized_retires.saturating_add(1),
            );
            return true;
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_wildcard_or_updater_that_did_not_introduce_subject() {
        let mut t = LastOwnerTable::new();
        assert!(t.on_publish("/f/a/pub/n1/s1/presence", 101));
        assert!(t.on_publish("/f/a/pub/n1/s1/presence", 202));
        assert!(!t.authorize_retire("/f/a/pub/n1/*/presence", 101));
        assert!(!t.authorize_retire("/f/a/pub/n1/s1/presence", 202));
        assert!(t.authorize_retire("/f/a/pub/n1/s1/presence", 101));
    }
}
