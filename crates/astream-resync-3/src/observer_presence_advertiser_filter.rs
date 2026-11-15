// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Observer presence `observer=1` advertiser-set & holder-liveness exclusion filter
//! (`docs/DESIGN-aterm-fabric.md` §11.2 register 19 lines 3664–3670, A5 line 3753;
//! `Astream.Agent.TlaObserverPresenceAdvertiserFilter`).
//!
//! Prevents read-only observer bridges (`aterm-link serve --sock`) from poisoning fleet routing:
//! - An observer bridge republishes presence for sessions it observes under its own `node_id` marked
//!   `observer=1`,
//! - Rows carrying `observer=1` MUST be excluded from BOTH §6.1's `sid` advertiser candidate set
//!   (otherwise opening one observer would flip every visible session `ERR ambiguous` fleet-wide!)
//!   AND holder-liveness checks,
//! - Faking `observer=1` can ONLY remove a node from the candidate set (never add one), so the flag
//!   fails safe!

#[cfg(clean_islands)]
#[path = "observer_presence_advertiser_filter_island.rs"]
mod observer_presence_advertiser_filter_island;
#[cfg(clean_islands)]
pub use observer_presence_advertiser_filter_island::{
    advertiser_count_clamp_b137, presence_fold_offset_advance_b137,
};

/// Maximum authoritative advertisers tracked per session (`64` — `> 1` already triggers `Ambiguous`).
pub const MAX_TRACKED_ADVERTISERS: u64 = 64;

#[cfg(not(clean_islands))]
/// Clamp authoritative advertiser count to `adv_cap`.
#[must_use]
pub const fn advertiser_count_clamp_b137(cand_count: u64, adv_cap: u64) -> u64 {
    if cand_count < adv_cap {
        cand_count
    } else {
        adv_cap
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance presence fold offset watermark.
#[must_use]
pub const fn presence_fold_offset_advance_b137(cur_off: u64, cand_off: u64) -> u64 {
    if cur_off < cand_off {
        cand_off
    } else {
        cur_off
    }
}

contract_fn! {
    /// True iff `!is_observer_row && !node_state_is_gone`.
    #[must_use]
    pub const fn row_counts_as_authoritative_host_b137(
        is_observer_row: bool,
        node_state_is_gone: bool,
    ) -> bool
    clauses [ensures result == (!is_observer_row && !node_state_is_gone)]
    {
        !is_observer_row && !node_state_is_gone
    }
}

/// Resolution of a session's authoritative hosting node after folding `Last` presence rows.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum AdvertiserResolution {
    /// Zero non-observer live/exited host rows seen.
    NoAuthoritativeHost { observer_sightings: u64 },
    /// Exactly one authoritative hosting node (`node_id`), regardless of how many `observer=1` rows exist!
    UniqueHost {
        node_id: u64,
        holder_is_live: bool,
        observer_sightings: u64,
    },
    /// Two or more distinct non-observer nodes claimed this `sid` -> `ERR ambiguous`!
    ConflictingHosts { distinct_hosts: u64 },
}

/// Presence fold state machine for a single `sid` across fleet nodes.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct SessionAdvertiserFold {
    adv_cap: u64,
    fold_offset: u64,
    primary_host: Option<(u64, bool)>, // (node_id, session_is_live)
    distinct_hosts: u64,
    observer_sightings: u64,
}

impl SessionAdvertiserFold {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            adv_cap: MAX_TRACKED_ADVERTISERS,
            fold_offset: 0,
            primary_host: None,
            distinct_hosts: 0,
            observer_sightings: 0,
        }
    }

    #[must_use]
    pub const fn distinct_hosts(&self) -> u64 {
        advertiser_count_clamp_b137(self.distinct_hosts, self.adv_cap)
    }

    #[must_use]
    pub const fn fold_offset(&self) -> u64 {
        self.fold_offset
    }

    /// Fold one presence row `(offset, advertising_node, is_observer_row, node_is_gone, session_is_live)`.
    pub fn fold_presence_row(
        &mut self,
        offset: u64,
        advertising_node: u64,
        is_observer_row: bool,
        node_is_gone: bool,
        session_is_live: bool,
    ) {
        self.fold_offset = presence_fold_offset_advance_b137(self.fold_offset, offset);
        if is_observer_row {
            // Excluded from both advertiser candidate set AND holder-liveness!
            self.observer_sightings = self.observer_sightings.saturating_add(1);
            return;
        }
        if !row_counts_as_authoritative_host_b137(false, node_is_gone) {
            if let Some((host, _)) = self.primary_host {
                if host == advertising_node && self.distinct_hosts == 1 {
                    self.primary_host = None;
                    self.distinct_hosts = 0;
                }
            }
            return;
        }
        match self.primary_host {
            None => {
                self.primary_host = Some((advertising_node, session_is_live));
                self.distinct_hosts = advertiser_count_clamp_b137(1, self.adv_cap);
            }
            Some((existing_node, _)) => {
                if existing_node == advertising_node {
                    self.primary_host = Some((existing_node, session_is_live));
                } else {
                    self.distinct_hosts = advertiser_count_clamp_b137(
                        self.distinct_hosts.saturating_add(1),
                        self.adv_cap,
                    );
                }
            }
        }
    }

    #[must_use]
    pub const fn resolve(&self) -> AdvertiserResolution {
        if self.distinct_hosts == 0 {
            AdvertiserResolution::NoAuthoritativeHost {
                observer_sightings: self.observer_sightings,
            }
        } else if self.distinct_hosts == 1 {
            match self.primary_host {
                Some((node_id, holder_is_live)) => AdvertiserResolution::UniqueHost {
                    node_id,
                    holder_is_live,
                    observer_sightings: self.observer_sightings,
                },
                None => AdvertiserResolution::NoAuthoritativeHost {
                    observer_sightings: self.observer_sightings,
                },
            }
        } else {
            AdvertiserResolution::ConflictingHosts {
                distinct_hosts: self.distinct_hosts,
            }
        }
    }
}

impl Default for SessionAdvertiserFold {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn observer_rows_neither_trigger_ambiguity_nor_keep_dead_holder_live() {
        let mut f = SessionAdvertiserFold::new();
        // Real host node 1 advertises `s-abc` live:
        f.fold_presence_row(10, 1, false, false, true);
        // Three observer bridges (`observer=1`) on nodes 2, 3, 4 also publish `s-abc`:
        f.fold_presence_row(11, 2, true, false, true);
        f.fold_presence_row(12, 3, true, false, true);
        f.fold_presence_row(13, 4, true, false, true);
        assert_eq!(
            f.resolve(),
            AdvertiserResolution::UniqueHost {
                node_id: 1,
                holder_is_live: true,
                observer_sightings: 3
            }
        );
        // When real host node 1 goes `gone`, observer sightings do NOT fake a live holder!
        f.fold_presence_row(14, 1, false, true, false);
        assert_eq!(
            f.resolve(),
            AdvertiserResolution::NoAuthoritativeHost {
                observer_sightings: 3
            }
        );
        // Two non-observer hosts (nodes 1 and 9) DO trigger `ConflictingHosts`:
        f.fold_presence_row(15, 1, false, false, true);
        f.fold_presence_row(16, 9, false, false, true);
        assert_eq!(
            f.resolve(),
            AdvertiserResolution::ConflictingHosts { distinct_hosts: 2 }
        );
    }
}
