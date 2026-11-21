// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Scoped `/f/<F>/...` [`astream_wire::Filter`] advertisement and epoch-versioned routing
//! information base (`Astream.Mesh.TlaSubtreeAnnounce`).
//!
//! Validates every advertised filter via [`Filter::new`], rejects god-root `/>` announcements
//! from regional spokes (`Filter` must start with `/f/`), resolves outbound [`Subject`]s to
//! the lowest-metric fresh regional gateway, and advances RIB versions monotonically via
//! Clean-origin `rib_version_advance`.

use std::collections::BTreeMap;

use astream_wire::{Filter, Subject};

#[cfg(clean_islands)]
#[path = "subtree_announce_island.rs"]
mod subtree_announce_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn rib_routes_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn rib_version_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use subtree_announce_island::{rib_routes_clamp, rib_version_advance};

/// Maximum active `(filter, region)` route entries in one mesh RIB.
pub const MAX_ANNOUNCED_SUBTREES: u64 = 512;

contract_fn! {
    /// Verified freshness check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `rib_route_fresh_isl`.
    #[must_use]
    pub const fn rib_route_fresh(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

fn clone_str(s: &str) -> String {
    let mut out = String::new();
    out.push_str(s);
    out
}

/// Validated regional route entry inside [`SubtreeRib`].
#[derive(Debug, Clone)]
pub struct RibRoute {
    pub filter: Filter,
    pub gateway_id: String,
    pub version: u64,
    pub metric: u64,
    pub expires_mono_ms: u64,
}

/// Epoch-versioned multi-region subject RIB.
#[derive(Debug, Clone)]
pub struct SubtreeRib {
    max_routes: u64,
    rib_epoch: u64,
    routes: BTreeMap<(String, String), RibRoute>,
}

impl Default for SubtreeRib {
    fn default() -> Self {
        Self::new()
    }
}

impl SubtreeRib {
    #[must_use]
    pub fn new() -> Self {
        Self::with_capacity(MAX_ANNOUNCED_SUBTREES)
    }

    #[must_use]
    pub fn with_capacity(max_routes: u64) -> Self {
        let cap = rib_routes_clamp(max_routes, MAX_ANNOUNCED_SUBTREES);
        Self {
            max_routes: if cap == 0 { 1 } else { cap },
            rib_epoch: 0,
            routes: BTreeMap::new(),
        }
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.routes.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.routes.is_empty()
    }

    /// Installs or refreshes a scoped `/f/<F>/...` route advertisement.
    pub fn announce(
        &mut self,
        filter_str: &str,
        gateway_id: &str,
        version: u64,
        metric: u64,
        expires_mono_ms: u64,
    ) -> Result<(), &'static str> {
        let Some(rest) = filter_str.strip_prefix("/f/") else {
            return Err("regional route must be scoped under /f/<fleet>/...");
        };
        if gateway_id.is_empty() {
            return Err("regional route must be scoped under /f/<fleet>/...");
        }
        let fleet_seg = match rest.split_once('/') {
            Some((seg, _)) => seg,
            None => rest,
        };
        if fleet_seg.is_empty() || fleet_seg == "*" || fleet_seg == ">" {
            return Err("regional route must bind concrete <fleet> segment");
        }
        let filter = match Filter::new(clone_str(filter_str)) {
            Ok(f) => f,
            Err(_) => return Err("invalid wire filter"),
        };
        let key = (clone_str(filter_str), clone_str(gateway_id));
        if let Some(existing) = self.routes.get(&key) {
            if version <= existing.version {
                return Err("stale or duplicate route version");
            }
        } else if (self.routes.len() as u64) >= self.max_routes {
            return Err("RIB route table full");
        }
        self.rib_epoch = rib_version_advance(self.rib_epoch, version);
        self.routes.insert(
            key,
            RibRoute {
                filter,
                gateway_id: clone_str(gateway_id),
                version,
                metric,
                expires_mono_ms,
            },
        );
        Ok(())
    }

    /// Resolves `subject` at `now_mono_ms` to the lowest-metric non-expired matching `gateway_id`.
    #[must_use]
    #[allow(clippy::manual_map)]
    pub fn lookup_best_gateway(
        &self,
        subject: &Subject,
        now_mono_ms: u64,
    ) -> Option<(String, u64)> {
        let mut best: Option<(&str, u64)> = None;
        for r in self.routes.values() {
            if !rib_route_fresh(r.expires_mono_ms, now_mono_ms) {
                continue;
            }
            if !r.filter.matches(subject) {
                continue;
            }
            match best {
                None => best = Some((r.gateway_id.as_str(), r.metric)),
                Some((_, best_m)) if r.metric < best_m => {
                    best = Some((r.gateway_id.as_str(), r.metric))
                }
                _ => {}
            }
        }
        match best {
            Some((gw, m)) => Some((clone_str(gw), m)),
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn subtree_rib_rejects_unscoped_filters_and_selects_lowest_metric_live_gateway() {
        let mut rib = SubtreeRib::new();
        assert!(rib.announce("/>", "gw-1", 1, 10, 5_000).is_err());
        rib.announce("/f/alpha/in/n2/>", "gw-backup", 1, 50, 5_000)
            .unwrap();
        rib.announce("/f/alpha/in/n2/>", "gw-primary", 2, 12, 3_000)
            .unwrap();

        let subj = Subject::new("/f/alpha/in/n2/mail").unwrap();
        assert_eq!(
            rib.lookup_best_gateway(&subj, 2_500),
            Some(("gw-primary".to_owned(), 12))
        );
        // Once primary route expires at 3_001, traffic fails over seamlessly to gw-backup!
        assert_eq!(
            rib.lookup_best_gateway(&subj, 3_001),
            Some(("gw-backup".to_owned(), 50))
        );
    }
}
