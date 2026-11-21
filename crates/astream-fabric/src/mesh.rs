// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Automatic multi-region peer discovery and loop-free hop-TTL federation routing
//! (`DESIGN-aterm-fabric.md` §15).
//!
//! Peers publish compact `v=1` [`PeerAnnouncement`] rows as retained `Last` records under
//! `/f/<fleet>/pub/<region>/peer/announce`. [`FederationMeshTable`] ingests those rows with:
//! - monotone epoch anti-replay ([`mesh_epoch_advance`]),
//! - split-horizon origin exclusion (`origin_region == local_region` rejected by
//!   [`mesh_route_admissible_code`]), and
//! - bounded hop-TTL progression (`hop < max_hops`, [`mesh_hop_clamp`];
//!   `Astream.Broker.TlaFederationMesh`),
//!
//! synthesizing deterministic [`FederationRule`] sets for [`astream_broker::federation::FederationRunner`]
//! across multi-region hub-and-spoke, ring, and full-mesh topologies without transitive echo
//! loops.

use astream_broker::federation::{
    FederationRule, SubjectRewrite, DEFAULT_FEDERATION_BATCH, MAX_FEDERATION_RULES,
};
use astream_wire::{Filter, Subject};
use std::collections::BTreeMap;

#[cfg(clean_islands)]
#[path = "mesh_island.rs"]
mod mesh_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn mesh_hop_below_max_code(hop: u64, max_hops: u64) -> u64 {
    if hop < max_hops {
        1
    } else {
        0
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn mesh_origin_gate_code(not_self_origin: u64, hop_ok: u64) -> u64 {
    if not_self_origin < 1 {
        0
    } else {
        hop_ok
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn mesh_hop_clamp(hop: u64, max_hops: u64) -> u64 {
    if hop < max_hops {
        hop
    } else {
        max_hops
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn mesh_epoch_advance(cur_epoch: u64, proposed_epoch: u64) -> u64 {
    if cur_epoch < proposed_epoch {
        proposed_epoch
    } else {
        cur_epoch
    }
}
#[cfg(clean_islands)]
pub use mesh_island::{
    mesh_epoch_advance, mesh_hop_below_max_code, mesh_hop_clamp, mesh_origin_gate_code,
};

/// Three-parameter split-horizon + hop-TTL admission kernel (`mesh_route_admissible_code_isl`),
/// composed over Clean-origin [`mesh_origin_gate_code`] and [`mesh_hop_below_max_code`].
#[must_use]
pub const fn mesh_route_admissible_code(not_self_origin: u64, hop: u64, max_hops: u64) -> u64 {
    mesh_origin_gate_code(not_self_origin, mesh_hop_below_max_code(hop, max_hops))
}

contract_fn! {
    /// Verified check that a mesh route admission code equals `1`, linked via
    /// `clean-kernel-defeq` to `mesh_code_is_admissible_isl`.
    #[must_use]
    pub const fn mesh_code_is_admissible(code: u64) -> bool
    clauses [ensures result == (code == 1)]
    {
        code == 1
    }
}

/// Hard cap on tracked peers in one [`FederationMeshTable`].
pub const MAX_MESH_PEERS: usize = 64;

/// Hard cap on exported subject prefixes in one [`PeerAnnouncement`].
pub const MAX_EXPORT_PREFIXES: usize = 16;

/// Default maximum hop count (`2`, supporting hub-and-spoke `A -> Hub -> B` without cycles).
pub const DEFAULT_MESH_MAX_HOPS: u8 = 2;

/// Compact `v=1` retained peer-discovery announcement published under
/// `/f/<fleet>/pub/<region>/peer/announce`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PeerAnnouncement {
    /// Advertising peer's region identifier (non-empty segment token, e.g. `"us-west"`).
    pub region: String,
    /// Origin region of the exported prefixes (equals `region` for direct advertisements).
    pub origin_region: String,
    /// Reachable broker endpoint (`host:port` or `unix:/path`).
    pub endpoint: String,
    /// Monotone announcement epoch per `(region, origin_region)`.
    pub epoch: u64,
    /// Hop distance from `origin_region` (`0` at the origin itself).
    pub hop: u8,
    /// Subject prefixes exported by `origin_region` (e.g. `["/f/prod/pub/n1"]`).
    pub prefixes: Vec<String>,
}

fn valid_region_token(tok: &str) -> bool {
    if tok.is_empty() || tok.len() > 64 {
        return false;
    }
    let mut rest = tok.as_bytes();
    while let &[b, ref tail @ ..] = rest {
        let ok = b.is_ascii_alphanumeric() || b == b'-' || b == b'_';
        if !ok {
            return false;
        }
        rest = tail;
    }
    true
}

fn valid_export_prefix(prefix: &str) -> bool {
    if !prefix.starts_with('/') || prefix.ends_with('/') || prefix.len() < 2 || prefix.len() > 192 {
        return false;
    }
    let filter_str = format!("{prefix}/>");
    Filter::new(&filter_str).is_ok()
}

impl PeerAnnouncement {
    /// Canonical `Last` subject `/f/<fleet>/pub/<region>/peer/announce` for a fleet and region.
    pub fn subject_for(fleet: &str, region: &str) -> Result<Subject, String> {
        if !valid_region_token(fleet) || !valid_region_token(region) {
            return Err("fleet and region must be non-empty [A-Za-z0-9_-] tokens".to_string());
        }
        let s = format!("/f/{fleet}/pub/{region}/peer/announce");
        match Subject::new(&s) {
            Ok(sub) => Ok(sub),
            Err(e) => Err(e.to_string()),
        }
    }

    /// Wildcard [`Filter`] `/f/<fleet>/pub/*/peer/announce` matching every peer announcement in `fleet`.
    pub fn fleet_filter(fleet: &str) -> Result<Filter, String> {
        if !valid_region_token(fleet) {
            return Err("fleet must be a non-empty [A-Za-z0-9_-] token".to_string());
        }
        let f = format!("/f/{fleet}/pub/*/peer/announce");
        match Filter::new(&f) {
            Ok(flt) => Ok(flt),
            Err(e) => Err(e.to_string()),
        }
    }

    /// Encode this announcement as a single-line `v=1` key-value payload.
    pub fn encode(&self) -> Result<String, String> {
        if !valid_region_token(&self.region) || !valid_region_token(&self.origin_region) {
            return Err("invalid region or origin_region token".to_string());
        }
        let mut ep_rest = self.endpoint.as_bytes();
        let mut has_ws = false;
        while let &[eb, ref etail @ ..] = ep_rest {
            if eb.is_ascii_whitespace() {
                has_ws = true;
                break;
            }
            ep_rest = etail;
        }
        if self.endpoint.is_empty() || self.endpoint.len() > 256 || has_ws {
            return Err("invalid endpoint in PeerAnnouncement".to_string());
        }
        if self.prefixes.is_empty() || self.prefixes.len() > MAX_EXPORT_PREFIXES {
            return Err("prefixes must contain 1..=MAX_EXPORT_PREFIXES entries".to_string());
        }
        let mut joined = String::new();
        let mut idx = 0usize;
        while let Some(p) = self.prefixes.get(idx) {
            if !valid_export_prefix(p) || p.contains(',') {
                return Err(format!("invalid export prefix {p:?}"));
            }
            if idx > 0 {
                joined.push(',');
            }
            joined.push_str(p);
            idx = idx.saturating_add(1);
        }
        Ok(format!(
            "v=1 region={} origin={} endpoint={} epoch={} hop={} prefixes={}",
            self.region, self.origin_region, self.endpoint, self.epoch, self.hop, joined
        ))
    }

    /// Decode a `v=1` [`PeerAnnouncement`] line, ignoring trailing `\n` and unknown keys.
    pub fn decode(raw: &[u8]) -> Result<Self, String> {
        let mut nl = raw.len();
        let mut ni = 0usize;
        while let Some(&rb) = raw.get(ni) {
            if rb == b'\n' {
                nl = ni;
                break;
            }
            ni = ni.saturating_add(1);
        }
        let line_bytes = match raw.get(..nl) {
            Some(s) => s,
            None => raw,
        };
        if line_bytes.len() > 8192 {
            return Err("PeerAnnouncement line exceeds 8 KiB".to_string());
        }
        let Ok(line) = core::str::from_utf8(line_bytes) else {
            return Err("PeerAnnouncement is not valid UTF-8".to_string());
        };
        let mut saw_v1 = false;
        let mut region: Option<String> = None;
        let mut origin: Option<String> = None;
        let mut endpoint: Option<String> = None;
        let mut epoch: Option<u64> = None;
        let mut hop: Option<u8> = None;
        let mut prefixes: Vec<String> = Vec::new();

        for tok in line.split_ascii_whitespace() {
            let Some((k, v)) = tok.split_once('=') else {
                return Err(format!("malformed token {tok:?}"));
            };
            if k == "v" {
                if v != "1" {
                    return Err(format!("unsupported PeerAnnouncement version {v:?}"));
                }
                saw_v1 = true;
            } else if k == "region" {
                if !valid_region_token(v) {
                    return Err(format!("invalid region {v:?}"));
                }
                region = Some(v.to_string());
            } else if k == "origin" {
                if !valid_region_token(v) {
                    return Err(format!("invalid origin {v:?}"));
                }
                origin = Some(v.to_string());
            } else if k == "endpoint" {
                if v.is_empty() || v.len() > 256 {
                    return Err("invalid endpoint".to_string());
                }
                endpoint = Some(v.to_string());
            } else if k == "epoch" {
                let Ok(ep) = v.parse::<u64>() else {
                    return Err(format!("invalid epoch {v:?}"));
                };
                epoch = Some(ep);
            } else if k == "hop" {
                let Ok(h) = v.parse::<u8>() else {
                    return Err(format!("invalid hop {v:?}"));
                };
                hop = Some(h);
            } else if k == "prefixes" {
                prefixes.clear();
                for item in v.split(',') {
                    if prefixes.len() >= MAX_EXPORT_PREFIXES || !valid_export_prefix(item) {
                        return Err(format!("invalid or excessive prefix {item:?}"));
                    }
                    prefixes.push(item.to_string());
                }
            }
        }

        if !saw_v1 {
            return Err("missing v=1 in PeerAnnouncement".to_string());
        }
        let Some(reg) = region else {
            return Err("missing region= in PeerAnnouncement".to_string());
        };
        let orig = match origin {
            Some(o) => o,
            None => reg.clone(),
        };
        let Some(ep_str) = endpoint else {
            return Err("missing endpoint= in PeerAnnouncement".to_string());
        };
        let Some(ep_num) = epoch else {
            return Err("missing epoch= in PeerAnnouncement".to_string());
        };
        let hop_val = hop.unwrap_or(0);
        if prefixes.is_empty() {
            return Err("missing prefixes= in PeerAnnouncement".to_string());
        }

        Ok(Self {
            region: reg,
            origin_region: orig,
            endpoint: ep_str,
            epoch: ep_num,
            hop: hop_val,
            prefixes,
        })
    }
}

/// Selected loop-free route to a remote `origin_region` via a direct or transit `via_region`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MeshRoute {
    /// Origin region that owns `prefixes`.
    pub origin_region: String,
    /// Next-hop peer region from which this node pulls `prefixes`.
    pub via_region: String,
    /// Next-hop peer broker endpoint.
    pub via_endpoint: String,
    /// Monotone epoch of the winning announcement from `via_region`.
    pub epoch: u64,
    /// Clamped outbound hop index (`1..=max_hops`).
    pub next_hop: u8,
    /// Exported subject prefixes for `origin_region`.
    pub prefixes: Vec<String>,
}

/// Outcome of ingesting a [`PeerAnnouncement`] into [`FederationMeshTable`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MeshIngestOutcome {
    /// Route inserted or upgraded.
    Accepted,
    /// Dropped by split-horizon (`origin_region == local_region` or `region == local_region`).
    RejectedSplitHorizon,
    /// Dropped because `announcement.hop >= max_hops`.
    RejectedHopLimit,
    /// Ignored because a newer or equal epoch (or strictly shorter hop at same epoch) already exists.
    IgnoredStale,
    /// Table is at [`MAX_MESH_PEERS`].
    TableFull,
}

/// Loop-free multi-region routing table synthesizing [`FederationRule`] sets from dynamic
/// [`PeerAnnouncement`] discovery records.
#[derive(Clone, Debug)]
pub struct FederationMeshTable {
    local_region: String,
    max_hops: u8,
    /// Keyed by `origin_region`.
    routes: BTreeMap<String, MeshRoute>,
}

impl FederationMeshTable {
    /// Construct a routing table for `local_region` enforcing `max_hops` (`1..=16`).
    pub fn new(local_region: &str, max_hops: u8) -> Result<Self, String> {
        if !valid_region_token(local_region) {
            return Err(format!("invalid local_region {local_region:?}"));
        }
        let clamped_max = max_hops.clamp(1, 16);
        Ok(Self {
            local_region: local_region.to_string(),
            max_hops: clamped_max,
            routes: BTreeMap::new(),
        })
    }

    /// Local region identifier.
    #[must_use]
    pub fn local_region(&self) -> &str {
        &self.local_region
    }

    /// Maximum allowed hop count (`1..=16`).
    #[must_use]
    pub const fn max_hops(&self) -> u8 {
        self.max_hops
    }

    /// Active routes keyed by `origin_region`.
    #[must_use]
    pub fn routes(&self) -> &BTreeMap<String, MeshRoute> {
        &self.routes
    }

    /// Ingest one [`PeerAnnouncement`], applying Clean-verified split-horizon, hop-TTL, and
    /// monotone-epoch checks (`Astream.Broker.TlaFederationMesh`).
    pub fn ingest(&mut self, ann: &PeerAnnouncement) -> MeshIngestOutcome {
        let not_self: u64 =
            if ann.origin_region != self.local_region && ann.region != self.local_region {
                1
            } else {
                0
            };
        let adm =
            mesh_route_admissible_code(not_self, u64::from(ann.hop), u64::from(self.max_hops));
        if !mesh_code_is_admissible(adm) {
            if not_self == 0 {
                return MeshIngestOutcome::RejectedSplitHorizon;
            }
            return MeshIngestOutcome::RejectedHopLimit;
        }

        let next_hop_u64 = mesh_hop_clamp(
            u64::from(ann.hop).saturating_add(1),
            u64::from(self.max_hops),
        );
        let next_hop = next_hop_u64 as u8;

        if let Some(cur) = self.routes.get(&ann.origin_region) {
            let adv = mesh_epoch_advance(cur.epoch, ann.epoch);
            if ann.epoch < cur.epoch {
                return MeshIngestOutcome::IgnoredStale;
            }
            if ann.epoch == cur.epoch && adv == cur.epoch {
                if cur.via_region == ann.region {
                    return MeshIngestOutcome::IgnoredStale;
                }
                // Equal origin epoch across distinct neighbors: prefer strictly shorter hop count,
                // then deterministic lexical via_region tie-breaker.
                let shorter = next_hop < cur.next_hop;
                let tie_winner = next_hop == cur.next_hop && ann.region < cur.via_region;
                if !shorter && !tie_winner {
                    return MeshIngestOutcome::IgnoredStale;
                }
            }
        } else if self.routes.len() >= MAX_MESH_PEERS {
            return MeshIngestOutcome::TableFull;
        }

        self.routes.insert(
            ann.origin_region.clone(),
            MeshRoute {
                origin_region: ann.origin_region.clone(),
                via_region: ann.region.clone(),
                via_endpoint: ann.endpoint.clone(),
                epoch: ann.epoch,
                next_hop,
                prefixes: ann.prefixes.clone(),
            },
        );
        MeshIngestOutcome::Accepted
    }

    /// Generate re-advertisements for transit forwarding (incremented hop count, preserving
    /// `origin_region`, with `region = self.local_region`) for routes still strictly below
    /// `max_hops`.
    #[must_use]
    pub fn transit_announcements(&self, local_endpoint: &str) -> Vec<PeerAnnouncement> {
        let cap = if self.routes.len() < MAX_MESH_PEERS {
            self.routes.len()
        } else {
            MAX_MESH_PEERS
        };
        let mut out = {
            let _ = cap;
            Vec::new()
        };
        for route in self.routes.values() {
            if route.next_hop < self.max_hops {
                out.push(PeerAnnouncement {
                    region: self.local_region.clone(),
                    origin_region: route.origin_region.clone(),
                    endpoint: local_endpoint.to_string(),
                    epoch: route.epoch,
                    hop: route.next_hop,
                    prefixes: route.prefixes.clone(),
                });
            }
        }
        out
    }

    /// Synthesize loop-free [`FederationRule`] sets grouped by `via_endpoint` so a local node
    /// pulls every reachable remote `origin_region` from its chosen next-hop peer while
    /// excluding local-origin prefixes (`local_exclude_prefixes`).
    pub fn build_rules_by_peer(
        &self,
        local_exclude_prefixes: &[String],
    ) -> Result<BTreeMap<String, Vec<FederationRule>>, String> {
        let mut by_peer: BTreeMap<String, Vec<FederationRule>> = BTreeMap::new();
        for route in self.routes.values() {
            let entry = by_peer.entry(route.via_endpoint.clone()).or_default();
            let mut p_idx = 0usize;
            while let Some(prefix) = route.prefixes.get(p_idx) {
                if entry.len() >= MAX_FEDERATION_RULES {
                    break;
                }
                let group = format!(
                    "/federation/mesh/{}/{}/{}",
                    self.local_region, route.origin_region, p_idx
                );
                if Subject::new(&group).is_err() {
                    return Err(format!("synthesized invalid mesh group subject {group:?}"));
                }
                let filter = format!("{prefix}/>");
                if Filter::new(&filter).is_err() {
                    return Err(format!("synthesized invalid mesh filter {filter:?}"));
                }
                let hop_idx = route.next_hop.saturating_sub(1);
                let mut rw = SubjectRewrite::passthrough().with_hop_budget(hop_idx, self.max_hops);
                let mut ex_idx = 0usize;
                while let Some(ex) = local_exclude_prefixes.get(ex_idx) {
                    rw = rw.with_excluded_prefix(ex)?;
                    ex_idx = ex_idx.saturating_add(1);
                }
                entry.push(FederationRule {
                    group,
                    filter,
                    rewrite: rw,
                    producer_id: None,
                    batch_size: DEFAULT_FEDERATION_BATCH,
                });
                p_idx = p_idx.saturating_add(1);
            }
        }
        Ok(by_peer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn peer_announcement_roundtrips_and_mesh_prevents_cycles_and_stale_epochs() {
        let ann_west = PeerAnnouncement {
            region: "us-west".to_string(),
            origin_region: "us-west".to_string(),
            endpoint: "10.0.1.10:9100".to_string(),
            epoch: 5,
            hop: 0,
            prefixes: vec!["/f/prod/pub/west".to_string()],
        };
        let encoded = ann_west.encode().expect("encode");
        let decoded = PeerAnnouncement::decode(encoded.as_bytes()).expect("decode");
        assert_eq!(decoded, ann_west);

        let mut hub = FederationMeshTable::new("us-central", 2).expect("hub");
        assert_eq!(hub.ingest(&decoded), MeshIngestOutcome::Accepted);
        // Stale or equal epoch from same via_region is ignored.
        let mut stale = decoded.clone();
        stale.epoch = 4;
        assert_eq!(hub.ingest(&stale), MeshIngestOutcome::IgnoredStale);

        // Hub emits transit announcement (`hop = 1 < max_hops = 2`) for us-east.
        let transit = hub.transit_announcements("10.0.2.10:9100");
        assert_eq!(transit.len(), 1);
        assert_eq!(transit[0].region, "us-central");
        assert_eq!(transit[0].origin_region, "us-west");
        assert_eq!(transit[0].hop, 1);

        // Self-origin echo back at us-west is rejected by split-horizon!
        let mut west_tbl = FederationMeshTable::new("us-west", 2).expect("west");
        assert_eq!(
            west_tbl.ingest(&transit[0]),
            MeshIngestOutcome::RejectedSplitHorizon
        );

        // us-east accepts the 2-hop transit route (`hop = 1 -> next_hop = 2 == max_hops`),
        // and does NOT re-advertise past `max_hops = 2`!
        let mut east_tbl = FederationMeshTable::new("us-east", 2).expect("east");
        assert_eq!(east_tbl.ingest(&transit[0]), MeshIngestOutcome::Accepted);
        assert!(east_tbl.transit_announcements("10.0.3.10:9100").is_empty());

        let rules = east_tbl
            .build_rules_by_peer(&["/f/prod/pub/east".to_string()])
            .expect("build rules");
        let peer_rules = rules.get("10.0.2.10:9100").expect("hub peer");
        assert_eq!(peer_rules.len(), 1);
        assert_eq!(peer_rules[0].filter, "/f/prod/pub/west/>");
        assert_eq!(peer_rules[0].rewrite.hops, 1);
        assert_eq!(peer_rules[0].rewrite.max_hops, 2);
    }

    #[test]
    fn newer_origin_epoch_supersedes_shorter_stale_route_and_tie_breaks_deterministically() {
        let mut tbl = FederationMeshTable::new("eu-north", 3).expect("tbl");
        let direct_old = PeerAnnouncement {
            region: "us-east".to_string(),
            origin_region: "us-west".to_string(),
            endpoint: "10.0.1.1:9100".to_string(),
            epoch: 2,
            hop: 0,
            prefixes: vec!["/f/old/pub/west".to_string()],
        };
        assert_eq!(tbl.ingest(&direct_old), MeshIngestOutcome::Accepted);

        // Newer origin epoch (epoch = 3) arriving over a 2-hop transit route must supersede
        // the stale 1-hop route so updated origin prefixes propagate mesh-wide.
        let transit_new = PeerAnnouncement {
            region: "eu-west".to_string(),
            origin_region: "us-west".to_string(),
            endpoint: "10.0.2.1:9100".to_string(),
            epoch: 3,
            hop: 1,
            prefixes: vec!["/f/new/pub/west".to_string()],
        };
        assert_eq!(tbl.ingest(&transit_new), MeshIngestOutcome::Accepted);
        assert_eq!(tbl.routes()["us-west"].epoch, 3);
        assert_eq!(
            tbl.routes()["us-west"].prefixes,
            vec!["/f/new/pub/west".to_string()]
        );

        // Equal epoch + equal hop tie-breaks deterministically on lexicographically smaller via_region.
        let tie_smaller = PeerAnnouncement {
            region: "ap-south".to_string(),
            origin_region: "us-west".to_string(),
            endpoint: "10.0.3.1:9100".to_string(),
            epoch: 3,
            hop: 1,
            prefixes: vec!["/f/new/pub/west".to_string()],
        };
        assert_eq!(tbl.ingest(&tie_smaller), MeshIngestOutcome::Accepted);
        assert_eq!(tbl.routes()["us-west"].via_region, "ap-south");

        let tie_larger = PeerAnnouncement {
            region: "sa-east".to_string(),
            origin_region: "us-west".to_string(),
            endpoint: "10.0.4.1:9100".to_string(),
            epoch: 3,
            hop: 1,
            prefixes: vec!["/f/new/pub/west".to_string()],
        };
        assert_eq!(tbl.ingest(&tie_larger), MeshIngestOutcome::IgnoredStale);
    }
}
