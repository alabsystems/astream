// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Multi-hop federation path-vector loop detector and hop-TTL clamp (`ROADMAP.md` line 124,
//! `Astream.Mesh.TlaSplitHorizon`).
//!
//! Prevents infinite echo storms across arbitrary cyclic multi-region federation topologies
//! (`A <-> B <-> C <-> A`) by carrying a compact path-vector header (`v=1 seq=<u64> hops=<n1,n2,...>`):
//! - Rejects any federated envelope whose `hops` already contains `local_broker_id` (split-horizon
//!   path-vector loop detection).
//! - Rejects any envelope whose hop count has reached `max_hops` (`horizon_hops_clamp`).
//! - Deduplicates per-origin sequence watermarks monotonically (`horizon_seq_advance`).

use std::collections::BTreeMap;

#[cfg(clean_islands)]
#[path = "split_horizon_island.rs"]
mod split_horizon_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn horizon_hops_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn horizon_seq_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use split_horizon_island::{horizon_hops_clamp, horizon_seq_advance};

/// Hard ceiling on federation forwarding hops across regions.
pub const MAX_FEDERATION_HOPS: u64 = 16;
/// Maximum tracked origin brokers in one split-horizon watermark map.
pub const MAX_TRACKED_ORIGINS: usize = 1024;

fn clone_str(s: &str) -> String {
    let mut out = String::new();
    out.push_str(s);
    out
}

fn push_u64_dec(out: &mut String, mut val: u64) {
    if val == 0 {
        out.push('0');
        return;
    }
    let mut digits = [0u8; 20];
    let mut len = 0usize;
    while val > 0 && len < digits.len() {
        let rem = (val % 10) as u8;
        if let Some(slot) = digits.get_mut(len) {
            *slot = b'0'.saturating_add(rem);
        }
        len = len.saturating_add(1);
        val /= 10;
    }
    while len > 0 {
        len = len.saturating_sub(1);
        if let Some(&b) = digits.get(len) {
            out.push(b as char);
        }
    }
}

#[allow(clippy::question_mark)]
fn parse_u64_dec(s: &str) -> Option<u64> {
    if s.is_empty() {
        return None;
    }
    let mut acc = 0u64;
    for &b in s.as_bytes() {
        if !b.is_ascii_digit() {
            return None;
        }
        acc = match acc.checked_mul(10) {
            Some(v) => v,
            None => return None,
        };
        acc = match acc.checked_add(b.saturating_sub(b'0') as u64) {
            Some(v) => v,
            None => return None,
        };
    }
    Some(acc)
}

contract_fn! {
    /// Verified TTL room check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `horizon_loop_free_isl`.
    #[must_use]
    pub const fn horizon_loop_free(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Parsed federation path-vector header.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PathVectorHeader {
    pub origin_seq: u64,
    pub hops: Vec<String>,
}

impl PathVectorHeader {
    #[must_use]
    pub fn encode(&self) -> String {
        let mut out = String::new();
        out.push_str("v=1 seq=");
        push_u64_dec(&mut out, self.origin_seq);
        out.push_str(" hops=");
        let mut first = true;
        for h in &self.hops {
            if !first {
                out.push(',');
            }
            first = false;
            out.push_str(h);
        }
        out
    }

    pub fn decode(line: &str) -> Result<Self, &'static str> {
        let mut ver = false;
        let mut seq = None;
        let mut hops = None;
        for tok in line.trim().split_ascii_whitespace() {
            let (k, v) = match tok.split_once('=') {
                Some(pair) => pair,
                None => return Err("bad path-vector token"),
            };
            match k {
                "v" => {
                    if ver || v != "1" {
                        return Err("bad v=");
                    }
                    ver = true;
                }
                "seq" => {
                    if seq.is_some() {
                        return Err("duplicate seq=");
                    }
                    let parsed = match parse_u64_dec(v) {
                        Some(n) => n,
                        None => return Err("bad seq="),
                    };
                    seq = Some(parsed);
                }
                "hops" => {
                    if hops.is_some() {
                        return Err("duplicate hops=");
                    }
                    let mut list: Vec<String> = Vec::new();
                    for seg in v.split(',') {
                        if seg.is_empty() {
                            return Err("empty hop segment");
                        }
                        if (list.len() as u64) >= MAX_FEDERATION_HOPS {
                            return Err("too many hops in header");
                        }
                        for existing in &list {
                            if existing == seg {
                                return Err("duplicate hop in path vector");
                            }
                        }
                        list.push(clone_str(seg));
                    }
                    if list.is_empty() {
                        return Err("empty hops vector");
                    }
                    hops = Some(list);
                }
                _ => {}
            }
        }
        if !ver {
            return Err("missing v=1");
        }
        let origin_seq = match seq {
            Some(s) => s,
            None => return Err("missing seq="),
        };
        let hops_vec = match hops {
            Some(h) => h,
            None => return Err("missing hops="),
        };
        Ok(Self {
            origin_seq,
            hops: hops_vec,
        })
    }
}

/// Decision for a federated message entering `local_broker_id`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HopVerdict {
    Forward(PathVectorHeader),
    DropLoopDetected,
    DropHopLimitExceeded,
    DropDuplicateOriginSeq,
}

/// Stateful path-vector loop and duplicate guard at one broker node.
#[derive(Debug, Clone)]
pub struct SplitHorizonGuard {
    local_broker_id: String,
    max_hops: u64,
    origin_watermarks: BTreeMap<String, u64>,
}

impl SplitHorizonGuard {
    #[must_use]
    pub fn new(local_broker_id: &str, max_hops: u64) -> Self {
        let cap = horizon_hops_clamp(max_hops, MAX_FEDERATION_HOPS);
        Self {
            local_broker_id: clone_str(local_broker_id),
            max_hops: if cap == 0 { 1 } else { cap },
            origin_watermarks: BTreeMap::new(),
        }
    }

    /// Evaluates an inbound `PathVectorHeader` and appends `local_broker_id` if forwarding is safe.
    pub fn admit_and_stamp(&mut self, hdr: &PathVectorHeader) -> HopVerdict {
        if self.local_broker_id.is_empty() {
            return HopVerdict::DropLoopDetected;
        }
        for h in &hdr.hops {
            if h.is_empty() || h == &self.local_broker_id {
                return HopVerdict::DropLoopDetected;
            }
        }
        let next_len = (hdr.hops.len() as u64).saturating_add(1);
        if !horizon_loop_free(self.max_hops, next_len) {
            return HopVerdict::DropHopLimitExceeded;
        }
        let Some(origin) = hdr.hops.first() else {
            return HopVerdict::DropLoopDetected;
        };
        if let Some(&seen) = self.origin_watermarks.get(origin) {
            if hdr.origin_seq <= seen {
                return HopVerdict::DropDuplicateOriginSeq;
            }
            self.origin_watermarks
                .insert(origin.clone(), horizon_seq_advance(seen, hdr.origin_seq));
        } else {
            if self.origin_watermarks.len() >= MAX_TRACKED_ORIGINS {
                return HopVerdict::DropHopLimitExceeded;
            }
            self.origin_watermarks
                .insert(origin.clone(), hdr.origin_seq);
        }
        let mut next_hops = hdr.hops.clone();
        next_hops.push(self.local_broker_id.clone());
        HopVerdict::Forward(PathVectorHeader {
            origin_seq: hdr.origin_seq,
            hops: next_hops,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn triangle_mesh_terminates_echo_loops_and_enforces_hop_ttl_and_origin_dedup() {
        let mut b = SplitHorizonGuard::new("broker-B", 4);
        let mut c = SplitHorizonGuard::new("broker-C", 4);
        let mut a = SplitHorizonGuard::new("broker-A", 4);

        let h0 = PathVectorHeader {
            origin_seq: 1,
            hops: vec!["broker-A".to_owned()],
        };
        let HopVerdict::Forward(h1) = b.admit_and_stamp(&h0) else {
            panic!("expected forward B")
        };
        let HopVerdict::Forward(h2) = c.admit_and_stamp(&h1) else {
            panic!("expected forward C")
        };
        let wire = h2.encode();
        let decoded = PathVectorHeader::decode(&wire).unwrap();
        // Returning to broker-A is caught immediately as a cycle!
        assert_eq!(a.admit_and_stamp(&decoded), HopVerdict::DropLoopDetected);
        // Replaying seq=1 into broker-B is caught by monotone origin watermark!
        assert_eq!(b.admit_and_stamp(&h0), HopVerdict::DropDuplicateOriginSeq);
    }
}
