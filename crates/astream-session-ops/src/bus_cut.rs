// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Chandy-Lamport causal `Cut` & `is_consistent` lattice directly over broker bus records
//! (`docs/DESIGN-aterm-fabric.md` §10).
//!
//! `astream-engine::fleet` computes consistent cuts over `astream-host` session envelope
//! logs, which previously forced `aterm-link` to re-derive `Cut` / `is_consistent` over
//! raw bus records. [`BusCausalTracker`] bridges that boundary cleanly: any fabric
//! consumer (`aterm-link`, `FederationRunner`, multi-agent orchestrators) feeds stamped
//! broker records `(stream_id, offset, optional_cause)` directly into [`BusCausalTracker`]
//! and obtains verified Chandy-Lamport consistent cuts (`CausalCut<String>`) and minimal
//! causal closures (`close_cut`) without wrapping payloads in PTY session envelopes.

use astream_wire::{CausalCut, CausalEdge, CutViolation, Offset};
use std::collections::BTreeMap;

#[cfg(clean_islands)]
#[path = "bus_cut_island.rs"]
mod bus_cut_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn bus_cut_frontier_advance(cur_off: u64, proposed_off: u64) -> u64 {
    if cur_off < proposed_off {
        proposed_off
    } else {
        cur_off
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn bus_cut_edges_clamp(edge_count: u64, max_edges: u64) -> u64 {
    if edge_count < max_edges {
        edge_count
    } else {
        max_edges
    }
}
#[cfg(clean_islands)]
pub use bus_cut_island::{bus_cut_edges_clamp, bus_cut_frontier_advance};

contract_fn! {
    /// Contracted check that record offset `off` is admitted by partition cut `cut_off`.
    #[must_use]
    pub const fn bus_cut_admits(off: u64, cut_off: u64) -> bool
    clauses [ensures result == (off <= cut_off)]
    {
        off <= cut_off
    }
}

/// Maximum cross-stream causal edges retained in a single [`BusCausalTracker`].
pub const MAX_BUS_CAUSAL_EDGES: usize = 16_384;

/// Canonical causal metadata extracted from or attached to a broker bus record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BusCausalRecord {
    /// Stream / topic / broker partition identifier (e.g. `"/f/prod/s/tab-1"`).
    pub stream: String,
    /// Assigned broker offset on `stream`.
    pub offset: Offset,
    /// Optional causal parent `(cause_stream, cause_offset)` that triggered this record.
    pub caused_by: Option<(String, Offset)>,
}

fn str_to_owned_string(s: &str) -> String {
    let mut out = String::new();
    out.push_str(s);
    out
}

fn push_u64_dec_str(out: &mut String, mut n: u64) {
    if n == 0 {
        out.push('0');
        return;
    }
    let mut digits = [0u8; 20];
    let mut len = 0usize;
    while n > 0 {
        if let Some(slot) = digits.get_mut(len) {
            *slot = b'0'.saturating_add((n % 10) as u8);
            len = len.saturating_add(1);
        }
        n /= 10;
    }
    while len > 0 {
        len = len.saturating_sub(1);
        if let Some(&d) = digits.get(len) {
            out.push(d as char);
        }
    }
}

const fn parse_u64_dec(s: &str) -> Option<u64> {
    let bytes = s.as_bytes();
    if bytes.is_empty() {
        return None;
    }
    let mut acc = 0u64;
    let mut rest = bytes;
    while let &[b, ref tail @ ..] = rest {
        if !b.is_ascii_digit() {
            return None;
        }
        let Some(mul) = acc.checked_mul(10) else {
            return None;
        };
        let Some(next) = mul.checked_add(b.saturating_sub(b'0') as u64) else {
            return None;
        };
        acc = next;
        rest = tail;
    }
    Some(acc)
}

/// Encode an inline 2-line ASCII causal header (`c=<stream>@<offset>\n`) prepended or
/// carried as metadata when bridging causal edges over plain bus subjects.
pub fn encode_bus_cause_tag(cause_stream: &str, cause_offset: Offset) -> String {
    let mut out = String::new();
    out.push_str("c=");
    out.push_str(cause_stream);
    out.push('@');
    push_u64_dec_str(&mut out, cause_offset.0);
    out.push('\n');
    out
}

/// Decode `c=<stream>@<offset>\n` produced by [`encode_bus_cause_tag`].
pub fn decode_bus_cause_tag(tag: &str) -> Option<(String, Offset)> {
    let trimmed = match tag.strip_suffix('\n') {
        Some(t) => t,
        None => tag,
    };
    let rest = trimmed.strip_prefix("c=")?;
    let (stream, off_str) = rest.rsplit_once('@')?;
    if stream.is_empty() || stream.contains('\n') || stream.contains('\r') {
        return None;
    }
    let off = parse_u64_dec(off_str)?;
    Some((str_to_owned_string(stream), Offset(off)))
}

/// Multi-stream causal tracker and Chandy-Lamport consistent-cut verifier over bus records.
#[derive(Debug, Clone, Default)]
pub struct BusCausalTracker {
    frontiers: BTreeMap<String, Offset>,
    edges: Vec<CausalEdge<String>>,
}

impl BusCausalTracker {
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of cross-stream causal edges currently tracked (`<= MAX_BUS_CAUSAL_EDGES`).
    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }

    /// Highest observed offset on `stream`, if any record has been ingested for it.
    pub fn stream_frontier(&self, stream: &str) -> Option<Offset> {
        self.frontiers.get(stream).copied()
    }

    /// Ingest a stamped bus record, advancing `stream`'s frontier monotonically via
    /// [`bus_cut_frontier_advance`] and recording any cross-stream causal edge up to
    /// [`MAX_BUS_CAUSAL_EDGES`].
    pub fn observe(&mut self, rec: BusCausalRecord) {
        let next_off = match self.frontiers.get(&rec.stream) {
            Some(cur) => Offset(bus_cut_frontier_advance(cur.0, rec.offset.0)),
            None => rec.offset,
        };
        self.frontiers.insert(rec.stream.clone(), next_off);

        if let Some((cause_stream, cause_off)) = rec.caused_by {
            if cause_stream != rec.stream {
                let allowed = bus_cut_edges_clamp(
                    self.edges.len().saturating_add(1) as u64,
                    MAX_BUS_CAUSAL_EDGES as u64,
                ) as usize;
                if self.edges.len() < allowed {
                    self.edges.push(CausalEdge {
                        cause: (cause_stream, cause_off),
                        effect: (rec.stream, rec.offset),
                    });
                }
            }
        }
    }

    /// Snapshot the current latest frontier across all observed streams (always a
    /// consistent cut provided every referenced cause has been observed).
    pub fn latest_cut(&self) -> CausalCut<String> {
        let mut cut = CausalCut::new();
        for (k, v) in &self.frontiers {
            cut.set(k.clone(), *v);
        }
        cut
    }

    /// Verify Chandy-Lamport consistency of `cut` against all observed cross-stream edges:
    /// if `cut` admits `effect`, it must also admit `cause`.
    #[allow(clippy::manual_unwrap_or_default)]
    pub fn check_consistent(&self, cut: &CausalCut<String>) -> Result<(), CutViolation<String>> {
        for edge in &self.edges {
            let effect_in = match cut.offset_of(&edge.effect.0) {
                Some(c) => bus_cut_admits(edge.effect.1 .0, c.0),
                None => false,
            };
            if effect_in {
                let cause_in = match cut.offset_of(&edge.cause.0) {
                    Some(c) => bus_cut_admits(edge.cause.1 .0, c.0),
                    None => false,
                };
                if !cause_in {
                    return Err(CutViolation {
                        edge: edge.clone(),
                        cause_frontier: cut.offset_of(&edge.cause.0),
                        effect_frontier: match cut.offset_of(&edge.effect.0) {
                            Some(o) => o,
                            None => Offset(0),
                        },
                    });
                }
            }
        }
        Ok(())
    }

    /// Advance `proposed` minimally (via join with missing causes) until it forms a
    /// Chandy-Lamport consistent cut across all recorded bus edges.
    pub fn close_to_consistent(&self, proposed: &CausalCut<String>) -> CausalCut<String> {
        let mut cut = proposed.clone();
        loop {
            let mut changed = false;
            for edge in &self.edges {
                let effect_in = match cut.offset_of(&edge.effect.0) {
                    Some(o) => bus_cut_admits(edge.effect.1 .0, o.0),
                    None => false,
                };
                if effect_in {
                    match cut.offset_of(&edge.cause.0) {
                        Some(o) => {
                            if !bus_cut_admits(edge.cause.1 .0, o.0) {
                                let next = Offset(bus_cut_frontier_advance(o.0, edge.cause.1 .0));
                                cut.set(edge.cause.0.clone(), next);
                                changed = true;
                            }
                        }
                        None => {
                            cut.set(edge.cause.0.clone(), edge.cause.1);
                            changed = true;
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }
        cut
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bus_causal_tracker_rejects_orphan_effects_and_closes_cuts_transitively() {
        let mut tracker = BusCausalTracker::new();
        tracker.observe(BusCausalRecord {
            stream: "/f/prod/s/leader".into(),
            offset: Offset(10),
            caused_by: None,
        });
        tracker.observe(BusCausalRecord {
            stream: "/f/prod/s/worker-a".into(),
            offset: Offset(4),
            caused_by: Some(("/f/prod/s/leader".into(), Offset(10))),
        });
        tracker.observe(BusCausalRecord {
            stream: "/f/prod/s/worker-b".into(),
            offset: Offset(2),
            caused_by: Some(("/f/prod/s/worker-a".into(), Offset(4))),
        });

        let inconsistent = CausalCut::from_first_wins([
            ("/f/prod/s/leader".to_string(), Offset(9)),
            ("/f/prod/s/worker-b".to_string(), Offset(2)),
        ]);
        assert!(tracker.check_consistent(&inconsistent).is_err());

        let repaired = tracker.close_to_consistent(&inconsistent);
        assert!(tracker.check_consistent(&repaired).is_ok());
        assert_eq!(
            repaired.offset_of(&"/f/prod/s/worker-a".to_string()),
            Some(Offset(4))
        );
        assert_eq!(
            repaired.offset_of(&"/f/prod/s/leader".to_string()),
            Some(Offset(10))
        );

        let tag = encode_bus_cause_tag("/f/prod/s/leader", Offset(10));
        assert_eq!(
            decode_bus_cause_tag(&tag),
            Some(("/f/prod/s/leader".to_string(), Offset(10)))
        );
    }
}
