// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `EVENT turn ... by=<driver_digest>` causal driver provenance codec and handoff ledger
//! (`DESIGN-aterm-fabric.md` §15 line 4059, `Astream.Presence.TlaTurnProvenance`).
//!
//! Computes domain-separated SHA-256 provenance digests (`ASTREAM-DRIVER-V1\0`) over
//! `(driver_kind, principal, cause_offset)`, formats and parses canonical `EVENT turn` lines,
//! verifies provenance digests in constant time via [`astream_digest::ct_eq`], and bounds
//! retained driver history via Clean-origin `prov_chain_clamp` while advancing turn numbers
//! monotonically via `prov_turn_advance`.

use std::collections::VecDeque;

use astream_digest::{ct_eq, Sha256};

#[cfg(clean_islands)]
#[path = "turn_provenance_island.rs"]
mod turn_provenance_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn prov_chain_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn prov_turn_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use turn_provenance_island::{prov_chain_clamp, prov_turn_advance};

/// Maximum driver provenance records kept in a bounded session ring.
pub const MAX_PROVENANCE_DRIVERS: u64 = 64;

contract_fn! {
    /// Verified turn-order predicate (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `prov_digest_matches_isl`.
    #[must_use]
    pub const fn prov_digest_matches(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Origin class of whoever drove an agent or terminal turn.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DriverKind {
    Human,
    Autopilot,
    PeerMail,
    Bridge,
}

impl DriverKind {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Human => "human",
            Self::Autopilot => "autopilot",
            Self::PeerMail => "peer",
            Self::Bridge => "bridge",
        }
    }

    pub fn parse(s: &str) -> Result<Self, &'static str> {
        match s {
            "human" => Ok(Self::Human),
            "autopilot" => Ok(Self::Autopilot),
            "peer" => Ok(Self::PeerMail),
            "bridge" => Ok(Self::Bridge),
            _ => Err("unknown driver kind"),
        }
    }
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

/// Computes the 32-byte `by=` provenance digest for `(kind, principal, cause_offset)`.
#[must_use]
pub fn compute_driver_digest(kind: DriverKind, principal: &str, cause_offset: u64) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update_slice(b"ASTREAM-DRIVER-V1\0");
    h.update_slice(kind.as_str().as_bytes());
    h.update_slice(b"\0");
    h.update_slice(&(principal.len() as u64).to_le_bytes());
    h.update_slice(principal.as_bytes());
    h.update_slice(b"\0");
    h.update_slice(&cause_offset.to_le_bytes());
    h.finalize()
}

fn hex_encode_32(d: &[u8; 32]) -> String {
    let lut = b"0123456789abcdef";
    let mut out = String::new();
    for &b in d {
        let hi = match lut.get(((b >> 4) & 0x0F) as usize) {
            Some(&c) => c,
            None => b'0',
        };
        let lo = match lut.get((b & 0x0F) as usize) {
            Some(&c) => c,
            None => b'0',
        };
        out.push(hi as char);
        out.push(lo as char);
    }
    out
}

fn hex_nibble(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b.saturating_sub(b'0')),
        b'a'..=b'f' => Some(b.saturating_sub(b'a').saturating_add(10)),
        b'A'..=b'F' => Some(b.saturating_sub(b'A').saturating_add(10)),
        _ => None,
    }
}

fn hex_decode_32(s: &str) -> Result<[u8; 32], &'static str> {
    if s.len() != 64 {
        return Err("by= digest must be 64 hex chars");
    }
    let raw = s.as_bytes();
    let mut out = [0u8; 32];
    let mut idx = 0usize;
    while idx < 32 {
        let base = idx.saturating_mul(2);
        let b_hi = match raw.get(base) {
            Some(&b) => b,
            None => return Err("short hex"),
        };
        let b_lo = match raw.get(base.saturating_add(1)) {
            Some(&b) => b,
            None => return Err("short hex"),
        };
        let hi = match hex_nibble(b_hi) {
            Some(v) => v,
            None => return Err("bad hex"),
        };
        let lo = match hex_nibble(b_lo) {
            Some(v) => v,
            None => return Err("bad hex"),
        };
        if let Some(slot) = out.get_mut(idx) {
            *slot = (hi << 4) | lo;
        }
        idx = idx.saturating_add(1);
    }
    Ok(out)
}

/// Decoded `EVENT turn` provenance record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenanceEntry {
    pub turn: u64,
    pub offset: u64,
    pub kind: DriverKind,
    pub by_digest: [u8; 32],
}

impl ProvenanceEntry {
    /// Formats `EVENT turn=<turn> offset=<offset> kind=<kind> by=<64-hex>`.
    #[must_use]
    pub fn encode_event_line(&self) -> String {
        let mut out = String::new();
        out.push_str("EVENT turn=");
        push_u64_dec(&mut out, self.turn);
        out.push_str(" offset=");
        push_u64_dec(&mut out, self.offset);
        out.push_str(" kind=");
        out.push_str(self.kind.as_str());
        out.push_str(" by=");
        out.push_str(&hex_encode_32(&self.by_digest));
        out
    }

    /// Parses `EVENT turn=<u64> offset=<u64> kind=<word> by=<64-hex>`.
    pub fn decode_event_line(line: &str) -> Result<Self, &'static str> {
        let first_line = match line.split_once('\n') {
            Some((first, _)) => first,
            None => line,
        };
        let trimmed = first_line.trim();
        let Some(rest) = trimmed.strip_prefix("EVENT ") else {
            return Err("missing EVENT prefix");
        };
        let mut turn = None;
        let mut offset = None;
        let mut kind = None;
        let mut by_digest = None;
        for tok in rest.split_ascii_whitespace() {
            let (k, v) = match tok.split_once('=') {
                Some(pair) => pair,
                None => return Err("malformed EVENT token"),
            };
            match k {
                "turn" => {
                    if turn.is_some() {
                        return Err("duplicate turn=");
                    }
                    let parsed = match parse_u64_dec(v) {
                        Some(n) => n,
                        None => return Err("bad turn="),
                    };
                    turn = Some(parsed);
                }
                "offset" => {
                    if offset.is_some() {
                        return Err("duplicate offset=");
                    }
                    let parsed = match parse_u64_dec(v) {
                        Some(n) => n,
                        None => return Err("bad offset="),
                    };
                    offset = Some(parsed);
                }
                "kind" => {
                    if kind.is_some() {
                        return Err("duplicate kind=");
                    }
                    kind = Some(DriverKind::parse(v)?);
                }
                "by" => {
                    if by_digest.is_some() {
                        return Err("duplicate by=");
                    }
                    by_digest = Some(hex_decode_32(v)?);
                }
                _ => {}
            }
        }
        let turn_val = match turn {
            Some(t) => t,
            None => return Err("missing turn="),
        };
        let offset_val = match offset {
            Some(o) => o,
            None => return Err("missing offset="),
        };
        let kind_val = match kind {
            Some(k) => k,
            None => return Err("missing kind="),
        };
        let by_val = match by_digest {
            Some(b) => b,
            None => return Err("missing by="),
        };
        Ok(Self {
            turn: turn_val,
            offset: offset_val,
            kind: kind_val,
            by_digest: by_val,
        })
    }

    /// Verifies in constant time whether `(principal, cause_offset)` matches `by_digest`.
    #[must_use]
    pub fn matches_claim(&self, principal: &str, cause_offset: u64) -> bool {
        let expected = compute_driver_digest(self.kind, principal, cause_offset);
        ct_eq(&self.by_digest, &expected)
    }
}

/// Bounded monotone provenance ring for a session.
#[derive(Debug, Clone)]
pub struct TurnProvenanceLedger {
    cap: u64,
    last_turn: u64,
    ring: VecDeque<ProvenanceEntry>,
}

impl Default for TurnProvenanceLedger {
    fn default() -> Self {
        Self::new()
    }
}

impl TurnProvenanceLedger {
    #[must_use]
    pub fn new() -> Self {
        Self::with_capacity(MAX_PROVENANCE_DRIVERS)
    }

    #[must_use]
    pub fn with_capacity(cap: u64) -> Self {
        let c = prov_chain_clamp(cap, MAX_PROVENANCE_DRIVERS);
        Self {
            cap: if c == 0 { 1 } else { c },
            last_turn: 0,
            ring: VecDeque::new(),
        }
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.ring.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.ring.is_empty()
    }

    /// Appends the next attributed turn (`turn > last_turn`) and evicts oldest past `cap`.
    pub fn record_turn(
        &mut self,
        turn: u64,
        offset: u64,
        kind: DriverKind,
        principal: &str,
        cause_offset: u64,
    ) -> Result<ProvenanceEntry, &'static str> {
        let min_next = self.last_turn.saturating_add(1);
        if !prov_digest_matches(turn, min_next) {
            return Err("non-monotonic turn number");
        }
        self.last_turn = prov_turn_advance(self.last_turn, turn);
        let entry = ProvenanceEntry {
            turn: self.last_turn,
            offset,
            kind,
            by_digest: compute_driver_digest(kind, principal, cause_offset),
        };
        while (self.ring.len() as u64) >= self.cap {
            self.ring.pop_front();
        }
        self.ring.push_back(entry.clone());
        Ok(entry)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn event_turn_by_digest_roundtrips_and_verifies_driver_attribution() {
        let mut ledger = TurnProvenanceLedger::with_capacity(2);
        let e1 = ledger
            .record_turn(1, 100, DriverKind::Human, "h-andrew", 99)
            .unwrap();
        let line = e1.encode_event_line();
        let parsed = ProvenanceEntry::decode_event_line(&line).unwrap();
        assert_eq!(parsed, e1);
        assert!(parsed.matches_claim("h-andrew", 99));
        assert!(!parsed.matches_claim("autopilot", 99));
        assert!(!parsed.matches_claim("h-andrew", 100));

        assert!(ledger
            .record_turn(1, 105, DriverKind::Autopilot, "cruise", 104)
            .is_err());
        let _e2 = ledger
            .record_turn(2, 105, DriverKind::Autopilot, "cruise", 104)
            .unwrap();
        let _e3 = ledger
            .record_turn(3, 112, DriverKind::PeerMail, "n-0123456789abcdef", 110)
            .unwrap();
        assert_eq!(ledger.len(), 2);
    }
}
