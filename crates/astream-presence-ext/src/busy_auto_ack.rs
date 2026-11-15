// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! §5.4 bridge barrier auto-responder (`DESIGN-aterm-fabric.md` lines 4028 & 4044,
//! `Astream.Presence.TlaBusyAutoAck`).
//!
//! Emits canonical `v=1` barrier answers (`pub/<node>/<sid>/ack/<B>`) verified compatible with
//! [`astream_wire::V1BarrierAck`] and enforces a monotone per-barrier state lattice via
//! Clean-origin `auto_ack_rank_advance`:
//! - Rank `1`: `absent` (bridge auto-answer when session does not exist / exited)
//! - Rank `2`: `busy` (bridge auto-answer when session is mid-turn)
//! - Rank `3`: `ready` / `refused` (terminal settled session answer; a late `busy` auto-ack
//!   can NEVER overwrite an already-published `ready` or `refused` answer!)

use std::collections::BTreeMap;

use astream_wire::{BarrierAckState, Subject, V1BarrierAck};

#[cfg(clean_islands)]
#[path = "busy_auto_ack_island.rs"]
mod busy_auto_ack_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn auto_ack_pending_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn auto_ack_rank_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use busy_auto_ack_island::{auto_ack_pending_clamp, auto_ack_rank_advance};

/// Maximum concurrent barrier offsets tracked per session bridge.
pub const MAX_PENDING_AUTO_BARRIERS: u64 = 64;

contract_fn! {
    /// Verified check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `auto_ack_settled_isl`. Rank `3` denotes terminal `ready`/`refused`.
    #[must_use]
    pub const fn auto_ack_settled(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

fn state_rank(st: BarrierAckState) -> u64 {
    match st {
        BarrierAckState::Absent => 1,
        BarrierAckState::Busy | BarrierAckState::Held => 2,
        BarrierAckState::Ready | BarrierAckState::Refused => 3,
    }
}

fn state_word(st: BarrierAckState) -> &'static str {
    st.as_str()
}

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

/// Wire publication planned for `/f/<fleet>/pub/<node>/<sid>/ack/<barrier_offset>`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AutoAckEmission {
    pub subject: String,
    pub body: String,
    pub state: BarrierAckState,
    pub settled: bool,
}

/// Stateful per-session §5.4 barrier auto-responder.
#[derive(Debug, Clone)]
pub struct BusyBarrierAutoResponder {
    fleet: String,
    node: String,
    sid: String,
    max_slots: u64,
    evicted_floor: u64,
    ranks: BTreeMap<u64, u64>,
}

impl BusyBarrierAutoResponder {
    /// Constructs a responder for `/f/<fleet>/pub/<node>/<sid>/ack/<B>`, validating the subject prefix.
    pub fn new(fleet: &str, node: &str, sid: &str) -> Result<Self, &'static str> {
        let mut probe = String::new();
        probe.push_str("/f/");
        probe.push_str(fleet);
        probe.push_str("/pub/");
        probe.push_str(node);
        probe.push('/');
        probe.push_str(sid);
        probe.push_str("/ack/0");
        if Subject::new(probe).is_err() {
            return Err("invalid fleet/node/sid segment for barrier ack");
        }
        Ok(Self {
            fleet: clone_str(fleet),
            node: clone_str(node),
            sid: clone_str(sid),
            max_slots: auto_ack_pending_clamp(MAX_PENDING_AUTO_BARRIERS, MAX_PENDING_AUTO_BARRIERS),
            evicted_floor: 0,
            ranks: BTreeMap::new(),
        })
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.ranks.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.ranks.is_empty()
    }

    /// Evaluates a proposed `state` for `barrier_offset` at `sender_t_ms`.
    /// Returns `Some(AutoAckEmission)` iff `state` strictly advances the barrier's rank;
    /// returns `None` when an equal-or-higher rank answer (`ready`/`refused`) already went out!
    pub fn propose_answer(
        &mut self,
        barrier_offset: u64,
        state: BarrierAckState,
        sender_t_ms: u64,
    ) -> Option<AutoAckEmission> {
        if barrier_offset < self.evicted_floor {
            return None;
        }
        let prev_rank = match self.ranks.get(&barrier_offset) {
            Some(&r) => r,
            None => 0,
        };
        let cand_rank = state_rank(state);
        let next_rank = auto_ack_rank_advance(prev_rank, cand_rank);
        if next_rank == prev_rank {
            return None;
        }
        while !self.ranks.contains_key(&barrier_offset)
            && (self.ranks.len() as u64) >= self.max_slots
        {
            let Some(&oldest) = self.ranks.keys().next() else {
                break;
            };
            self.ranks.remove(&oldest);
            let floor_cand = oldest.saturating_add(1);
            if floor_cand > self.evicted_floor {
                self.evicted_floor = floor_cand;
            }
            if barrier_offset < self.evicted_floor {
                return None;
            }
        }
        self.ranks.insert(barrier_offset, next_rank);
        let mut subject = String::new();
        subject.push_str("/f/");
        subject.push_str(&self.fleet);
        subject.push_str("/pub/");
        subject.push_str(&self.node);
        subject.push('/');
        subject.push_str(&self.sid);
        subject.push_str("/ack/");
        push_u64_dec(&mut subject, barrier_offset);

        let mut body = String::new();
        body.push_str("v=1 t=");
        push_u64_dec(&mut body, sender_t_ms);
        body.push_str(" re=");
        push_u64_dec(&mut body, barrier_offset);
        body.push_str(" state=");
        body.push_str(state_word(state));

        // Self-verify against astream-wire's canonical V1BarrierAck decoder!
        if V1BarrierAck::decode(body.as_bytes()).is_err() {
            return None;
        }
        Some(AutoAckEmission {
            subject,
            body,
            state,
            settled: auto_ack_settled(next_rank, 3),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn busy_auto_ack_upgrades_to_ready_and_blocks_downgrade_while_matching_v1_wire_decoder() {
        let mut resp = BusyBarrierAutoResponder::new("alpha", "n1", "s7").unwrap();
        let e1 = resp
            .propose_answer(400, BarrierAckState::Busy, 1_000)
            .unwrap();
        assert_eq!(e1.subject, "/f/alpha/pub/n1/s7/ack/400");
        assert!(!e1.settled);
        let parsed1 = V1BarrierAck::decode(e1.body.as_bytes()).unwrap();
        assert_eq!(parsed1.state, BarrierAckState::Busy);

        // Duplicate busy is suppressed.
        assert!(resp
            .propose_answer(400, BarrierAckState::Busy, 1_010)
            .is_none());

        // Session finishes turn and posts ready -> upgrades cleanly!
        let e2 = resp
            .propose_answer(400, BarrierAckState::Ready, 1_050)
            .unwrap();
        assert!(e2.settled);
        let parsed2 = V1BarrierAck::decode(e2.body.as_bytes()).unwrap();
        assert_eq!(parsed2.state, BarrierAckState::Ready);

        // Late auto-ack (`busy` or `absent`) cannot overwrite settled `ready`!
        assert!(resp
            .propose_answer(400, BarrierAckState::Busy, 1_060)
            .is_none());
        assert!(resp
            .propose_answer(400, BarrierAckState::Absent, 1_070)
            .is_none());
    }
}
