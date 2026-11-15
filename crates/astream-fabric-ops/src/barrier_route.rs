// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Retained §5.4 barrier auto-responder, `post kind=ack re=<B>` router, and bounded
//! subject-budget retirement planner (`DESIGN-aterm-fabric.md` §5.4 / §15 lines 4028 & 4044,
//! `Astream.Broker.TlaBarrierRouter`).
//!
//! Solves two concrete `DESIGN-aterm-fabric.md` §5.4 gaps without exhausting a node's
//! `MAX_SUBJECTS_PER_PRODUCER` budget:
//! 1. **Auto-answering `barrier` records on `pub/<owner>/fleet`:** evaluates targeted
//!    member sessions (`Ready`, `Busy`, `Absent`) and produces retained `v=1` barrier
//!    ack records on `pub/<owner>/ack/<barrier_off>`.
//! 2. **Routing session `post kind=ack re=<B>`:** redirects explicit session barrier acks
//!    away from an addressee's inbox lane onto the retained `pub/<owner>/ack/<B>` face so
//!    `Last` barrier counting (`broker.barrier-count-by-last`) sees every member's answer,
//!    while bounding active `ack/<B>` subjects to `max_slots` (`<= MAX_ACTIVE_BARRIER_SLOTS`)
//!    and emitting subject-retirement candidates as `settled_floor` advances.

#![allow(clippy::for_kv_map)]

use std::collections::BTreeMap;

#[cfg(clean_islands)]
#[path = "barrier_route_island.rs"]
mod barrier_route_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn barrier_active_slots_clamp(slots: u64, max_slots: u64) -> u64 {
    if slots < max_slots {
        slots
    } else {
        max_slots
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn barrier_settled_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}
#[cfg(clean_islands)]
pub use barrier_route_island::{barrier_active_slots_clamp, barrier_settled_advance};

/// Hard ceiling on tracked active `pub/<owner>/ack/<B>` subjects per node router.
pub const MAX_ACTIVE_BARRIER_SLOTS: u64 = 64;

contract_fn! {
    /// Verified check that a barrier has gathered at least `required` member answers
    /// (`acked >= required`), linked via `clean-kernel-defeq` to `barrier_quorum_reached_isl`.
    #[must_use]
    pub const fn barrier_quorum_reached(acked: u64, required: u64) -> bool
    clauses [ensures result == (required <= acked)]
    {
        required <= acked
    }
}

/// Live local session availability when a §5.4 `barrier` record arrives on a fleet face.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BarrierMemberState {
    /// Session is idle/parked at the barrier point and immediately answers `ready`.
    Ready,
    /// Session is mid-turn; bridge auto-answers `busy` immediately, and the session's later
    /// `post kind=ack re=<B>` overwrites the retained face with `ready`.
    Busy,
    /// Session is not hosted or has exited on this node; bridge auto-answers `absent`.
    Absent,
}

impl BarrierMemberState {
    /// Wire token written in `state=<word>` on `pub/<owner>/ack/<B>`.
    #[must_use]
    pub const fn as_wire_str(self) -> &'static str {
        match self {
            Self::Ready => "ready",
            Self::Busy => "busy",
            Self::Absent => "absent",
        }
    }
}

/// Retained publish action + subject-retirement list synthesized by [`BarrierRouter`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BarrierRouteAction {
    /// Target retained subject (`pub/<owner>/ack/<barrier_off>`).
    pub subject: String,
    /// Canonical `v=1` barrier-ack payload (`v=1 t=<ms> from=<sid> re=<B> state=<word>`).
    pub body: Vec<u8>,
    /// Evicted or settled `pub/<owner>/ack/<old>` subjects ready for `Client::retire_subject`
    /// so `MAX_SUBJECTS_PER_PRODUCER` is never exhausted across long-lived nodes.
    pub retire_subjects: Vec<String>,
}

/// Routing outcome for an outbound session `post`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OutboundPostRoute {
    /// Ordinary inbox post — leave on the addressee's inbox lane.
    InboxLane,
    /// Barrier ack (`kind=ack re=<B>`) — redirect onto the retained `pub/<owner>/ack/<B>` face.
    RetainedBarrierFace(BarrierRouteAction),
}

#[derive(Debug, Clone)]
struct ActiveBarrierSlot {
    owner: String,
    subject: String,
    required_members: u64,
    ready_members: Vec<String>,
}

/// Stateful per-node §5.4 barrier auto-responder, `post kind=ack` router, and subject-budget manager.
#[derive(Debug, Clone)]
pub struct BarrierRouter {
    max_slots: u64,
    settled_floor: u64,
    slots: BTreeMap<u64, ActiveBarrierSlot>,
}

impl BarrierRouter {
    /// Create a router bounding active `pub/<owner>/ack/<B>` faces to `max_slots`
    /// (clamped into `1..=MAX_ACTIVE_BARRIER_SLOTS` via [`barrier_active_slots_clamp`]).
    #[must_use]
    pub fn new(max_slots: u64) -> Self {
        let clamped = barrier_active_slots_clamp(max_slots, MAX_ACTIVE_BARRIER_SLOTS);
        let effective = if clamped == 0 { 1 } else { clamped };
        Self {
            max_slots: effective,
            settled_floor: 0,
            slots: BTreeMap::new(),
        }
    }

    /// Monotone highest barrier offset settled and retired so far.
    #[must_use]
    pub const fn settled_floor(&self) -> u64 {
        self.settled_floor
    }

    /// Current count of active retained barrier subjects tracked by this router.
    #[must_use]
    pub fn active_slot_count(&self) -> u64 {
        barrier_active_slots_clamp(self.slots.len() as u64, self.max_slots)
    }

    /// Handle an incoming fleet `barrier` announcement at `barrier_off` owned by `owner`
    /// requesting `required_members` total quorum, producing an immediate auto-answer for
    /// `member_sid` in `member_state` at `now_ms`.
    pub fn on_fleet_barrier(
        &mut self,
        owner: &str,
        barrier_off: u64,
        required_members: u64,
        member_sid: &str,
        member_state: BarrierMemberState,
        now_ms: u64,
    ) -> Result<BarrierRouteAction, &'static str> {
        validate_segment(owner)?;
        validate_segment(member_sid)?;
        if barrier_off < self.settled_floor && !self.slots.contains_key(&barrier_off) {
            return Err("barrier offset precedes settled floor");
        }
        if let Some(existing) = self.slots.get(&barrier_off) {
            if existing.owner != owner {
                return Err("conflicting barrier owner");
            }
        }
        let mut retire_subjects = Vec::new();
        self.ensure_slot(owner, barrier_off, required_members, &mut retire_subjects);
        if member_state == BarrierMemberState::Ready {
            self.record_member_ready(barrier_off, member_sid, &mut retire_subjects);
        }
        let subject = format_barrier_ack_subject(owner, barrier_off);
        let body = format_barrier_ack_body(now_ms, member_sid, barrier_off, member_state);
        Ok(BarrierRouteAction {
            subject,
            body,
            retire_subjects,
        })
    }

    /// Inspect an outbound session post (`kind`, optional `re_offset`, `from_sid`, `target_owner`)
    /// and route `kind == "ack"` targeting an active or named barrier `re=<B>` onto the retained
    /// `pub/<owner>/ack/<B>` face (`DESIGN-aterm-fabric.md` §5.4 / line 4028).
    pub fn route_session_post(
        &mut self,
        kind: &str,
        re_offset: Option<u64>,
        target_owner: &str,
        from_sid: &str,
        is_barrier_ack: bool,
        now_ms: u64,
    ) -> Result<OutboundPostRoute, &'static str> {
        if kind != "ack" || !is_barrier_ack {
            return Ok(OutboundPostRoute::InboxLane);
        }
        let Some(barrier_off) = re_offset else {
            return Err("barrier ack missing re=<offset>");
        };
        validate_segment(target_owner)?;
        validate_segment(from_sid)?;
        if barrier_off < self.settled_floor && !self.slots.contains_key(&barrier_off) {
            return Err("barrier offset precedes settled floor");
        }
        let owner = match self.slots.get(&barrier_off) {
            Some(slot) => {
                if slot.owner != target_owner {
                    return Err("conflicting barrier owner");
                }
                slot.owner.clone()
            }
            None => str_to_owned_string(target_owner),
        };
        let mut retire_subjects = Vec::new();
        self.ensure_slot(&owner, barrier_off, 0, &mut retire_subjects);
        self.record_member_ready(barrier_off, from_sid, &mut retire_subjects);
        let subject = format_barrier_ack_subject(&owner, barrier_off);
        let body =
            format_barrier_ack_body(now_ms, from_sid, barrier_off, BarrierMemberState::Ready);
        Ok(OutboundPostRoute::RetainedBarrierFace(BarrierRouteAction {
            subject,
            body,
            retire_subjects,
        }))
    }

    /// Explicitly advance `settled_floor` through `upto_barrier_off` (inclusive), retiring
    /// all tracked `pub/<owner>/ack/<B>` subjects with `B <= upto_barrier_off`.
    pub fn settle_through(&mut self, upto_barrier_off: u64) -> Vec<String> {
        let next_floor = upto_barrier_off.saturating_add(1);
        self.settled_floor = barrier_settled_advance(self.settled_floor, next_floor);
        let mut keys_to_retire = Vec::new();
        for (&b_off, _) in &self.slots {
            if b_off <= upto_barrier_off {
                keys_to_retire.push(b_off);
            }
        }
        let mut retired = Vec::new();
        let mut k_rest = keys_to_retire.as_slice();
        while let &[key_off, ref tail @ ..] = k_rest {
            if let Some(slot) = self.slots.remove(&key_off) {
                retired.push(slot.subject);
            }
            k_rest = tail;
        }
        retired
    }

    fn ensure_slot(
        &mut self,
        owner: &str,
        barrier_off: u64,
        required_members: u64,
        retire_subjects: &mut Vec<String>,
    ) {
        if let Some(existing) = self.slots.get_mut(&barrier_off) {
            if required_members > existing.required_members {
                existing.required_members = required_members;
            }
            return;
        }
        while (self.slots.len() as u64) >= self.max_slots {
            let oldest_key = match self.slots.keys().next() {
                Some(&k) => k,
                None => break,
            };
            if let Some(evicted) = self.slots.remove(&oldest_key) {
                let cand = oldest_key.saturating_add(1);
                self.settled_floor = barrier_settled_advance(self.settled_floor, cand);
                retire_subjects.push(evicted.subject);
            }
        }
        let subject = format_barrier_ack_subject(owner, barrier_off);
        self.slots.insert(
            barrier_off,
            ActiveBarrierSlot {
                owner: str_to_owned_string(owner),
                subject,
                required_members,
                ready_members: Vec::new(),
            },
        );
    }

    fn record_member_ready(
        &mut self,
        barrier_off: u64,
        member_sid: &str,
        retire_subjects: &mut Vec<String>,
    ) {
        let mut settled_now = false;
        if let Some(slot) = self.slots.get_mut(&barrier_off) {
            let mut already = false;
            let mut m_rest = slot.ready_members.as_slice();
            while let [existing_sid, tail @ ..] = m_rest {
                if existing_sid == member_sid {
                    already = true;
                    break;
                }
                m_rest = tail;
            }
            if !already {
                slot.ready_members.push(str_to_owned_string(member_sid));
            }
            if slot.required_members > 0
                && barrier_quorum_reached(slot.ready_members.len() as u64, slot.required_members)
            {
                settled_now = true;
            }
        }
        if settled_now {
            if let Some(done) = self.slots.remove(&barrier_off) {
                let cand = barrier_off.saturating_add(1);
                self.settled_floor = barrier_settled_advance(self.settled_floor, cand);
                retire_subjects.push(done.subject);
            }
        }
    }
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

fn push_u64_dec_bytes(out: &mut Vec<u8>, mut n: u64) {
    if n == 0 {
        out.push(b'0');
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
            out.push(d);
        }
    }
}

fn validate_segment(seg: &str) -> Result<(), &'static str> {
    if seg.is_empty() || seg.len() > 64 {
        return Err("invalid segment length");
    }
    let mut rest = seg.as_bytes();
    while let &[b, ref tail @ ..] = rest {
        let ok = b.is_ascii_alphanumeric() || b == b'-' || b == b'_' || b == b'.';
        if !ok {
            return Err("invalid segment character");
        }
        rest = tail;
    }
    Ok(())
}

fn format_barrier_ack_subject(owner: &str, barrier_off: u64) -> String {
    let mut out = String::new();
    out.push_str("/pub/");
    out.push_str(owner);
    out.push_str("/ack/");
    push_u64_dec_str(&mut out, barrier_off);
    out
}

fn format_barrier_ack_body(
    now_ms: u64,
    from_sid: &str,
    barrier_off: u64,
    state: BarrierMemberState,
) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(b"v=1 t=");
    push_u64_dec_bytes(&mut out, now_ms);
    out.extend_from_slice(b" from=");
    out.extend_from_slice(from_sid.as_bytes());
    out.extend_from_slice(b" re=");
    push_u64_dec_bytes(&mut out, barrier_off);
    out.extend_from_slice(b" state=");
    out.extend_from_slice(state.as_wire_str().as_bytes());
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn auto_answers_busy_and_absent_then_routes_session_ack_to_retained_face_and_retires() {
        let mut router = BarrierRouter::new(4);

        // Bridge auto-answers `busy` for s-1 and `absent` for s-2 on barrier 42 (quorum 2).
        let a1 = router
            .on_fleet_barrier("n-alpha", 42, 2, "s-1", BarrierMemberState::Busy, 1000)
            .unwrap();
        assert_eq!(a1.subject, "/pub/n-alpha/ack/42");
        assert_eq!(a1.body, b"v=1 t=1000 from=s-1 re=42 state=busy");
        assert!(a1.retire_subjects.is_empty());

        let a2 = router
            .on_fleet_barrier("n-alpha", 42, 2, "s-2", BarrierMemberState::Ready, 1001)
            .unwrap();
        assert_eq!(a2.body, b"v=1 t=1001 from=s-2 re=42 state=ready");
        assert!(a2.retire_subjects.is_empty());
        assert_eq!(router.active_slot_count(), 1);

        // Ordinary inbox post stays on InboxLane.
        let inbox = router
            .route_session_post("note", None, "n-alpha", "s-1", false, 1005)
            .unwrap();
        assert_eq!(inbox, OutboundPostRoute::InboxLane);

        // Session s-1 finishes its turn and posts `kind=ack re=42` -> routed onto `/pub/n-alpha/ack/42`
        // AND quorum 2/2 settles barrier 42, emitting `/pub/n-alpha/ack/42` for subject retirement!
        let routed = router
            .route_session_post("ack", Some(42), "n-alpha", "s-1", true, 1010)
            .unwrap();
        match routed {
            OutboundPostRoute::RetainedBarrierFace(act) => {
                assert_eq!(act.subject, "/pub/n-alpha/ack/42");
                assert_eq!(act.body, b"v=1 t=1010 from=s-1 re=42 state=ready");
                assert_eq!(act.retire_subjects, vec!["/pub/n-alpha/ack/42".to_string()]);
            }
            OutboundPostRoute::InboxLane => panic!("expected RetainedBarrierFace"),
        }
        assert_eq!(router.active_slot_count(), 0);
        assert_eq!(router.settled_floor(), 43);
    }

    #[test]
    fn slot_cap_evicts_oldest_barrier_subject_monotonically() {
        let mut router = BarrierRouter::new(2);
        router
            .on_fleet_barrier("n-alpha", 10, 3, "s-1", BarrierMemberState::Busy, 100)
            .unwrap();
        router
            .on_fleet_barrier("n-alpha", 20, 3, "s-1", BarrierMemberState::Busy, 200)
            .unwrap();
        let third = router
            .on_fleet_barrier("n-alpha", 30, 3, "s-1", BarrierMemberState::Busy, 300)
            .unwrap();
        assert_eq!(
            third.retire_subjects,
            vec!["/pub/n-alpha/ack/10".to_string()]
        );
        assert_eq!(router.active_slot_count(), 2);
        assert_eq!(router.settled_floor(), 11);
        assert!(router
            .route_session_post("ack", Some(10), "n-alpha", "s-2", true, 305)
            .is_err());
        assert!(router
            .on_fleet_barrier("n-other", 20, 3, "s-2", BarrierMemberState::Busy, 310)
            .is_err());
        assert!(router
            .route_session_post("ack", Some(20), "n-other", "s-2", true, 315)
            .is_err());
    }
}
