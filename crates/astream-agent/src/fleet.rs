// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Multi-agent Chandy-Lamport consistent-cut replay and causal counterfactual forking
//! at the **Cognition** rung (all four streams: Inputs, Outputs, Effects, Cognition).
//!
//! [`crate::unified`] replays and forks a single agent session's 4-stream log;
//! `astream-engine::fleet` replays Chandy-Lamport cuts across multiple terminal
//! sessions' VT logs (Inputs + Outputs). This module joins the two: a fleet of
//! [`AgentSession`]s connected by cross-session causal provenance (`caused_by`,
//! modelling an orchestrator spawning workers, dispatching mail/prompts, and awaiting
//! worker results) can be:
//!
//! 1. **Replayed at a verified Chandy-Lamport cut** ([`replay_fleet_cut`]): refuses any
//!    [`CausalCut`] that admits a cross-session effect without its cause
//!    ([`FleetReplayError::InconsistentCut`]), and deterministically reconstructs every
//!    included session's 4-stream [`Replay`] plus a fleet-wide content digest.
//! 2. **Counterfactually forked across causal boundaries** ([`fork_fleet_session`] +
//!    [`replay_fleet_causal`]): swapping one recorded cognition record on an upstream
//!    agent (e.g. changing an orchestrator's `"TEST FAILED"` tool result to `"TEST OK"`)
//!    re-drives all agents along causal event edges. If the upstream agent's planner
//!    now finishes BEFORE the offset that spawned or messaged a downstream worker,
//!    that downstream causal edge is never reached (`!fleet_cause_reached`), so the
//!    worker (and its transitive sub-workers) are causally gated and all four streams
//!    diverge coherently across the entire fleet while keeping `effective_cut`
//!    Chandy-Lamport consistent.

use std::collections::BTreeMap;

use astream_wire::{CausalCut, CausalEdge, CutViolation, Offset};

use crate::turn::{trace_fnv, Action, Planner, ReplayPlanner};
use crate::unified::{fold_bytes, fold_u64, replay_session, unified_fork_in_bounds, Event, Replay};

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "fleet_island.rs"]
mod fleet_island;
#[cfg(not(clean_islands))]
pub use crate::twins::fleet_clamp_cut_len;
#[cfg(clean_islands)]
pub use fleet_island::fleet_clamp_cut_len;

contract_fn! {
    /// Verified check that a source session's replayed prefix (`reached_count` events,
    /// covering offsets `0..reached_count`) reached causal offset `cause_offset`
    /// (`cause_offset < reached_count`), linked via `clean-kernel-defeq` to
    /// `fleet_cause_reached_isl`.
    #[must_use]
    pub const fn fleet_cause_reached(cause_offset: u64, reached_count: u64) -> bool
    clauses [ensures result == (cause_offset < reached_count)]
    {
        cause_offset < reached_count
    }
}

/// Cross-session causal provenance of a [`FleetEvent`]: the event at `offset` on
/// `session` causally produced this event (e.g. an orchestrator's spawn or prompt
/// dispatch at `(orch_sid, k)` causing a worker's initial event at `(worker_sid, 0)`,
/// or a worker's completion at `(worker_sid, m)` causing an orchestrator's follow-up
/// tool result at `(orch_sid, n)`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AgentCause {
    /// Identifier of the causal source session.
    pub session: String,
    /// Zero-based event offset on `session` that caused this event.
    pub offset: Offset,
}

/// One event on an [`AgentSession`]'s unified 4-stream offset axis, optionally linked
/// to a cross-session causal predecessor (`caused_by`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FleetEvent {
    /// The 4-stream event (Input, Output, Effect, or Cognition).
    pub event: Event,
    /// Optional cross-session causal provenance.
    pub caused_by: Option<AgentCause>,
}

impl FleetEvent {
    /// An event with no cross-session causal predecessor.
    #[must_use]
    pub const fn local(event: Event) -> Self {
        Self {
            event,
            caused_by: None,
        }
    }

    /// An event causally produced by `(session, offset)`.
    #[must_use]
    pub fn caused(event: Event, session: impl Into<String>, offset: Offset) -> Self {
        Self {
            event,
            caused_by: Some(AgentCause {
                session: session.into(),
                offset,
            }),
        }
    }
}

/// One recorded agent session in a multi-agent fleet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AgentSession {
    /// Unique session identifier (e.g. `"s-orch"`, `"s-worker-1"`).
    pub id: String,
    /// Terminal viewport width in columns.
    pub cols: u16,
    /// Terminal viewport height in rows.
    pub rows: u16,
    /// Unified 4-stream events at offsets `0..events.len()`.
    pub events: Vec<FleetEvent>,
}

impl AgentSession {
    /// Construct a recorded agent session.
    #[must_use]
    pub fn new(id: impl Into<String>, cols: u16, rows: u16, events: Vec<FleetEvent>) -> Self {
        Self {
            id: id.into(),
            cols,
            rows,
            events,
        }
    }
}

/// Errors returned by multi-agent fleet replay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FleetReplayError {
    /// The requested [`CausalCut`] admits a cross-session effect without admitting its
    /// cause (Chandy-Lamport snapshot violation).
    InconsistentCut(CutViolation<String>),
    /// Active sessions form an event-level causal cycle (`(A, i)` waits on `(B, j)`
    /// while `(B, j)` waits on `(A, i')` with `i <= i'`), or duplicate session IDs
    /// make causal references ambiguous.
    CausalCycle {
        /// Identifier of the session where the cycle or duplicate ID was detected.
        session: String,
    },
}

/// Deterministic multi-agent 4-stream replay result across a fleet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FleetReplay {
    /// Replayed 4-stream state for each session in ascending session-ID order.
    pub sessions: BTreeMap<String, Replay>,
    /// The effective [`CausalCut`] of events actually reached across the fleet: each
    /// session with `events_reached > 0` sits at `Offset(events_reached - 1)`, while
    /// sessions that reached `0` events are absent from the cut (admitting nothing).
    pub effective_cut: CausalCut<String>,
    /// Deterministic FNV-1a content address over all entries in `sessions` (session id,
    /// decision-trace hash, `inputs_applied`, `screen_hash`, `effect_digest`, and
    /// `events_reached`).
    pub fleet_digest: u64,
}

const FNV_OFFSET_BASIS: u64 = 0xcbf2_9ce4_8422_2325;

fn compute_fleet_digest(sessions: &BTreeMap<String, Replay>) -> u64 {
    let mut acc = fold_u64(FNV_OFFSET_BASIS, sessions.len() as u64);
    for (id, rep) in sessions {
        acc = fold_bytes(acc, id.as_bytes());
        acc = fold_u64(acc, trace_fnv(&rep.decisions));
        acc = fold_u64(acc, rep.inputs_applied as u64);
        acc = fold_u64(acc, rep.screen_hash);
        acc = fold_u64(acc, rep.effect_digest);
        acc = fold_u64(acc, rep.events_reached as u64);
    }
    acc
}

/// Extract all cross-session [`CausalEdge`]s (`cause.session != effect_session`) from
/// `sessions` in deterministic session and event-offset order.
#[must_use]
pub fn fleet_causal_edges(sessions: &[AgentSession]) -> Vec<CausalEdge<String>> {
    let mut edges = Vec::new();
    for session in sessions {
        for (idx, fev) in session.events.iter().enumerate() {
            if let Some(cause) = &fev.caused_by {
                if cause.session != session.id {
                    edges.push(CausalEdge {
                        cause: (cause.session.clone(), cause.offset),
                        effect: (session.id.clone(), Offset(idx as u64)),
                    });
                }
            }
        }
    }
    edges
}

/// Replay a multi-agent fleet up to a verified Chandy-Lamport [`CausalCut`].
///
/// Refuses any cut that violates cross-session causal consistency before replaying a
/// single session. Sessions absent from `cut` are omitted from [`FleetReplay::sessions`].
pub fn replay_fleet_cut(
    sessions: &[AgentSession],
    cut: &CausalCut<String>,
) -> Result<FleetReplay, FleetReplayError> {
    let edges = fleet_causal_edges(sessions);
    if let Some(v) = cut.first_violation(&edges) {
        return Err(FleetReplayError::InconsistentCut(v));
    }

    let mut out_sessions = BTreeMap::new();
    let mut effective_cut = CausalCut::new();

    for session in sessions {
        if out_sessions.contains_key(&session.id) {
            return Err(FleetReplayError::CausalCycle {
                session: session.id.clone(),
            });
        }
        let Some(upto) = cut.offset_of(&session.id) else {
            continue;
        };
        let want_len = upto.0.saturating_add(1);
        let clamped_len = fleet_clamp_cut_len(want_len, session.events.len() as u64) as usize;
        let prefix: Vec<Event> = session.events[..clamped_len]
            .iter()
            .map(|fe| fe.event.clone())
            .collect();
        let rep = replay_session(&prefix, session.cols, session.rows);
        if rep.events_reached > 0 {
            effective_cut.set(session.id.clone(), Offset((rep.events_reached - 1) as u64));
        }
        out_sessions.insert(session.id.clone(), rep);
    }

    let fleet_digest = compute_fleet_digest(&out_sessions);
    Ok(FleetReplay {
        sessions: out_sessions,
        effective_cut,
        fleet_digest,
    })
}

/// Counterfactual multi-session fork: replace the [`Event`] at zero-based offset `at` on
/// `session_id` (preserving its `caused_by` edge). Out-of-range offsets or unknown
/// session IDs leave the fleet unchanged.
#[must_use]
pub fn fork_fleet_session(
    sessions: &[AgentSession],
    session_id: &str,
    at: usize,
    replacement: Event,
) -> Vec<AgentSession> {
    let mut out = sessions.to_vec();
    for s in &mut out {
        if s.id == session_id && unified_fork_in_bounds(at, s.events.len()) {
            if let Some(slot) = s.events.get_mut(at) {
                slot.event = replacement;
            }
            break;
        }
    }
    out
}

struct SessionCursor {
    planner: ReplayPlanner,
    decisions_len: u32,
    reached: usize,
    done: bool,
}

/// Replay a multi-agent fleet under **event-level causal gating** — the multi-agent
/// counterfactual engine.
///
/// Steps sessions deterministically, admitting an event with `caused_by = Some((src, k))`
/// if and only if `src` has already reached offset `k` (`fleet_cause_reached(k,
/// reached[src])`). Supports arbitrary multi-round parent <-> worker <-> sub-worker
/// RPC chains as long as event-level causality is acyclic.
///
/// When an upstream counterfactual fork causes `src`'s [`ReplayPlanner`] to finish
/// early (before reaching `k`), every downstream session waiting on `(src, k)` (and
/// its transitive causal descendants) cleanly halts prior to that unreached causal
/// edge, keeping [`FleetReplay::effective_cut`] Chandy-Lamport consistent across the
/// entire fleet.
pub fn replay_fleet_causal(sessions: &[AgentSession]) -> Result<FleetReplay, FleetReplayError> {
    let mut id_to_idx: BTreeMap<&str, usize> = BTreeMap::new();
    let mut cursors: Vec<SessionCursor> = Vec::new();
    for (i, s) in sessions.iter().enumerate() {
        if id_to_idx.insert(s.id.as_str(), i).is_some() {
            return Err(FleetReplayError::CausalCycle {
                session: s.id.clone(),
            });
        }
        cursors.push(SessionCursor {
            planner: ReplayPlanner,
            decisions_len: 0,
            reached: 0,
            done: s.events.is_empty(),
        });
    }

    let n = sessions.len();

    loop {
        // 1. Close any session whose next event depends on an impossible cause:
        //    - unknown source session,
        //    - source offset past the source session's total length,
        //    - self-causal forward/self reference (`cause.offset >= current_idx`), or
        //    - source session is already `done` without having reached `cause.offset`.
        loop {
            let mut closed_any = false;
            for i in 0..n {
                let (cur, is_done) = match cursors.get(i) {
                    Some(c) => (c.reached, c.done),
                    None => continue,
                };
                if is_done {
                    continue;
                }
                let Some(sess) = sessions.get(i) else {
                    continue;
                };
                let Some(fev) = sess.events.get(cur) else {
                    if let Some(c) = cursors.get_mut(i) {
                        c.done = true;
                    }
                    closed_any = true;
                    continue;
                };
                if let Some(cause) = &fev.caused_by {
                    if cause.session == sess.id {
                        if !fleet_cause_reached(cause.offset.0, cur as u64) {
                            return Err(FleetReplayError::CausalCycle {
                                session: sess.id.clone(),
                            });
                        }
                    } else {
                        match id_to_idx.get(cause.session.as_str()).copied() {
                            None => {
                                if let Some(c) = cursors.get_mut(i) {
                                    c.done = true;
                                }
                                closed_any = true;
                            }
                            Some(src_idx) => {
                                let src_total = sessions
                                    .get(src_idx)
                                    .map_or(0u64, |s| s.events.len() as u64);
                                let (src_reached, src_done) = cursors
                                    .get(src_idx)
                                    .map_or((0u64, true), |c| (c.reached as u64, c.done));
                                if cause.offset.0 >= src_total
                                    || (src_done
                                        && !fleet_cause_reached(cause.offset.0, src_reached))
                                {
                                    if let Some(c) = cursors.get_mut(i) {
                                        c.done = true;
                                    }
                                    closed_any = true;
                                }
                            }
                        }
                    }
                }
            }
            if !closed_any {
                break;
            }
        }

        // 2. If all sessions are done, we have the exact causal horizon of the fleet.
        if cursors.iter().all(|c| c.done) {
            break;
        }

        // 3. Advance every active session whose next event is causally ready.
        let mut progressed = false;
        for i in 0..n {
            let (cur, is_done) = match cursors.get(i) {
                Some(c) => (c.reached, c.done),
                None => continue,
            };
            if is_done {
                continue;
            }
            let Some(sess) = sessions.get(i) else {
                continue;
            };
            let Some(fev) = sess.events.get(cur) else {
                continue;
            };
            let ready = match &fev.caused_by {
                None => true,
                Some(cause) if cause.session == sess.id => {
                    fleet_cause_reached(cause.offset.0, cur as u64)
                }
                Some(cause) => match id_to_idx.get(cause.session.as_str()).copied() {
                    Some(src_idx) => {
                        let src_reached = cursors.get(src_idx).map_or(0u64, |c| c.reached as u64);
                        fleet_cause_reached(cause.offset.0, src_reached)
                    }
                    None => false,
                },
            };
            if !ready {
                continue;
            }
            progressed = true;
            if let Some(c) = cursors.get_mut(i) {
                c.reached = cur.saturating_add(1);
                if let Event::Cognition(rec) = &fev.event {
                    let step = c.decisions_len;
                    c.decisions_len = c.decisions_len.wrapping_add(1);
                    let action = c.planner.decide(step, rec);
                    if matches!(action, Action::Finish) {
                        c.done = true;
                    }
                }
                if c.reached >= sess.events.len() {
                    c.done = true;
                }
            }
        }

        // 4. If active sessions remain and none could step, they form a true event-level
        //    causal cycle (`(A, cur_A) <- ... <- (B, cur_B) <- (A, >= cur_A)`).
        if !progressed {
            let stuck_idx = cursors.iter().position(|c| !c.done).unwrap_or(0);
            let stuck_id = sessions
                .get(stuck_idx)
                .map_or_else(String::new, |s| s.id.clone());
            return Err(FleetReplayError::CausalCycle { session: stuck_id });
        }
    }

    let mut out_sessions = BTreeMap::new();
    let mut effective_cut = CausalCut::new();
    for (i, session) in sessions.iter().enumerate() {
        let reached_i = cursors.get(i).map_or(0usize, |c| c.reached);
        let slice = session.events.get(..reached_i).unwrap_or(&[]);
        let mut prefix = Vec::new();
        for fe in slice {
            prefix.push(fe.event.clone());
        }
        let rep = replay_session(&prefix, session.cols, session.rows);
        debug_assert_eq!(rep.events_reached, reached_i);
        if rep.events_reached > 0 {
            effective_cut.set(session.id.clone(), Offset((rep.events_reached - 1) as u64));
        }
        out_sessions.insert(session.id.clone(), rep);
    }

    let fleet_digest = compute_fleet_digest(&out_sessions);
    Ok(FleetReplay {
        sessions: out_sessions,
        effective_cut,
        fleet_digest,
    })
}
