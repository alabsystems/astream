// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Multi-session semantic wake & stalled-worker heartbeat multiplexer (`Astream.Pump.TlaSemanticWake`).
//!
//! Coordinates N supervised worker sessions for `aterm ctl await task @<sid>,...`:
//! - Ingests [`SessionEvent`] boundaries (`PromptReady`, `CommandStart`, `CommandEnd`,
//!   `Quiesced`) per session and assigns strictly monotone wake sequences via
//!   [`sem_wake_seq_advance`],
//! - Tracks per-session idle ticks while a command is running (between `CommandStart`
//!   and `CommandEnd`/`PromptReady`), clamping to `stall_limit` via
//!   [`sem_idle_ticks_clamp`] and emitting a one-shot [`SemanticWakeKind::Stalled`]
//!   alert when [`sem_stall_reached`] triggers (without spamming repeated stall wakes
//!   until new output or a lifecycle transition resets the idle counter).

#![allow(clippy::question_mark)]

use astream_term::events::SessionEvent;

#[cfg(clean_islands)]
#[path = "semantic_wake_island.rs"]
mod semantic_wake_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sem_wake_seq_advance(cur_seq: u64, next_seq: u64) -> u64 {
    if cur_seq < next_seq {
        next_seq
    } else {
        cur_seq
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sem_idle_ticks_clamp(idle_ticks: u64, stall_limit: u64) -> u64 {
    if idle_ticks < stall_limit {
        idle_ticks
    } else {
        stall_limit
    }
}
#[cfg(clean_islands)]
pub use semantic_wake_island::{sem_idle_ticks_clamp, sem_wake_seq_advance};

/// Maximum concurrently tracked sessions in a single [`SemanticWakeMux`].
pub const MAX_MUX_SESSIONS: usize = 256;

/// Default idle heartbeat ticks before an executing command is flagged [`SemanticWakeKind::Stalled`].
pub const DEFAULT_STALL_LIMIT_TICKS: u64 = 30;

contract_fn! {
    /// Kernel-certified stall-threshold predicate (`stall_limit <= idle_ticks`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `sem_stall_reached_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn sem_stall_reached(idle_ticks: u64, stall_limit: u64) -> bool
    clauses [ensures result == (stall_limit <= idle_ticks)]
    {
        stall_limit <= idle_ticks
    }
}

/// High-level wake classification surfaced to an outer supervisor (`aterm ctl await task`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SemanticWakeKind {
    /// Interactive prompt returned (`OSC 133 ; A` / prompt match).
    PromptReady,
    /// Foreground command started (`OSC 133 ; C`).
    CommandStarted,
    /// Foreground command exited with status `0` (or unknown exit code when `exit == None`).
    CommandSucceeded { exit_code: Option<i32> },
    /// Foreground command failed (`exit_code != 0`).
    CommandFailed { exit_code: i32 },
    /// Screen settled after output burst.
    Quiesced,
    /// Executing session produced zero output across `stall_limit` heartbeat ticks.
    Stalled { idle_ticks: u64 },
}

/// Sequenced wake envelope emitted by [`SemanticWakeMux`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticWake {
    /// Strictly increasing multiplexer sequence (`>= 1`).
    pub wake_seq: u64,
    /// Session identifier (`sid`).
    pub session_id: String,
    /// Broker offset of the latest delivery observed for `session_id`.
    pub broker_offset: u64,
    /// Semantic reason for waking the supervisor.
    pub kind: SemanticWakeKind,
}

#[derive(Debug, Clone)]
struct TrackedSession {
    session_id: String,
    last_offset: u64,
    executing: bool,
    idle_ticks: u64,
    stall_reported: bool,
}

/// Multi-session semantic wake & stall detector with Clean-verified sequence monotonicity.
#[derive(Debug, Clone)]
pub struct SemanticWakeMux {
    stall_limit: u64,
    wake_seq: u64,
    sessions: Vec<TrackedSession>,
}

impl Default for SemanticWakeMux {
    fn default() -> Self {
        Self::new(DEFAULT_STALL_LIMIT_TICKS)
    }
}

impl SemanticWakeMux {
    /// Create a multiplexer with `stall_limit` heartbeat ticks (`>= 1`).
    #[must_use]
    pub fn new(stall_limit: u64) -> Self {
        let limit = if stall_limit == 0 { 1 } else { stall_limit };
        Self {
            stall_limit: limit,
            wake_seq: 0,
            sessions: Vec::new(),
        }
    }

    /// Configured stall threshold in heartbeat ticks.
    #[must_use]
    pub const fn stall_limit(&self) -> u64 {
        self.stall_limit
    }

    /// Current high-water wake sequence number (`0` before the first wake).
    #[must_use]
    pub const fn wake_seq(&self) -> u64 {
        self.wake_seq
    }

    /// Number of currently registered sessions (`<= MAX_MUX_SESSIONS`).
    #[must_use]
    pub fn session_count(&self) -> usize {
        self.sessions.len()
    }

    /// Register a session if not already present. Returns `false` if [`MAX_MUX_SESSIONS`] is full.
    pub fn register_session(&mut self, session_id: &str) -> bool {
        if self.find_session_idx(session_id).is_some() {
            return true;
        }
        if self.sessions.len() >= MAX_MUX_SESSIONS {
            return false;
        }
        self.sessions.push(TrackedSession {
            session_id: session_id.to_string(),
            last_offset: 0,
            executing: false,
            idle_ticks: 0,
            stall_reported: false,
        });
        true
    }

    /// Record raw output activity on `session_id` at `broker_offset` (resets idle stall ticks
    /// even when no discrete [`SessionEvent`] boundary fired on this chunk).
    pub fn note_activity(&mut self, session_id: &str, broker_offset: u64) {
        let Some(idx) = self.ensure_session_idx(session_id) else {
            return;
        };
        if let Some(slot) = self.sessions.get_mut(idx) {
            if broker_offset > slot.last_offset {
                slot.last_offset = broker_offset;
            }
            slot.idle_ticks = 0;
            slot.stall_reported = false;
        }
    }

    /// Ingest a [`SessionEvent`] from `session_id` at `broker_offset`, returning its
    /// sequenced [`SemanticWake`] envelope (or `None` if `MAX_MUX_SESSIONS` prevented
    /// registering an unknown session).
    pub fn ingest_event(
        &mut self,
        session_id: &str,
        broker_offset: u64,
        event: &SessionEvent,
    ) -> Option<SemanticWake> {
        let Some(idx) = self.ensure_session_idx(session_id) else {
            return None;
        };
        let (kind, eff_offset) = {
            let Some(slot) = self.sessions.get_mut(idx) else {
                return None;
            };
            if broker_offset > slot.last_offset {
                slot.last_offset = broker_offset;
            }
            slot.idle_ticks = 0;
            slot.stall_reported = false;
            let k = match event {
                SessionEvent::PromptReady { .. } => {
                    slot.executing = false;
                    SemanticWakeKind::PromptReady
                }
                SessionEvent::CommandStart { .. } => {
                    slot.executing = true;
                    SemanticWakeKind::CommandStarted
                }
                SessionEvent::CommandEnd { exit, .. } => {
                    slot.executing = false;
                    match *exit {
                        Some(code) if code != 0 => {
                            SemanticWakeKind::CommandFailed { exit_code: code }
                        }
                        other => SemanticWakeKind::CommandSucceeded { exit_code: other },
                    }
                }
                SessionEvent::Quiesced { .. } => SemanticWakeKind::Quiesced,
            };
            (k, slot.last_offset)
        };
        let seq = self.next_seq();
        Some(SemanticWake {
            wake_seq: seq,
            session_id: session_id.to_string(),
            broker_offset: eff_offset,
            kind,
        })
    }

    /// Advance one heartbeat tick across all tracked executing sessions, returning one-shot
    /// [`SemanticWakeKind::Stalled`] wakes for any executing session whose clamped idle
    /// counter reaches `stall_limit`.
    pub fn tick_idle(&mut self) -> Vec<SemanticWake> {
        let limit = self.stall_limit;
        let mut ready_indices = Vec::new();
        let mut i = 0usize;
        while i < self.sessions.len() {
            if let Some(slot) = self.sessions.get_mut(i) {
                if slot.executing {
                    let raw_next = slot.idle_ticks.saturating_add(1);
                    slot.idle_ticks = sem_idle_ticks_clamp(raw_next, limit);
                    if !slot.stall_reported && sem_stall_reached(slot.idle_ticks, limit) {
                        slot.stall_reported = true;
                        ready_indices.push(i);
                    }
                }
            }
            i += 1;
        }

        let mut wakes = Vec::new();
        let mut ri = 0usize;
        while ri < ready_indices.len() {
            let Some(&idx) = ready_indices.get(ri) else {
                break;
            };
            let seq = self.next_seq();
            if let Some(slot) = self.sessions.get(idx) {
                wakes.push(SemanticWake {
                    wake_seq: seq,
                    session_id: slot.session_id.clone(),
                    broker_offset: slot.last_offset,
                    kind: SemanticWakeKind::Stalled {
                        idle_ticks: slot.idle_ticks,
                    },
                });
            }
            ri += 1;
        }
        wakes
    }

    fn next_seq(&mut self) -> u64 {
        let proposed = self.wake_seq.saturating_add(1);
        self.wake_seq = sem_wake_seq_advance(self.wake_seq, proposed);
        self.wake_seq
    }

    fn find_session_idx(&self, session_id: &str) -> Option<usize> {
        let mut i = 0usize;
        while i < self.sessions.len() {
            if let Some(s) = self.sessions.get(i) {
                if s.session_id == session_id {
                    return Some(i);
                }
            }
            i += 1;
        }
        None
    }

    fn ensure_session_idx(&mut self, session_id: &str) -> Option<usize> {
        if let Some(idx) = self.find_session_idx(session_id) {
            return Some(idx);
        }
        if !self.register_session(session_id) {
            return None;
        }
        self.find_session_idx(session_id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clean_twins_and_stall_predicate_hold() {
        assert_eq!(sem_wake_seq_advance(4, 5), 5);
        assert_eq!(sem_wake_seq_advance(5, 2), 5);
        assert_eq!(sem_idle_ticks_clamp(3, 10), 3);
        assert_eq!(sem_idle_ticks_clamp(15, 10), 10);
        assert!(sem_stall_reached(10, 10));
        assert!(!sem_stall_reached(9, 10));
    }

    #[test]
    fn classifies_command_outcomes_and_emits_one_shot_stall_until_activity() {
        let mut mux = SemanticWakeMux::new(3);
        let w1 = mux
            .ingest_event("s-alpha", 10, &SessionEvent::CommandStart { offset: 10 })
            .unwrap();
        assert_eq!(w1.wake_seq, 1);
        assert_eq!(w1.kind, SemanticWakeKind::CommandStarted);

        // Two idle ticks: below stall_limit=3.
        assert!(mux.tick_idle().is_empty());
        assert!(mux.tick_idle().is_empty());

        // Third idle tick hits stall_limit=3 -> emits one-shot Stalled wake.
        let stalled = mux.tick_idle();
        assert_eq!(stalled.len(), 1);
        assert_eq!(stalled[0].wake_seq, 2);
        assert_eq!(stalled[0].kind, SemanticWakeKind::Stalled { idle_ticks: 3 });

        // Fourth idle tick does NOT spam a duplicate Stalled wake.
        assert!(mux.tick_idle().is_empty());

        // New output activity resets the stall state, allowing another 3-tick window.
        mux.note_activity("s-alpha", 14);
        assert!(mux.tick_idle().is_empty());
        assert!(mux.tick_idle().is_empty());
        let stalled_again = mux.tick_idle();
        assert_eq!(stalled_again.len(), 1);
        assert_eq!(stalled_again[0].wake_seq, 3);
        assert_eq!(stalled_again[0].broker_offset, 14);

        // Non-zero exit classifies as CommandFailed and clears executing state so idle ticks stop.
        let w_end = mux
            .ingest_event(
                "s-alpha",
                20,
                &SessionEvent::CommandEnd {
                    offset: 20,
                    exit: Some(2),
                },
            )
            .unwrap();
        assert_eq!(w_end.wake_seq, 4);
        assert_eq!(w_end.kind, SemanticWakeKind::CommandFailed { exit_code: 2 });
        for _ in 0..5 {
            assert!(mux.tick_idle().is_empty());
        }
    }
}
