//! The replay loop: drive an agent turn from a recorded transcript, **planner-driven**.
//!
//! The loop processes records in order, painting each onto the agent's screen,
//! until the policy [`Action::Finish`]es — records AFTER the finish are **not
//! reached** and **not painted**. That is the load-bearing property: a swapped
//! tool result that makes the policy finish early genuinely changes the screen, so
//! divergence is a consequence of *cognition*, not raw byte substitution.

use crate::cog::{CogRecord, StopReason};
use astream_term::{screen, Record, Screen};
use astream_wire::fnv1a_64;

/// What the policy decided to do at one step.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Action {
    /// Emit text and continue.
    Speak,
    /// Call a tool and continue to its result.
    CallTool,
    /// End the turn — later records are not reached.
    Finish,
}

/// One step of the decision trace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Decision {
    /// The record index this decision was made at.
    pub step: u32,
    /// The action taken.
    pub action: Action,
}

/// A turn policy. A real model is nondeterministic; a [`Planner`] is the fixed,
/// recorded **stand-in** that makes replay hermetic (it makes no model-fidelity
/// claim).
pub trait Planner {
    /// Decide what to do at `record` (the `step`-th record reached).
    fn decide(&mut self, step: u32, record: &CogRecord) -> Action;
}

/// The recorded replay policy: a content-keyed dispatcher. A completion that calls
/// a tool → `CallTool`; a completion that ends the turn → `Finish`; a tool result
/// that errored → `Speak` (keep going to recover); a clean tool result → `Finish`
/// (satisfied — so the recovery records are never reached).
pub struct ReplayPlanner;

impl Planner for ReplayPlanner {
    fn decide(&mut self, _step: u32, record: &CogRecord) -> Action {
        match record {
            CogRecord::Completion {
                stop: StopReason::EndTurn,
                ..
            } => Action::Finish,
            CogRecord::Completion { .. } => Action::CallTool,
            CogRecord::ToolResult { is_error: true, .. } => Action::Speak,
            CogRecord::ToolResult {
                is_error: false, ..
            } => Action::Finish,
        }
    }
}

/// A degenerate policy used ONLY as a mutation guard: it always finishes, so it
/// reaches exactly one record and yields a different decision trace — proving the
/// trace below is real decision content, not `f(x) == f(x)`.
pub struct ConstantPlanner;

impl Planner for ConstantPlanner {
    fn decide(&mut self, _step: u32, _record: &CogRecord) -> Action {
        Action::Finish
    }
}

/// Drive a turn planner-driven: process records until the policy finishes, paint
/// the reached records onto a screen via the `astream-term` fold, and return the
/// decision trace plus that screen.
pub fn run_turn<P: Planner>(
    planner: &mut P,
    records: &[CogRecord],
    cols: u16,
    rows: u16,
) -> (Vec<Decision>, Screen) {
    let mut decisions = Vec::new();
    let mut painted: Vec<u8> = Vec::new();
    for (i, record) in records.iter().enumerate() {
        let action = planner.decide(i as u32, record);
        decisions.push(Decision {
            step: i as u32,
            action,
        });
        painted.extend_from_slice(record.display());
        painted.extend_from_slice(b"\r\n");
        if action == Action::Finish {
            break; // STOP — later records are not reached or painted.
        }
    }
    let scr = screen::fold(cols, rows, &[Record::Out(painted)]);
    (decisions, scr)
}

/// Serialize the **decision trace** (not the raw records) to bytes — so mutating
/// the planner changes this, which is what keeps the replay oracle non-vacuous.
pub fn trace_bytes(decisions: &[Decision]) -> Vec<u8> {
    let mut out = Vec::with_capacity(decisions.len() * 5);
    for d in decisions {
        out.extend_from_slice(&d.step.to_le_bytes());
        out.push(match d.action {
            Action::Speak => 0,
            Action::CallTool => 1,
            Action::Finish => 2,
        });
    }
    out
}

/// A content address for a decision trace (FNV-1a over [`trace_bytes`]).
pub fn trace_fnv(decisions: &[Decision]) -> u64 {
    fnv1a_64(&trace_bytes(decisions))
}
