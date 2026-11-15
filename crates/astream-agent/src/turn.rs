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

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "turn_island.rs"]
mod turn_island;
#[cfg(not(clean_islands))]
pub use crate::twins::turn_step_advance;
#[cfg(clean_islands)]
pub use turn_island::turn_step_advance;

contract_fn! {
    /// Verified check that an encoded action tag represents [`Action::Finish`] (`action_tag == 2`),
    /// linked via `clean-kernel-defeq` to `turn_action_is_finish_isl`.
    #[must_use]
    pub const fn turn_action_is_finish(action_tag: u8) -> bool
    clauses [ensures result == (action_tag == 2)]
    {
        action_tag == 2
    }
}

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

impl Action {
    /// Wire tag for this action in [`trace_bytes`].
    #[must_use]
    pub const fn tag(self) -> u8 {
        match self {
            Action::Speak => 0,
            Action::CallTool => 1,
            Action::Finish => 2,
        }
    }

    /// Whether this action ends the turn.
    #[must_use]
    pub const fn is_finish(self) -> bool {
        matches!(self, Action::Finish)
    }
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
    let mut cur_step = 0u64;
    let mut rest = records;
    let mut i = 0u64;
    while let [record, tail @ ..] = rest {
        cur_step = turn_step_advance(cur_step, i);
        let step = cur_step as u32;
        let action = planner.decide(step, record);
        decisions.push(Decision { step, action });
        painted.extend_from_slice(record.display());
        painted.extend_from_slice(b"\r\n");
        if action.is_finish() {
            break; // STOP — later records are not reached or painted.
        }
        i = i.saturating_add(1);
        rest = tail;
    }
    let scr = screen::fold(cols, rows, &[Record::Out(painted)]);
    (decisions, scr)
}

/// Encode one 5-byte [`Decision`] entry `(step: u32 LE, action_tag: u8)`.
#[inline]
#[must_use]
pub const fn encode_decision(d: Decision) -> [u8; 5] {
    let s = d.step;
    let tag = match d.action {
        Action::Speak => 0,
        Action::CallTool => 1,
        Action::Finish => 2,
    };
    [
        s as u8,
        (s >> 8) as u8,
        (s >> 16) as u8,
        (s >> 24) as u8,
        tag,
    ]
}

/// Decode one 5-byte [`Decision`] entry into `(step: u32, action_tag: u8)`.
#[inline]
#[must_use]
pub const fn decode_decision(raw: &[u8; 5]) -> (u32, u8) {
    let step = (raw[0] as u32)
        | ((raw[1] as u32) << 8)
        | ((raw[2] as u32) << 16)
        | ((raw[3] as u32) << 24);
    (step, raw[4])
}

/// Serialize the **decision trace** (not the raw records) to bytes — so mutating
/// the planner changes this, which is what keeps the replay oracle non-vacuous.
pub fn trace_bytes(decisions: &[Decision]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut rest = decisions;
    while let [d, tail @ ..] = rest {
        out.extend_from_slice(&encode_decision(*d));
        rest = tail;
    }
    out
}

/// A content address for a decision trace (FNV-1a over [`trace_bytes`]).
pub fn trace_fnv(decisions: &[Decision]) -> u64 {
    fnv1a_64(trace_bytes(decisions).as_slice())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trace_bytes_is_step_le_then_action_tag_per_decision() {
        assert!(trace_bytes(&[]).is_empty());
        let trace = [
            Decision {
                step: 0,
                action: Action::Speak,
            },
            Decision {
                step: 0x0102_0304,
                action: Action::CallTool,
            },
            Decision {
                step: u32::MAX,
                action: Action::Finish,
            },
        ];
        assert_eq!(
            trace_bytes(&trace),
            [
                0, 0, 0, 0, 0, //
                4, 3, 2, 1, 1, //
                0xFF, 0xFF, 0xFF, 0xFF, 2,
            ]
        );
    }
}
