#![forbid(unsafe_code)]
//! `astream-agent` — the **Cognition** rung of the determinism dial: the summit.
//!
//! An agent turn's nondeterministic inputs — the model's completions and the tool
//! results the world returned — are recorded as a separate cognition log
//! ([`CogRecord`] framed in `COG_VERSION` envelopes, disjoint from the VT record
//! envelope). Replay is **hermetic**: no network, no live tools. A fixed,
//! hand-authored transcript is consumed by a [`Planner`]-driven loop whose
//! [`ReplayPlanner`] is a deterministic content-keyed **stand-in for model
//! cognition**, and the turn replays to a bit-identical decision trace and screen.
//! A counterfactual [`cog_fork_swap`] of one recorded tool result re-drives the
//! same fixed policy down a different branch.
//!
//! ### Honest boundary
//!
//! Replay re-FEEDS the model's recorded completion bytes and re-drives a fixed
//! recorded policy over the (possibly swapped) tool result; it does **not**
//! recompute the model or re-infer a completion. The `ReplayPlanner` is a labelled
//! stand-in, making no model-fidelity claim. The **record-with-live-API** pass is
//! non-hermetic (a real model call differs run to run) and is therefore never a
//! green claim; it is implemented in `astream-live` (`capture_live` via `curl`,
//! `capture_via_cli` via the `claude` CLI — both `#[ignore]`-gated) and feeds
//! [`replay_session`] here. Note that bridge captures the model's **completion**
//! only: the tool result and effect clock it assembles are caller-supplied
//! placeholders, not a real tool run under a recording seam — that seam-recorded
//! tool pass remains a documented seed.

pub mod cog;
pub mod envelope;
pub mod fixtures;
pub mod fork;
pub mod turn;
pub mod unified;

pub use astream_wire::Offset;
pub use cog::{CogRecord, StopReason, ToolUse};
pub use envelope::{CogEnvelope, CogError, COG_VERSION};
pub use fork::{cog_fork_swap, decode_turn, decode_turn_strict, record_turn, try_cog_fork_swap};
pub use turn::{
    run_turn, trace_bytes, trace_fnv, Action, ConstantPlanner, Decision, Planner, ReplayPlanner,
};
pub use unified::{fork_session, replay_session, Event, Replay};
