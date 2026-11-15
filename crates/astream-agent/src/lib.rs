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

// A contracted fn is written once, through `contract_fn!`: under a Trust compiler
// (`cfg(clean_islands)`, build.rs) it carries its `ensures` clause, which no stock rustc can
// parse, and every other compiler gets the plain fn.
#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

// Plain-Rust twins of the functions this crate's Clean islands compile, for a compiler
// that cannot lex the islands.
#[cfg(any(test, not(clean_islands)))]
mod twins;

pub mod cog;
pub mod envelope;
pub mod fixtures;
pub mod fleet;
pub mod foreign_tape;
pub mod fork;
pub mod turn;
pub mod unified;

pub use astream_wire::Offset;
pub use cog::{cog_clamp_call_count, cog_is_end_turn, CogRecord, StopReason, ToolUse};
pub use envelope::{
    envelope_clamp_call_cap, envelope_version_matches, CogEnvelope, CogError, COG_VERSION,
};
pub use fixtures::{fixture_clamp_transcript_len, fixture_has_expected_len};
pub use fleet::{
    fleet_causal_edges, fleet_cause_reached, fleet_clamp_cut_len, fork_fleet_session,
    replay_fleet_causal, replay_fleet_cut, AgentCause, AgentSession, FleetEvent, FleetReplay,
    FleetReplayError,
};
pub use foreign_tape::{
    decode_effects_tape_strict, encode_effects_tape, foreign_tape_clamp_records,
    foreign_tape_cursor_advance, foreign_tape_exhausted, replay_session_with_foreign_tape,
    splice_foreign_tape, EffectEnvelope, EffectTapeError, ForeignTapeSpliceError, ToolEffectSpan,
    EFFECT_TAPE_VERSION, MAX_EFFECT_FIELD_BYTES, MAX_FOREIGN_TAPE_RECORDS,
};
pub use fork::{
    cog_fork_prefix, cog_fork_swap, decode_turn, decode_turn_strict, fork_offset_in_range,
    fork_prefix_bound, record_turn, try_cog_fork_swap,
};
pub use turn::{
    run_turn, trace_bytes, trace_fnv, turn_action_is_finish, turn_step_advance, Action,
    ConstantPlanner, Decision, Planner, ReplayPlanner,
};
pub use unified::{
    fork_session, replay_session, unified_fork_in_bounds, unified_reached_advance, Event, Replay,
};
