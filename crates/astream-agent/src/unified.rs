//! The capstone: a whole session as **one log on one offset axis**, carrying all
//! four streams of the determinism dial — **Inputs**, **Outputs**, **Effects**,
//! and **Cognition** — replayed hermetically and forkable at any offset.
//!
//! This is that session's *hermetic* form: replay one recorded session to a
//! bit-identical (decision trace, screen, effect digest), then fork it on a single
//! recorded cognition record and watch **all four streams diverge coherently** —
//! because the loop is planner-driven, a swapped tool result that finishes the
//! turn early stops every later Input/Output/Effect/Cognition event from being
//! reached.
//!
//! The one thing this does NOT do is *capture* a live turn — that record pass
//! needs a live model call and is non-hermetic, so it is never a green claim. It
//! is implemented next door in `astream-live` (`capture_live` / `capture_via_cli`,
//! `#[ignore]`-gated) and feeds [`replay_session`] here. What is proven here is
//! that once recorded, the four streams are one replayable, forkable, auditable
//! object.

use crate::cog::CogRecord;
use crate::turn::{Action, Decision, Planner, ReplayPlanner};
use astream_effects::EffectRecord;
use astream_term::{frame_hash, screen, Record, Screen};

/// One event on the unified session offset axis — the four record kinds of a
/// Claude Code session, interleaved on ONE log.
#[derive(Debug, Clone, Eq)]
pub enum Event {
    /// An **Input** the agent issued (a keystroke/command). Recorded, does not paint.
    In(Vec<u8>),
    /// An **Output** the terminal produced. Paints the screen.
    Out(Vec<u8>),
    /// An **Effect** the agent/tool consumed (clock/rng/file).
    Effect(EffectRecord),
    /// A **Cognition** record (a completion or a tool result) — the decision layer.
    Cognition(CogRecord),
}

impl PartialEq for Event {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Event::In(a), Event::In(b)) | (Event::Out(a), Event::Out(b)) => {
                a.as_slice() == b.as_slice()
            }
            (Event::Effect(a), Event::Effect(b)) => a == b,
            (Event::Cognition(a), Event::Cognition(b)) => a == b,
            _ => false,
        }
    }
}

/// The result of replaying a unified session — one value per stream.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Replay {
    /// The cognition stream: the decision trace.
    pub decisions: Vec<Decision>,
    /// The inputs stream: how many `In` events were reached.
    pub inputs_applied: usize,
    /// The outputs stream: the screen folded from the reached `Out` events.
    pub screen: Screen,
    /// A content address for that screen (the "pixels", deterministically).
    pub screen_hash: u64,
    /// The effects stream: a digest of the reached effect records — kind- and
    /// path-aware, so `Clock(v)` and `Rand(v)` differ, and two file reads of the
    /// same bytes from different paths differ (see `fold_effect`).
    pub effect_digest: u64,
    /// How many events the policy reached before finishing.
    pub events_reached: usize,
}

const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "unified_island.rs"]
mod unified_island;
#[cfg(not(clean_islands))]
pub use crate::twins::unified_reached_advance;
#[cfg(clean_islands)]
pub use unified_island::unified_reached_advance;

contract_fn! {
    /// Verified check that a unified session fork index `at_idx` lies strictly within
    /// `0..len` (`at_idx < len`), linked via `clean-kernel-defeq` to `unified_fork_in_bounds_isl`.
    #[must_use]
    pub const fn unified_fork_in_bounds(at_idx: usize, len: usize) -> bool
    clauses [ensures result == (at_idx < len)]
    {
        at_idx < len
    }
}

pub(crate) const fn fold_u64(d: u64, v: u64) -> u64 {
    (d ^ v).wrapping_mul(FNV_PRIME)
}

pub(crate) const fn fold_bytes(d: u64, bytes: &[u8]) -> u64 {
    // Length-prefixed, so `path` and `bytes` cannot slide into each other.
    let mut acc = fold_u64(d, bytes.len() as u64);
    let mut rest = bytes;
    while let &[b, ref tail @ ..] = rest {
        acc = fold_u64(acc, b as u64);
        rest = tail;
    }
    acc
}

/// Fold one effect record into the digest. Every record mixes in a **kind tag**
/// first, then its full content — the clock/rand value, a file read's path AND
/// bytes (or path AND error kind), an exchange's door, request AND reply, an
/// output's door AND bytes, a raised flag's door AND false-read count. Without
/// the tag, `Effect(Clock(99))` swapped for `Effect(Rand(99))` (or for
/// `Effect(Mono(99))`) would digest identically; without the path, a read moved
/// to a different file with the same contents would; without the length
/// prefixes, an exchange whose door absorbed the head of its request would —
/// and `Replay` carries only this digest for the effects stream, so it must be
/// as discriminating as the record. The match is exhaustive on purpose: a new
/// record kind does not compile here until it has a tag of its own.
fn fold_effect(d: u64, e: &EffectRecord) -> u64 {
    match e {
        EffectRecord::Clock(c) => fold_u64(fold_u64(d, 1), *c),
        EffectRecord::Rand(r) => fold_u64(fold_u64(d, 2), *r),
        EffectRecord::File { path, bytes } => fold_bytes(
            fold_bytes(fold_u64(d, 3), path.as_bytes()),
            bytes.as_slice(),
        ),
        EffectRecord::FileErr { path, kind } => fold_bytes(
            fold_bytes(fold_u64(d, 4), path.as_bytes()),
            format!("{kind:?}").as_bytes(),
        ),
        EffectRecord::Mono(m) => fold_u64(fold_u64(d, 5), *m),
        EffectRecord::Exchange {
            door,
            request,
            reply,
        } => fold_bytes(
            fold_bytes(
                fold_bytes(fold_u64(d, 6), door.as_bytes()),
                request.as_slice(),
            ),
            reply.as_slice(),
        ),
        EffectRecord::Emit { door, bytes } => fold_bytes(
            fold_bytes(fold_u64(d, 7), door.as_bytes()),
            bytes.as_slice(),
        ),
        EffectRecord::Raised { door, false_reads } => {
            fold_u64(fold_bytes(fold_u64(d, 8), door.as_bytes()), *false_reads)
        }
    }
}

/// Replay a unified session, planner-driven: process events in order, driving the
/// [`ReplayPlanner`] on each cognition record and applying each Input/Output/Effect
/// to its stream, until the policy [`Action::Finish`]es — events AFTER the finish
/// are not reached. Returns one reconstructed value per stream.
pub fn replay_session(events: &[Event], cols: u16, rows: u16) -> Replay {
    let mut planner = ReplayPlanner;
    let mut decisions = Vec::new();
    let mut painted: Vec<u8> = Vec::new();
    let mut inputs = 0usize;
    let mut effect_digest = 0xcbf2_9ce4_8422_2325u64;
    let mut reached = 0u64;
    let mut rest = events;
    while let [ev, tail @ ..] = rest {
        // Both counters are bounded by `events.len()`, so saturation never engages;
        // it only removes an add that could wrap.
        reached = unified_reached_advance(reached, reached.saturating_add(1));
        match ev {
            Event::In(_) => inputs = inputs.saturating_add(1),
            Event::Out(bytes) => painted.extend_from_slice(bytes.as_slice()),
            Event::Effect(e) => effect_digest = fold_effect(effect_digest, e),
            Event::Cognition(rec) => {
                // The step is the count of decisions so far, as a `u32` like
                // `run_turn`'s `i as u32`: the value the old `step += 1` counter held
                // (wrapping, as its release build did, past `u32::MAX` decisions).
                let step = decisions.len() as u32;
                let action = planner.decide(step, rec);
                decisions.push(Decision { step, action });
                if matches!(action, Action::Finish) {
                    break; // STOP — later events are not reached.
                }
            }
        }
        rest = tail;
    }
    let scr = screen::fold(cols, rows, &[Record::Out(painted)]);
    let screen_hash = frame_hash(&scr);
    Replay {
        decisions,
        inputs_applied: inputs,
        screen: scr,
        screen_hash,
        effect_digest,
        events_reached: reached as usize,
    }
}

/// Counterfactual fork: replace the event at `at` — e.g. swap one recorded tool
/// result `BUILD FAILED` for `BUILD OK`. Out-of-range leaves the session unchanged.
pub fn fork_session(events: &[Event], at: usize, replacement: Event) -> Vec<Event> {
    let mut out = events.to_vec();
    if unified_fork_in_bounds(at, out.len()) {
        if let Some(slot) = out.get_mut(at) {
            *slot = replacement;
        }
    }
    out
}
