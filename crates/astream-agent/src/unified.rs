//! The capstone: a whole session as **one log on one offset axis**, carrying all
//! four streams of the determinism dial — **Inputs**, **Outputs**, **Effects**,
//! and **Cognition** — replayed hermetically and forkable at any offset.
//!
//! This is the master seed's *hermetic* form: replay one recorded session to a
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
#[derive(Debug, Clone, PartialEq, Eq)]
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

fn fold_u64(d: u64, v: u64) -> u64 {
    (d ^ v).wrapping_mul(FNV_PRIME)
}

fn fold_bytes(d: u64, bytes: &[u8]) -> u64 {
    // Length-prefixed, so `path` and `bytes` cannot slide into each other.
    let d = fold_u64(d, bytes.len() as u64);
    bytes.iter().fold(d, |a, &b| fold_u64(a, b as u64))
}

/// Fold one effect record into the digest. Every record mixes in a **kind tag**
/// first, then its full content — the clock/rand value, or a file read's path AND
/// bytes (or path AND error kind). Without the tag, `Effect(Clock(99))` swapped
/// for `Effect(Rand(99))` would digest identically; without the path, a read
/// moved to a different file with the same contents would — and `Replay` carries
/// only this digest for the effects stream, so it must be as discriminating as the
/// record.
fn fold_effect(d: u64, e: &EffectRecord) -> u64 {
    match e {
        EffectRecord::Clock(c) => fold_u64(fold_u64(d, 1), *c),
        EffectRecord::Rand(r) => fold_u64(fold_u64(d, 2), *r),
        EffectRecord::File { path, bytes } => {
            fold_bytes(fold_bytes(fold_u64(d, 3), path.as_bytes()), bytes)
        }
        EffectRecord::FileErr { path, kind } => fold_bytes(
            fold_bytes(fold_u64(d, 4), path.as_bytes()),
            format!("{kind:?}").as_bytes(),
        ),
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
    let mut step = 0u32;
    let mut reached = 0usize;
    for ev in events {
        reached += 1;
        match ev {
            Event::In(_) => inputs += 1,
            Event::Out(bytes) => painted.extend_from_slice(bytes),
            Event::Effect(e) => effect_digest = fold_effect(effect_digest, e),
            Event::Cognition(rec) => {
                let action = planner.decide(step, rec);
                decisions.push(Decision { step, action });
                step += 1;
                if action == Action::Finish {
                    break; // STOP — later events are not reached.
                }
            }
        }
    }
    let scr = screen::fold(cols, rows, &[Record::Out(painted)]);
    let screen_hash = frame_hash(&scr);
    Replay {
        decisions,
        inputs_applied: inputs,
        screen: scr,
        screen_hash,
        effect_digest,
        events_reached: reached,
    }
}

/// Counterfactual fork: replace the event at `at` — e.g. swap one recorded tool
/// result `BUILD FAILED` for `BUILD OK`. Out-of-range leaves the session unchanged.
pub fn fork_session(events: &[Event], at: usize, replacement: Event) -> Vec<Event> {
    let mut out = events.to_vec();
    if at < out.len() {
        out[at] = replacement;
    }
    out
}
