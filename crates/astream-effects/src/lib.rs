#![forbid(unsafe_code)]
//! `astream-effects` — the **Effects** rung of the determinism dial, cooperative form.
//!
//! A program written ONCE against [`EffectSeam`] (clock / randomness / file reads)
//! runs two ways over the same code:
//!
//! * a RECORD pass through [`RecordingSeam`] wrapping the real OS, which returns
//!   each live value and appends a typed [`EffectRecord`] to an [`EffectsLog`];
//! * a REPLAY pass through [`ReplaySeam`], which re-feeds the recorded values in
//!   consumption order and makes **no OS call at all** — so the program's output
//!   is byte-identical, deterministically, from the tape alone. A tape that cannot
//!   reproduce the run (short, wrong kind, different file) is refused with a typed
//!   [`ReplayDivergence`], never answered from the real world; one longer than the
//!   run is refused where the program ends, by [`ReplaySeam::finish`].
//!
//! This is the dial one notch below Cognition. Where
//! `astream_engine::effects::Effects` is the *pure seeded* seam the engine already
//! records through, this crate records the effects of a program touching the
//! *real* clock/rng/filesystem and replays them hermetically.
//!
//! ### Honest boundary
//!
//! This crate is byte-exact record/replay of a **seam-cooperative** program (one
//! that calls the seam). The **foreign-process** form — a forked, NON-cooperating
//! child whose syscalls a `ptrace` tracer intercepts (still an astream-authored
//! program written for the tracer: it self-attaches with `PTRACE_TRACEME` and
//! takes the raw syscall path, so it is NOT yet an unmodified binary) — is built
//! in `astream-host::foreign` (Linux, claim
//! `effects.foreign-process.record-replay`, platform-gated) and tapes into this
//! same [`EffectsLog`]. `astream-agent::unified` folds this same [`EffectRecord`]
//! type on ONE offset axis with the In/Out/Cognition streams (claim
//! `term.session.unified-replay-and-fork`) — but only the TYPE is shared today:
//! nothing feeds a foreign-process tape into that unified replay.
//!
//! ### The doors a program supplies the value for
//!
//! Beside the three backend doors (wall clock, randomness, files) the seam has a
//! monotonic clock ([`EffectSeam::mono_nanos`], its own record kind, never
//! interchangeable with the wall clock) and three doors whose live value the
//! PROGRAM hands in as a closure, because the seam cannot own every socket and
//! flag a program talks to:
//!
//! * [`exchange`](EffectSeam::exchange) — the socket-reply door: a request out,
//!   a reply back, taped as one [`EffectRecord::Exchange`]; replay returns the
//!   taped reply and never calls the closure;
//! * [`emit`](EffectSeam::emit) — an output, taped; replay compares instead of
//!   writing, so a replay that says something different is caught where it says
//!   it;
//! * [`raised`](EffectSeam::raised) — a sticky flag (a stop) another thread
//!   raises; only the first true read is taped, with the count of false reads
//!   before it, so polling a flag costs nothing until it rises. The door
//!   latches on every seam, so it suits a flag whose rise is final for the
//!   reader, not one its owner may lower again.
//!
//! [`LiveSeam`] runs the same program on the real world with no tape;
//! [`RecordingSeam::with_sink`] streams records to a writer instead of keeping
//! them; [`ReplaySeam::streaming`] replays from a reader instead of a `Vec`; and
//! [`KeyedView`] answers "what had this door replied to this request once the
//! program had read N records?" without consuming anything — the read-only
//! second reader a counterfactual re-decision needs beside the replay that
//! drives the program — and [`KeyedIndex`] is that index over records it
//! holds, built once and asked by every look of every decision re-decided on
//! one tape.
//!
//! Still open: tracing a separately-exec'd unmodified binary, a seccomp-bpf
//! pre-filter and full syscall neutralization for the foreign form, and durable
//! framing / offset-addressing of a standalone effects tape (today it is an
//! in-memory log or a caller's sink; a framing layer lives with its first
//! caller, so this crate still never needs the wire frame).

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

pub mod demo;
pub mod keyed;
pub mod record;
pub mod replay;
pub mod seam;
pub mod shadow;

pub use demo::{
    converse, converse_oracle, converse_values, demo_clamp_poll_index, demo_poll_in_range, oracle,
    run, tape_values, ConverseValues,
};
pub use keyed::{keyed_clamp_cutoff, keyed_hit_within_cutoff, KeyedIndex, KeyedReply, KeyedView};
pub use record::{
    record_mono_advance, record_seed_non_zero, LiveSeam, OsEffects, RealEffects, RecordSink,
    RecordingSeam,
};
pub use replay::{replay_cursor_in_bounds, replay_cursor_monotone, ReplayDivergence, ReplaySeam};
pub use seam::{
    seam_false_reads_advance, seam_false_reads_matches, EffectRecord, EffectSeam, EffectsLog,
};
pub use shadow::{
    shadow_code_in_range, shadow_code_select, shadow_exit_code, shadow_nonzero_bit,
    shadow_taint_latch, ShadowDecisionOutcome, ShadowEmit, ShadowLedger, ShadowNeed, ShadowPoint,
    ShadowSeam, MAX_SHADOW_EMITS, MAX_SHADOW_NEEDS, MAX_SHADOW_ROWS,
};
