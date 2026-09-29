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
//!   is byte-identical, deterministically, from the tape alone.
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
//! Still open: tracing a separately-exec'd unmodified binary, a seccomp-bpf
//! pre-filter and full syscall neutralization for the foreign form, and durable
//! framing / offset-addressing of a standalone effects tape (today it is an
//! in-memory log).

pub mod demo;
pub mod record;
pub mod replay;
pub mod seam;

pub use demo::{oracle, run, tape_values};
pub use record::{OsEffects, RealEffects, RecordingSeam};
pub use replay::ReplaySeam;
pub use seam::{EffectRecord, EffectSeam, EffectsLog};
