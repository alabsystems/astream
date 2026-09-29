#![forbid(unsafe_code)]
//! # astream-engine
//!
//! **Rung 1** of the astream-term plan (`docs/DESIGN-astream-term.md`, §2
//! ledger and §3 dial): the per-partition deterministic single-writer log,
//! pulled over an effect seam so determinism is load-bearing from the start.
//!
//! ## What it is
//!
//! A single-partition [`Log`] appends [`astream_term::Record`]s under an effect
//! seam ([`Effects`]: [`Clock`]/[`Rng`]/[`Disk`]/[`Net`]). Each record is stamped
//! with its own [`Offset`] and a `ts_logical` **read through the seam Clock at
//! append time** — a recorded input, never a live wall-clock read — then framed
//! as a versioned [`Envelope`] inside an `astream_wire::Frame` and written to the
//! seam [`Disk`]. [`Log::read_from`] is a genuinely separate read-by-offset pass
//! that decodes records back out of the stored bytes.
//!
//! ## The honesty boundary
//!
//! The rung-1 [`Disk`] is an in-memory buffer the same process reads back, so the
//! guarantee at that layer is **byte-codec and recorded-clock honesty**: two
//! seeded record passes produce byte-identical logs (including every recorded
//! `ts_logical`), and the screen folded from the *stored bytes* equals the live
//! screen. Rung 1.5 ([`store`]) adds the **Strict durability dial**: [`FileLog`]
//! fsyncs every append and [`recover`]s a torn tail on open — and *refuses* to
//! open over a mid-log fault (an unreadable envelope version, an out-of-sequence
//! record, a corrupt frame with intact frames after it) rather than truncating
//! acked records away — so a process killed mid-append comes back to the last
//! acked record. A recovered log is *continued* by [`Session::resume_from`], not
//! restarted. Still *not* a live PTY: the engine feeds captured records as seam
//! inputs.
//!
//! The layering: this crate is the apex of a diamond over the leaf crates
//! `astream-wire` (frame/offset) and `astream-term` (record/screen fold), which
//! have no dependencies of their own. The record envelope lives here because the
//! engine is the first layer that owns offsets and a clock.

pub mod control;
pub mod durable;
pub mod effects;
pub mod envelope;
pub mod fleet;
pub mod fork;
pub mod log;
pub mod session;
pub mod store;

pub use astream_wire::Offset;
pub use control::ControlToken;
pub use durable::{scan_steps, StepScan, WorkflowJournal, STEP_VERSION};
pub use effects::{Clock, Disk, Effects, LogicalClock, MemDisk, Net, Rng, Seeded, SplitMix64};
pub use envelope::{CausedBy, Envelope, EnvelopeError, ENV_VERSION};
pub use fleet::{
    cross_edges_from_logs, cut_includes, is_consistent, replay_to_cut, CrossEdge, Cut, CutReplay,
    Partition,
};
pub use fork::{fork_swap, record_session, try_fork_swap};
pub use log::{EngineError, Log, LogReader, ReadError};
pub use session::{
    high_water_from_log, materialize, resume, try_materialize, Session, StateSnapshot,
};
pub use store::{recover, FaultKind, FileLog, LogFault, RecoverReport, Tail};
