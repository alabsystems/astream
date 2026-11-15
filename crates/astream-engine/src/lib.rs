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

pub mod control;
pub mod dag;
pub mod distributed;
pub mod durable;
pub mod effects;
pub mod envelope;
pub mod fleet;
pub mod fork;
pub mod log;
pub mod merkle;
pub mod session;
pub mod store;

pub use astream_wire::Offset;
pub use control::{control_handoff_holder, holder_matches, ControlToken};
pub use dag::{
    dag_committed_advance, dag_deps_satisfied, decode_dag_record, encode_dag_record, DagError,
    DagJournal, DagJournalFault, DagSpec, DagStep, DAG_HEADER_LEN, DAG_RECORD_MAGIC,
    DAG_RECORD_VERSION,
};
pub use distributed::{
    decode_lease_record, dist_lease_expired, dist_lease_expiry_advance, dist_winner_offset_min,
    encode_lease_record, ActiveLease, BusRecord, DistributedDag, DistributedFault,
    DistributedStepOutcome, DistributedWorkflow, InMemoryWorkflowBus, WorkflowBus, DIST_LEASE_LEN,
    DIST_LEASE_MAGIC, DIST_LEASE_VERSION, MAX_DISTRIBUTED_STEPS, MAX_WORKFLOW_PREFIX_BYTES,
};
pub use durable::{
    journal_admit_step_commit, journal_committed_monotone, journal_step_match_or_keep, scan_steps,
    step_matches_next, StepScan, WorkflowJournal, STEP_VERSION,
};
pub use effects::{
    logical_clock_advance_past_tick, logical_clock_at_max, Clock, Disk, Effects, LogicalClock,
    MemDisk, Net, Rng, Seeded, SplitMix64,
};
pub use envelope::{
    envelope_clamp_cause_len, envelope_version_valid, CausedBy, Envelope, EnvelopeError,
    ENV_VERSION,
};
pub use fleet::{
    cross_edges_from_logs, cut_includes, first_violation, fleet_clamp_to_cut, fleet_seq_within_cut,
    heal_cut, is_consistent, materialize_fleet_cut, replay_to_cut, resume_fleet_cut, CrossEdge,
    Cut, CutReplay, FleetError, FleetPartitionState, FleetSnapshot, Partition,
};
pub use fork::{fork_clamped_index, fork_index_in_bounds, try_fork_swap};
pub use log::{
    log_advance_offset_monotone, log_same_log_cause_valid, EngineError, Log, LogReader, ReadError,
};
pub use merkle::{
    compute_node_hash, diff_chains, lca, merge_input_branches, merkle_offset_matches,
    merkle_parent_count_clamp, CommitHash, MergeSide, MerkleChain, MerkleDiff, MerkleError,
    MerkleNode, MAX_MERKLE_PARENTS,
};
pub use session::{
    high_water_from_log, materialize, resume, session_bump_high_water, session_seq_is_duplicate,
    try_materialize, Session, StateSnapshot,
};
pub use store::{
    recover, store_advance_valid_len, store_seq_matches_expected, FaultKind, FileLog, LogFault,
    Poisoned, RecoverReport, Tail,
};

#[cfg(test)]
#[path = "metadata_validation_tests.rs"]
mod metadata_validation_tests;
