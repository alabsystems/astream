#![forbid(unsafe_code)]
//! # astream-evidence
//!
//! The honesty harness that makes the predecessor's failure modes structurally
//! impossible in astream:
//!
//! * [`manifest`] — the evidence manifest: the single source of truth for
//!   every claim astream makes.
//! * [`runner`] — runs each claim's command and hashes its output, so a claim
//!   is true only if a re-runnable command says so.
//! * [`render`] — generates the README evidence table *from* the manifest, so
//!   a claim cannot cite an artifact the harness does not produce.
//! * [`gate`] — the merge-gate lints: undeclared cfg-features, git deps,
//!   drift/checkpoint markers, constant-only tests, doc tampering, and
//!   verification-workspace coupling.
//! * [`needles`] — builds the lint search strings from fragments so this
//!   crate's own source never trips its own lints.

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

pub mod gate;
pub mod manifest;
pub mod needles;
pub mod render;
pub mod runner;
pub mod timeout;

pub use gate::{gate_is_clean, gate_violation_advance};
pub use manifest::{manifest_claim_count_advance, manifest_has_claims};
pub use needles::{needle_clamp_count, needle_non_empty};
pub use render::{render_clamp_span_start, render_markers_ordered};
pub use timeout::{
    claim_elapsed_clamp, claim_timed_out, claim_timeout_floor, effective_claim_timeout_ms,
    run_command_with_timeout, BoundedCommandOutput, DEFAULT_CLAIM_TIMEOUT_SECS,
    MIN_CLAIM_TIMEOUT_MS,
};
