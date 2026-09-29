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

pub mod gate;
pub mod manifest;
pub mod needles;
pub mod render;
pub mod runner;
