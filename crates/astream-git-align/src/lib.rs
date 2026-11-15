// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bidirectional `git fetch && git rebase origin/main` divergence planner, pre-rebase file-disjointness fence, `aterm` `[OB-1]` vendored-crate drift auditor, `--locked` Cargo.lock guard, session-owned untracked sweep, and signed release manifests. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod conflict_file_fence;
pub mod ff_rebase_planner;
pub mod lockfile_drift_guard;
pub mod signed_tag_manifest;
pub mod untracked_sweep_filter;
pub mod vendor_pin_auditor;
