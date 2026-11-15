// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Multi-agent isolated worktree file-claim leases, rebase-and-test merge queue, `free>=room` LRU build-cache reclamation, macOS `syspolicyd=stuck` circuit breaker, TCC protected-folder path guard, and ticket-ordered `.cargo-build` lock fairness. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod build_lock_fairness;
pub mod file_claim_lease;
pub mod merge_queue_fifo;
pub mod pkg_cache_reclaim;
pub mod privacy_tcc_guard;
pub mod syspolicyd_circuit;
