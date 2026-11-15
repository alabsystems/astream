// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bounded-step LastStep::Pending subject retirement history gated by visible_head, producer subject-budget reclaim across compaction, conditional Retire CAS classifiers, held-store spill ledgers, and Linux seccomp-bpf replay syscall neutralization. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod charge_reclaim;
pub mod held_floor_sync;
pub mod moot_cas;
pub mod pending_retire;
pub mod ptrace_abi_guard;
pub mod seccomp_neutralize;
