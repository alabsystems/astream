// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Autonomous replicated-tier lease-heartbeat failover daemon, majority quorum witness tally, epoch fencing tokens, divergent-tail catchup, flap dampening, and crash-safe lineage cutover. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod candidate_quorum;
pub mod failover_cutover;
pub mod fencing_epoch;
pub mod flap_dampener;
pub mod lease_heartbeat;
pub mod replica_catchup;
