// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Deterministic SplitMix64 fabric simulation packet scheduler, asymmetric network-partition matrix, `F_BARRIERFSYNC` power-loss epoch cutter, synthetic week-long retention bound mirror, partial-order history checker, and fault-schedule minimizer. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod linearizability_por;
pub mod partition_matrix;
pub mod power_loss_epoch;
pub mod prng_network_schedule;
pub mod retention_plan_mirror;
pub mod seed_minimizer;
