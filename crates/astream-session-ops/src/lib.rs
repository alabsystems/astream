// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Deterministic session operational primitives: fuel-metered WebAssembly MVP sandbox, workspace file-sync deltas, Linux seccomp-bpf replay filters, Chandy-Lamport bus cuts, flight-recorder step rings, fleet await barriers, and shared volume disk-room budgets. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod bus_cut;
pub mod disk_room;
pub mod filesync;
pub mod fleet_await;
pub mod flight_recorder;
pub mod seccomp;
pub mod wasm;
