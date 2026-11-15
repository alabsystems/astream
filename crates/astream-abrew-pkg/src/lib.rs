// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `atpkg` / `abrew` content-addressed bottle SHA-256 verification, stale `trust` rustup link repair planner, `brew --real` bypass refusal, `Brewfile` topological sorting, active `aterm` binary overwrite shield, and compiler lane probing. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod bottle_sha_verify;
pub mod brewfile_toposort;
pub mod reroute_refusal;
pub mod self_binary_shield;
pub mod target_lane_probe;
pub mod toolchain_link_check;
