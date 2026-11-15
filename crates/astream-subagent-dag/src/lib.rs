// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Hierarchical subagent recursion/fanout caps, reactive wakeup inbox cursors, `inherit`/`branch`/`share` workspace isolation leases, bottom-up cascade reaping, token rollup, and SHA-256 handoff pins. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod conv_inbox_cursor;
pub mod depth_fanout_cap;
pub mod descendant_reaper;
pub mod handoff_digest_pin;
pub mod token_cost_rollup;
pub mod workspace_mode_lease;
