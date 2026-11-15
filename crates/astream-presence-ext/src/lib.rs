// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Extended DESIGN-aterm-fabric §4.2 presence fields (driving, watchers, parent, autopilot), §5.4 busy/absent barrier auto-responder, EVENT turn by= driver provenance, watcher lag shedding, parent trees, and autopilot cadence gates. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod autopilot_gate;
pub mod busy_auto_ack;
pub mod parent_tree;
pub mod presence_v2;
pub mod turn_provenance;
pub mod watcher_fanout;
