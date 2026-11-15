// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Automatic multi-region federation mesh routing, SWIM-style incarnation peer discovery, EWMA RTT gateway selection, path-vector loop prevention, BDP WAN pacing, and graceful gateway drain. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod gateway_drain;
pub mod peer_gossip;
pub mod region_rtt;
pub mod split_horizon;
pub mod subtree_announce;
pub mod wan_pacing;
