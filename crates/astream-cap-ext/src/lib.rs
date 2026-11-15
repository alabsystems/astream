// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Offline Macaroon sub-agent capability delegation, provenance chains, TOFU host pinning, forward-secret HChaCha20 symmetric ratcheting, agent receipt adapters, quota pools, and restart handoffs. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod adapter;
pub mod delegation;
pub mod handoff;
pub mod provenance;
pub mod quota_pool;
pub mod ratchet;
pub mod tofu;
