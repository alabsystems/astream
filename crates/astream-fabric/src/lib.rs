// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Fabric replication, peer mesh routing, fan-out caching, cold-prefix RAM eviction, frame delta compression, and adaptive reconnect backoff over astream-broker. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod backoff;
pub mod cold_page;
pub mod delta;
pub mod fanout;
pub mod held_sync;
pub mod mesh;
