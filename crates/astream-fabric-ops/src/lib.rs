// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Fabric operational routing, prefix-indexed Last scanning, presence leases, barrier quorum routing, CRC32 binary payload chunking, cruise cadence control, and RFC 6962 Merkle audit proofs. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod barrier_route;
pub mod binbody;
pub mod cruise_cadence;
pub mod last_index;
pub mod merkle_proof;
pub mod presence;
