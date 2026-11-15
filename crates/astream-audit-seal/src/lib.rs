// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Forward-secure HMAC/HKDF key-epoch ratcheting, domain-separated SHA-256 hash-chain links, M-of-N witness checkpoint cosigning, commitment-preserving payload redaction tombstones, WORM compliance holds, and logarithmic tamper bisection. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod audit_chain_link;
pub mod checkpoint_cosign;
pub mod compliance_hold;
pub mod ratchet_key_epoch;
pub mod redact_tombstone;
pub mod tamper_bisect;
