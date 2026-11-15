// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! External-authority cryptographic identity binding: OpenSSH ssh-ed25519-cert-v01@openssh.com validity and serial verification, OIDC claim mapping, dual-root CA rotation, CRL epochs, principal namespaces, and PoA delegation. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod ca_rotation;
pub mod crl_epoch;
pub mod oidc_claims;
pub mod openssh_cert;
pub mod poa_delegation;
pub mod principal_ns;
