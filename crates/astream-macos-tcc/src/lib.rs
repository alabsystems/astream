// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! macOS TCC privacy-consent folder/volume fence, cross-app `defaults`/container guard, `EPERM` privacy classifier, `syspolicyd=stuck` deadlock detector, live `~/.local/bin/aterm` overwrite blocker, and FDA epoch tracker. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod defaults_domain_guard;
pub mod eperm_privacy_classifier;
pub mod fda_grant_epoch;
pub mod live_bundle_install_guard;
pub mod protected_folder_fence;
pub mod syspolicyd_deadlock_probe;
