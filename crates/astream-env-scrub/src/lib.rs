// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm` child-shell AI environment variable stripper (`CLAUDE*`..`_DEVTOOL_*`), `${VAR:?}` fail-safe `rm` operand guard, inline secret argv refusal, session-env detection, `restart pid=` validation, and `NEEDS YOU:` banner multiplexing. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod argv_secret_refusal;
pub mod aterm_detect_probe;
pub mod needs_you_banner_mux;
pub mod provider_env_strip;
pub mod restart_pid_validator;
pub mod rm_var_fail_safe;
