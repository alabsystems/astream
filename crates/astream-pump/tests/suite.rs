// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The astream-pump integration tests, linked as ONE test binary: each module here
//! was a `tests/*.rs` file of its own, and every one of those was a separate link
//! of this crate and its dependencies. Run one module with
//! `targo --unverified test -p astream-pump --test suite -- <module>::`.

#[path = "suite/aspump_argv.rs"]
mod aspump_argv;
#[path = "suite/aspump_cli.rs"]
mod aspump_cli;
#[path = "suite/aspump_stderr_status.rs"]
mod aspump_stderr_status;
#[path = "suite/aspump_transports.rs"]
mod aspump_transports;
#[path = "suite/nested_claude_drive.rs"]
mod nested_claude_drive;
#[path = "suite/pump.rs"]
mod pump;
#[path = "suite/wake_adapters.rs"]
mod wake_adapters;
