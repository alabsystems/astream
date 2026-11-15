// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The astream-evidence integration tests, linked as ONE test binary: each module here
//! was a `tests/*.rs` file of its own, and every one of those was a separate link
//! of this crate and its dependencies. Run one module with
//! `targo --unverified test -p astream-evidence --test suite -- <module>::`.

#[path = "suite/cli.rs"]
mod cli;
#[path = "suite/gate_tests.rs"]
mod gate_tests;
#[cfg(unix)]
#[path = "suite/stock_check.rs"]
mod stock_check;
#[path = "suite/trust_pin.rs"]
mod trust_pin;
#[cfg(unix)]
#[path = "suite/verify_ready.rs"]
mod verify_ready;
