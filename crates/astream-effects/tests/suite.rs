// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The astream-effects integration tests, linked as ONE test binary: each module here
//! was a `tests/*.rs` file of its own, and every one of those was a separate link
//! of this crate and its dependencies. Run one module with
//! `targo --unverified test -p astream-effects --test suite -- <module>::`.

#[path = "suite/cooperative_replay.rs"]
mod cooperative_replay;
#[path = "suite/exchange_replay.rs"]
mod exchange_replay;
#[path = "suite/keyed_view.rs"]
mod keyed_view;
