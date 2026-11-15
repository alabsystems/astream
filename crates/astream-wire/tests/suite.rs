// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The astream-wire integration tests, linked as ONE test binary: each module here
//! was a `tests/*.rs` file of its own, and every one of those was a separate link
//! of this crate and its dependencies. Run one module with
//! `targo --unverified test -p astream-wire --test suite -- <module>::`.

#[path = "suite/filter_containment.rs"]
mod filter_containment;
#[path = "suite/router_differential.rs"]
mod router_differential;
#[path = "suite/steps.rs"]
mod steps;
#[path = "suite/summary.rs"]
mod summary;
