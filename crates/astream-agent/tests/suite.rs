// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The astream-agent integration tests, linked as ONE test binary: each module here
//! was a `tests/*.rs` file of its own, and every one of those was a separate link
//! of this crate and its dependencies. Run one module with
//! `targo --unverified test -p astream-agent --test suite -- <module>::`.

#[path = "suite/cognition.rs"]
mod cognition;
#[path = "suite/unified.rs"]
mod unified;
