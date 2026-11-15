// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The astream-host integration tests, linked as ONE test binary: each module here
//! was a `tests/*.rs` file of its own, and every one of those was a separate link
//! of this crate and its dependencies. Run one module with
//! `targo --unverified test -p astream-host --test suite -- <module>::`.
//!
//! Kept as binaries of their own, because each needs its own process:
//! - `tests/effects_foreign_process.rs` forks the test process itself (ptrace); the
//!   fewer threads beside the fork, the better.

#[path = "suite/drive.rs"]
mod drive;
#[path = "suite/orchestrate.rs"]
mod orchestrate;
#[path = "suite/pty_record_replay.rs"]
mod pty_record_replay;
