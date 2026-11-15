// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The astream-engine integration tests, linked as ONE test binary: each module here
//! was a `tests/*.rs` file of its own, and every one of those was a separate link
//! of this crate and its dependencies. Run one module with
//! `targo --unverified test -p astream-engine --test suite -- <module>::`.

#[path = "suite/caused_by_retire.rs"]
mod caused_by_retire;
#[path = "suite/control_handoff.rs"]
mod control_handoff;
#[path = "suite/crash_recovery.rs"]
mod crash_recovery;
#[path = "suite/durable.rs"]
mod durable;
#[path = "suite/fleet_consistent_cut.rs"]
mod fleet_consistent_cut;
#[path = "suite/fleet_durable_watermark.rs"]
mod fleet_durable_watermark;
#[path = "suite/fork.rs"]
mod fork;
#[path = "suite/fork_prefix_stable.rs"]
mod fork_prefix_stable;
#[path = "suite/merkle_dag.rs"]
mod merkle_dag;
#[path = "suite/recorded.rs"]
mod recorded;
#[path = "suite/replay.rs"]
mod replay;
#[path = "suite/resume.rs"]
mod resume;
#[path = "suite/step_scan_parity.rs"]
mod step_scan_parity;
#[path = "suite/watermark_retire.rs"]
mod watermark_retire;
