// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The astream-term integration tests, linked as ONE test binary: each module here
//! was a `tests/*.rs` file of its own, and every one of those was a separate link
//! of this crate and its dependencies. Run one module with
//! `targo --unverified test -p astream-term --test suite -- <module>::`.

#[path = "suite/bce.rs"]
mod bce;
#[path = "suite/events.rs"]
mod events;
#[path = "suite/lr_margins.rs"]
mod lr_margins;
#[path = "suite/perceive.rs"]
mod perceive;
#[path = "suite/predict.rs"]
mod predict;
#[path = "suite/render.rs"]
mod render;
#[path = "suite/screen_fold.rs"]
mod screen_fold;
#[path = "suite/screen_ops.rs"]
mod screen_ops;
#[path = "suite/scroll_region.rs"]
mod scroll_region;
#[path = "suite/underline.rs"]
mod underline;
#[path = "suite/wide.rs"]
mod wide;
