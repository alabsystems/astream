// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm` Autopilot `cruise`/`land` 6-spoke prompt rotator, duplicate-reply loop breaker, `Nothing left:` clean-git verifier, 10-minute human-turn yield, `@<sid>:<rev>` worker await, and strict `ATERM-TASK-DONE` gate. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod cruise_wheel_rotator;
pub mod done_token_gate;
pub mod human_turn_yield;
pub mod land_nothing_left;
pub mod repeat_reply_stopper;
pub mod worker_await_rev;
