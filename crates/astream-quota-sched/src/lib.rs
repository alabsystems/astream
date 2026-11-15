// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Multi-pool (`Gemini`, `Claude`, `GPT`) 5-hour and weekly rolling quota buckets, `aterm harness agy pick` low-pool model rotation, worker fanout admission, EWMA burn forecasting, and FNV-1a retry jitter. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod burn_rate_ewma;
pub mod cooldown_jitter;
pub mod fanout_admission;
pub mod model_rotator;
pub mod pool_window_5h;
pub mod pool_window_weekly;
