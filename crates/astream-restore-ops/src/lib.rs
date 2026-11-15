// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Crash-restore region keyframe stride controller, zero-padded physical ring scanner, layout-version migration, dirty-cell coalescing, cold scrollback tiering, and boot-session crash seal verification. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod crash_seal_marker;
pub mod dirty_cell_coalesce;
pub mod keyframe_stride;
pub mod layout_migrator;
pub mod ring_wrap_cursor;
pub mod scrollback_tier;
