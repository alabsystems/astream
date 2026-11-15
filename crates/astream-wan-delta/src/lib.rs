// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Low-bandwidth WAN terminal delta transport: blank/uniform-SGR cell run-length encoding, per-row FNV-1a dirty bitmaps, RTT-adaptive FPS governing, single-loss XOR FEC parity shards, cursor-only fast-path frames, and path-MTU coalescing. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod adaptive_fps_tick;
pub mod cursor_only_fastpath;
pub mod keyframe_fec_parity;
pub mod mtu_frame_packer;
pub mod rle_blank_cells;
pub mod row_hash_diff;
