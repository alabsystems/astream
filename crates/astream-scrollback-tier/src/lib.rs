// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Tiered terminal scrollback page-ring allocator, cold run-block frame verifier, 64-bit trigram search bloom filter, logical resize-reflow viewport anchor, `?1049` alternate-screen isolation guard, and OSC 133 output folding. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod alt_screen_switcher;
pub mod command_output_fold;
pub mod lz4_block_frame;
pub mod page_ring_allocator;
pub mod reflow_cursor_anchor;
pub mod trigram_line_bloom;
