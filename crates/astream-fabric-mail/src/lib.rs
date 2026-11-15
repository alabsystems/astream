// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm ctl @self inbox` and `aterm ctl survey` untrusted `PeerData` taint envelopes, bounded survey excerpt rings, monotone inbox ack cursors, prompt-injection fences, `@<sid> result` collectors, and `ctl ls` peer directory. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod inbox_cursor_ack;
pub mod mail_taint_envelope;
pub mod peer_session_directory;
pub mod prompt_injection_fence;
pub mod survey_excerpt_ring;
pub mod worker_result_collector;
