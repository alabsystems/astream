// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! PTY `TIOCSWINSZ` resize-epoch synchronization, master-FD read-pause flow watermarks, bracketed-paste close-marker sanitization, foreground signal escalation, split-chunk UTF-8 carry, and `OSC 52` clipboard ACLs. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod osc_clipboard_acl;
pub mod paste_chunker;
pub mod pty_flow_watermark;
pub mod signal_coalesce;
pub mod utf8_boundary_hold;
pub mod winsize_epoch;
