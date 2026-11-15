// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Modern VT and aterm terminal protocol extensions: soft-wrap grid reflow, OSC 8 hyperlinks, Kitty progressive keyboard, OSC 133 shell marks, OSC 52 clipboard guard, NEEDS YOU directives, and bracketed-paste sanitization. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod hyperlink;
pub mod kitty_kbd;
pub mod needs_you;
pub mod osc52;
pub mod paste_guard;
pub mod reflow;
pub mod shell_mark;
