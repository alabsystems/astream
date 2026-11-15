// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Terminal OSC 52 base64 clipboard budget, OSC 8 URI scheme sanitizer, OSC 133 semantic prompt zone state machine, Kitty graphics pixel-RAM quota, DEC `?2026` synchronized-output timeout flush, and `?2004` bracketed-paste armor. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod bracketed_paste_armor;
pub mod kitty_image_quota;
pub mod osc133_prompt_zones;
pub mod osc52_clipboard_budget;
pub mod osc8_uri_sanitizer;
pub mod synchronized_output_gate;
