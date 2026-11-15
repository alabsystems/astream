// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Unicode UAX #29 ZWJ grapheme cluster byte budget, VS15/VS16 emoji width resolver, East Asian Ambiguous width toggle, Trojan-Source bidirectional control sanitizer, VT `HTS`/`TBC` tabstop bitmap, and Metal glyph-atlas LRU. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod atlas_glyph_lru;
pub mod bidi_isolate_guard;
pub mod east_asian_ambig;
pub mod tabstop_bitmap;
pub mod vs16_emoji_width;
pub mod zwj_cluster_budget;
