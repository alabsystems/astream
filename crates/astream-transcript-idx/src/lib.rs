// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Sparse `step_index` byte-offset `.jsonl` trajectory index, `truncated_fields` selective hydration from `transcript_full.jsonl`, media URI manifest tracking, `/compact` anchor retention, `conversation://` link extraction, and rolling CRC-32 seals. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod context_compactor;
pub mod jsonl_step_index;
pub mod media_uri_manifest;
pub mod step_crc_checkpoint;
pub mod subagent_link_scan;
pub mod truncation_resolver;
