// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! MCP JSON-RPC 2.0 `Content-Length` framing, request-id correlation, least-privilege tool allowlists, `file://` URI sandboxing, untrusted output tagging, and deterministic shadow replay. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod jsonrpc_frame;
pub mod mcp_id_correlator;
pub mod mcp_tape_dedup;
pub mod prompt_injection_tag;
pub mod resource_uri_jail;
pub mod tool_schema_acl;
