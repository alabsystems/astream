// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! HTTP `CONNECT` corporate-proxy framing, multiplexed stream credit flow control, HMAC-SHA256 NAT-traversal relay tickets, strict ALPN protocol version negotiation, `Closer` half-close TCP drain, and `SealedStream` record-aligned splice sizing. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod alpn_proto_select;
pub mod connect_proxy_frame;
pub mod derp_relay_ticket;
pub mod half_close_drain;
pub mod splice_zero_copy_meter;
pub mod ssh_mux_channel;
