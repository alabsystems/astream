// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The astream-broker integration tests, linked as ONE test binary: each module here
//! was a `tests/*.rs` file of its own, and every one of those was a separate link
//! of this crate and its dependencies. Run one module with
//! `targo --unverified test -p astream-broker --test suite -- <module>::`.
//!
//! Kept as binaries of their own, because each needs its own process:
//! - `tests/cli_status_and_range.rs` serializes every spawn in its binary behind one
//!   lock (the macOS pipe() + FD_CLOEXEC race).
//! - `tests/sharded.rs` reads the PROCESS-wide fd table and serializes its own tests
//!   to keep it still.
//! - `tests/tail_retention.rs` reads the PROCESS's CPU time to prove an idle
//!   subscriber parks.
//! - `tests/replicated.rs` gives each follower round trip `FOLLOWER_TIMEOUT` (400 ms),
//!   which a real, fsyncing follower misses when this binary's other fsync-heavy tests
//!   run beside it: linked in here, four copies at once failed a round trip in 9 of 12
//!   runs, against 0 of 12 as a binary of its own.

#[path = "suite/agent_native.rs"]
mod agent_native;
#[path = "suite/anti_rollback.rs"]
mod anti_rollback;
#[path = "suite/any_connection.rs"]
mod any_connection;
#[path = "suite/asb_regressions.rs"]
mod asb_regressions;
#[path = "suite/at_rest.rs"]
mod at_rest;
#[path = "suite/at_rest_fixture.rs"]
mod at_rest_fixture;
#[path = "suite/aterm_fixture.rs"]
mod aterm_fixture;
#[path = "suite/aterm_retention.rs"]
mod aterm_retention;
#[path = "suite/attach_settled_bind.rs"]
mod attach_settled_bind;
#[path = "suite/barrier.rs"]
mod barrier;
#[path = "suite/blocking_accept.rs"]
mod blocking_accept;
#[path = "suite/brec_fixtures.rs"]
mod brec_fixtures;
#[path = "suite/broker_core_regressions.rs"]
mod broker_core_regressions;
#[path = "suite/broker_health.rs"]
mod broker_health;
#[path = "suite/broker_time_and_stats.rs"]
mod broker_time_and_stats;
#[path = "suite/cap_enforcement.rs"]
mod cap_enforcement;
#[path = "suite/cap_expiry.rs"]
mod cap_expiry;
#[path = "suite/cap_hardening.rs"]
mod cap_hardening;
#[path = "suite/cap_keyring.rs"]
mod cap_keyring;
#[path = "suite/certified_transport.rs"]
mod certified_transport;
#[path = "suite/clean_tla_protocol_surface.rs"]
mod clean_tla_protocol_surface;
#[path = "suite/cli_defects.rs"]
mod cli_defects;
#[path = "suite/cli_fleet.rs"]
mod cli_fleet;
#[path = "suite/cli_fleet_sealed.rs"]
mod cli_fleet_sealed;
#[path = "suite/cli_health.rs"]
mod cli_health;
#[path = "suite/cli_roundtrip.rs"]
mod cli_roundtrip;
#[path = "suite/cli_serve_durability.rs"]
mod cli_serve_durability;
#[path = "suite/cli_serve_guarded.rs"]
mod cli_serve_guarded;
#[path = "suite/cli_tcp.rs"]
mod cli_tcp;
#[path = "suite/client_idle_frame_atomic.rs"]
mod client_idle_frame_atomic;
#[path = "suite/client_regressions.rs"]
mod client_regressions;
#[path = "suite/client_sealed_idle.rs"]
mod client_sealed_idle;
#[path = "suite/client_sealed_resume.rs"]
mod client_sealed_resume;
#[path = "suite/conn_cap.rs"]
mod conn_cap;
#[path = "suite/cross_face_ack.rs"]
mod cross_face_ack;
#[path = "suite/dedup_bursts.rs"]
mod dedup_bursts;
#[path = "suite/dedup_short_producers.rs"]
mod dedup_short_producers;
#[path = "suite/exactly_once_e2e.rs"]
mod exactly_once_e2e;
#[path = "suite/exactly_once_pubsub_resume.rs"]
mod exactly_once_pubsub_resume;
#[cfg(unix)]
#[path = "suite/federation.rs"]
mod federation;
#[path = "suite/federation_push.rs"]
mod federation_push;
#[path = "suite/federation_relay.rs"]
mod federation_relay;
#[path = "suite/fetch.rs"]
mod fetch;
#[path = "suite/group_commit.rs"]
mod group_commit;
#[path = "suite/guarded_at_rest.rs"]
mod guarded_at_rest;
#[path = "suite/guarded_durability.rs"]
mod guarded_durability;
#[path = "suite/guarded_preauth.rs"]
mod guarded_preauth;
#[path = "suite/handshake_transport.rs"]
mod handshake_transport;
#[path = "suite/identity_transport.rs"]
mod identity_transport;
#[path = "suite/inbox_drain.rs"]
mod inbox_drain;
#[path = "suite/keepalive.rs"]
mod keepalive;
#[path = "suite/last_snapshot.rs"]
mod last_snapshot;
#[path = "suite/last_value.rs"]
mod last_value;
#[path = "suite/last_walk.rs"]
mod last_walk;
#[path = "suite/lifecycle.rs"]
mod lifecycle;
#[path = "suite/log_identity.rs"]
mod log_identity;
#[path = "suite/ordered_tier.rs"]
mod ordered_tier;
#[path = "suite/peer_probe.rs"]
mod peer_probe;
#[path = "suite/pipeline.rs"]
mod pipeline;
#[path = "suite/poisoned_log.rs"]
mod poisoned_log;
#[path = "suite/prepared_open.rs"]
mod prepared_open;
#[path = "suite/protocol_mismatch.rs"]
mod protocol_mismatch;
#[cfg(unix)]
#[path = "suite/rate_limit.rs"]
mod rate_limit;
#[path = "suite/relaxed_tier.rs"]
mod relaxed_tier;
#[path = "suite/replica_injection.rs"]
mod replica_injection;
#[path = "suite/replicated_retained_open.rs"]
mod replicated_retained_open;
#[path = "suite/replicated_retention.rs"]
mod replicated_retention;
#[path = "suite/replicated_transport.rs"]
mod replicated_transport;
#[path = "suite/request_bounds.rs"]
mod request_bounds;
#[path = "suite/retention.rs"]
mod retention;
#[path = "suite/retention_planner.rs"]
mod retention_planner;
#[path = "suite/roaming_transport.rs"]
mod roaming_transport;
#[path = "suite/sealed_transport.rs"]
mod sealed_transport;
#[path = "suite/settle.rs"]
mod settle;
#[path = "suite/sim_device.rs"]
mod sim_device;
#[cfg(unix)]
#[path = "suite/stale_socket.rs"]
mod stale_socket;
#[path = "suite/store_regressions.rs"]
mod store_regressions;
#[path = "suite/stream_link.rs"]
mod stream_link;
#[path = "suite/subscription_liveness.rs"]
mod subscription_liveness;
#[path = "suite/tail_chunks.rs"]
mod tail_chunks;
#[path = "suite/tail_wakes.rs"]
mod tail_wakes;
#[path = "suite/tcp_transport.rs"]
mod tcp_transport;
#[path = "suite/unclean_stop.rs"]
mod unclean_stop;
#[path = "suite/unlocked_write.rs"]
mod unlocked_write;
#[path = "suite/will.rs"]
mod will;
#[path = "suite/will_bound.rs"]
mod will_bound;
#[path = "suite/will_fence.rs"]
mod will_fence;
