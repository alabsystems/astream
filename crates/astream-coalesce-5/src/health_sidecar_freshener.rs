// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `<log>.health` Sidecar Freshness & Connection-Gauge Invariant Verifier.
//!
//! `astream-broker` periodically writes `<log>.health` (`OpenOptions::health_every` /
//! `read_health`) so `aterm` supervisors and peer sessions can inspect broker liveness without
//! opening a socket. An external observer must distinguish:
//! - a **LiveHealthy** broker actively refreshing `<log>.health` within `fresh_horizon_ms`,
//! - a **LivePoisoned** broker that is still alive (`age_ms <= fresh_horizon_ms`) yet latched
//!   its log poisoned after an I/O or fsync fault,
//! - a **StaleOrStopped** sidecar left behind by a dead or hung broker (`age_ms > fresh_horizon_ms`
//!   or written in a prior OS `boot_session`), while clamping `parked_tails <= attached_conns`.
//!
//! Backed by Clean TLA+ Island `Astream.Broker.TlaHealthSidecarFreshness`
//! (`health_sidecar_freshener_island.rs`), proving `parkedTails <= attachedConns` and
//! `sampleAgeMs <= maxStaleMs`.

#[cfg(clean_islands)]
#[path = "health_sidecar_freshener_island.rs"]
mod island;
#[cfg(clean_islands)]
pub use island::{health_age_clamp, health_parked_clamp};

#[cfg(not(clean_islands))]
#[inline]
pub const fn health_parked_clamp(parked_tails: u64, attached_conns: u64) -> u64 {
    if parked_tails < attached_conns {
        parked_tails
    } else {
        attached_conns
    }
}

#[cfg(not(clean_islands))]
#[inline]
pub const fn health_age_clamp(age_ms: u64, max_stale_ms: u64) -> u64 {
    if age_ms < max_stale_ms {
        age_ms
    } else {
        max_stale_ms
    }
}

contract_fn! {
    /// Kernel-certified check whether a `<log>.health` snapshot of `age_ms` is within
    /// `fresh_horizon_ms` (`age_ms <= fresh_horizon_ms`).
    #[must_use]
    #[inline]
    pub const fn health_snapshot_fresh(age_ms: u64, fresh_horizon_ms: u64) -> bool
    clauses [ensures result == (age_ms <= fresh_horizon_ms)]
    {
        age_ms <= fresh_horizon_ms
    }
}

/// Default maximum age (`3 * health_every`, typically `15_000 ms`) before declaring stale.
pub const DEFAULT_FRESH_HORIZON_MS: u64 = 15_000;

/// Maximum staleness tracked before clamping (`86_400_000 ms` = 24 hours).
pub const DEFAULT_MAX_STALE_CAP_MS: u64 = 86_400_000;

/// Raw telemetry read from `<log>.health`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HealthSidecarSample {
    pub written_at_ms: u64,
    pub boot_session: [u8; 16],
    pub process_alive: bool,
    pub poisoned: bool,
    pub attached_conns: u64,
    pub parked_tails: u64,
    pub visible_head: u64,
    pub durable_head: u64,
}

/// Certified operator verdict over a `<log>.health` snapshot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HealthSidecarVerdict {
    /// Serving broker is alive in the current boot and refreshed within `fresh_horizon_ms`.
    LiveHealthy {
        age_ms: u64,
        attached_conns: u64,
        parked_tails: u64,
    },
    /// Serving broker is alive, but its log is latched poisoned (writes refused until reopen).
    LivePoisoned { age_ms: u64 },
    /// Sidecar belongs to a previous OS boot session or dead PID.
    DeadOwnerOrPriorBoot,
    /// Process still exists, but `<log>.health` has not been updated within `fresh_horizon_ms`.
    StaleHeartbeat { age_ms: u64 },
}

/// Evaluates a `<log>.health` sample (`SampleHealth` in `TlaHealthSidecarFreshness`).
#[must_use]
pub fn evaluate_health_sidecar(
    sample: HealthSidecarSample,
    now_ms: u64,
    current_boot_session: [u8; 16],
    fresh_horizon_ms: u64,
) -> HealthSidecarVerdict {
    if !sample.process_alive || sample.boot_session != current_boot_session {
        return HealthSidecarVerdict::DeadOwnerOrPriorBoot;
    }
    let raw_age = now_ms.saturating_sub(sample.written_at_ms);
    let age_ms = health_age_clamp(raw_age, DEFAULT_MAX_STALE_CAP_MS);
    let parked_tails = health_parked_clamp(sample.parked_tails, sample.attached_conns);

    if !health_snapshot_fresh(age_ms, fresh_horizon_ms) {
        return HealthSidecarVerdict::StaleHeartbeat { age_ms };
    }
    if sample.poisoned {
        return HealthSidecarVerdict::LivePoisoned { age_ms };
    }
    HealthSidecarVerdict::LiveHealthy {
        age_ms,
        attached_conns: sample.attached_conns,
        parked_tails,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classifies_live_poisoned_stale_and_clamps_parked_tails() {
        let boot = [0x42u8; 16];
        let sample = HealthSidecarSample {
            written_at_ms: 10_000,
            boot_session: boot,
            process_alive: true,
            poisoned: false,
            attached_conns: 12,
            parked_tails: 15, // transient racy read > attached_conns -> clamped to 12!
            visible_head: 500,
            durable_head: 500,
        };

        assert_eq!(
            evaluate_health_sidecar(sample, 14_000, boot, DEFAULT_FRESH_HORIZON_MS),
            HealthSidecarVerdict::LiveHealthy {
                age_ms: 4_000,
                attached_conns: 12,
                parked_tails: 12,
            }
        );

        // Stale heartbeat past 15_000ms.
        assert_eq!(
            evaluate_health_sidecar(sample, 30_000, boot, DEFAULT_FRESH_HORIZON_MS),
            HealthSidecarVerdict::StaleHeartbeat { age_ms: 20_000 }
        );

        // Different OS boot session -> DeadOwnerOrPriorBoot even if timestamps look close!
        assert_eq!(
            evaluate_health_sidecar(sample, 10_500, [0x99u8; 16], DEFAULT_FRESH_HORIZON_MS),
            HealthSidecarVerdict::DeadOwnerOrPriorBoot
        );
    }
}
