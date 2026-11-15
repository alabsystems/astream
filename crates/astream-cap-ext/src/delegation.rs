// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Offline Macaroon sub-agent capability delegation & hop-depth attenuation builder
//! (`Astream.Cap.TlaSubagentDelegation`).
//!
//! Enables a parent session or supervisor (`aterm ctl @self spawn`) holding a root or
//! already-attenuated [`Capability`] to mint strictly narrower worker capabilities
//! (mode downgrade, principal binding, TTL expiry tightening, and subject subtree
//! scoping) **without** possessing the broker's master HMAC secret, while enforcing
//! [`MAX_MACAROON_DEPTH`] hop limits and non-escalating expiry bounds.

#![allow(clippy::manual_map, clippy::question_mark)]

use astream_cap::{
    attenuate_offline, attenuation_depth, effective_bounded_expiry_ms, Capability, Grant, Mode,
    MAX_MACAROON_DEPTH,
};

fn valid_principal(p: &str) -> bool {
    Grant::parse(&format!("rw,p={p}:/a")).is_ok()
}

#[cfg(clean_islands)]
#[path = "delegation_island.rs"]
mod delegation_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn delegation_hop_clamp(hops: u64, max_hops: u64) -> u64 {
    if hops < max_hops {
        hops
    } else {
        max_hops
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn delegation_expiry_tighten(parent_exp: u64, child_exp: u64) -> u64 {
    if child_exp < parent_exp {
        child_exp
    } else {
        parent_exp
    }
}
#[cfg(clean_islands)]
pub use delegation_island::{delegation_expiry_tighten, delegation_hop_clamp};

contract_fn! {
    /// Kernel-certified Macaroon delegation hop-depth check (`hops <= max_hops`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `delegation_within_hops_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn delegation_within_hops(hops: usize, max_hops: usize) -> bool
    clauses [ensures result == (hops <= max_hops)]
    {
        hops <= max_hops
    }
}

/// Specification for deriving an offline-attenuated sub-agent [`Capability`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubagentSpec {
    /// Target mode (`ReadOnly` or `ReadWrite`). Must not widen a `ReadOnly` parent.
    pub mode: Mode,
    /// Optional bound principal (e.g. `"a-worker1"` or `"s-sub42"`). If the parent
    /// already binds a principal, `None` inherits the parent's principal automatically.
    pub principal: Option<String>,
    /// Target subject filter subtree (must be contained in the parent's filter).
    pub filter: String,
    /// Requested relative time-to-live in milliseconds from `now_ms`. Tightened
    /// automatically against any shorter ancestor `exp=` via [`delegation_expiry_tighten`].
    pub ttl_ms: Option<u64>,
}

impl SubagentSpec {
    /// Construct a read-only observer sub-agent capability spec for `filter`.
    #[must_use]
    pub fn read_only(filter: &str) -> Self {
        Self {
            mode: Mode::ReadOnly,
            principal: None,
            filter: filter.to_string(),
            ttl_ms: None,
        }
    }

    /// Construct a read-write worker sub-agent capability spec for `filter`.
    #[must_use]
    pub fn read_write(filter: &str) -> Self {
        Self {
            mode: Mode::ReadWrite,
            principal: None,
            filter: filter.to_string(),
            ttl_ms: None,
        }
    }

    /// Bind writes on this delegated capability to `principal` (`s-*`, `n-*`, `h-*`, `a-*`).
    #[must_use]
    pub fn with_principal(mut self, principal: &str) -> Self {
        self.principal = Some(principal.to_string());
        self
    }

    /// Bound the delegated capability's lifetime to `ttl_ms` from `now_ms`.
    #[must_use]
    pub const fn with_ttl_ms(mut self, ttl_ms: u64) -> Self {
        self.ttl_ms = Some(ttl_ms);
        self
    }
}

/// Count the number of `via=` Macaroon delegation hops already present in `grant`,
/// or `None` if `grant` is malformed or exceeds [`MAX_MACAROON_DEPTH`].
#[must_use]
pub fn delegation_hop_count(grant: &str) -> Option<usize> {
    attenuation_depth(grant)
}

/// Clamp a raw hop count to [`MAX_MACAROON_DEPTH`] using the Clean-verified transition.
#[must_use]
pub fn clamp_delegation_hops(raw_hops: usize) -> usize {
    delegation_hop_clamp(raw_hops as u64, MAX_MACAROON_DEPTH as u64) as usize
}

/// Derive a single offline-attenuated sub-agent [`Capability`] from `parent` at `now_ms`
/// without requiring the broker's master secret.
///
/// Automatically inherits any bound principal on `parent` when `spec.principal` is `None`,
/// tightens `now_ms + ttl_ms` against the ancestor chain's effective expiry so a longer
/// requested TTL never fails due to exceeding `parent`'s `exp=`, and refuses chains that
/// have already reached [`MAX_MACAROON_DEPTH`].
pub fn delegate_subagent_cap(
    parent: &Capability,
    spec: &SubagentSpec,
    now_ms: u64,
) -> Result<Capability, String> {
    let Some(hops) = delegation_hop_count(&parent.filter) else {
        return Err(
            "parent capability grant is malformed or exceeds max delegation hops".to_string(),
        );
    };
    let next_hops = hops.saturating_add(1);
    if !delegation_within_hops(next_hops, MAX_MACAROON_DEPTH) {
        let cap_hops = clamp_delegation_hops(next_hops);
        return Err(format!(
            "subagent delegation hop {next_hops} exceeds max macaroon depth {cap_hops}"
        ));
    }

    let parent_parsed = match Grant::parse(&parent.filter) {
        Ok(g) => g,
        Err(e) => return Err(e),
    };
    let eff_principal: Option<String> = match (&parent_parsed.principal, &spec.principal) {
        (Some(pp), None) => Some(pp.clone()),
        (Some(pp), Some(cp)) => {
            if pp != cp {
                return Err(format!(
                    "cannot rebind principal-bound parent {pp:?} to {cp:?}"
                ));
            }
            Some(cp.clone())
        }
        (None, Some(cp)) => {
            if !valid_principal(cp) {
                return Err(format!("invalid subagent principal {cp:?}"));
            }
            Some(cp.clone())
        }
        (None, None) => None,
    };

    let parent_eff_exp = effective_bounded_expiry_ms(&parent.filter, now_ms);
    if parent_eff_exp == Some(0) {
        return Err(format!(
            "parent capability chain has already expired at {now_ms}"
        ));
    }

    let requested_exp = match spec.ttl_ms {
        Some(ttl) => Some(now_ms.saturating_add(ttl)),
        None => None,
    };
    let eff_exp: Option<u64> = match (parent_eff_exp, requested_exp) {
        (Some(pe), Some(re)) => Some(delegation_expiry_tighten(pe, re)),
        (Some(pe), None) => Some(pe),
        (None, Some(re)) => Some(re),
        (None, None) => None,
    };
    if let Some(exp) = eff_exp {
        if exp <= now_ms {
            return Err(format!(
                "delegated subagent expiry {exp} is not after now_ms {now_ms}"
            ));
        }
    }

    let mode_tok = match spec.mode {
        Mode::ReadWrite => "rw",
        Mode::ReadOnly => "ro",
    };
    let mut prefix = String::from(mode_tok);
    if let Some(ref p) = eff_principal {
        prefix.push_str(",p=");
        prefix.push_str(p);
    }
    if let Some(exp) = eff_exp {
        prefix.push_str(&format!(",exp={exp}"));
    }
    let child_grant = format!("{prefix}:{}", spec.filter);
    attenuate_offline(parent, &child_grant, now_ms)
}

/// Mint a standard two-capability least-privilege ring for a spawned `aterm` worker:
/// 1. `ro` observer capability over `observe_filter` (e.g. `/f/lab/term/node1/>`), and
/// 2. `rw,p=<worker_principal>` writer capability over `write_filter` (e.g.
///    `/f/lab/in/node1/sid1/a-worker1/>`), both tightened to `ttl_ms` from `now_ms`.
pub fn delegate_worker_ring(
    parent: &Capability,
    worker_principal: &str,
    observe_filter: &str,
    write_filter: &str,
    ttl_ms: u64,
    now_ms: u64,
) -> Result<[Capability; 2], String> {
    let obs = SubagentSpec::read_only(observe_filter).with_ttl_ms(ttl_ms);
    let wr = SubagentSpec::read_write(write_filter)
        .with_principal(worker_principal)
        .with_ttl_ms(ttl_ms);
    let cap_obs = match delegate_subagent_cap(parent, &obs, now_ms) {
        Ok(c) => c,
        Err(e) => return Err(e),
    };
    let cap_wr = match delegate_subagent_cap(parent, &wr, now_ms) {
        Ok(c) => c,
        Err(e) => return Err(e),
    };
    Ok([cap_obs, cap_wr])
}

#[cfg(test)]
mod tests {
    use super::*;
    use astream_cap::{grants_filter, grants_publish, mint, producer_id_of, verify};

    #[test]
    fn clean_twins_and_hop_predicates_hold() {
        assert_eq!(delegation_hop_clamp(3, 8), 3);
        assert_eq!(delegation_hop_clamp(99, 8), 8);
        assert_eq!(delegation_expiry_tighten(5000, 3000), 3000);
        assert_eq!(delegation_expiry_tighten(5000, 9000), 5000);
        assert!(delegation_within_hops(8, 8));
        assert!(!delegation_within_hops(9, 8));
        assert_eq!(clamp_delegation_hops(20), MAX_MACAROON_DEPTH);
    }

    #[test]
    fn worker_ring_delegates_offline_and_verifies_on_broker_without_secret() {
        let secret = b"fleet-root-secret-32-bytes-exact";
        let root = mint(secret, "rw,exp=20000:/f/lab/>").unwrap();
        assert_eq!(delegation_hop_count(&root.filter), Some(0));

        // Requesting ttl_ms=50_000 from now_ms=1_000 (51_000 > 20_000) automatically
        // tightens to root's 20_000 expiry!
        let [obs, wr] = delegate_worker_ring(
            &root,
            "a-worker1",
            "/f/lab/term/node1/>",
            "/f/lab/in/node1/sid1/a-worker1/>",
            50_000,
            1_000,
        )
        .unwrap();

        assert_eq!(delegation_hop_count(&obs.filter), Some(1));
        assert_eq!(delegation_hop_count(&wr.filter), Some(1));
        assert!(verify(secret, &obs));
        assert!(verify(secret, &wr));

        // Observer can read `/f/lab/term/node1/out` at t=19_999, never write, and expires at 20_000.
        assert!(grants_filter(secret, &obs, "/f/lab/term/node1/out", 19_999));
        assert!(!grants_filter(
            secret,
            &obs,
            "/f/lab/term/node1/out",
            20_000
        ));
        assert!(!grants_publish(
            secret,
            &obs,
            "/f/lab/term/node1/out",
            producer_id_of("a-worker1"),
            1_500
        ));

        // Writer can publish only as `producer_id_of("a-worker1")` inside its scoped subtree.
        let pid_ok = producer_id_of("a-worker1");
        let pid_bad = producer_id_of("a-impostor");
        assert!(grants_publish(
            secret,
            &wr,
            "/f/lab/in/node1/sid1/a-worker1/cmd",
            pid_ok,
            1_500
        ));
        assert!(!grants_publish(
            secret,
            &wr,
            "/f/lab/in/node1/sid1/a-worker1/cmd",
            pid_bad,
            1_500
        ));
        assert!(!grants_publish(
            secret,
            &wr,
            "/f/lab/in/node1/sid2/a-worker1/cmd",
            pid_ok,
            1_500
        ));
    }

    #[test]
    fn multi_hop_delegation_enforces_max_macaroon_depth() {
        let secret = b"fleet-root-secret-32-bytes-exact";
        let mut cur = mint(secret, "rw:/>").unwrap();
        for hop in 1..=MAX_MACAROON_DEPTH {
            let spec = SubagentSpec::read_write("/a");
            cur = delegate_subagent_cap(&cur, &spec, 100).unwrap();
            assert_eq!(delegation_hop_count(&cur.filter), Some(hop));
            assert!(verify(secret, &cur));
        }
        // Hop MAX_MACAROON_DEPTH + 1 is deterministically refused by `delegation_within_hops`.
        let over = SubagentSpec::read_only("/a");
        assert!(delegate_subagent_cap(&cur, &over, 100).is_err());
    }
}
