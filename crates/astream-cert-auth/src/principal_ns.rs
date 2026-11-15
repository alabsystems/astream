// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Enforced `n-<16 hex>` / `h-<slug>` / `a-<slug>` / `s-<service>` principal namespace isolator
//! (`DESIGN-aterm-fabric.md` §8.2, `cap.ring-ceiling`, `Astream.CertAuth.TlaPrincipalNs`).
//!
//! Prevents cross-class principal impersonation when external certificates or OIDC claims mint
//! fabric capabilities:
//! - `Node` (`n-<16 lowercase hex>`): must be exact 16 lowercase hex chars; cannot write halt faces.
//! - `Human` (`h-<slug>`): only class permitted to write fleet halt faces (`/f/<F>/fleet/halt`).
//! - `Agent` (`a-<slug>`) and `Service` (`s-<slug>`): strictly denied halt authority (`!may_halt`).

use astream_wire::Subject;

#[cfg(clean_islands)]
#[path = "principal_ns_island.rs"]
mod principal_ns_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ns_depth_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ns_bound_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use principal_ns_island::{ns_bound_advance, ns_depth_clamp};

/// Maximum subject segments inspected by [`PrincipalNamespaceGuard`].
pub const MAX_NAMESPACE_SEGMENTS: u64 = 8;

contract_fn! {
    /// Verified privilege check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ns_class_matches_isl`.
    #[must_use]
    pub const fn ns_class_matches(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Canonical principal class in an `aterm` fabric.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrincipalClass {
    Node,
    Human,
    Agent,
    Service,
}

impl PrincipalClass {
    #[must_use]
    const fn privilege_level(self) -> u64 {
        match self {
            Self::Human => 3,
            Self::Node => 2,
            Self::Service => 1,
            Self::Agent => 1,
        }
    }
}

fn valid_slug(s: &str) -> bool {
    if s.is_empty() || s.len() > 64 {
        return false;
    }
    for &b in s.as_bytes() {
        let ok = b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-' || b == b'_';
        if !ok {
            return false;
        }
    }
    true
}

#[allow(clippy::manual_range_contains)]
fn valid_lower_hex_16(s: &str) -> bool {
    if s.len() != 16 {
        return false;
    }
    for &b in s.as_bytes() {
        let ok = b.is_ascii_digit() || (b >= b'a' && b <= b'f');
        if !ok {
            return false;
        }
    }
    true
}

/// Parses and validates a strict `n-`, `h-`, `a-`, or `s-` principal identifier.
pub fn classify_principal(principal: &str) -> Result<PrincipalClass, &'static str> {
    if let Some(hex) = principal.strip_prefix("n-") {
        if valid_lower_hex_16(hex) {
            return Ok(PrincipalClass::Node);
        }
        return Err("node principal must be n-<16 lowercase hex>");
    }
    if let Some(slug) = principal.strip_prefix("h-") {
        if valid_slug(slug) {
            return Ok(PrincipalClass::Human);
        }
        return Err("invalid human principal slug");
    }
    if let Some(slug) = principal.strip_prefix("a-") {
        if valid_slug(slug) {
            return Ok(PrincipalClass::Agent);
        }
        return Err("invalid agent principal slug");
    }
    if let Some(slug) = principal.strip_prefix("s-") {
        if valid_slug(slug) {
            return Ok(PrincipalClass::Service);
        }
        return Err("invalid service principal slug");
    }
    Err("principal missing required n-/h-/a-/s- namespace prefix")
}

/// Stateful namespace isolator tracking checked bindings monotonically.
#[derive(Debug, Clone, Default)]
pub struct PrincipalNamespaceGuard {
    checked_epoch: u64,
}

impl PrincipalNamespaceGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self { checked_epoch: 0 }
    }

    /// Verifies whether `principal` is permitted by namespace class to publish onto `subject`.
    pub fn authorize_publish_namespace(
        &mut self,
        principal: &str,
        subject: &Subject,
    ) -> Result<PrincipalClass, &'static str> {
        let cls = classify_principal(principal)?;
        let mut segs: Vec<&str> = Vec::new();
        for seg in subject.as_str().split('/') {
            if !seg.is_empty() {
                segs.push(seg);
            }
        }
        let _clamped = ns_depth_clamp(segs.len() as u64, MAX_NAMESPACE_SEGMENTS);
        self.checked_epoch =
            ns_bound_advance(self.checked_epoch, self.checked_epoch.saturating_add(1));

        // `/f/<F>/fleet/halt` requires privilege_level >= 3 (`Human` only!).
        if segs.len() >= 4
            && segs.first() == Some(&"f")
            && segs.get(2) == Some(&"fleet")
            && segs.get(3) == Some(&"halt")
            && !ns_class_matches(cls.privilege_level(), 3)
        {
            return Err("only h-<human> principals may publish fleet halt directives");
        }
        // `/f/<F>/pub/<node>/...` published by a Node must match its own principal!
        if cls == PrincipalClass::Node
            && segs.len() >= 4
            && segs.first() == Some(&"f")
            && segs.get(2) == Some(&"pub")
            && segs.get(3) != Some(&principal)
        {
            return Err("node principal cannot spoof another node's pub/<node> face");
        }
        Ok(cls)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn principal_namespace_enforces_node_hex_human_only_halt_and_anti_spoofing() {
        let mut g = PrincipalNamespaceGuard::new();
        let halt = Subject::new("/f/alpha/fleet/halt").unwrap();
        assert_eq!(
            g.authorize_publish_namespace("h-andrew", &halt).unwrap(),
            PrincipalClass::Human
        );
        assert!(g.authorize_publish_namespace("a-claude", &halt).is_err());
        assert!(g
            .authorize_publish_namespace("n-0123456789abcdef", &halt)
            .is_err());
        assert!(classify_principal("n-SHORT").is_err());

        let own_pub = Subject::new("/f/alpha/pub/n-0123456789abcdef/s1/presence").unwrap();
        let other_pub = Subject::new("/f/alpha/pub/n-fedcba9876543210/s1/presence").unwrap();
        assert!(g
            .authorize_publish_namespace("n-0123456789abcdef", &own_pub)
            .is_ok());
        assert!(g
            .authorize_publish_namespace("n-0123456789abcdef", &other_pub)
            .is_err());
    }
}
