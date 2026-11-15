// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Least-privilege capability-ring ceiling verification (`DESIGN-aterm-fabric.md` §8.2,
//! §9.3, and §14 Open Question 5).
//!
//! When an endpoint such as `aterm-link serve` or a person CLI loads a `--cap-file`,
//! verifying HMAC authenticity alone proves only that *someone with the mint secret*
//! issued the capabilities — it does **not** prevent an operator or test harness from
//! accidentally deploying an over-privileged fleet-root god cap (`rw:/f/<fleet>/>`)
//! onto a node or agent box.
//!
//! [`GrantCeiling`] enforces a least-privilege upper bound over a capability ring:
//! every capability in the ring must be **monotonically subsumed** ([`can_attenuate`])
//! by at least one rule in the ceiling across all four grant dimensions:
//! 1. **Mode** (`ReadOnly <= ReadWrite`, checked via [`ceiling_mode_subsumes`]),
//! 2. **Principal binding** (an unbound `None` grant is refused wherever the ceiling
//!    rule binds `p=<principal>`),
//! 3. **Expiry** (a non-expiring or later-expiring grant is refused when the ceiling
//!    rule sets `exp=<unix_ms>`), and
//! 4. **Subject subtree** (`ceiling_filter.contains(&member_filter)`).

use astream_wire::{Filter, Subject};

use crate::{
    can_attenuate, is_expired, parse_grant, valid_principal, verify, Capability, Grant, Mode,
};

#[cfg(clean_islands)]
#[path = "ceiling_island.rs"]
mod ceiling_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{ceiling_mode_subsumes_code, ceiling_rule_index_clamp};
#[cfg(clean_islands)]
pub use ceiling_island::{ceiling_mode_subsumes_code, ceiling_rule_index_clamp};

/// Maximum number of grant rules permitted in a single [`GrantCeiling`].
pub const MAX_CEILING_RULES: usize = 64;

/// Maximum number of capabilities verified in a single ring check.
pub const MAX_RING_CAPS: usize = 256;

contract_fn! {
    /// Kernel-certified rule-index bound check (`idx <= max_rules`).
    #[must_use]
    pub const fn ceiling_rule_within_cap(idx: u64, max_rules: u64) -> bool
    clauses [ensures result == (idx <= max_rules)]
    {
        idx <= max_rules
    }
}

/// Pure mode-subsumption predicate backed by the Clean-origin
/// [`ceiling_mode_subsumes_code`] kernel (`ReadOnly <= ReadWrite`).
#[must_use]
pub const fn ceiling_mode_subsumes(ceiling_mode: Mode, member_mode: Mode) -> bool {
    let c_rw = match ceiling_mode {
        Mode::ReadOnly => 0,
        Mode::ReadWrite => 1,
    };
    let m_rw = match member_mode {
        Mode::ReadOnly => 0,
        Mode::ReadWrite => 1,
    };
    ceiling_mode_subsumes_code(c_rw, m_rw) == 1
}

/// Reason a capability in a ring failed [`GrantCeiling`] verification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CeilingViolationKind {
    /// Ring exceeded [`MAX_RING_CAPS`].
    RingTooLarge { count: usize, max: usize },
    /// Grant string in the ring could not be parsed.
    MalformedGrant(String),
    /// Capability HMAC tag failed verification under the broker secret (`check_authenticated_ring`).
    UnauthenticatedTag,
    /// Capability has already expired at `now_ms` (`check_authenticated_ring`).
    Expired { now_ms: u64 },
    /// Capability is an unbound `ReadWrite` grant (god cap) not permitted by any ceiling rule.
    UnboundGodCap { closest_reason: String },
    /// Capability exceeds every rule in the ceiling (mode, principal, expiry, or filter scope).
    ExceedsCeiling { closest_reason: String },
}

/// Structured diagnostic naming the first capability in a ring that violated a [`GrantCeiling`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CeilingViolation {
    /// Zero-based index of the offending capability in the ring.
    pub index: usize,
    /// Grant string of the offending capability.
    pub grant: String,
    /// Detailed classification of why the capability was refused.
    pub kind: CeilingViolationKind,
}

impl core::fmt::Display for CeilingViolation {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match &self.kind {
            CeilingViolationKind::RingTooLarge { count, max } => write!(
                f,
                "capability ring has {count} entries, exceeding ceiling check limit {max}"
            ),
            CeilingViolationKind::MalformedGrant(err) => {
                write!(f, "ring[{idx}] {:?} is malformed: {err}", self.grant, idx = self.index)
            }
            CeilingViolationKind::UnauthenticatedTag => write!(
                f,
                "ring[{idx}] {:?} failed HMAC tag verification",
                self.grant,
                idx = self.index
            ),
            CeilingViolationKind::Expired { now_ms } => write!(
                f,
                "ring[{idx}] {:?} is expired at {now_ms} ms",
                self.grant,
                idx = self.index
            ),
            CeilingViolationKind::UnboundGodCap { closest_reason } => write!(
                f,
                "ring[{idx}] {:?} is an unbound read-write god capability outside ceiling ({closest_reason})",
                self.grant,
                idx = self.index
            ),
            CeilingViolationKind::ExceedsCeiling { closest_reason } => write!(
                f,
                "ring[{idx}] {:?} exceeds capability ceiling ({closest_reason})",
                self.grant,
                idx = self.index
            ),
        }
    }
}

impl std::error::Error for CeilingViolation {}

#[derive(Debug, Clone)]
struct CeilingEntry {
    raw: String,
    grant: Grant,
    filter: Filter,
}

/// Validated least-privilege capability ceiling (`1..=MAX_CEILING_RULES` grant rules).
#[derive(Debug, Clone)]
pub struct GrantCeiling {
    entries: Vec<CeilingEntry>,
}

fn validate_fleet_segment(fleet: &str) -> Result<(), String> {
    if fleet.is_empty() || fleet.len() > 64 {
        return Err(format!(
            "invalid fleet name {fleet:?}: expected 1..=64 ASCII bytes"
        ));
    }
    if fleet.contains('/') || fleet.contains('*') || fleet.contains('>') {
        return Err(format!(
            "invalid fleet name {fleet:?}: must be a single literal segment"
        ));
    }
    let probe = format!("/f/{fleet}");
    if Subject::new(&probe).is_err() {
        return Err(format!(
            "invalid fleet name {fleet:?}: rejected by subject grammar"
        ));
    }
    Ok(())
}

impl GrantCeiling {
    /// Parse and validate a non-empty slice of ceiling grant strings.
    pub fn parse<S: AsRef<str>>(rules: &[S]) -> Result<Self, String> {
        if rules.is_empty() {
            return Err("capability ceiling must contain at least one grant rule".to_string());
        }
        if !ceiling_rule_within_cap(rules.len() as u64, MAX_CEILING_RULES as u64) {
            return Err(format!(
                "capability ceiling has {} rules, exceeding max {MAX_CEILING_RULES}",
                rules.len()
            ));
        }
        let cap = rules.len().min(MAX_CEILING_RULES);
        let mut entries = Vec::with_capacity(cap);
        let mut rest = rules;
        while let [rule, ref tail @ ..] = rest {
            let raw_str = rule.as_ref().trim();
            let (grant, filter) = parse_grant(raw_str)?;
            entries.push(CeilingEntry {
                raw: raw_str.to_string(),
                grant,
                filter,
            });
            rest = tail;
        }
        Ok(Self { entries })
    }

    /// Parse a newline-delimited ceiling specification (blank lines and `#` comments ignored).
    pub fn parse_text(text: &str) -> Result<Self, String> {
        let mut lines: Vec<&str> = Vec::new();
        for raw_line in text.lines() {
            let trimmed = raw_line.trim();
            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }
            if lines.len() >= MAX_CEILING_RULES {
                return Err(format!(
                    "capability ceiling exceeds max {MAX_CEILING_RULES} rules"
                ));
            }
            lines.push(trimmed);
        }
        Self::parse(&lines)
    }

    /// Construct the canonical 8-grant `aterm-link` node ring ceiling for `(fleet, node)`
    /// (`DESIGN-aterm-fabric.md` §8.2). aterm mints a node's ring from its [`Self::rules`]
    /// and checks a ring it holds against it (§14 Open Question 5). No grant reaches
    /// `/f/<fleet>/term/`: the drive face those grants served is cut.
    ///
    /// The last two are the fleet-wide halts (aterm's one-mesh design, §4.11): the node reads
    /// every node's halt subject (`/f/<fleet>/halt/<node>`, each record signed by its origin
    /// and relayed to every member) and publishes on its own alone. It writes no other node's,
    /// and no person's halt row (`/f/<fleet>/fleet/>` stays read-only).
    pub fn aterm_node_ring(fleet: &str, node: &str) -> Result<Self, String> {
        validate_fleet_segment(fleet)?;
        if !node.starts_with("n-") || !valid_principal(node) {
            return Err(format!(
                "invalid node principal {node:?}: expected \"n-<id>\" principal"
            ));
        }
        let rules = [
            format!("rw,p={node}:/f/{fleet}/pub/{node}/>"),
            format!("ro:/f/{fleet}/pub/>"),
            format!("ro:/f/{fleet}/fleet/>"),
            format!("rw,p={node}:/f/{fleet}/in/*/*/{node}/*"),
            format!("ro:/f/{fleet}/in/{node}/>"),
            format!("rw,p={node}:/f/{fleet}/cur/{node}/>"),
            format!("ro:/f/{fleet}/halt/>"),
            format!("rw,p={node}:/f/{fleet}/halt/{node}"),
        ];
        Self::parse(&rules)
    }

    /// Construct the canonical `aterm-link` person ring ceiling for `(fleet, person)`:
    /// 6 grants for a human (`h-*`, including `/f/<fleet>/fleet/<person>/>` halt authority)
    /// and 5 grants for an agent/service (`a-*`, never permitted to write a fleet halt).
    /// aterm mints a person's ring from its [`Self::rules`].
    pub fn aterm_person_ring(fleet: &str, person: &str) -> Result<Self, String> {
        validate_fleet_segment(fleet)?;
        if (!person.starts_with("h-") && !person.starts_with("a-")) || !valid_principal(person) {
            return Err(format!(
                "invalid person principal {person:?}: expected \"h-<id>\" or \"a-<id>\""
            ));
        }
        let mut rules: Vec<String> = Vec::with_capacity(6);
        if person.starts_with("h-") {
            rules.push(format!("rw,p={person}:/f/{fleet}/fleet/{person}/>"));
        }
        rules.push(format!("rw,p={person}:/f/{fleet}/in/*/*/{person}/*"));
        rules.push(format!("rw,p={person}:/f/{fleet}/pub/p/{person}/>"));
        rules.push(format!("ro:/f/{fleet}/in/p/{person}/>"));
        rules.push(format!("rw,p={person}:/f/{fleet}/cur/p/{person}/>"));
        rules.push(format!("ro:/f/{fleet}/pub/>"));
        Self::parse(&rules)
    }

    /// Number of grant rules in this ceiling.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether this ceiling has zero rules (always `false` for constructed [`GrantCeiling`]s).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// The ceiling's grant rules in order, each as it was parsed (trimmed): the grants a
    /// minter issues for the ring this ceiling bounds, so a ring minted from them is the
    /// ceiling exactly and [`Self::check_ring`] accepts it.
    #[must_use]
    pub fn rules(&self) -> Vec<String> {
        let mut rules = Vec::with_capacity(self.entries.len());
        let mut rest = self.entries.as_slice();
        while let [entry, ref tail @ ..] = rest {
            rules.push(entry.raw.clone());
            rest = tail;
        }
        rules
    }

    /// Verify that a single `grant` string is monotonically subsumed by at least one
    /// rule in this ceiling, returning the matching rule's index on `Ok`.
    pub fn check_grant(&self, grant: &str) -> Result<usize, CeilingViolationKind> {
        let (mg, mf) = match parse_grant(grant) {
            Ok(pair) => pair,
            Err(e) => return Err(CeilingViolationKind::MalformedGrant(e)),
        };
        let max_rules = self.entries.len() as u64;
        let mut closest_err = String::from("no ceiling rules matched");
        let mut best_score = 0u8;
        let mut i = 0usize;
        while i < self.entries.len() {
            let clamped = ceiling_rule_index_clamp(i as u64, max_rules) as usize;
            let Some(entry) = self.entries.get(clamped) else {
                break;
            };
            let mode_ok = ceiling_mode_subsumes(entry.grant.mode, mg.mode);
            let filter_ok = entry.filter.contains(&mf);
            if mode_ok && filter_ok {
                if let Ok(()) = can_attenuate(&entry.raw, grant) {
                    return Ok(clamped);
                }
            }
            // Record the most informative mismatch reason for operator diagnostics.
            let score = (if filter_ok { 2u8 } else { 0u8 }) + (if mode_ok { 1u8 } else { 0u8 });
            if let Err(reason) = can_attenuate(&entry.raw, grant) {
                if score >= best_score {
                    best_score = score;
                    closest_err = reason;
                }
            }
            i = i.saturating_add(1);
        }
        if mg.mode == Mode::ReadWrite && mg.principal.is_none() {
            Err(CeilingViolationKind::UnboundGodCap {
                closest_reason: closest_err,
            })
        } else {
            Err(CeilingViolationKind::ExceedsCeiling {
                closest_reason: closest_err,
            })
        }
    }

    /// Verify that every [`Capability`] in `caps` falls within this ceiling.
    ///
    /// Does not need the mint `secret`, so bridges and CLIs (`aterm-link serve`,
    /// `asb verify-ring`) can enforce least-privilege `--cap-file` bounds offline
    /// before dialing the broker (`DESIGN-aterm-fabric.md` §14 Open Question 5).
    pub fn check_ring(&self, caps: &[Capability]) -> Result<(), CeilingViolation> {
        if caps.len() > MAX_RING_CAPS {
            return Err(CeilingViolation {
                index: MAX_RING_CAPS,
                grant: String::new(),
                kind: CeilingViolationKind::RingTooLarge {
                    count: caps.len(),
                    max: MAX_RING_CAPS,
                },
            });
        }
        let mut i = 0usize;
        let mut rest = caps;
        while let [cap, ref tail @ ..] = rest {
            let grant = &cap.filter;
            if let Err(kind) = self.check_grant(grant) {
                return Err(CeilingViolation {
                    index: i,
                    grant: grant.clone(),
                    kind,
                });
            }
            rest = tail;
            i = i.saturating_add(1);
        }
        Ok(())
    }

    /// Verify HMAC authenticity (`secret`), non-expiry (`now_ms`), and least-privilege
    /// ceiling subsumption across every capability in `caps`.
    pub fn check_authenticated_ring(
        &self,
        secret: &[u8],
        caps: &[Capability],
        now_ms: u64,
    ) -> Result<(), CeilingViolation> {
        if caps.len() > MAX_RING_CAPS {
            return Err(CeilingViolation {
                index: MAX_RING_CAPS,
                grant: String::new(),
                kind: CeilingViolationKind::RingTooLarge {
                    count: caps.len(),
                    max: MAX_RING_CAPS,
                },
            });
        }
        let mut i = 0usize;
        let mut rest = caps;
        while let [cap, ref tail @ ..] = rest {
            if !verify(secret, cap) {
                return Err(CeilingViolation {
                    index: i,
                    grant: cap.filter.clone(),
                    kind: CeilingViolationKind::UnauthenticatedTag,
                });
            }
            if is_expired(&cap.filter, now_ms) {
                return Err(CeilingViolation {
                    index: i,
                    grant: cap.filter.clone(),
                    kind: CeilingViolationKind::Expired { now_ms },
                });
            }
            if let Err(kind) = self.check_grant(&cap.filter) {
                return Err(CeilingViolation {
                    index: i,
                    grant: cap.filter.clone(),
                    kind,
                });
            }
            rest = tail;
            i = i.saturating_add(1);
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{attenuate_offline, mint};

    const SECRET: &[u8] = b"0123456789abcdef0123456789abcdef";

    #[test]
    fn aterm_node_ring_accepts_exact_and_attenuated_ring_and_rejects_god_cap() {
        let node = "n-0123456789abcdef";
        let ceiling = GrantCeiling::aterm_node_ring("f1", node).unwrap();
        assert_eq!(ceiling.len(), 8);

        let exact_grants = [
            format!("rw,p={node}:/f/f1/pub/{node}/>"),
            "ro:/f/f1/pub/>".to_string(),
            "ro:/f/f1/fleet/>".to_string(),
            format!("rw,p={node}:/f/f1/in/*/*/{node}/*"),
            format!("ro:/f/f1/in/{node}/>"),
            format!("rw,p={node}:/f/f1/cur/{node}/>"),
            "ro:/f/f1/halt/>".to_string(),
            format!("rw,p={node}:/f/f1/halt/{node}"),
        ];
        assert_eq!(ceiling.rules(), exact_grants, "the rules, in mint order");
        let mut ring: Vec<Capability> = ceiling
            .rules()
            .iter()
            .map(|g| mint(SECRET, g).unwrap())
            .collect();
        ceiling.check_ring(&ring).unwrap();
        ceiling
            .check_authenticated_ring(SECRET, &ring, 1_700_000_000_000)
            .unwrap();

        // Offline Macaroon attenuation with an expiry narrowing one sender's lane stays valid.
        let narrowed = attenuate_offline(
            &ring[3],
            &format!("rw,p={node},exp=1900000000000:/f/f1/in/n-peer/s-1/{node}/ask"),
            1_700_000_000_000,
        )
        .unwrap();
        ring[3] = narrowed;
        ceiling
            .check_authenticated_ring(SECRET, &ring, 1_700_000_000_000)
            .unwrap();

        // The cut drive face's grants are outside the ring: neither the screen write nor the
        // read of the node's term subtree.
        for term in [
            format!("rw,p={node}:/f/f1/term/{node}/*/screen"),
            format!("ro:/f/f1/term/{node}/>"),
        ] {
            let err = ceiling
                .check_ring(&[mint(SECRET, &term).unwrap()])
                .unwrap_err();
            assert!(
                matches!(err.kind, CeilingViolationKind::ExceedsCeiling { .. }),
                "{term}: {err}"
            );
        }

        // Unbound fleet-root god cap (`DESIGN-aterm-fabric` §14 Q5) is refused by name!
        let mut with_god = ring.clone();
        with_god.push(mint(SECRET, "rw:/f/f1/>").unwrap());
        let err = ceiling.check_ring(&with_god).unwrap_err();
        assert_eq!(err.index, 8);
        assert!(matches!(
            err.kind,
            CeilingViolationKind::UnboundGodCap { .. }
        ));

        // Unbound write cap on the node's own pub subtree (dedup-poisoning risk) is refused!
        let unbound_node_pub = vec![mint(SECRET, &format!("rw:/f/f1/pub/{node}/>")).unwrap()];
        let err = ceiling.check_ring(&unbound_node_pub).unwrap_err();
        assert!(matches!(
            err.kind,
            CeilingViolationKind::UnboundGodCap { .. }
        ));

        // Another node's bound cap is refused!
        let wrong_node = vec![mint(
            SECRET,
            "rw,p=n-fedcba9876543210:/f/f1/pub/n-fedcba9876543210/>",
        )
        .unwrap()];
        let err = ceiling.check_ring(&wrong_node).unwrap_err();
        assert!(matches!(
            err.kind,
            CeilingViolationKind::ExceedsCeiling { .. }
        ));

        // Escalating `ro:/f/f1/fleet/>` to `rw` (forging human halts) is refused!
        let forge_halt =
            vec![mint(SECRET, &format!("rw,p={node}:/f/f1/fleet/{node}/halt")).unwrap()];
        let err = ceiling.check_ring(&forge_halt).unwrap_err();
        assert!(matches!(
            err.kind,
            CeilingViolationKind::ExceedsCeiling { .. }
        ));

        // A node publishes its own halt subject alone: another node's, or every node's under
        // its own principal, is refused, and an unbound halt write is the god cap's kind.
        for forged in [
            format!("rw,p={node}:/f/f1/halt/n-fedcba9876543210"),
            format!("rw,p={node}:/f/f1/halt/>"),
        ] {
            let err = ceiling
                .check_ring(&[mint(SECRET, &forged).unwrap()])
                .unwrap_err();
            assert!(
                matches!(err.kind, CeilingViolationKind::ExceedsCeiling { .. }),
                "{forged}: {err}"
            );
        }
        let unbound_halt = vec![mint(SECRET, &format!("rw:/f/f1/halt/{node}")).unwrap()];
        let err = ceiling.check_ring(&unbound_halt).unwrap_err();
        assert!(matches!(
            err.kind,
            CeilingViolationKind::UnboundGodCap { .. }
        ));
    }

    #[test]
    fn aterm_person_ring_distinguishes_human_halt_from_agent_no_halt() {
        let human_ceiling = GrantCeiling::aterm_person_ring("lab", "h-alice").unwrap();
        let agent_ceiling = GrantCeiling::aterm_person_ring("lab", "a-worker").unwrap();
        assert_eq!(human_ceiling.len(), 6);
        assert_eq!(agent_ceiling.len(), 5);
        assert_eq!(
            human_ceiling.rules(),
            [
                "rw,p=h-alice:/f/lab/fleet/h-alice/>",
                "rw,p=h-alice:/f/lab/in/*/*/h-alice/*",
                "rw,p=h-alice:/f/lab/pub/p/h-alice/>",
                "ro:/f/lab/in/p/h-alice/>",
                "rw,p=h-alice:/f/lab/cur/p/h-alice/>",
                "ro:/f/lab/pub/>",
            ],
            "a human's rules, in mint order"
        );
        assert_eq!(
            agent_ceiling.rules(),
            human_ceiling.rules()[1..]
                .iter()
                .map(|r| r.replace("h-alice", "a-worker"))
                .collect::<Vec<_>>(),
            "an agent's are a human's without the halt grant"
        );
        for ceiling in [&human_ceiling, &agent_ceiling] {
            let minted: Vec<Capability> = ceiling
                .rules()
                .iter()
                .map(|g| mint(SECRET, g).unwrap())
                .collect();
            ceiling
                .check_authenticated_ring(SECRET, &minted, 1_700_000_000_000)
                .unwrap();
        }

        let h_halt = mint(SECRET, "rw,p=h-alice:/f/lab/fleet/h-alice/halt").unwrap();
        human_ceiling.check_ring(&[h_halt]).unwrap();

        let a_halt = mint(SECRET, "rw,p=a-worker:/f/lab/fleet/a-worker/halt").unwrap();
        let err = agent_ceiling.check_ring(&[a_halt]).unwrap_err();
        assert!(matches!(
            err.kind,
            CeilingViolationKind::ExceedsCeiling { .. }
        ));

        let a_mail = mint(SECRET, "rw,p=a-worker:/f/lab/in/n-1/s-1/a-worker/ask").unwrap();
        agent_ceiling.check_ring(&[a_mail]).unwrap();
    }

    /// `rules` renders each rule as parsed (trimmed), in order, and a ceiling parsed back from
    /// them has the same rules.
    #[test]
    fn rules_render_the_parsed_grants_in_order() {
        let ceiling = GrantCeiling::parse_text(
            "# comment\n  ro:/f/a/pub/>  \n\nrw,p=a-b:/f/a/in/*/*/a-b/*\n",
        )
        .unwrap();
        assert_eq!(
            ceiling.rules(),
            ["ro:/f/a/pub/>", "rw,p=a-b:/f/a/in/*/*/a-b/*"]
        );
        assert_eq!(
            GrantCeiling::parse(&ceiling.rules()).unwrap().rules(),
            ceiling.rules()
        );
    }

    #[test]
    fn authenticated_ring_catches_forged_tag_and_expired_grant() {
        let ceiling =
            GrantCeiling::parse_text("# comment\nrw,p=a-bot:/f/f1/in/*/*/a-bot/*\n").unwrap();
        let mut forged = mint(SECRET, "rw,p=a-bot:/f/f1/in/*/*/a-bot/*").unwrap();
        forged.tag[0] ^= 0x01;
        let err = ceiling
            .check_authenticated_ring(SECRET, &[forged], 1_000)
            .unwrap_err();
        assert_eq!(err.kind, CeilingViolationKind::UnauthenticatedTag);

        let expiring = mint(SECRET, "rw,p=a-bot,exp=5000:/f/f1/in/*/*/a-bot/*").unwrap();
        assert_eq!(
            ceiling
                .check_authenticated_ring(SECRET, &[expiring], 5000)
                .unwrap_err()
                .kind,
            CeilingViolationKind::Expired { now_ms: 5000 }
        );
    }
}
