// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Receiver-computed orthogonal `(provenance, trust=)` inbox label classifier
//! (`docs/DESIGN-aterm-fabric.md` §4.1 & §4.3 lines 886–929;
//! `Astream.Agent.TlaReceiverTrustLabelClassifier`).
//!
//! No sender ever writes `trust=` in a message body: the receiving bridge computes it purely from
//! `(face, cap_forced_src_class, via_hops)` so "screen content is data, not instructions" appears
//! first in every inbox row:
//! - `ev`, `term`, or bridge-quoted screen excerpt -> [`ReceiverTrustLabel::Screen`],
//! - `via_hops > 0` (`via=<p>[,<p>…]` present) -> [`ReceiverTrustLabel::Relayed`],
//! - `h-*` without `via=` on a non-screen face -> [`ReceiverTrustLabel::Human`],
//! - `n-*` / `s-*` / `a-*` without `via=` on a non-screen face -> [`ReceiverTrustLabel::Agent`].
//!
//! Also validates that `from=<sid>` in body is honored ONLY when cap-forced `<src>` is `n-*`!

#[cfg(clean_islands)]
#[path = "receiver_trust_label_classifier_island.rs"]
mod receiver_trust_label_classifier_island;
#[cfg(clean_islands)]
pub use receiver_trust_label_classifier_island::{
    trust_classified_advance_b132, trust_via_hops_clamp_b132,
};

/// Maximum tracked `via=` relay chain hops (`16`).
pub const MAX_VIA_RELAY_HOPS: u64 = 16;

#[cfg(not(clean_islands))]
/// Clamp `via=` hop count to `max_via_hops`.
#[must_use]
pub const fn trust_via_hops_clamp_b132(cand_hops: u64, max_via_hops: u64) -> u64 {
    if cand_hops < max_via_hops {
        cand_hops
    } else {
        max_via_hops
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance count of inbox rows labeled by the receiver.
#[must_use]
pub const fn trust_classified_advance_b132(cur_count: u64, cand_count: u64) -> u64 {
    if cur_count < cand_count {
        cand_count
    } else {
        cur_count
    }
}

contract_fn! {
    /// True iff `via_hops > 0` (demotes human/agent authority to `trust=relayed`).
    #[must_use]
    pub const fn trust_demoted_by_via_b132(via_hops: u64) -> bool
    clauses [ensures result == (via_hops > 0)]
    {
        via_hops > 0
    }
}

/// Cap-enforced `<src>` principal class prefix (`§3.2`).
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum SourcePrincipalClass {
    /// `h-<name>`
    Human,
    /// `n-<16 hex>`
    Node,
    /// `s-<20 hex>`
    Session,
    /// `a-<name>`
    Service,
}

/// Bus face family from which the row arrived.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum DeliveryFaceKind {
    /// `/f/<F>/in/…` or `/f/<F>/fleet/…` or `/f/<F>/pub/…/say/…`
    MessageOrBroadcast,
    /// `/f/<F>/pub/…/ev`, `/f/<F>/term/…`, or bridge-quoted screen excerpt
    ScreenOrEventsDigest,
}

/// Closed receiver-computed `trust=` vocabulary (`§4.3`).
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ReceiverTrustLabel {
    Human,
    Agent,
    Relayed,
    Screen,
}

impl ReceiverTrustLabel {
    #[must_use]
    pub const fn as_token(self) -> &'static str {
        match self {
            Self::Human => "human",
            Self::Agent => "agent",
            Self::Relayed => "relayed",
            Self::Screen => "screen",
        }
    }
}

/// Attested provenance decision for an optional body `from=<sid>` token.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ProvenanceFromMode {
    /// Use bare cap-forced `<src>` segment (`body from=` absent or ignored on non-node `<src>`).
    DirectSourceOnly,
    /// Render `<sid>@<node>` because cap-forced `<src>` is a `Node` (`n-*`) attesting its own session!
    NodeAttestedSession,
}

/// Stateful receiver-computed trust & provenance classifier.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ReceiverTrustClassifier {
    classified_rows: u64,
    last_via_hops: u64,
}

impl Default for ReceiverTrustClassifier {
    fn default() -> Self {
        Self::new()
    }
}

impl ReceiverTrustClassifier {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            classified_rows: 0,
            last_via_hops: 0,
        }
    }

    #[must_use]
    pub const fn classified_rows(&self) -> u64 {
        self.classified_rows
    }

    /// Compute `(ProvenanceFromMode, ReceiverTrustLabel)` strictly from receiver-verified metadata.
    pub fn classify_delivery(
        &mut self,
        face: DeliveryFaceKind,
        src_class: SourcePrincipalClass,
        via_hops: u64,
        body_has_valid_sid_from: bool,
    ) -> (ProvenanceFromMode, ReceiverTrustLabel) {
        let clamped_hops = trust_via_hops_clamp_b132(via_hops, MAX_VIA_RELAY_HOPS);
        self.last_via_hops = clamped_hops;
        let cand = self.classified_rows.saturating_add(1);
        self.classified_rows = trust_classified_advance_b132(self.classified_rows, cand);

        let prov = if matches!(src_class, SourcePrincipalClass::Node) && body_has_valid_sid_from {
            ProvenanceFromMode::NodeAttestedSession
        } else {
            ProvenanceFromMode::DirectSourceOnly
        };

        let trust = match face {
            DeliveryFaceKind::ScreenOrEventsDigest => ReceiverTrustLabel::Screen,
            DeliveryFaceKind::MessageOrBroadcast => {
                if trust_demoted_by_via_b132(clamped_hops) {
                    ReceiverTrustLabel::Relayed
                } else {
                    match src_class {
                        SourcePrincipalClass::Human => ReceiverTrustLabel::Human,
                        SourcePrincipalClass::Node
                        | SourcePrincipalClass::Session
                        | SourcePrincipalClass::Service => ReceiverTrustLabel::Agent,
                    }
                }
            }
        };

        (prov, trust)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn screen_and_via_demote_human_and_non_node_cannot_spoof_session_from() {
        let mut c = ReceiverTrustClassifier::new();
        assert_eq!(
            c.classify_delivery(
                DeliveryFaceKind::MessageOrBroadcast,
                SourcePrincipalClass::Human,
                0,
                true, // human cannot spoof node-attested session `from=s-...`
            ),
            (
                ProvenanceFromMode::DirectSourceOnly,
                ReceiverTrustLabel::Human
            )
        );
        // Relayed human message MUST demote to `trust=relayed`!
        assert_eq!(
            c.classify_delivery(
                DeliveryFaceKind::MessageOrBroadcast,
                SourcePrincipalClass::Human,
                1,
                false,
            ),
            (
                ProvenanceFromMode::DirectSourceOnly,
                ReceiverTrustLabel::Relayed
            )
        );
        // Node attesting its hosted session -> `s-...@n-...` + `trust=agent`.
        assert_eq!(
            c.classify_delivery(
                DeliveryFaceKind::MessageOrBroadcast,
                SourcePrincipalClass::Node,
                0,
                true,
            ),
            (
                ProvenanceFromMode::NodeAttestedSession,
                ReceiverTrustLabel::Agent
            )
        );
        // Any `ev`/`term` face -> `trust=screen` even if `h-*`!
        assert_eq!(
            c.classify_delivery(
                DeliveryFaceKind::ScreenOrEventsDigest,
                SourcePrincipalClass::Human,
                0,
                false,
            )
            .1
            .as_token(),
            "screen"
        );
        assert_eq!(c.classified_rows(), 4);
    }
}
