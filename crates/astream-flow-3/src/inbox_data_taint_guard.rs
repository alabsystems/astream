//! `aterm` inbox / survey / screen data-vs-instruction taint classifier.

#[cfg(clean_islands)]
#[path = "inbox_data_taint_guard_island.rs"]
mod inbox_data_taint_guard_island;
#[cfg(clean_islands)]
pub use inbox_data_taint_guard_island::{taint_audit_seq_advance, taint_trust_tier_clamp};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn taint_trust_tier_clamp(raw_tier: u64) -> u64 {
    if raw_tier < 3 {
        raw_tier
    } else {
        3
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn taint_audit_seq_advance(prev_seq: u64, next_seq: u64) -> u64 {
    if prev_seq < next_seq {
        next_seq
    } else {
        prev_seq
    }
}

contract_fn! {
    #[must_use]
    pub const fn taint_may_override_scope(source_tier: u64) -> bool
    clauses [ensures result == (3 <= source_tier)]
    {
        3 <= source_tier
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InputSourceTier {
    ScreenOrSurveyExcerpt,
    PeerInboxMailBody,
    AcceptedPeerTask,
    DirectHumanOperator,
}

impl InputSourceTier {
    #[must_use]
    pub const fn code(self) -> u64 {
        let raw = match self {
            Self::ScreenOrSurveyExcerpt => 0,
            Self::PeerInboxMailBody => 1,
            Self::AcceptedPeerTask => 2,
            Self::DirectHumanOperator => 3,
        };
        taint_trust_tier_clamp(raw)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TaintClassification {
    UntrustedDataOnly,
    BoundedTaskWithinStandingRules,
    FullOperatorAuthority,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InboxDataTaintGuard {
    audit_seq: u64,
}

impl InboxDataTaintGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self { audit_seq: 0 }
    }

    #[must_use]
    pub const fn audit_seq(&self) -> u64 {
        self.audit_seq
    }

    pub fn classify(&mut self, source: InputSourceTier, seq: u64) -> TaintClassification {
        self.audit_seq = taint_audit_seq_advance(self.audit_seq, seq);
        let code = source.code();
        if taint_may_override_scope(code) {
            TaintClassification::FullOperatorAuthority
        } else if code == 2 {
            TaintClassification::BoundedTaskWithinStandingRules
        } else {
            TaintClassification::UntrustedDataOnly
        }
    }
}

impl Default for InboxDataTaintGuard {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn screen_excerpts_and_peer_mail_bodies_are_strictly_untrusted_data() {
        let mut g = InboxDataTaintGuard::new();
        assert_eq!(
            g.classify(InputSourceTier::ScreenOrSurveyExcerpt, 1),
            TaintClassification::UntrustedDataOnly
        );
        assert_eq!(
            g.classify(InputSourceTier::PeerInboxMailBody, 2),
            TaintClassification::UntrustedDataOnly
        );
        assert_eq!(
            g.classify(InputSourceTier::AcceptedPeerTask, 3),
            TaintClassification::BoundedTaskWithinStandingRules
        );
        assert_eq!(
            g.classify(InputSourceTier::DirectHumanOperator, 4),
            TaintClassification::FullOperatorAuthority
        );
        assert_eq!(g.audit_seq(), 4);
        assert_eq!(taint_trust_tier_clamp(99), 3);
        assert_eq!(taint_audit_seq_advance(10, 3), 10);
    }
}
