//! `<log>.seal` v2 domain-separated AAD builder (`ASTREAM-ATREST-V2\0`).

#[cfg(clean_islands)]
#[path = "at_rest_seal_domain_guard_island.rs"]
mod at_rest_seal_domain_guard_island;
#[cfg(clean_islands)]
pub use at_rest_seal_domain_guard_island::{seal_domain_tag_clamp, seal_index_advance};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn seal_domain_tag_clamp(tag: u64) -> u64 {
    if tag < 3 {
        tag
    } else {
        3
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn seal_index_advance(prev_idx: u64, next_idx: u64) -> u64 {
    if prev_idx < next_idx {
        next_idx
    } else {
        prev_idx
    }
}

contract_fn! {
    #[must_use]
    pub const fn seal_domain_valid(raw_tag: u64) -> bool
    clauses [ensures result == ((raw_tag < 4))]
    {
        raw_tag < 4
    }
}

pub const ATREST_V2_PREFIX: &[u8; 18] = b"ASTREAM-ATREST-V2\0";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AtRestDomain {
    RecordFrame,
    CompactedStateSidecar,
    HeldStoreSidecar,
    HighWatermarkSidecar,
}

impl AtRestDomain {
    #[must_use]
    pub const fn code(self) -> u64 {
        match self {
            Self::RecordFrame => 0,
            Self::CompactedStateSidecar => 1,
            Self::HeldStoreSidecar => 2,
            Self::HighWatermarkSidecar => 3,
        }
    }

    #[must_use]
    pub const fn from_tag(raw: u8) -> Option<Self> {
        if !seal_domain_valid(raw as u64) {
            return None;
        }
        match seal_domain_tag_clamp(raw as u64) {
            0 => Some(Self::RecordFrame),
            1 => Some(Self::CompactedStateSidecar),
            2 => Some(Self::HeldStoreSidecar),
            _ => Some(Self::HighWatermarkSidecar),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AtRestSealDomainGuard {
    seal_id: [u8; 32],
    highest_record_index: u64,
}

impl AtRestSealDomainGuard {
    #[must_use]
    pub const fn new(seal_id: [u8; 32]) -> Self {
        Self {
            seal_id,
            highest_record_index: 0,
        }
    }

    #[must_use]
    pub const fn seal_id(&self) -> &[u8; 32] {
        &self.seal_id
    }

    #[must_use]
    pub const fn highest_record_index(&self) -> u64 {
        self.highest_record_index
    }

    #[must_use]
    pub fn build_aad(&mut self, domain: AtRestDomain, index_or_seq: u64) -> Vec<u8> {
        if matches!(domain, AtRestDomain::RecordFrame) {
            self.highest_record_index = seal_index_advance(self.highest_record_index, index_or_seq);
        }
        let mut aad = Vec::new();
        aad.extend_from_slice(ATREST_V2_PREFIX);
        aad.extend_from_slice(&self.seal_id);
        aad.push(seal_domain_tag_clamp(domain.code()) as u8);
        aad.extend_from_slice(&index_or_seq.to_le_bytes());
        aad
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn separates_domains_and_seal_ids_preventing_cross_log_or_cross_sidecar_swap() {
        let mut g1 = AtRestSealDomainGuard::new([0x11; 32]);
        let mut g2 = AtRestSealDomainGuard::new([0x22; 32]);
        assert_eq!(g1.seal_id(), &[0x11; 32]);
        let rec_aad = g1.build_aad(AtRestDomain::RecordFrame, 7);
        assert_eq!(g1.highest_record_index(), 7);
        let state_aad = g1.build_aad(AtRestDomain::CompactedStateSidecar, 7);
        let other_log_aad = g2.build_aad(AtRestDomain::RecordFrame, 7);
        assert_ne!(rec_aad, state_aad);
        assert_ne!(rec_aad, other_log_aad);
        assert_eq!(AtRestDomain::from_tag(4), None);
    }
}
