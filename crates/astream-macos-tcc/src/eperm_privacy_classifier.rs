// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! macOS `Operation not permitted` (`EPERM`, `errno == 1`) classifier mapping filesystem errors to
//! `aterm ctl privacy` consent categories (`Astream.MacTcc.TlaEpermPrivacyClassifier`).

#[cfg(clean_islands)]
#[path = "eperm_privacy_classifier_island.rs"]
mod eperm_privacy_classifier_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tcc_err_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tcc_cls_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use eperm_privacy_classifier_island::{tcc_cls_advance, tcc_err_clamp};

/// POSIX errno upper clamp (`255`).
pub const MAX_ERRNO_CODE: u64 = 255;
/// macOS `EPERM` (`Operation not permitted`).
pub const MACOS_EPERM: u64 = 1;

contract_fn! {
    /// Verified privacy-consent classification (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `tcc_is_privacy_block_isl`.
    #[must_use]
    pub const fn tcc_is_privacy_block(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrivacyVerdict {
    NotPrivacyError,
    NeedsPersonPrivacyGrant,
}

#[derive(Debug, Clone, Default)]
pub struct EpermClassifier {
    events_classified: u64,
}

impl EpermClassifier {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            events_classified: 0,
        }
    }

    pub fn classify(&mut self, raw_errno: u64, immutable_flag_set: bool) -> PrivacyVerdict {
        let code = tcc_err_clamp(raw_errno, MAX_ERRNO_CODE);
        self.events_classified = tcc_cls_advance(
            self.events_classified,
            self.events_classified.saturating_add(1),
        );
        let match_score = if code == MACOS_EPERM && !immutable_flag_set {
            1u64
        } else {
            0u64
        };
        if tcc_is_privacy_block(match_score, 1) {
            PrivacyVerdict::NeedsPersonPrivacyGrant
        } else {
            PrivacyVerdict::NotPrivacyError
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn maps_macos_eperm_without_uchg_to_person_privacy_grant() {
        let mut c = EpermClassifier::new();
        assert_eq!(
            c.classify(1, false),
            PrivacyVerdict::NeedsPersonPrivacyGrant
        );
        assert_eq!(c.classify(13, false), PrivacyVerdict::NotPrivacyError);
        assert_eq!(c.classify(1, true), PrivacyVerdict::NotPrivacyError);
    }
}
