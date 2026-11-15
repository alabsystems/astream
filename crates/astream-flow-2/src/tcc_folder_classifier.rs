//! macOS TCC protected-folder & modal-dialog preflight classifier (`aterm ctl privacy`).

#[cfg(clean_islands)]
#[path = "tcc_folder_classifier_island.rs"]
mod tcc_folder_classifier_island;
#[cfg(clean_islands)]
pub use tcc_folder_classifier_island::{tcc_denial_watermark, tcc_target_class_clamp};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tcc_target_class_clamp(raw_class: u64) -> u64 {
    if raw_class < 4 {
        raw_class
    } else {
        4
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tcc_denial_watermark(prev_seq: u64, next_seq: u64) -> u64 {
    if prev_seq < next_seq {
        next_seq
    } else {
        prev_seq
    }
}

contract_fn! {
    #[must_use]
    pub const fn tcc_is_non_protected(target_class: u64) -> bool
    clauses [ensures result == (target_class < 1)]
    {
        target_class < 1
    }
}

#[inline]
#[must_use]
pub const fn tcc_probe_safe(target_class: u64, has_fda: u64) -> bool {
    tcc_is_non_protected(target_class) || (target_class < 2 && has_fda >= 1)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrivacyTargetClass {
    WorkspaceOrPublic,
    UserFolderOrVolume,
    AppContainerOrMediaLibrary,
    DefaultsDomain,
    SyncedCloudFolder,
}

impl PrivacyTargetClass {
    #[must_use]
    pub const fn code(self) -> u64 {
        let raw = match self {
            Self::WorkspaceOrPublic => 0,
            Self::UserFolderOrVolume => 1,
            Self::AppContainerOrMediaLibrary => 2,
            Self::DefaultsDomain => 3,
            Self::SyncedCloudFolder => 4,
        };
        tcc_target_class_clamp(raw)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrivacyPreflight {
    SafeWithoutPrompt,
    BlockModalDialogRisk { target: PrivacyTargetClass },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TccFolderClassifier {
    has_full_disk_access: bool,
    explicit_operator_request: bool,
    denial_watermark: u64,
}

impl TccFolderClassifier {
    #[must_use]
    pub const fn new(has_full_disk_access: bool, explicit_operator_request: bool) -> Self {
        Self {
            has_full_disk_access,
            explicit_operator_request,
            denial_watermark: 0,
        }
    }

    #[must_use]
    pub const fn has_full_disk_access(&self) -> bool {
        self.has_full_disk_access
    }

    #[must_use]
    pub const fn explicit_operator_request(&self) -> bool {
        self.explicit_operator_request
    }

    #[must_use]
    pub const fn denial_watermark(&self) -> u64 {
        self.denial_watermark
    }

    pub fn record_eperm_denial(&mut self, seq: u64) -> u64 {
        self.denial_watermark = tcc_denial_watermark(self.denial_watermark, seq);
        self.denial_watermark
    }

    #[must_use]
    pub const fn preflight(&self, target: PrivacyTargetClass) -> PrivacyPreflight {
        let has_fda = if self.has_full_disk_access { 1 } else { 0 };
        if tcc_probe_safe(target.code(), has_fda) || self.explicit_operator_request {
            PrivacyPreflight::SafeWithoutPrompt
        } else {
            PrivacyPreflight::BlockModalDialogRisk { target }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fda_exempts_only_three_folders_and_volumes_never_containers_or_defaults() {
        let no_fda = TccFolderClassifier::new(false, false);
        assert!(!no_fda.has_full_disk_access());
        assert!(!no_fda.explicit_operator_request());
        assert_eq!(
            no_fda.preflight(PrivacyTargetClass::WorkspaceOrPublic),
            PrivacyPreflight::SafeWithoutPrompt
        );
        assert_eq!(
            no_fda.preflight(PrivacyTargetClass::UserFolderOrVolume),
            PrivacyPreflight::BlockModalDialogRisk {
                target: PrivacyTargetClass::UserFolderOrVolume,
            }
        );

        let mut with_fda = TccFolderClassifier::new(true, false);
        assert_eq!(
            with_fda.preflight(PrivacyTargetClass::UserFolderOrVolume),
            PrivacyPreflight::SafeWithoutPrompt
        );
        assert_eq!(
            with_fda.preflight(PrivacyTargetClass::AppContainerOrMediaLibrary),
            PrivacyPreflight::BlockModalDialogRisk {
                target: PrivacyTargetClass::AppContainerOrMediaLibrary,
            }
        );
        assert_eq!(
            with_fda.preflight(PrivacyTargetClass::DefaultsDomain),
            PrivacyPreflight::BlockModalDialogRisk {
                target: PrivacyTargetClass::DefaultsDomain,
            }
        );
        assert_eq!(with_fda.record_eperm_denial(7), 7);
        assert_eq!(with_fda.record_eperm_denial(3), 7);
    }

    #[test]
    fn twin_grid_matches_clean_definitions() {
        let mut got_adv = String::new();
        for a in [0u64, 1, 2] {
            for b in [0u64, 1, 2] {
                got_adv.push_str(&tcc_denial_watermark(a, b).to_string());
            }
        }
        assert_eq!(got_adv, "012112222");
        assert_eq!(tcc_target_class_clamp(99), 4);
    }
}
