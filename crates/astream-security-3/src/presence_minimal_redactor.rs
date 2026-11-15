// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Fabric `presence` field redaction, OSC-title leak fence, & `attention=` 256-byte clamp
//! (`docs/DESIGN-aterm-fabric.md` §4.2, §7, §15; `Astream.Broker.TlaPresenceMinimalRedactor`).
//!
//! Enforces `aterm-link`'s presence secrecy invariants:
//! - `title=` is emitted ONLY when sourced from explicit `meta set title` (`TitleOrigin::MetaSet`);
//!   a program-emitted `TitleOrigin::ProgramOsc` is ALWAYS withheld so cwds, argv secrets, and
//!   conversation summaries never leak onto `/f/<F>/pub/<owner>/presence`.
//! - Under `PresenceMode::Minimal` (`presence = "minimal"`), `title=`, `role=`, `detail=`, and
//!   `phase=` are all withheld.
//! - `attention=` byte length is clamped to `MAX_ATTENTION_BYTES` (`256`), and `incarnation`
//!   advances monotonically across bridge re-attaches.

#[cfg(clean_islands)]
#[path = "presence_minimal_redactor_island.rs"]
mod presence_minimal_redactor_island;
#[cfg(clean_islands)]
pub use presence_minimal_redactor_island::{
    presence_attention_clamp_b125, presence_inc_advance_b125,
};

#[cfg(not(clean_islands))]
/// Clamp `attention=` byte length to `max_bytes` (`256`).
#[must_use]
pub const fn presence_attention_clamp_b125(cand_len: u64, max_bytes: u64) -> u64 {
    if cand_len < max_bytes {
        cand_len
    } else {
        max_bytes
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the bridge presence incarnation (`inc=`).
#[must_use]
pub const fn presence_inc_advance_b125(cur_inc: u64, cand_inc: u64) -> u64 {
    if cur_inc < cand_inc {
        cand_inc
    } else {
        cur_inc
    }
}

contract_fn! {
    /// True iff `title=` may be published: mode is `Meta` (`mode_is_meta`) AND title came from `meta set title` (`from_meta_set`).
    #[must_use]
    pub const fn presence_title_permitted_b125(mode_is_meta: bool, from_meta_set: bool) -> bool
    clauses [ensures result == (mode_is_meta && from_meta_set)]
    {
        mode_is_meta && from_meta_set
    }
}

pub const MAX_ATTENTION_BYTES: u64 = 256;

/// Bridge presence verbosity configuration (`presence = "meta"` vs `presence = "minimal"`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PresenceMode {
    Meta,
    Minimal,
}

/// Source of a session's candidate title (`aterm ctl status` `subject_source`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TitleOrigin {
    None,
    /// Program-controlled OSC 0/2 terminal title (can contain secrets/cwd/prompts -> NEVER published).
    ProgramOsc,
    /// Explicit operator/owner `aterm ctl meta set title` -> safe in `Meta` mode.
    MetaSet,
}

/// Sanitized field visibility mask & sizes for one emitted `presence` row.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SanitizedPresenceProjection {
    pub incarnation: u64,
    pub emit_role_detail_phase: bool,
    pub emit_title: bool,
    pub clamped_attention_bytes: u64,
}

/// Stateful presence redactor & incarnation tracker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PresenceMinimalRedactor {
    mode: PresenceMode,
    incarnation: u64,
    max_attention_bytes: u64,
}

impl PresenceMinimalRedactor {
    #[must_use]
    pub const fn new(mode: PresenceMode, initial_incarnation: u64) -> Self {
        Self {
            mode,
            incarnation: initial_incarnation,
            max_attention_bytes: MAX_ATTENTION_BYTES,
        }
    }

    pub fn set_mode(&mut self, mode: PresenceMode) {
        self.mode = mode;
    }

    /// Advance incarnation on bridge attach / seamless update (`inc + 1`).
    pub fn on_bridge_attach(&mut self, candidate_inc: u64) -> u64 {
        self.incarnation = presence_inc_advance_b125(self.incarnation, candidate_inc);
        self.incarnation
    }

    /// Compute the redacted projection of a session's presence fields.
    #[must_use]
    pub const fn project_session_row(
        &self,
        title_origin: TitleOrigin,
        raw_attention_bytes: u64,
    ) -> SanitizedPresenceProjection {
        let is_meta = matches!(self.mode, PresenceMode::Meta);
        let from_meta_set = matches!(title_origin, TitleOrigin::MetaSet);
        SanitizedPresenceProjection {
            incarnation: self.incarnation,
            emit_role_detail_phase: is_meta,
            emit_title: presence_title_permitted_b125(is_meta, from_meta_set),
            clamped_attention_bytes: presence_attention_clamp_b125(
                raw_attention_bytes,
                self.max_attention_bytes,
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn withholds_osc_titles_always_and_withholds_meta_fields_in_minimal_mode() {
        let mut redactor = PresenceMinimalRedactor::new(PresenceMode::Meta, 3);
        assert_eq!(redactor.on_bridge_attach(4), 4);

        // Even in Meta mode, an OSC title is strictly withheld!
        assert_eq!(
            redactor.project_session_row(TitleOrigin::ProgramOsc, 600),
            SanitizedPresenceProjection {
                incarnation: 4,
                emit_role_detail_phase: true,
                emit_title: false,
                clamped_attention_bytes: MAX_ATTENTION_BYTES,
            }
        );

        // Explicit `meta set title` is emitted in Meta mode.
        assert_eq!(
            redactor.project_session_row(TitleOrigin::MetaSet, 80),
            SanitizedPresenceProjection {
                incarnation: 4,
                emit_role_detail_phase: true,
                emit_title: true,
                clamped_attention_bytes: 80,
            }
        );

        // Minimal mode withholds role, detail, phase, AND meta-set title.
        redactor.set_mode(PresenceMode::Minimal);
        assert_eq!(
            redactor.project_session_row(TitleOrigin::MetaSet, 80),
            SanitizedPresenceProjection {
                incarnation: 4,
                emit_role_detail_phase: false,
                emit_title: false,
                clamped_attention_bytes: 80,
            }
        );
    }
}
