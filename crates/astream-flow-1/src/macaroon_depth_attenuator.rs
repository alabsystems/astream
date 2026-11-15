// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Offline bearer-attenuated Macaroon chain depth & expiry narrowing planner
//! (`Astream.Cap.TlaMacaroonAttenuation`).
//!
//! Coordinates offline `via=<hex-parent-grant>` capability delegation from an `aterm`
//! supervisor session to spawned Claude Code / `codex-alab` / `agy` worker tabs without
//! exposing the broker's root HMAC mint secret:
//! - Enforces `chain_depth <= MAX_MACAROON_DEPTH` (`8`).
//! - Narrows expiry monotonically (`child_expiry_ms <= parent_expiry_ms`) and mode
//!   monotonically (`ro <= rw`).

#[cfg(clean_islands)]
#[path = "macaroon_depth_attenuator_island.rs"]
mod macaroon_depth_attenuator_island;
#[cfg(clean_islands)]
pub use macaroon_depth_attenuator_island::{macaroon_depth_clamp, macaroon_expiry_narrow};

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn macaroon_depth_clamp(depth: u64, max_depth: u64) -> u64 {
    if depth < max_depth {
        depth
    } else {
        max_depth
    }
}

#[cfg(not(clean_islands))]
#[inline]
#[must_use]
pub const fn macaroon_expiry_narrow(child_exp: u64, parent_exp: u64) -> u64 {
    if child_exp < parent_exp {
        child_exp
    } else {
        parent_exp
    }
}

contract_fn! {
    /// Verified check that a child Macaroon deadline does not widen its parent's deadline
    /// (`child_exp <= parent_exp`), linked via `clean-kernel-defeq` to
    /// `macaroon_expiry_within_parent_isl`.
    #[must_use]
    pub const fn macaroon_expiry_within_parent(
        child_exp: u64,
        parent_exp: u64,
    ) -> bool
    clauses [ensures result == (child_exp <= parent_exp)]
    {
        child_exp <= parent_exp
    }
}

/// Maximum number of `via=` offline attenuation links accepted by `astream-cap`.
pub const MAX_MACAROON_DEPTH: u64 = 8;

/// Access mode lattice (`ReadOnly <= ReadWrite`) for Macaroon link validation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AttenuatedMode {
    /// Read-only (`ro:`).
    ReadOnly,
    /// Read-write (`rw:`).
    ReadWrite,
}

impl AttenuatedMode {
    /// Returns `true` iff `child` is no wider than `self` (`ro <= rw`).
    #[must_use]
    pub const fn allows_child_mode(self, child: Self) -> bool {
        !matches!((self, child), (Self::ReadOnly, Self::ReadWrite))
    }
}

/// Result of attempting to append one offline Macaroon attenuation step.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MacaroonLinkResult {
    /// Attenuation accepted; returns `(new_depth, narrowed_expiry_ms, child_mode)`.
    Accepted {
        /// Updated chain depth (`1..=MAX_MACAROON_DEPTH`).
        new_depth: u64,
        /// Narrowed effective deadline (`<= parent_expiry_ms`).
        narrowed_expiry_ms: u64,
        /// Narrowed mode.
        mode: AttenuatedMode,
    },
    /// Refused because `chain_depth` already reached `MAX_MACAROON_DEPTH`.
    DepthExceeded,
    /// Refused because `requested_expiry_ms > parent_expiry_ms` attempted to widen authority.
    ExpiryWidened,
    /// Refused because `ro -> rw` attempted to widen mode authority.
    ModeWidened,
}

/// Stateful offline Macaroon chain narrowing tracker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MacaroonDepthAttenuator {
    chain_depth: u64,
    max_depth: u64,
    current_expiry_ms: u64,
    parent_expiry_ms: u64,
    mode: AttenuatedMode,
}

impl MacaroonDepthAttenuator {
    /// Anchor a new delegation chain on a root grant with `root_expiry_ms` (`u64::MAX` for
    /// non-expiring) and `root_mode`.
    #[must_use]
    pub const fn from_root(root_expiry_ms: u64, root_mode: AttenuatedMode) -> Self {
        Self {
            chain_depth: 0,
            max_depth: MAX_MACAROON_DEPTH,
            current_expiry_ms: root_expiry_ms,
            parent_expiry_ms: root_expiry_ms,
            mode: root_mode,
        }
    }

    /// Current `via=` link count (`<= MAX_MACAROON_DEPTH`).
    #[must_use]
    pub const fn chain_depth(&self) -> u64 {
        self.chain_depth
    }

    /// Configured maximum chain depth (`MAX_MACAROON_DEPTH`).
    #[must_use]
    pub const fn max_depth(&self) -> u64 {
        self.max_depth
    }

    /// Current effective deadline in Unix ms (`<= parent_expiry_ms`).
    #[must_use]
    pub const fn current_expiry_ms(&self) -> u64 {
        self.current_expiry_ms
    }

    /// Immediate parent link's deadline in Unix ms.
    #[must_use]
    pub const fn parent_expiry_ms(&self) -> u64 {
        self.parent_expiry_ms
    }

    /// Current access mode.
    #[must_use]
    pub const fn mode(&self) -> AttenuatedMode {
        self.mode
    }

    /// Validate and append one child attenuation link `(requested_expiry_ms, child_mode)`.
    pub fn attenuate(
        &mut self,
        requested_expiry_ms: u64,
        child_mode: AttenuatedMode,
    ) -> MacaroonLinkResult {
        if !self.mode.allows_child_mode(child_mode) {
            return MacaroonLinkResult::ModeWidened;
        }
        if self.chain_depth >= self.max_depth {
            return MacaroonLinkResult::DepthExceeded;
        }
        if !macaroon_expiry_within_parent(requested_expiry_ms, self.current_expiry_ms) {
            return MacaroonLinkResult::ExpiryWidened;
        }
        let raw_depth = self.chain_depth.saturating_add(1);
        self.parent_expiry_ms = self.current_expiry_ms;
        self.chain_depth = macaroon_depth_clamp(raw_depth, self.max_depth);
        self.current_expiry_ms = macaroon_expiry_narrow(requested_expiry_ms, self.parent_expiry_ms);
        self.mode = child_mode;
        MacaroonLinkResult::Accepted {
            new_depth: self.chain_depth,
            narrowed_expiry_ms: self.current_expiry_ms,
            mode: self.mode,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_max_depth_eight_monotone_expiry_and_ro_mode_narrowing() {
        let mut att = MacaroonDepthAttenuator::from_root(10_000, AttenuatedMode::ReadWrite);
        assert_eq!(att.parent_expiry_ms(), 10_000);
        assert_eq!(att.mode(), AttenuatedMode::ReadWrite);

        // Extending expiry past 10_000 is refused!
        assert_eq!(
            att.attenuate(12_000, AttenuatedMode::ReadWrite),
            MacaroonLinkResult::ExpiryWidened
        );

        // Narrowing rw -> ro with tighter expiry 9_000 succeeds.
        assert_eq!(
            att.attenuate(9_000, AttenuatedMode::ReadOnly),
            MacaroonLinkResult::Accepted {
                new_depth: 1,
                narrowed_expiry_ms: 9_000,
                mode: AttenuatedMode::ReadOnly,
            }
        );

        // Escalating ro -> rw is refused!
        assert_eq!(
            att.attenuate(8_000, AttenuatedMode::ReadWrite),
            MacaroonLinkResult::ModeWidened
        );

        // Append links 2..=8 cleanly, then link 9 hits DepthExceeded!
        let mut step = 2u64;
        while step <= MAX_MACAROON_DEPTH {
            let exp = 9_000 - step * 100;
            assert!(matches!(
                att.attenuate(exp, AttenuatedMode::ReadOnly),
                MacaroonLinkResult::Accepted { .. }
            ));
            step += 1;
        }
        assert_eq!(att.chain_depth(), MAX_MACAROON_DEPTH);
        assert!(att.current_expiry_ms() <= att.parent_expiry_ms());
        assert_eq!(
            att.attenuate(5_000, AttenuatedMode::ReadOnly),
            MacaroonLinkResult::DepthExceeded
        );
    }
}
