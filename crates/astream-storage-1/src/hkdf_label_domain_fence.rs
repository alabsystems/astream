// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pure stack TLS-1.3-style length-prefixed HKDF `info` domain-separation framer
//! (`Astream.Digest.TlaHkdfLabelDomainFence`).
//!
//! Encodes `(out_len_u16_be || prefix_and_label_len_u8 || "astream-v1 " || label || ctx_len_u8 || ctx)`
//! into a fixed `[u8; 96]` stack buffer with **zero heap allocations** and **zero
//! `unknown` obligations**, eliminating concatenation collisions across distinct
//! cryptographic subsystems (`cap`, `aead`, `at-rest`).

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "hkdf_label_domain_fence_island.rs"]
mod hkdf_label_domain_fence_island;
#[cfg(clean_islands)]
pub use hkdf_label_domain_fence_island::{hkdf_derive_seq_advance, hkdf_label_len_clamp};

/// Maximum domain label length (`1..=32` ASCII bytes).
pub const MAX_HKDF_DOMAIN_LABEL_BYTES: usize = 32;

/// Maximum context digest/salt tag length (`0..=32` bytes).
pub const MAX_HKDF_CONTEXT_BYTES: usize = 32;

/// Fixed stack buffer capacity (`2 + 1 + 11 + 32 + 1 + 32 = 79 <= 96`).
pub const HKDF_INFO_BUF_CAP: usize = 96;

const DOMAIN_NAMESPACE: &[u8; 11] = b"astream-v1 ";

#[cfg(not(clean_islands))]
/// Monotonically advance count of domain-separated HKDF `info` blocks framed.
#[must_use]
pub const fn hkdf_derive_seq_advance(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}

#[cfg(not(clean_islands))]
/// Clamp domain label byte length to `max_label_len`.
#[must_use]
pub const fn hkdf_label_len_clamp(cand_len: u64, max_label_len: u64) -> u64 {
    if cand_len < max_label_len {
        cand_len
    } else {
        max_label_len
    }
}

contract_fn! {
    /// True iff `label_len <= max_label_len`.
    #[must_use]
    pub const fn hkdf_label_valid(label_len: u64, max_label_len: u64) -> bool
    clauses [ensures result == (label_len <= max_label_len)]
    {
        label_len <= max_label_len
    }
}

/// Refusal reasons when framing a domain-separated HKDF `info` block.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum HkdfDomainError {
    EmptyOrOverlongLabel,
    ContextTooLong,
    ZeroOutputLength,
}

/// Pure stack HKDF `info` domain-separation framer.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct HkdfLabelDomainFence {
    derive_seq: u64,
    last_label_len: u64,
}

impl Default for HkdfLabelDomainFence {
    fn default() -> Self {
        Self::new()
    }
}

impl HkdfLabelDomainFence {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            derive_seq: 0,
            last_label_len: 0,
        }
    }

    #[must_use]
    pub const fn derive_seq(&self) -> u64 {
        self.derive_seq
    }

    #[must_use]
    pub const fn last_label_len(&self) -> u64 {
        self.last_label_len
    }

    /// Frame an injective length-prefixed HKDF `info` block into `[u8; HKDF_INFO_BUF_CAP]`.
    pub fn frame_info(
        &mut self,
        output_len: u16,
        label: &[u8],
        context: &[u8],
    ) -> Result<([u8; HKDF_INFO_BUF_CAP], usize), HkdfDomainError> {
        if output_len == 0 {
            return Err(HkdfDomainError::ZeroOutputLength);
        }
        if label.is_empty()
            || !hkdf_label_valid(label.len() as u64, MAX_HKDF_DOMAIN_LABEL_BYTES as u64)
        {
            return Err(HkdfDomainError::EmptyOrOverlongLabel);
        }
        if context.len() > MAX_HKDF_CONTEXT_BYTES {
            return Err(HkdfDomainError::ContextTooLong);
        }

        let clamped_lbl =
            hkdf_label_len_clamp(label.len() as u64, MAX_HKDF_DOMAIN_LABEL_BYTES as u64) as usize;
        self.last_label_len = clamped_lbl as u64;
        let cand_seq = self.derive_seq.saturating_add(1);
        self.derive_seq = hkdf_derive_seq_advance(self.derive_seq, cand_seq);

        let mut buf = [0u8; HKDF_INFO_BUF_CAP];
        let [o0, o1] = output_len.to_be_bytes();
        let full_label_len = DOMAIN_NAMESPACE.len().saturating_add(clamped_lbl);
        buf[0] = o0;
        buf[1] = o1;
        buf[2] = full_label_len as u8;

        let mut pos = 3usize;
        copy_slice_at(&mut buf, pos, DOMAIN_NAMESPACE, DOMAIN_NAMESPACE.len());
        pos = pos.saturating_add(DOMAIN_NAMESPACE.len());

        copy_slice_at(&mut buf, pos, label, clamped_lbl);
        pos = pos.saturating_add(clamped_lbl);

        if let Some(slot) = buf.get_mut(pos) {
            *slot = context.len() as u8;
        }
        pos = pos.saturating_add(1);

        copy_slice_at(&mut buf, pos, context, context.len());
        pos = pos.saturating_add(context.len());

        Ok((buf, pos))
    }
}

fn copy_slice_at(buf: &mut [u8; HKDF_INFO_BUF_CAP], base: usize, src: &[u8], count: usize) {
    let mut k = 0usize;
    while k < count {
        if let (Some(d), Some(&s)) = (buf.get_mut(base.saturating_add(k)), src.get(k)) {
            *d = s;
        }
        k = k.saturating_add(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prevents_label_context_concatenation_collision() {
        let mut fence = HkdfLabelDomainFence::new();
        // ("ab", "c") vs ("a", "bc") MUST produce distinct info byte slices!
        let (b1, n1) = fence.frame_info(32, b"ab", b"c").unwrap();
        let (b2, n2) = fence.frame_info(32, b"a", b"bc").unwrap();
        assert_ne!(&b1[..n1], &b2[..n2]);
        assert_eq!(fence.derive_seq(), 2);

        assert_eq!(
            fence.frame_info(32, b"", b"ctx"),
            Err(HkdfDomainError::EmptyOrOverlongLabel)
        );
        assert_eq!(
            fence.frame_info(0, b"cap", b"ctx"),
            Err(HkdfDomainError::ZeroOutputLength)
        );
    }
}
