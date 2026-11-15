// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bounded `OSC 8` (`ESC ] 8 ; params ; URI ST`) hyperlink arena & URI scheme sanitizer
//! (`Astream.Term.TlaOsc8HyperlinkUriFence`).
//!
//! Protects `astream-term` and `aterm` clickable terminal hyperlinks against unbounded `OSC 8`
//! link-table growth, control-character injection, and dangerous URI schemes (`javascript:`,
//! `data:`, `vbscript:`), while enabling safe `file://`, `https://`, and `http://` links.

#[cfg(clean_islands)]
#[path = "osc8_hyperlink_uri_fence_island.rs"]
mod osc8_hyperlink_uri_fence_island;
#[cfg(clean_islands)]
pub use osc8_hyperlink_uri_fence_island::{osc8_epoch_advance_b108, osc8_slot_clamp_b108};

#[cfg(not(clean_islands))]
/// Clamp active `OSC 8` link-table entries to `max_slots`.
#[must_use]
pub const fn osc8_slot_clamp_b108(cand_slots: u64, max_slots: u64) -> u64 {
    if cand_slots < max_slots {
        cand_slots
    } else {
        max_slots
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance the `OSC 8` hyperlink table generation.
#[must_use]
pub const fn osc8_epoch_advance_b108(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `uri_len` is non-empty and within `max_uri_bytes`.
    #[must_use]
    pub const fn osc8_uri_len_valid_b108(uri_len: u64, max_uri_bytes: u64) -> bool
    clauses [ensures result == (0 < uri_len && uri_len <= max_uri_bytes)]
    {
        0 < uri_len && uri_len <= max_uri_bytes
    }
}

/// Maximum concurrent deduplicated `OSC 8` hyperlink digests per screen ring.
pub const MAX_OSC8_SLOTS: usize = 16;
/// Maximum permitted `OSC 8` URI byte length.
pub const MAX_OSC8_URI_BYTES: u64 = 2048;

/// Verdict for an `OSC 8` URI sequence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Osc8Verdict {
    ClosedLink,
    Accepted { slot_index: usize, epoch: u64 },
    RejectedInvalidLength { uri_len: usize },
    RejectedControlOrScheme,
}

fn has_ascii_prefix_ignore_case(mut bytes: &[u8], mut prefix_lower: &[u8]) -> bool {
    while let [pb, p_tail @ ..] = prefix_lower {
        let [b, b_tail @ ..] = bytes else {
            return false;
        };
        if b.to_ascii_lowercase() != *pb {
            return false;
        }
        prefix_lower = p_tail;
        bytes = b_tail;
    }
    prefix_lower.is_empty()
}

/// Bounded `OSC 8` hyperlink URI sanitizer and ring-evicting deduplicator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Osc8HyperlinkUriFence {
    digests: [u64; MAX_OSC8_SLOTS],
    used_slots: u64,
    evict_cursor: usize,
    epoch: u64,
}

impl Default for Osc8HyperlinkUriFence {
    fn default() -> Self {
        Self::new()
    }
}

impl Osc8HyperlinkUriFence {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            digests: [0; MAX_OSC8_SLOTS],
            used_slots: 0,
            evict_cursor: 0,
            epoch: 0,
        }
    }

    #[must_use]
    pub const fn used_slots(&self) -> u64 {
        self.used_slots
    }

    /// Validate `uri` bytes and intern `uri_digest` into the bounded 16-slot ring.
    pub fn intern_uri(&mut self, uri: &[u8], uri_digest: u64) -> Osc8Verdict {
        if uri.is_empty() {
            return Osc8Verdict::ClosedLink;
        }
        if !osc8_uri_len_valid_b108(uri.len() as u64, MAX_OSC8_URI_BYTES) {
            return Osc8Verdict::RejectedInvalidLength { uri_len: uri.len() };
        }
        let mut scan = uri;
        while let [b, tail @ ..] = scan {
            if *b <= 0x20 || *b == 0x7f {
                return Osc8Verdict::RejectedControlOrScheme;
            }
            scan = tail;
        }
        let safe_scheme = has_ascii_prefix_ignore_case(uri, b"file://")
            || has_ascii_prefix_ignore_case(uri, b"https://")
            || has_ascii_prefix_ignore_case(uri, b"http://");
        if !safe_scheme {
            return Osc8Verdict::RejectedControlOrScheme;
        }

        let next_ep = self.epoch.saturating_add(1);
        self.epoch = osc8_epoch_advance_b108(self.epoch, next_ep);

        let count = self.used_slots as usize;
        let mut s = 0usize;
        while s < count {
            let Some(&existing) = self.digests.get(s) else {
                break;
            };
            if existing == uri_digest {
                return Osc8Verdict::Accepted {
                    slot_index: s,
                    epoch: self.epoch,
                };
            }
            s = s.saturating_add(1);
        }
        if let Some(dst) = self.digests.get_mut(count) {
            *dst = uri_digest;
            let cand = self.used_slots.saturating_add(1);
            self.used_slots = osc8_slot_clamp_b108(cand, MAX_OSC8_SLOTS as u64);
            Osc8Verdict::Accepted {
                slot_index: count,
                epoch: self.epoch,
            }
        } else {
            let target = self.evict_cursor % MAX_OSC8_SLOTS;
            if let Some(dst) = self.digests.get_mut(target) {
                *dst = uri_digest;
            }
            self.evict_cursor = target.wrapping_add(1) % MAX_OSC8_SLOTS;
            Osc8Verdict::Accepted {
                slot_index: target,
                epoch: self.epoch,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accepts_file_and_https_while_blocking_javascript_and_control_bytes() {
        let mut fence = Osc8HyperlinkUriFence::new();
        assert_eq!(
            fence.intern_uri(b"file:///fixture-home/astream/README.md", 0x1111),
            Osc8Verdict::Accepted {
                slot_index: 0,
                epoch: 1,
            }
        );
        assert_eq!(
            fence.intern_uri(b"javascript:alert(1)", 0x2222),
            Osc8Verdict::RejectedControlOrScheme
        );
        assert_eq!(
            fence.intern_uri(b"https://example.com/\x1b]52;c;bad", 0x3333),
            Osc8Verdict::RejectedControlOrScheme
        );
    }
}
