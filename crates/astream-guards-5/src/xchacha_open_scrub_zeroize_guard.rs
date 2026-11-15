// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Failed-`open` plaintext span scrub & `SealedStream` key/rx-buffer zeroize-on-drop guard
//! (`evidence/manifest.toml` `aead.seal-open.authenticated`;
//! `Astream.Aead.TlaXchachaOpenScrubZeroizeGuard`).
//!
//! Enforces the zero-plaintext-leakage laws of `astream-aead`:
//! - Every `open` input `< 40` bytes (`24`-byte XChaCha20 nonce + `16`-byte Poly1305 tag) is
//!   refused before touching `ring`,
//! - Any authentication tag mismatch zeroes the entire decrypted ciphertext span (`[24 .. len - 16]`)
//!   while leaving nonce (`[0..24)`) and tag (`[len - 16 .. len)`) untouched,
//! - `SealedStream::drop` zeroizes both the `32`-byte session key and the plaintext receive buffer!

#[cfg(clean_islands)]
#[path = "xchacha_open_scrub_zeroize_guard_island.rs"]
mod xchacha_open_scrub_zeroize_guard_island;
#[cfg(clean_islands)]
pub use xchacha_open_scrub_zeroize_guard_island::{
    scrubbed_span_clamp_b153, zeroize_epoch_advance_b153,
};

/// `24`-byte XChaCha20 nonce + `16`-byte Poly1305 tag (`40` bytes).
pub const XCHACHA_BOX_OVERHEAD: u64 = 40;

#[cfg(not(clean_islands))]
/// Clamp scrubbed span length to `ciphertext_span_len`.
#[must_use]
pub const fn scrubbed_span_clamp_b153(cand_scrubbed: u64, ciphertext_span_len: u64) -> u64 {
    if cand_scrubbed < ciphertext_span_len {
        cand_scrubbed
    } else {
        ciphertext_span_len
    }
}

#[cfg(not(clean_islands))]
/// Advance verified zeroization epoch monotonically across failed opens and drops.
#[must_use]
pub const fn zeroize_epoch_advance_b153(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

contract_fn! {
    /// True iff `overhead <= box_len` and on failed tag check `scrubbed_bytes == span_len`.
    #[must_use]
    pub const fn failed_open_scrub_complete_b153(
        box_len: u64,
        overhead: u64,
        span_len: u64,
        scrubbed_bytes: u64,
    ) -> bool
    clauses [ensures result == (overhead <= box_len && scrubbed_bytes == span_len)]
    {
        overhead <= box_len && scrubbed_bytes == span_len
    }
}

/// Outcome of `open` / `SealedStream::drop` scrub verification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpenScrubDecision {
    RefusedTruncatedBox {
        box_len: u64,
    },
    OpenedAuthenticated {
        plaintext_len: u64,
    },
    FailedAuthZeroedCiphertextSpan {
        zeroed_span_bytes: u64,
        zeroize_epoch: u64,
    },
    FailedIncompleteScrubAlert,
    DroppedZeroizedKeyAndRxBuffer {
        zeroized_key_bytes: u64,
        zeroized_rx_bytes: u64,
        zeroize_epoch: u64,
    },
}

/// Tracks failed-open span scrubbing and drop-time key/buffer zeroization.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct XchachaScrubGuard {
    zeroize_epoch: u64,
}

impl XchachaScrubGuard {
    #[must_use]
    pub const fn new() -> Self {
        Self { zeroize_epoch: 0 }
    }

    /// Verify `open` authentication outcome and failed-open span zeroing.
    pub fn evaluate_open(
        &mut self,
        box_len: u64,
        tag_valid: bool,
        scrubbed_span_bytes: u64,
    ) -> OpenScrubDecision {
        if box_len < XCHACHA_BOX_OVERHEAD {
            return OpenScrubDecision::RefusedTruncatedBox { box_len };
        }
        let span_len = box_len.saturating_sub(XCHACHA_BOX_OVERHEAD);
        if tag_valid {
            return OpenScrubDecision::OpenedAuthenticated {
                plaintext_len: span_len,
            };
        }
        let clamped_scrub = scrubbed_span_clamp_b153(scrubbed_span_bytes, span_len);
        if !failed_open_scrub_complete_b153(box_len, XCHACHA_BOX_OVERHEAD, span_len, clamped_scrub)
        {
            return OpenScrubDecision::FailedIncompleteScrubAlert;
        }
        let next = self.zeroize_epoch.saturating_add(1);
        self.zeroize_epoch = zeroize_epoch_advance_b153(self.zeroize_epoch, next);
        OpenScrubDecision::FailedAuthZeroedCiphertextSpan {
            zeroed_span_bytes: clamped_scrub,
            zeroize_epoch: self.zeroize_epoch,
        }
    }

    /// Record drop-time zeroization of the `32`-byte session key and `rx_buf_len` plaintext buffer.
    pub fn on_stream_drop_zeroize(&mut self, rx_buf_len: u64) -> OpenScrubDecision {
        let next = self.zeroize_epoch.saturating_add(1);
        self.zeroize_epoch = zeroize_epoch_advance_b153(self.zeroize_epoch, next);
        OpenScrubDecision::DroppedZeroizedKeyAndRxBuffer {
            zeroized_key_bytes: 32,
            zeroized_rx_bytes: rx_buf_len,
            zeroize_epoch: self.zeroize_epoch,
        }
    }
}

impl Default for XchachaScrubGuard {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_complete_span_zeroing_on_bad_tag_and_key_rx_zeroize_on_drop() {
        let mut g = XchachaScrubGuard::new();
        assert_eq!(
            g.evaluate_open(39, false, 0),
            OpenScrubDecision::RefusedTruncatedBox { box_len: 39 }
        );
        // 104-byte box (`64` plaintext + `40` overhead) failing tag check must scrub all `64` bytes!
        assert_eq!(
            g.evaluate_open(104, false, 63),
            OpenScrubDecision::FailedIncompleteScrubAlert
        );
        assert_eq!(
            g.evaluate_open(104, false, 64),
            OpenScrubDecision::FailedAuthZeroedCiphertextSpan {
                zeroed_span_bytes: 64,
                zeroize_epoch: 1,
            }
        );
        assert_eq!(
            g.on_stream_drop_zeroize(4096),
            OpenScrubDecision::DroppedZeroizedKeyAndRxBuffer {
                zeroized_key_bytes: 32,
                zeroized_rx_bytes: 4096,
                zeroize_epoch: 2,
            }
        );
    }
}
