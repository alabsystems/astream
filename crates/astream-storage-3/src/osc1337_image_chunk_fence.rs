// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Inline terminal image (`OSC 1337 ; File=...` / Kitty graphics) byte & pixel
//! budget fence (`Astream.Term.TlaOsc1337ImageChunkFence`).
//!
//! Protects `aterm` tabs from memory exhaustion and decompression bombs inside
//! inline image escape sequences by enforcing `accum_bytes <= max_image_bytes`
//! and `pixel_count <= max_pixels` across multi-chunk transfers.

#[cfg(clean_islands)]
#[path = "osc1337_image_chunk_fence_island.rs"]
mod osc1337_image_chunk_fence_island;
#[cfg(clean_islands)]
pub use osc1337_image_chunk_fence_island::{img_bytes_clamp, img_seq_advance};

#[cfg(not(clean_islands))]
/// Clamp accumulated inline-image transfer bytes to `max_bytes`.
#[must_use]
pub const fn img_bytes_clamp(cand_bytes: u64, max_bytes: u64) -> u64 {
    if cand_bytes < max_bytes {
        cand_bytes
    } else {
        max_bytes
    }
}

#[cfg(not(clean_islands))]
/// Monotonically advance completed/aborted image transfer sequence.
#[must_use]
pub const fn img_seq_advance(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}

contract_fn! {
    /// True iff `width_px * height_px` (`total_pixels`) and `next_bytes` fit within budget.
    #[must_use]
    pub const fn img_transfer_admissible(
        next_bytes: u64,
        max_bytes: u64,
        total_pixels: u64,
        max_pixels: u64,
    ) -> bool
    clauses [ensures result == (next_bytes <= max_bytes && total_pixels <= max_pixels)]
    {
        next_bytes <= max_bytes && total_pixels <= max_pixels
    }
}

/// Verdict when feeding an `OSC 1337` or Kitty graphics chunk.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ImageChunkVerdict {
    Accepted {
        accum_bytes: u64,
    },
    RejectedDimension {
        total_pixels: u64,
        max_pixels: u64,
    },
    RejectedByteBudget {
        attempted_bytes: u64,
        max_bytes: u64,
    },
    Completed {
        transfer_seq: u64,
        total_bytes: u64,
    },
}

/// Pure stack inline-image chunk budget fence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Osc1337ImageChunkFence {
    max_image_bytes: u64,
    max_pixels: u64,
    accum_bytes: u64,
    declared_pixels: u64,
    aborted: bool,
    transfer_seq: u64,
}

impl Osc1337ImageChunkFence {
    #[must_use]
    pub const fn new(max_image_bytes: u64, max_pixels: u64) -> Self {
        let b_cap = if max_image_bytes == 0 {
            16 * 1024 * 1024
        } else {
            max_image_bytes
        };
        let p_cap = if max_pixels == 0 {
            4096 * 4096
        } else {
            max_pixels
        };
        Self {
            max_image_bytes: b_cap,
            max_pixels: p_cap,
            accum_bytes: 0,
            declared_pixels: 0,
            aborted: false,
            transfer_seq: 0,
        }
    }

    #[must_use]
    pub const fn accum_bytes(&self) -> u64 {
        self.accum_bytes
    }

    #[must_use]
    pub const fn transfer_seq(&self) -> u64 {
        self.transfer_seq
    }

    /// Start a new image transfer with declared `(width_px, height_px)`.
    pub fn begin_transfer(
        &mut self,
        width_px: u32,
        height_px: u32,
    ) -> Result<(), ImageChunkVerdict> {
        self.accum_bytes = 0;
        let pixels = (width_px as u64).saturating_mul(height_px as u64);
        self.declared_pixels = pixels;
        if pixels == 0 || !img_transfer_admissible(0, self.max_image_bytes, pixels, self.max_pixels)
        {
            self.aborted = true;
            return Err(ImageChunkVerdict::RejectedDimension {
                total_pixels: pixels,
                max_pixels: self.max_pixels,
            });
        }
        self.aborted = false;
        Ok(())
    }

    /// Feed a decoded chunk of `chunk_bytes`.
    pub fn feed_chunk(&mut self, chunk_bytes: u64, is_final: bool) -> ImageChunkVerdict {
        if self.aborted {
            return ImageChunkVerdict::RejectedDimension {
                total_pixels: self.declared_pixels,
                max_pixels: self.max_pixels,
            };
        }
        let next_bytes = self.accum_bytes.saturating_add(chunk_bytes);
        if !img_transfer_admissible(
            next_bytes,
            self.max_image_bytes,
            self.declared_pixels,
            self.max_pixels,
        ) {
            self.aborted = true;
            self.accum_bytes = 0;
            let cand_seq = self.transfer_seq.saturating_add(1);
            self.transfer_seq = img_seq_advance(self.transfer_seq, cand_seq);
            return ImageChunkVerdict::RejectedByteBudget {
                attempted_bytes: next_bytes,
                max_bytes: self.max_image_bytes,
            };
        }
        self.accum_bytes = img_bytes_clamp(next_bytes, self.max_image_bytes);
        if is_final {
            let total = self.accum_bytes;
            self.accum_bytes = 0;
            let cand_seq = self.transfer_seq.saturating_add(1);
            self.transfer_seq = img_seq_advance(self.transfer_seq, cand_seq);
            ImageChunkVerdict::Completed {
                transfer_seq: self.transfer_seq,
                total_bytes: total,
            }
        } else {
            ImageChunkVerdict::Accepted {
                accum_bytes: self.accum_bytes,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_pixel_and_byte_ceilings_on_osc1337_transfers() {
        let mut fence = Osc1337ImageChunkFence::new(4096, 1024 * 1024);
        assert!(fence.begin_transfer(2048, 2048).is_err());

        fence.begin_transfer(256, 256).unwrap();
        assert_eq!(
            fence.feed_chunk(2000, false),
            ImageChunkVerdict::Accepted { accum_bytes: 2000 }
        );
        assert_eq!(
            fence.feed_chunk(1500, true),
            ImageChunkVerdict::Completed {
                transfer_seq: 1,
                total_bytes: 3500,
            }
        );

        fence.begin_transfer(256, 256).unwrap();
        assert_eq!(
            fence.feed_chunk(5000, true),
            ImageChunkVerdict::RejectedByteBudget {
                attempted_bytes: 5000,
                max_bytes: 4096,
            }
        );
    }
}
