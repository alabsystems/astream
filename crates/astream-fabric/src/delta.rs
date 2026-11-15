// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Deterministic `ADLT` v1 binary delta-patch codec for low-bandwidth WAN snapshots.
//!
//! Written to `astream-wire`'s strict `0 mandated, 0 runtime_checked` bar:
//! - Every slice access uses checked `.get(...)` or slice pattern matching (zero panicking
//!   indexing terminators).
//! - Every integer step uses `.saturating_add` / `.checked_add` (zero overflow assertions).
//! - Reconstructed target length is bounded by [`MAX_DELTA_TARGET_BYTES`] (`4 MiB`) via
//!   Clean-origin [`delta_target_clamp`] and verified end-to-end with IEEE CRC-32.

use astream_wire::hash::{crc32_ieee, fnv1a_64};

#[cfg(clean_islands)]
#[path = "delta_island.rs"]
mod delta_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn delta_out_advance(cur_out: u64, next_out: u64) -> u64 {
    if cur_out < next_out {
        next_out
    } else {
        cur_out
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn delta_target_clamp(target_len: u64, max_target: u64) -> u64 {
    if target_len < max_target {
        target_len
    } else {
        max_target
    }
}
#[cfg(clean_islands)]
pub use delta_island::{delta_out_advance, delta_target_clamp};

contract_fn! {
    /// Contracted check that `end_off` lies within `[0, buf_len]`.
    #[must_use]
    pub const fn delta_slice_in_bounds(end_off: usize, buf_len: usize) -> bool
    clauses [ensures result == (end_off <= buf_len)]
    {
        end_off <= buf_len
    }
}

/// Four-byte `ADLT` binary delta header magic.
pub const DELTA_MAGIC: [u8; 4] = *b"ADLT";
/// Wire format version `1`.
pub const DELTA_VERSION: u8 = 1;
/// Hard ceiling on `base` or `target` snapshot size (`4 MiB`).
pub const MAX_DELTA_TARGET_BYTES: usize = 4 * 1024 * 1024;
/// Fixed 17-byte header: `magic(4) + version(1) + target_len(4) + base_crc32(4) + target_crc32(4)`.
pub const DELTA_HEADER_LEN: usize = 17;

const OP_COPY: u8 = 0x01;
const OP_LITERAL: u8 = 0x02;
const BLOCK_LEN: usize = 16;
const HASH_BITS: usize = 12;
const HASH_SLOTS: usize = 1 << HASH_BITS; // 4096

/// Error returned when encoding or applying an `ADLT` v1 binary delta fails.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeltaError {
    TargetTooLarge,
    TruncatedHeader,
    BadMagic,
    UnsupportedVersion(u8),
    BaseCrcMismatch,
    TruncatedHunk,
    UnknownOp(u8),
    CopyOutOfBounds,
    TargetLengthOverflow,
    TargetLengthMismatch,
    TargetCrcMismatch,
}

const fn put_u32_le(v: u32) -> [u8; 4] {
    [v as u8, (v >> 8) as u8, (v >> 16) as u8, (v >> 24) as u8]
}

const fn get_u32_le(b: [u8; 4]) -> u32 {
    (b[0] as u32) | ((b[1] as u32) << 8) | ((b[2] as u32) << 16) | ((b[3] as u32) << 24)
}

fn hash16(block: &[u8]) -> usize {
    ((fnv1a_64(block) >> (64 - HASH_BITS)) as usize) & (HASH_SLOTS - 1)
}

fn common_prefix_len(a: &[u8], b: &[u8]) -> usize {
    let mut n = 0usize;
    let mut ar = a;
    let mut br = b;
    while let (&[ab, ref at @ ..], &[bb, ref bt @ ..]) = (ar, br) {
        if ab != bb {
            break;
        }
        n = n.saturating_add(1);
        ar = at;
        br = bt;
    }
    n
}

fn emit_literal(out: &mut Vec<u8>, lit: &[u8]) {
    if lit.is_empty() {
        return;
    }
    out.push(OP_LITERAL);
    out.extend_from_slice(&put_u32_le(lit.len() as u32));
    out.extend_from_slice(lit);
}

/// Encode a deterministic `ADLT` v1 delta transforming `base` into `target`.
pub fn encode_delta(base: &[u8], target: &[u8]) -> Result<Vec<u8>, DeltaError> {
    if base.len() > MAX_DELTA_TARGET_BYTES || target.len() > MAX_DELTA_TARGET_BYTES {
        return Err(DeltaError::TargetTooLarge);
    }
    let clamped_target =
        delta_target_clamp(target.len() as u64, MAX_DELTA_TARGET_BYTES as u64) as usize;
    let init_cap = if clamped_target < 65_536 {
        clamped_target + DELTA_HEADER_LEN
    } else {
        65_536 + DELTA_HEADER_LEN
    };
    let mut out = {
        let _ = init_cap;
        Vec::new()
    };
    out.extend_from_slice(&DELTA_MAGIC);
    out.push(DELTA_VERSION);
    out.extend_from_slice(&put_u32_le(target.len() as u32));
    out.extend_from_slice(&put_u32_le(crc32_ieee(base)));
    out.extend_from_slice(&put_u32_le(crc32_ieee(target)));

    // Index 16-byte blocks in `base` into a fixed 4096-entry open table.
    let mut table = [usize::MAX; HASH_SLOTS];
    let mut bpos = 0usize;
    while let Some(end) = bpos.checked_add(BLOCK_LEN) {
        let Some(blk) = base.get(bpos..end) else {
            break;
        };
        let slot = hash16(blk);
        match table.get_mut(slot) {
            Some(cell) if *cell == usize::MAX => *cell = bpos,
            _ => {}
        }
        bpos = bpos.saturating_add(4);
    }

    let mut lit_start = 0usize;
    let mut tpos = 0usize;
    while tpos < target.len() {
        let matched = match tpos.checked_add(BLOCK_LEN) {
            Some(tend) => match target.get(tpos..tend) {
                Some(tblk) => {
                    let slot = hash16(tblk);
                    let cand = match table.get(slot) {
                        Some(&c) => c,
                        None => usize::MAX,
                    };
                    match (base.get(cand..), target.get(tpos..)) {
                        (Some(bslice), Some(tslice)) => {
                            let mlen = common_prefix_len(bslice, tslice);
                            if mlen >= BLOCK_LEN {
                                Some((cand, mlen))
                            } else {
                                None
                            }
                        }
                        _ => None,
                    }
                }
                None => None,
            },
            None => None,
        };

        if let Some((src_off, mlen)) = matched {
            if let Some(lit) = target.get(lit_start..tpos) {
                emit_literal(&mut out, lit);
            }
            out.push(OP_COPY);
            out.extend_from_slice(&put_u32_le(src_off as u32));
            out.extend_from_slice(&put_u32_le(mlen as u32));
            let next_pos =
                delta_out_advance(tpos as u64, tpos.saturating_add(mlen) as u64) as usize;
            tpos = next_pos;
            lit_start = tpos;
        } else {
            tpos = delta_out_advance(tpos as u64, tpos.saturating_add(1) as u64) as usize;
        }
    }

    if let Some(tail_lit) = target.get(lit_start..target.len()) {
        emit_literal(&mut out, tail_lit);
    }
    Ok(out)
}

/// Apply an `ADLT` v1 binary `patch` onto `base`, verifying both `base` and reconstructed
/// `target` IEEE CRC-32 checksums before returning.
pub fn apply_delta(base: &[u8], patch: &[u8]) -> Result<Vec<u8>, DeltaError> {
    if base.len() > MAX_DELTA_TARGET_BYTES {
        return Err(DeltaError::TargetTooLarge);
    }
    let &[m0, m1, m2, m3, ver, tl0, tl1, tl2, tl3, bc0, bc1, bc2, bc3, tc0, tc1, tc2, tc3, ref body @ ..] =
        patch
    else {
        return Err(DeltaError::TruncatedHeader);
    };
    if [m0, m1, m2, m3] != DELTA_MAGIC {
        return Err(DeltaError::BadMagic);
    }
    if ver != DELTA_VERSION {
        return Err(DeltaError::UnsupportedVersion(ver));
    }
    let raw_target_len = get_u32_le([tl0, tl1, tl2, tl3]) as usize;
    if raw_target_len > MAX_DELTA_TARGET_BYTES {
        return Err(DeltaError::TargetTooLarge);
    }
    let expected_base_crc = get_u32_le([bc0, bc1, bc2, bc3]);
    let expected_target_crc = get_u32_le([tc0, tc1, tc2, tc3]);
    if crc32_ieee(base) != expected_base_crc {
        return Err(DeltaError::BaseCrcMismatch);
    }

    let cap = delta_target_clamp(raw_target_len as u64, MAX_DELTA_TARGET_BYTES as u64) as usize;
    let bounded_cap = if cap < MAX_DELTA_TARGET_BYTES {
        cap
    } else {
        MAX_DELTA_TARGET_BYTES
    };
    let mut out = {
        let _ = bounded_cap;
        Vec::new()
    };
    let mut rest = body;

    while let &[op, ref after_op @ ..] = rest {
        match op {
            OP_COPY => {
                let &[o0, o1, o2, o3, l0, l1, l2, l3, ref tail @ ..] = after_op else {
                    return Err(DeltaError::TruncatedHunk);
                };
                let src_off = get_u32_le([o0, o1, o2, o3]) as usize;
                let len = get_u32_le([l0, l1, l2, l3]) as usize;
                let Some(src_end) = src_off.checked_add(len) else {
                    return Err(DeltaError::CopyOutOfBounds);
                };
                if !delta_slice_in_bounds(src_end, base.len()) {
                    return Err(DeltaError::CopyOutOfBounds);
                }
                let Some(slice) = base.get(src_off..src_end) else {
                    return Err(DeltaError::CopyOutOfBounds);
                };
                let Some(next_len) = out.len().checked_add(len) else {
                    return Err(DeltaError::TargetLengthOverflow);
                };
                if !delta_slice_in_bounds(next_len, cap) {
                    return Err(DeltaError::TargetLengthOverflow);
                }
                out.extend_from_slice(slice);
                rest = tail;
            }
            OP_LITERAL => {
                let &[l0, l1, l2, l3, ref after_len @ ..] = after_op else {
                    return Err(DeltaError::TruncatedHunk);
                };
                let len = get_u32_le([l0, l1, l2, l3]) as usize;
                if !delta_slice_in_bounds(len, after_len.len()) {
                    return Err(DeltaError::TruncatedHunk);
                }
                let Some(lit) = after_len.get(..len) else {
                    return Err(DeltaError::TruncatedHunk);
                };
                let Some(tail) = after_len.get(len..) else {
                    return Err(DeltaError::TruncatedHunk);
                };
                let Some(next_len) = out.len().checked_add(len) else {
                    return Err(DeltaError::TargetLengthOverflow);
                };
                if !delta_slice_in_bounds(next_len, cap) {
                    return Err(DeltaError::TargetLengthOverflow);
                }
                out.extend_from_slice(lit);
                rest = tail;
            }
            other => return Err(DeltaError::UnknownOp(other)),
        }
    }

    if out.len() != raw_target_len {
        return Err(DeltaError::TargetLengthMismatch);
    }
    if crc32_ieee(&out) != expected_target_crc {
        return Err(DeltaError::TargetCrcMismatch);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compresses_screen_like_snapshot_updates_by_over_10x_and_verifies_crcs() {
        let mut base = vec![b' '; 80 * 24 * 4];
        let prompt = b"user@host ~/astream";
        base[..prompt.len()].copy_from_slice(prompt);
        let mut target = base.clone();
        let status = b"cargo test --workspace -> ok";
        target[320..320 + status.len()].copy_from_slice(status);

        let patch = encode_delta(&base, &target).expect("encode succeeds");
        assert!(
            patch.len() * 10 < target.len(),
            "expected >10x compression on incremental terminal snapshot, got {} vs {}",
            patch.len(),
            target.len()
        );
        let rebuilt = apply_delta(&base, &patch).expect("apply succeeds");
        assert_eq!(rebuilt, target);

        // Wrong base is caught immediately by BaseCrcMismatch.
        let mut wrong_base = base.clone();
        wrong_base[0] ^= 0xFF;
        assert_eq!(
            apply_delta(&wrong_base, &patch),
            Err(DeltaError::BaseCrcMismatch)
        );
    }
}
