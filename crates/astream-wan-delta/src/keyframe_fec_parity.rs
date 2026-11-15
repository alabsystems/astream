// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Systematic `K + 1` XOR Forward Error Correction (`FEC`) parity shard codec recovering any
//! single lost WAN keyframe shard in `0` extra RTTs (`Astream.WanDelta.TlaKeyframeFecParity`).

#[cfg(clean_islands)]
#[path = "keyframe_fec_parity_island.rs"]
mod keyframe_fec_parity_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn fec_shards_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn fec_group_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use keyframe_fec_parity_island::{fec_group_advance, fec_shards_clamp};

/// Maximum data shards per XOR parity group.
pub const MAX_FEC_DATA_SHARDS: u64 = 16;
/// Maximum byte length per FEC shard (`64 KiB`).
pub const MAX_FEC_SHARD_BYTES: usize = 65_536;

contract_fn! {
    /// Verified recoverability check (`threshold <= observed`, i.e. `data_count <= received_total`),
    /// linked via `clean-kernel-defeq` to `fec_recoverable_isl`.
    #[must_use]
    pub const fn fec_recoverable(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Computes the equal-length XOR parity shard across `data_shards`.
pub fn compute_xor_parity_shard(
    data_shards: &[Vec<u8>],
    shard_len: usize,
) -> Result<Vec<u8>, &'static str> {
    if shard_len > MAX_FEC_SHARD_BYTES {
        return Err("shard length exceeds MAX_FEC_SHARD_BYTES");
    }
    let k = fec_shards_clamp(data_shards.len() as u64, MAX_FEC_DATA_SHARDS) as usize;
    if k == 0 || k != data_shards.len() {
        return Err("invalid FEC group size");
    }
    let mut parity = Vec::new();
    let mut z = 0usize;
    while z < shard_len {
        parity.push(0u8);
        z = z.saturating_add(1);
    }
    for s in data_shards {
        if s.len() != shard_len {
            return Err("non-uniform shard length");
        }
        let mut j = 0usize;
        while j < shard_len {
            if let (Some(p), Some(&b)) = (parity.get_mut(j), s.get(j)) {
                *p ^= b;
            }
            j = j.saturating_add(1);
        }
    }
    let _ = fec_group_advance(0, 1);
    Ok(parity)
}

/// Reconstructs `shards` (`Option<Vec<u8>>` of length `K`) using `parity` when at most 1 shard is `None`.
pub fn reconstruct_missing_shard(
    shards: &[Option<Vec<u8>>],
    parity: Option<&[u8]>,
    shard_len: usize,
) -> Result<Vec<Vec<u8>>, &'static str> {
    if shard_len > MAX_FEC_SHARD_BYTES {
        return Err("shard length exceeds MAX_FEC_SHARD_BYTES");
    }
    let k = fec_shards_clamp(shards.len() as u64, MAX_FEC_DATA_SHARDS) as usize;
    if k == 0 || k != shards.len() {
        return Err("invalid FEC group size");
    }
    if let Some(par) = parity {
        if par.len() != shard_len {
            return Err("bad parity length");
        }
    }
    let mut present_data = 0u64;
    let mut missing_idx: Option<usize> = None;
    let mut idx = 0usize;
    while idx < shards.len() {
        match shards.get(idx) {
            Some(Some(s)) => {
                if s.len() != shard_len {
                    return Err("bad shard length");
                }
                present_data = present_data.saturating_add(1);
            }
            Some(None) => {
                if missing_idx.is_none() {
                    missing_idx = Some(idx);
                }
            }
            None => break,
        }
        idx = idx.saturating_add(1);
    }
    let parity_count = if parity.is_some() { 1u64 } else { 0u64 };
    let total_present = present_data.saturating_add(parity_count);
    if !fec_recoverable(total_present, shards.len() as u64) {
        return Err("too many missing shards for single-parity FEC recovery");
    }
    let mut out = Vec::new();
    if let Some(m_idx) = missing_idx {
        let Some(par) = parity else {
            return Err("parity required to recover missing data shard");
        };
        let mut rec = Vec::new();
        rec.extend_from_slice(par);
        let mut scan = 0usize;
        while scan < shards.len() {
            if scan != m_idx {
                let Some(Some(s)) = shards.get(scan) else {
                    return Err("multiple missing shards");
                };
                let mut j = 0usize;
                while j < shard_len {
                    if let (Some(r), Some(&b)) = (rec.get_mut(j), s.get(j)) {
                        *r ^= b;
                    }
                    j = j.saturating_add(1);
                }
            }
            scan = scan.saturating_add(1);
        }
        let mut emit = 0usize;
        while emit < shards.len() {
            if emit == m_idx {
                out.push(rec.clone());
            } else if let Some(Some(s)) = shards.get(emit) {
                out.push(s.clone());
            }
            emit = emit.saturating_add(1);
        }
    } else {
        let mut emit = 0usize;
        while emit < shards.len() {
            if let Some(Some(s)) = shards.get(emit) {
                out.push(s.clone());
            }
            emit = emit.saturating_add(1);
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn xor_fec_recovers_dropped_middle_keyframe_shard_in_zero_rtts() {
        let d0 = b"SHARD-00".to_vec();
        let d1 = b"SHARD-01".to_vec();
        let d2 = b"SHARD-02".to_vec();
        let parity = compute_xor_parity_shard(&[d0.clone(), d1.clone(), d2.clone()], 8).unwrap();
        let rx = vec![Some(d0.clone()), None, Some(d2.clone())];
        let healed = reconstruct_missing_shard(&rx, Some(&parity), 8).unwrap();
        assert_eq!(healed, vec![d0, d1, d2]);
    }
}
