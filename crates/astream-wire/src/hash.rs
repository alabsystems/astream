//! Small, dependency-free, deterministic hashes.
//!
//! These are *not* cryptographic. They exist so partitioning and frame
//! integrity are stable across processes with no external crate. Each function
//! is named for exactly what it computes.

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "hash_island.rs"]
mod hash_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{
    crc32_poly_select, crc_table_index_clamp, fnv1a_64_mul_prime, fnv1a_64_xor,
};
#[cfg(clean_islands)]
pub use hash_island::{crc32_poly_select, crc_table_index_clamp, fnv1a_64_mul_prime, fnv1a_64_xor};

/// The reflected IEEE 802.3 CRC-32 generator polynomial (`0xEDB8_8320`).
pub const CRC32_IEEE_POLY: u32 = 0xEDB8_8320;

/// The 64-bit FNV-1a offset basis (`0xcbf2_9ce4_8422_2325`).
pub const FNV1A_64_INIT: u64 = 0xcbf2_9ce4_8422_2325;

/// The 64-bit FNV-1a prime (`0x0000_0100_0000_01b3`).
pub const FNV1A_64_PRIME: u64 = 0x0000_0100_0000_01b3;

contract_fn! {
    /// Whether a CRC-32 Slicing-by-8 table lookup index `idx` is within `[0, max_idx]`
    /// (`255` for a 256-entry row).
    ///
    /// Verified against `Astream.Wire.TlaSlicingCrc32.crc_table_index_in_bounds_isl` by
    /// `clean-kernel-defeq`.
    pub const fn crc_table_index_in_bounds(idx: u64, max_idx: u64) -> bool
    clauses [ensures result == (idx <= max_idx)]
    {
        idx <= max_idx
    }
}

contract_fn! {
    /// Whether an ongoing 64-bit FNV-1a hash state `h` equals `expected`
    /// (for example [`FNV1A_64_INIT`] or [`FNV1A_64_PRIME`]).
    ///
    /// Verified against `Astream.Wire.TlaSlicingCrc32.fnv1a_64_state_matches_isl` by
    /// `clean-kernel-defeq`.
    pub const fn fnv1a_64_state_matches(h: u64, expected: u64) -> bool
    clauses [ensures result == (h == expected)]
    {
        h == expected
    }
}

contract_fn! {
    /// Whether `poly` is the reflected IEEE 802.3 CRC-32 generator polynomial
    /// [`CRC32_IEEE_POLY`] (`0xEDB8_8320`).
    ///
    /// Verified against `Astream.Wire.TlaSlicingCrc32.crc32_is_ieee_poly_isl` by
    /// `clean-kernel-defeq`.
    #[must_use]
    pub const fn crc32_is_ieee_poly(poly: u32) -> bool
    clauses [ensures result == (poly == 0xEDB8_8320)]
    {
        poly == CRC32_IEEE_POLY
    }
}

contract_fn! {
    /// Whether `h` is the published 64-bit FNV-1a offset basis [`FNV1A_64_INIT`]
    /// (`0xcbf2_9ce4_8422_2325`).
    ///
    /// Verified against `Astream.Wire.TlaSlicingCrc32.fnv1a_64_is_init_isl` by
    /// `clean-kernel-defeq`.
    #[must_use]
    pub const fn fnv1a_64_is_init(h: u64) -> bool
    clauses [ensures result == (h == 0xcbf2_9ce4_8422_2325)]
    {
        h == FNV1A_64_INIT
    }
}

contract_fn! {
    /// Whether `p` is the published 64-bit FNV-1a prime [`FNV1A_64_PRIME`]
    /// (`0x0000_0100_0000_01b3`).
    ///
    /// Verified against `Astream.Wire.TlaSlicingCrc32.fnv1a_64_is_prime_isl` by
    /// `clean-kernel-defeq`.
    #[must_use]
    pub const fn fnv1a_64_is_prime(p: u64) -> bool
    clauses [ensures result == (p == 0x0000_0100_0000_01b3)]
    {
        p == FNV1A_64_PRIME
    }
}

/// Mix a 64-bit word `word` into an ongoing 64-bit FNV-1a hash state `h`:
/// `(h ^ word).wrapping_mul(FNV1A_64_PRIME)`, composed from the Clean-origin
/// [`fnv1a_64_xor`] and [`fnv1a_64_mul_prime`] kernels
/// (`Astream.Wire.TlaSlicingCrc32.fnv1a_64_mix_u64_eq_pieces`).
#[must_use]
pub const fn fnv1a_64_mix_u64(h: u64, word: u64) -> u64 {
    fnv1a_64_mul_prime(fnv1a_64_xor(h, word), FNV1A_64_PRIME)
}

/// Feed `bytes` into an ongoing 64-bit FNV-1a hash state `h` (started at
/// [`FNV1A_64_INIT`]). Allows hashing multi-field length-prefixed tuples with
/// zero heap allocation.
///
/// Functional refinement contract (`Astream.Wire.TlaSlicingCrc32.fnv1a_64_fold`):
/// left fold of `fnv1a_64_mul_prime(h ^ (b as u64), FNV1A_64_PRIME)` over `bytes`,
/// satisfying `fnv1a_64_update(fnv1a_64_update(h, a), b) == fnv1a_64_update(h, [a, b])`
/// (`fnv1a_64_fold_append`).
#[must_use]
pub const fn fnv1a_64_update(mut h: u64, bytes: &[u8]) -> u64 {
    let mut rest = bytes;
    while let &[b, ref tail @ ..] = rest {
        h = fnv1a_64_mul_prime(h ^ (b as u64), FNV1A_64_PRIME);
        rest = tail;
    }
    h
}

/// FNV-1a, 64-bit. A stable non-cryptographic hash used for partition
/// assignment. Stable across processes and architectures (no `Hash` RNG).
#[must_use]
pub const fn fnv1a_64(bytes: &[u8]) -> u64 {
    fnv1a_64_update(FNV1A_64_INIT, bytes)
}

/// Lookup of a byte index in a 256-entry CRC table row. Because `idx` is a `u8`
/// (`0..=255`), the bounds check always holds: Trust proves it and LLVM drops it,
/// so this is a single unbranched load, and the lookup states its bound instead of
/// a fallback value no index can reach.
#[inline(always)]
const fn crc_table_at(row: &[u32; 256], idx: u8) -> u32 {
    row[idx as usize]
}

/// The reflected CRC-32/IEEE of the single byte `byte`: eight polynomial steps
/// under `0xEDB8_8320`, the Sarwate table's entry. The explicit branch below
/// selects the same zero-or-polynomial tap as [`crc32_poly_select`]; it does
/// not call that helper (`Astream.Wire.TlaSlicingCrc32.crc32_row0_entry`).
const fn crc32_entry(byte: u8) -> u32 {
    let mut crc = byte as u32;
    let mut step = 0usize;
    while step < 8 {
        if crc & 1 != 0 {
            crc = (crc >> 1) ^ CRC32_IEEE_POLY;
        } else {
            crc >>= 1;
        }
        step = step.saturating_add(1);
    }
    crc
}

/// Slicing-by-8 row 0, the Sarwate table, at compile time. The index is a `u8`,
/// so every store is in bounds by its type (and proved so), and the loop ends
/// after entry 255 without an overflowing increment.
const fn crc32_row0() -> [u32; 256] {
    let mut row = [0u32; 256];
    let mut i = 0u8;
    loop {
        row[i as usize] = crc32_entry(i);
        if i == u8::MAX {
            return row;
        }
        i = i.wrapping_add(1);
    }
}

/// Slicing-by-8 row `k` from row `k - 1` (`prev`) and the Sarwate row `t0`: one
/// more zero byte after a CRC `c` is one more Sarwate step,
/// `(c >> 8) ^ t0[c as u8]`. Every index is a `u8`, as in [`crc32_row0`].
const fn crc32_next_row(prev: &[u32; 256], t0: &[u32; 256]) -> [u32; 256] {
    let mut row = [0u32; 256];
    let mut i = 0u8;
    loop {
        let c = prev[i as usize];
        row[i as usize] = (c >> 8) ^ crc_table_at(t0, c as u8);
        if i == u8::MAX {
            return row;
        }
        i = i.wrapping_add(1);
    }
}

/// The CRC-32/IEEE slicing-by-8 tables, built at COMPILE TIME from the
/// reflected polynomial. `const fn`, so the 8 KiB of tables land in `.rodata`
/// with zero runtime init and no `once_cell`/`lazy_static`.
///
/// `T[0]` is the classic Sarwate table (the CRC of each single byte);
/// `T[k][i]` is the CRC of byte `i` followed by `k` zero bytes, so one
/// lookup in each of the eight tables advances the CRC by eight bytes at once.
const fn crc32_tables() -> [[u32; 256]; 8] {
    let t0 = crc32_row0();
    let t1 = crc32_next_row(&t0, &t0);
    let t2 = crc32_next_row(&t1, &t0);
    let t3 = crc32_next_row(&t2, &t0);
    let t4 = crc32_next_row(&t3, &t0);
    let t5 = crc32_next_row(&t4, &t0);
    let t6 = crc32_next_row(&t5, &t0);
    let t7 = crc32_next_row(&t6, &t0);
    [t0, t1, t2, t3, t4, t5, t6, t7]
}

const CRC32_TABLES: [[u32; 256]; 8] = crc32_tables();

#[inline(always)]
const fn u32_le(b0: u8, b1: u8, b2: u8, b3: u8) -> u32 {
    (b0 as u32) | ((b1 as u32) << 8) | ((b2 as u32) << 16) | ((b3 as u32) << 24)
}

/// Feed `data` into an ongoing CRC-32/IEEE computation started at `0`
/// (`crc32_ieee(b"")`).
///
/// For any split `data = [a, b]`,
/// `crc32_ieee_update(crc32_ieee_update(0, a), b) == crc32_ieee(data)`.
/// Uses the same compile-time Slicing-by-8 tables as [`crc32_ieee`] and
/// allows computing frame CRCs across non-contiguous fields without
/// intermediate buffer copies.
#[must_use]
pub const fn crc32_ieee_update(crc: u32, data: &[u8]) -> u32 {
    let [t0, t1, t2, t3, t4, t5, t6, t7] = &CRC32_TABLES;
    let mut state: u32 = !crc;
    let mut rest = data;
    while let &[c0, c1, c2, c3, c4, c5, c6, c7, ref tail @ ..] = rest {
        let lo = state ^ u32_le(c0, c1, c2, c3);
        let hi = u32_le(c4, c5, c6, c7);
        state = crc_table_at(t7, lo as u8)
            ^ crc_table_at(t6, (lo >> 8) as u8)
            ^ crc_table_at(t5, (lo >> 16) as u8)
            ^ crc_table_at(t4, (lo >> 24) as u8)
            ^ crc_table_at(t3, hi as u8)
            ^ crc_table_at(t2, (hi >> 8) as u8)
            ^ crc_table_at(t1, (hi >> 16) as u8)
            ^ crc_table_at(t0, (hi >> 24) as u8);
        rest = tail;
    }
    while let &[b, ref tail @ ..] = rest {
        state = (state >> 8) ^ crc_table_at(t0, (state as u8) ^ b);
        rest = tail;
    }
    !state
}

/// Compute the CRC-32/IEEE of the first `len` bytes of `data`, or `None` if
/// `data.len() < len`. Uses built-in slice pattern matching (`Subslice`) so
/// it requires no `split_at_checked` call.
#[must_use]
pub const fn crc32_ieee_prefix(data: &[u8], len: usize) -> Option<u32> {
    if data.len() < len {
        return None;
    }
    let [t0, t1, t2, t3, t4, t5, t6, t7] = &CRC32_TABLES;
    let mut state: u32 = !0u32;
    let mut rest = data;
    let mut done = 0usize;
    while let &[c0, c1, c2, c3, c4, c5, c6, c7, ref tail @ ..] = rest {
        if done >= len || len.wrapping_sub(done) < 8 {
            break;
        }
        let lo = state ^ u32_le(c0, c1, c2, c3);
        let hi = u32_le(c4, c5, c6, c7);
        state = crc_table_at(t7, lo as u8)
            ^ crc_table_at(t6, (lo >> 8) as u8)
            ^ crc_table_at(t5, (lo >> 16) as u8)
            ^ crc_table_at(t4, (lo >> 24) as u8)
            ^ crc_table_at(t3, hi as u8)
            ^ crc_table_at(t2, (hi >> 8) as u8)
            ^ crc_table_at(t1, (hi >> 16) as u8)
            ^ crc_table_at(t0, (hi >> 24) as u8);
        done = done.saturating_add(8);
        rest = tail;
    }
    while let &[b, ref tail @ ..] = rest {
        if done >= len {
            return Some(!state);
        }
        state = (state >> 8) ^ crc_table_at(t0, (state as u8) ^ b);
        done = done.saturating_add(1);
        rest = tail;
    }
    if done == len {
        Some(!state)
    } else {
        None
    }
}

/// CRC-32, IEEE 802.3 polynomial (reflected `0xEDB88320`). Used for frame
/// payload integrity — computed on every frame encode and decode, so this is
/// the broker's per-record hot path.
///
/// Slicing-by-8: eight independent table lookups per 8-byte chunk, so the
/// loads are not one serial dependency chain as in the one-lookup-per-byte
/// Sarwate form (still used for the final `len % 8` bytes). Every index is a
/// `u8` passed to `crc_table_at`, so each `[u32; 256]` lookup is in bounds by
/// its type, and proved so. Output is byte-identical to the bitwise reference — the
/// canonical `123456789 -> 0xCBF43926` vector and a differential test against
/// that reference both pin it.
#[must_use]
pub const fn crc32_ieee(data: &[u8]) -> u32 {
    crc32_ieee_update(0, data)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fnv_is_deterministic_and_distinguishes() {
        assert_eq!(fnv1a_64(b"agent-7"), fnv1a_64(b"agent-7"));
        assert_ne!(fnv1a_64(b"agent-7"), fnv1a_64(b"agent-8"));
        assert_ne!(fnv1a_64(b""), fnv1a_64(b"\0"));
    }

    #[test]
    fn crc32_matches_known_vector() {
        // The canonical CRC-32/IEEE check value for the ASCII string "123456789".
        assert_eq!(crc32_ieee(b"123456789"), 0xCBF4_3926);
        assert_eq!(crc32_ieee(b""), 0x0000_0000);
        // Streaming update across arbitrary chunk boundaries matches one-shot CRC.
        let c1 = crc32_ieee_update(0, b"123");
        let c2 = crc32_ieee_update(c1, b"4567");
        let c3 = crc32_ieee_update(c2, b"89");
        assert_eq!(c3, 0xCBF4_3926);
    }

    /// The bitwise CRC-32/IEEE (eight shifts per byte) — the reference the
    /// table-driven [`crc32_ieee`] must reproduce byte-for-byte.
    fn crc32_bitwise_reference(data: &[u8]) -> u32 {
        let mut crc: u32 = 0xFFFF_FFFF;
        for &b in data {
            crc ^= b as u32;
            for _ in 0..8 {
                let mask = (crc & 1).wrapping_neg();
                crc = (crc >> 1) ^ (0xEDB8_8320 & mask);
            }
        }
        !crc
    }

    #[test]
    fn crc32_table_equals_bitwise_reference() {
        // Every length from empty to 600 -- every `len % 8` tail after any
        // number of 8-byte chunks -- filled from a seeded xorshift so the input
        // covers all byte values and the carry across the table lookups is
        // exercised, plus a few fixed vectors.
        let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            (state & 0xFF) as u8
        };
        let mut buf = Vec::new();
        for len in 0..=600usize {
            buf.clear();
            for _ in 0..len {
                buf.push(next());
            }
            assert_eq!(
                crc32_ieee(&buf),
                crc32_bitwise_reference(&buf),
                "table CRC diverged from bitwise reference at len {len}"
            );
        }
        for v in [
            &b""[..],
            b"123456789",
            b"\x00",
            b"\xff\xff\xff\xff",
            b"the quick brown fox",
        ] {
            assert_eq!(crc32_ieee(v), crc32_bitwise_reference(v));
        }
    }

    #[test]
    fn clean_origin_crc_table_index_clamp_and_bounds() {
        assert_eq!(crc_table_index_clamp(0, 255), 0);
        assert_eq!(crc_table_index_clamp(255, 255), 255);
        assert_eq!(crc_table_index_clamp(1024, 255), 255);
        assert!(crc_table_index_in_bounds(0, 255));
        assert!(crc_table_index_in_bounds(255, 255));
        assert!(!crc_table_index_in_bounds(256, 255));
        assert_eq!(crc32_poly_select(0, CRC32_IEEE_POLY), 0);
        assert_eq!(crc32_poly_select(1, CRC32_IEEE_POLY), CRC32_IEEE_POLY);
        assert_eq!(crc32_poly_select(2, CRC32_IEEE_POLY), 0);
        assert_eq!(crc32_poly_select(3, CRC32_IEEE_POLY), CRC32_IEEE_POLY);
        assert!(crc32_is_ieee_poly(CRC32_IEEE_POLY));
        assert!(!crc32_is_ieee_poly(0));
        assert!(fnv1a_64_is_init(FNV1A_64_INIT));
        assert!(!fnv1a_64_is_init(0));
        assert!(fnv1a_64_is_prime(FNV1A_64_PRIME));
        assert!(!fnv1a_64_is_prime(0));
        assert!(fnv1a_64_state_matches(FNV1A_64_INIT, FNV1A_64_INIT));
        assert!(!fnv1a_64_state_matches(0, FNV1A_64_INIT));
        assert_eq!(fnv1a_64_mul_prime(0, FNV1A_64_PRIME), 0);
        assert_eq!(fnv1a_64_mul_prime(1, FNV1A_64_PRIME), FNV1A_64_PRIME);
        assert_eq!(
            fnv1a_64_mix_u64(FNV1A_64_INIT, 0x1234_5678_9abc_def0),
            (FNV1A_64_INIT ^ 0x1234_5678_9abc_def0).wrapping_mul(FNV1A_64_PRIME)
        );
        // Verify row 0 matches 8 steps of Clean-origin `crc32_poly_select` for all 256 bytes,
        // and row k matches the register after byte n followed by k zero bytes from register 0.
        for b in 0u8..=255u8 {
            let mut c = b as u32;
            for _ in 0..8 {
                c = (c >> 1) ^ crc32_poly_select(c, CRC32_IEEE_POLY);
            }
            assert_eq!(CRC32_TABLES[0][b as usize], c);
            let mut zero_run = [0u8; 8];
            zero_run[0] = b;
            for k in 0..8usize {
                // Register starting from 0 (which corresponds to pre-inverted crc = !0u32 = 0xFFFF_FFFF,
                // i.e. `!crc32_ieee_update(!0u32, &zero_run[..=k])`).
                let reg = !crc32_ieee_update(!0u32, &zero_run[..=k]);
                assert_eq!(
                    CRC32_TABLES[k][b as usize], reg,
                    "table row {k} byte {b} mismatch against zero-run register"
                );
            }
        }
        // Verify split-invariance (homomorphism) of crc32_ieee_update and fnv1a_64_update.
        let sample = b"astream-wire functional contracts for aterm-codec, aterm-png, aterm-hash";
        let full_crc = crc32_ieee(sample);
        let full_fnv = fnv1a_64(sample);
        for split in 0..=sample.len() {
            let (p, d) = sample.split_at(split);
            assert_eq!(crc32_ieee_update(crc32_ieee(p), d), full_crc);
            assert_eq!(fnv1a_64_update(fnv1a_64(p), d), full_fnv);
        }
    }
}
