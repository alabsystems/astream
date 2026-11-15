// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pure stack macOS/BSD `sockaddr_un.sun_path` length budget & `/tmp` fallback formatter
//! (`Astream.Wire.TlaUnixSockPathBudget`).
//!
//! Darwin's `sockaddr_un.sun_path` is 104 bytes (`103` usable path bytes before
//! trailing NUL). Long `TMPDIR` roots (`/var/folders/...`) frequently push nested
//! session sockets past 103 bytes; this module validates path fit on the stack and
//! formats a deterministic 30-byte `/tmp/asb-<16-hex>.sock` fallback with **zero
//! heap allocations**.

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
#[path = "unix_sock_path_budget_island.rs"]
mod unix_sock_path_budget_island;
#[cfg(clean_islands)]
pub use unix_sock_path_budget_island::{sun_fallback_gen_advance, sun_path_len_clamp};

/// Portable usable byte ceiling for `sockaddr_un.sun_path` (Darwin `104 - 1 = 103`).
pub const DARWIN_MAX_SUN_PATH_BYTES: usize = 103;

/// Exact byte length of `/tmp/asb-<16-hex>.sock` (`9 + 16 + 5 = 30` bytes).
pub const SHORT_FALLBACK_SOCK_LEN: usize = 30;

const FNV_OFFSET_BASIS: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

#[cfg(not(clean_islands))]
/// Monotonically advance the shortened-socket fallback counter.
#[must_use]
pub const fn sun_fallback_gen_advance(cur_gen: u64, cand_gen: u64) -> u64 {
    if cur_gen < cand_gen {
        cand_gen
    } else {
        cur_gen
    }
}

#[cfg(not(clean_islands))]
/// Clamp resolved socket path byte length to `max_sun_bytes`.
#[must_use]
pub const fn sun_path_len_clamp(cand_len: u64, max_sun_bytes: u64) -> u64 {
    if cand_len < max_sun_bytes {
        cand_len
    } else {
        max_sun_bytes
    }
}

contract_fn! {
    /// True iff `path_len <= max_sun_bytes`.
    #[must_use]
    pub const fn sun_path_fits(path_len: u64, max_sun_bytes: u64) -> bool
    clauses [ensures result == (path_len <= max_sun_bytes)]
    {
        path_len <= max_sun_bytes
    }
}

const fn hex_nibble(n: u8) -> u8 {
    let v = n & 0x0f;
    if v < 10 {
        b'0' + v
    } else {
        b'a'.saturating_add(v.saturating_sub(10))
    }
}

fn fnv1a_path(bytes: &[u8], disambiguator: u64) -> u64 {
    let mut h = FNV_OFFSET_BASIS ^ disambiguator;
    let mut rest = bytes;
    while let &[b, ref tail @ ..] = rest {
        h = (h ^ (b as u64)).wrapping_mul(FNV_PRIME);
        rest = tail;
    }
    h
}

/// Format `/tmp/asb-<16-hex>.sock` (`30` ASCII bytes) on the stack.
#[must_use]
pub fn format_short_tmp_sock(
    long_path: &[u8],
    disambiguator: u64,
) -> [u8; SHORT_FALLBACK_SOCK_LEN] {
    let d = fnv1a_path(long_path, disambiguator);
    [
        b'/',
        b't',
        b'm',
        b'p',
        b'/',
        b'a',
        b's',
        b'b',
        b'-',
        hex_nibble((d >> 60) as u8),
        hex_nibble((d >> 56) as u8),
        hex_nibble((d >> 52) as u8),
        hex_nibble((d >> 48) as u8),
        hex_nibble((d >> 44) as u8),
        hex_nibble((d >> 40) as u8),
        hex_nibble((d >> 36) as u8),
        hex_nibble((d >> 32) as u8),
        hex_nibble((d >> 28) as u8),
        hex_nibble((d >> 24) as u8),
        hex_nibble((d >> 20) as u8),
        hex_nibble((d >> 16) as u8),
        hex_nibble((d >> 12) as u8),
        hex_nibble((d >> 8) as u8),
        hex_nibble((d >> 4) as u8),
        hex_nibble(d as u8),
        b'.',
        b's',
        b'o',
        b'c',
        b'k',
    ]
}

/// Pure stack `sockaddr_un` path budget resolver.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct UnixSockPathBudget {
    fallback_gen: u64,
    last_chosen_len: u64,
}

impl Default for UnixSockPathBudget {
    fn default() -> Self {
        Self::new()
    }
}

impl UnixSockPathBudget {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            fallback_gen: 0,
            last_chosen_len: 0,
        }
    }

    #[must_use]
    pub const fn fallback_gen(&self) -> u64 {
        self.fallback_gen
    }

    #[must_use]
    pub const fn last_chosen_len(&self) -> u64 {
        self.last_chosen_len
    }

    /// Resolve `requested_path` into a stack `[u8; DARWIN_MAX_SUN_PATH_BYTES]` buffer + length.
    /// Uses `requested_path` verbatim if `1..=103` bytes and NUL-free; otherwise deterministically
    /// shortens to `/tmp/asb-<16-hex>.sock` (`30` bytes).
    pub fn resolve_sun_path(
        &mut self,
        requested_path: &[u8],
    ) -> ([u8; DARWIN_MAX_SUN_PATH_BYTES], usize, bool) {
        let mut has_nul = false;
        let mut scan = requested_path;
        while let &[b, ref tail @ ..] = scan {
            if b == 0 {
                has_nul = true;
                break;
            }
            scan = tail;
        }

        let mut buf = [0u8; DARWIN_MAX_SUN_PATH_BYTES];
        if !requested_path.is_empty()
            && !has_nul
            && sun_path_fits(
                requested_path.len() as u64,
                DARWIN_MAX_SUN_PATH_BYTES as u64,
            )
        {
            let clamped = sun_path_len_clamp(
                requested_path.len() as u64,
                DARWIN_MAX_SUN_PATH_BYTES as u64,
            ) as usize;
            let mut k = 0usize;
            while k < clamped {
                if let (Some(d), Some(&s)) = (buf.get_mut(k), requested_path.get(k)) {
                    *d = s;
                }
                k = k.saturating_add(1);
            }
            self.last_chosen_len = clamped as u64;
            return (buf, clamped, false);
        }

        let cand_gen = self.fallback_gen.saturating_add(1);
        self.fallback_gen = sun_fallback_gen_advance(self.fallback_gen, cand_gen);
        let short = format_short_tmp_sock(requested_path, self.fallback_gen);
        let mut k = 0usize;
        while k < SHORT_FALLBACK_SOCK_LEN {
            if let (Some(d), Some(&s)) = (buf.get_mut(k), short.get(k)) {
                *d = s;
            }
            k = k.saturating_add(1);
        }
        self.last_chosen_len = sun_path_len_clamp(
            SHORT_FALLBACK_SOCK_LEN as u64,
            DARWIN_MAX_SUN_PATH_BYTES as u64,
        );
        (buf, SHORT_FALLBACK_SOCK_LEN, true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preserves_short_paths_and_shortens_overlong_darwin_tmpdir_paths() {
        let mut budget = UnixSockPathBudget::new();
        let short_req = b"/tmp/aterm-test.sock";
        let (buf1, len1, used_fb1) = budget.resolve_sun_path(short_req);
        assert!(!used_fb1);
        assert_eq!(&buf1[..len1], short_req);

        let overlong = [b'a'; 120];
        let (buf2, len2, used_fb2) = budget.resolve_sun_path(&overlong);
        assert!(used_fb2);
        assert_eq!(len2, 30);
        assert!(buf2[..len2].starts_with(b"/tmp/asb-"));
        assert!(buf2[..len2].ends_with(b".sock"));
        assert_eq!(budget.fallback_gen(), 1);
    }
}
