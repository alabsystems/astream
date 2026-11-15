// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Independent SHA-256 replay-vs-oracle stdout digest parity verifier (`docs/ROADMAP.md` §4:
//! *"replayed with no real syscall reaching the kernel, to a byte-identical digest equal to an
//! independent oracle over the taped values"*, `Astream.SecReplay.TlaOracleSha256Parity`).

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

use astream_digest::{ct_eq, Sha256};

#[cfg(clean_islands)]
#[path = "oracle_sha256_parity_island.rs"]
mod oracle_sha256_parity_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sec_out_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn sec_ver_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use oracle_sha256_parity_island::{sec_out_clamp, sec_ver_advance};

/// Maximum captured stdout bytes verified per hermetic seed (`16_777_216` bytes).
pub const MAX_ORACLE_STDOUT_BYTES: u64 = 16_777_216;

contract_fn! {
    /// Verified byte-identical SHA-256 parity (`threshold <= observed`), linked via
    /// `clean-kernel-defeq` to `sec_digest_equal_isl`.
    #[must_use]
    pub const fn sec_digest_equal(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Default)]
pub struct OracleParityVerifier {
    verified_runs: u64,
}

impl OracleParityVerifier {
    #[must_use]
    pub const fn new() -> Self {
        Self { verified_runs: 0 }
    }

    pub fn verify(&mut self, replayed_stdout: &[u8], oracle_stdout: &[u8]) -> bool {
        let r_len = sec_out_clamp(replayed_stdout.len() as u64, MAX_ORACLE_STDOUT_BYTES);
        if r_len != replayed_stdout.len() as u64 || replayed_stdout.len() != oracle_stdout.len() {
            return false;
        }
        let d_replay = Sha256::digest_slice(replayed_stdout);
        let d_oracle = Sha256::digest_slice(oracle_stdout);
        let eq = u64::from(ct_eq(&d_replay, &d_oracle));
        if !sec_digest_equal(eq, 1) {
            return false;
        }
        self.verified_runs =
            sec_ver_advance(self.verified_runs, self.verified_runs.saturating_add(1));
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn confirms_constant_time_sha256_parity_with_independent_oracle() {
        let mut v = OracleParityVerifier::new();
        assert!(v.verify(
            b"ts=1700000000 rnd=0a1b file=ok\n",
            b"ts=1700000000 rnd=0a1b file=ok\n"
        ));
        assert!(!v.verify(
            b"ts=1700000001 rnd=0a1b file=ok\n",
            b"ts=1700000000 rnd=0a1b file=ok\n"
        ));
    }
}
