// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! The answer sheet each astream crate's `twins.rs` tests read: a function of `N` `u64`
//! operands, run over every `N`-tuple of [`EDGES`], written as one index into `EDGES` per
//! tuple. Every crate mounts this file by path, so the sheet has one spelling.

/// Operands at the boundaries a comparison of two `u64`s turns on: below, equal, above, and
/// the top of the range.
pub const EDGES: [u64; 3] = [0, 1, u64::MAX];

/// `f`'s answers over every `N`-tuple of [`EDGES`], the first operand slowest, each written
/// as the index of the answer in `EDGES` (`?` for an answer off the edges).
pub fn answers<const N: usize>(f: impl Fn([u64; N]) -> u64) -> String {
    let tuples = (0..N).fold(1, |count, _| count * EDGES.len());
    (0..tuples)
        .map(|mut tuple| {
            let mut operands = [0; N];
            for operand in operands.iter_mut().rev() {
                *operand = EDGES[tuple % EDGES.len()];
                tuple /= EDGES.len();
            }
            let answer = f(operands);
            match EDGES.iter().position(|&edge| edge == answer) {
                Some(0) => '0',
                Some(1) => '1',
                Some(2) => '2',
                _ => '?',
            }
        })
        .collect()
}
