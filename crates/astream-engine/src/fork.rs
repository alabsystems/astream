//! Rung 3: counterfactual fork — astream's headline determinism thesis applied
//! to a shell.
//!
//! Record an agent's session — what it typed (`In`) and what the world answered
//! (`Out`), both seam-recorded effects — then fork the log at an offset, swap one
//! recorded effect (say, the build result the agent saw), and re-derive the
//! alternate history. Because every record is a seam-recorded effect, the swap
//! yields a **real, byte-exact, screen-exact alternate timeline** — not a guess.
//!
//! Honest scope: a live agent in the loop would additionally *re-decide* on the
//! swapped output (re-drive its behaviour). Rung 3 demonstrates the part astream
//! owns — the substrate's exact, deterministic fork of the recorded history —
//! which is precisely what no SSH/mosh/tmux can do. Re-driving a live agent is
//! sound only because its effects are seam-mediated; that loop is a later rung.

use astream_term::Record;
use astream_wire::Offset;

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "fork_island.rs"]
mod fork_island;
#[cfg(not(clean_islands))]
pub use crate::twins::fork_clamped_index;
#[cfg(clean_islands)]
pub use fork_island::fork_clamped_index;

contract_fn! {
    /// Kernel-certified bounds check that a decoded fork index `idx` lies strictly
    /// within the dense record slice length `len` (`idx < len`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `fork_index_in_bounds_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn fork_index_in_bounds(idx: u64, len: u64) -> bool
    clauses [ensures result == (idx < len)]
    {
        idx < len
    }
}

/// The index of `at` in a dense record list, if it is in range. Checked as `u64`
/// against `records.len() as u64` before casting to `usize`, so on a 32-bit target
/// `Offset(1 << 32 | 1)` is rejected before any cast can truncate it.
const fn index_of(records: &[Record], at: Offset) -> Option<usize> {
    let len = records.len();
    if fork_index_in_bounds(at.0, len as u64) {
        let _ = fork_clamped_index(at.0, len as u64);
        Some(at.0 as usize)
    } else {
        None
    }
}

/// Fork a recorded session: keep the records before `at`, replace the record at
/// `at` with `replacement`, keep the rest. The result is the alternate timeline;
/// re-recording it yields its own byte-exact, offset-stamped log.
///
/// Returns `None` if `at` is past the end of `records` (no record to swap), so a
/// caller forking at a bad offset gets a signal, not a no-op masquerading as a
/// fork.
pub fn try_fork_swap(records: &[Record], at: Offset, replacement: Record) -> Option<Vec<Record>> {
    let i = index_of(records, at)?;
    let mut out = records.to_vec();
    if let Some(slot) = out.get_mut(i) {
        *slot = replacement;
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn try_fork_swap_signals_out_of_range() {
        let recs = vec![Record::Out(b"a".to_vec()), Record::Out(b"b".to_vec())];
        let swapped =
            try_fork_swap(&recs, Offset(1), Record::Out(b"B".to_vec())).expect("in-range swap");
        assert_eq!(swapped[1], Record::Out(b"B".to_vec()));
        assert_eq!(swapped[0], recs[0], "prefix untouched");
        // Out of range yields None, not a silent unchanged copy.
        assert!(try_fork_swap(&recs, Offset(2), Record::Out(b"X".to_vec())).is_none());
    }

    #[test]
    fn offsets_beyond_usize_are_out_of_range_never_truncated() {
        // On a 32-bit usize these offsets would truncate to index 1 / 0 under `as`;
        // with try_from they are simply out of range on every target.
        let recs = vec![Record::Out(b"a".to_vec()), Record::Out(b"b".to_vec())];
        for at in [
            Offset(u64::MAX),
            Offset((1u64 << 32) | 1),
            Offset(1u64 << 32),
        ] {
            assert!(try_fork_swap(&recs, at, Record::Out(b"X".to_vec())).is_none());
        }
    }
}
