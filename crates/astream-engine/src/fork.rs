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

use crate::effects::{Disk, Effects};
use crate::log::Log;
use crate::Seeded;
use astream_term::Record;
use astream_wire::Offset;

/// Record a session into log bytes under a seeded seam.
pub fn record_session(seed: u64, records: &[Record]) -> Vec<u8> {
    let mut fx = Seeded::new(seed);
    let mut log = Log::new();
    for rec in records {
        log.append(&mut fx, rec.clone()).expect("append");
    }
    fx.disk().read_all().to_vec()
}

/// The index of `at` in a dense record list, if it is in range. Converted with
/// `try_from`, never `as`: on a 32-bit target `Offset(1 << 32 | 1) as usize`
/// would silently become index 1 and swap the wrong record.
fn index_of(records: &[Record], at: Offset) -> Option<usize> {
    usize::try_from(at.0).ok().filter(|&i| i < records.len())
}

/// Fork a recorded session: keep the records before `at`, replace the record at
/// `at` with `replacement`, keep the rest. The result is the alternate timeline;
/// re-recording it yields its own byte-exact, offset-stamped log.
///
/// An out-of-range `at` leaves the records unchanged (the lenient form). When the
/// caller needs to *know* the offset was in range, use [`try_fork_swap`].
pub fn fork_swap(records: &[Record], at: Offset, replacement: Record) -> Vec<Record> {
    let mut out = records.to_vec();
    if let Some(i) = index_of(records, at) {
        out[i] = replacement;
    }
    out
}

/// Like [`fork_swap`], but returns `None` if `at` is past the end of `records`
/// (no record to swap) instead of silently returning an unchanged copy — so a
/// caller forking at a bad offset gets a signal, not a no-op masquerading as a
/// fork.
pub fn try_fork_swap(records: &[Record], at: Offset, replacement: Record) -> Option<Vec<Record>> {
    let i = index_of(records, at)?;
    let mut out = records.to_vec();
    out[i] = replacement;
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
        // The lenient form returns an unchanged copy for the same bad offset.
        assert_eq!(
            fork_swap(&recs, Offset(2), Record::Out(b"X".to_vec())),
            recs
        );
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
            assert_eq!(fork_swap(&recs, at, Record::Out(b"X".to_vec())), recs);
        }
    }
}
