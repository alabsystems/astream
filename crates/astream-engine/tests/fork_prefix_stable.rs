//! Evidence for `term.fork.prefix-stable`: the counterfactual fork is
//! prefix-stable over the *built* single-writer log — the "branch sharing a
//! prefix" half of the content-addressed-history seed in
//! `docs/THEORY-deterministic-sessions.md` §4, as machine-checked evidence.
//!
//! Forking a recorded session at offset N and re-recording under the same seed
//! produces a byte log whose first N framed records are BIT-IDENTICAL to the
//! original, that diverges from the original at and after N (when the swapped
//! record differs), and that is deterministic across re-records. This holds
//! because the seeded `LogicalClock` tick is positional (tick == append index —
//! a rejected append consumes no tick) and each `Envelope` is independently
//! framed — so records before the fork point are byte-for-byte reproduced.
//! "Counterfactual = branch sharing a bit-identical prefix" is therefore a
//! property of the log, not an assertion.
//!
//! HONEST: nothing here is hash-linked. The log carries no digest of its
//! history; the prefix is shared by BYTES (asserted with byte equality), and a
//! content-addressed / Merkle history remains a designed seed.

use astream_engine::{fork_swap, record_session, Offset};
use astream_term::Record;
use proptest::prelude::*;

const SEED: u64 = 0xF02C;

/// An agent session: it ran a build, the world answered, it reacted.
fn agent_session() -> Vec<Record> {
    vec![
        Record::Out(b"$ make\r\n".to_vec()),
        Record::In {
            bytes: b"make\n".to_vec(),
            client_id: 1,
            client_seq: 1,
        },
        Record::Out(b"BUILD FAILED: 3 errors\r\n".to_vec()),
        Record::In {
            bytes: b"echo recover\n".to_vec(),
            client_id: 1,
            client_seq: 2,
        },
        Record::Out(b"recover\r\n".to_vec()),
    ]
}

#[test]
fn fork_shares_a_bit_identical_prefix_and_diverges_only_after_n() {
    let orig = agent_session();
    let n = 2usize; // fork at the world's answer (offset 2)

    let orig_log = record_session(SEED, &orig);
    let alt = fork_swap(
        &orig,
        Offset(n as u64),
        Record::Out(b"BUILD OK: 0 errors\r\n".to_vec()),
    );
    let alt_log = record_session(SEED, &alt);

    // The shared prefix = the framed bytes of records [0..N], recorded alone.
    let prefix = record_session(SEED, &orig[..n]);
    assert!(prefix.len() <= orig_log.len() && prefix.len() <= alt_log.len());

    // Both timelines OPEN with the bit-identical prefix.
    assert_eq!(
        &orig_log[..prefix.len()],
        &prefix[..],
        "original opens with the prefix"
    );
    assert_eq!(
        &alt_log[..prefix.len()],
        &prefix[..],
        "the fork shares the bit-identical prefix"
    );

    // They branch at the fork point: the bytes from N on differ.
    assert_ne!(
        orig_log[prefix.len()..],
        alt_log[prefix.len()..],
        "the timelines diverge from the fork"
    );

    // Deterministic: re-recording the same fork is byte-identical.
    assert_eq!(
        alt_log,
        record_session(SEED, &alt),
        "the fork is deterministic"
    );
}

proptest! {
    /// For an arbitrary session of Out records, any fork point, and any
    /// replacement body (made to differ from the record it replaces), the first
    /// N framed records are bit-identical across the branch, the bytes from N on
    /// DIFFER, and re-recording is deterministic.
    #[test]
    fn prefix_is_stable_and_the_tail_diverges_for_arbitrary_sessions(
        bodies in prop::collection::vec(prop::collection::vec(any::<u8>(), 0..8), 2..8),
        swap in prop::collection::vec(any::<u8>(), 0..8),
    ) {
        let orig: Vec<Record> = bodies.iter().map(|b| Record::Out(b.clone())).collect();
        let n = orig.len() / 2; // a valid fork point in 1..len
        // A swap equal to the original record would be a no-op fork; make it differ.
        let mut swap = swap;
        if swap == bodies[n] {
            swap.push(0x2A);
        }
        let alt = fork_swap(&orig, Offset(n as u64), Record::Out(swap));

        let prefix = record_session(SEED, &orig[..n]);
        let orig_log = record_session(SEED, &orig);
        let alt_log = record_session(SEED, &alt);

        prop_assert_eq!(&orig_log[..prefix.len()], &prefix[..]);
        prop_assert_eq!(&alt_log[..prefix.len()], &prefix[..]);
        prop_assert_ne!(&orig_log[prefix.len()..], &alt_log[prefix.len()..]);
        prop_assert_eq!(&alt_log, &record_session(SEED, &alt));
    }
}
