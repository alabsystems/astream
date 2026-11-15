//! Claim `broker.ack-key-is-one-wire-contract`: the library helper `client::ack` and
//! the `asb ack` CLI verb derive an ack's `producer_seq` from the acknowledged offset
//! THE SAME WAY, so the broker's dedup recognises a retry that crosses faces.
//!
//! This is not a hypothetical seam. A bridge shells out to `asb ack` on one path and
//! links this crate on another; when the first attempt's outcome is in doubt it retries
//! through whichever path is at hand. If the two faces derived different keys for the
//! same `(producer_id, offset)`, that retry would not be a retry at all — the ack would
//! append a second answer record and re-apply its commit, and the "exactly once" the
//! inbox claim advertises would hold only as long as nobody mixed the two faces.
//!
//! `asb` derives `ACK_SEQ_BASE | offset`. This file pins that the library does too, by
//! constructing the CLI's key by hand and asserting the broker dedups it against the
//! library helper's record. No sleeps: every assertion is on an ack's own return value.
#![cfg(unix)]

use astream_broker::client::ack;
use astream_broker::{Broker, BrokerHandle, Client, ACK_SEQ_BASE};
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);

const GROUP: &str = "/f/F/cur/n1/node/inbox";
const OUT: &str = "/f/F/pub/n1/s1/answer";

struct Paths {
    sock: String,
    log: String,
}

fn fresh(tag: &str) -> Paths {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let p = Paths {
        sock: format!("/tmp/asxface_{tag}_{pid}_{n}.sock"),
        log: format!("/tmp/asxface_{tag}_{pid}_{n}.log"),
    };
    let _ = std::fs::remove_file(&p.sock);
    let _ = std::fs::remove_file(&p.log);
    p
}

impl Drop for Paths {
    /// Remove the socket, the log and every `<path>.*` sidecar beside them (the
    /// broker's `.hw`, `.base`, `.replica`, …) on success and on panic alike. A test
    /// binds its `Paths` before serving on them, so this runs after the broker is gone.
    fn drop(&mut self) {
        remove_with_sidecars(&self.sock);
        remove_with_sidecars(&self.log);
    }
}

/// Remove `path` and every `<path>.*` sidecar in its directory.
fn remove_with_sidecars(path: impl AsRef<std::path::Path>) {
    let path = path.as_ref();
    let _ = std::fs::remove_file(path);
    let (Some(dir), Some(name)) = (path.parent(), path.file_name()) else {
        return;
    };
    let prefix = format!("{}.", name.to_string_lossy());
    for entry in std::fs::read_dir(dir).into_iter().flatten().flatten() {
        if entry.file_name().to_string_lossy().starts_with(&prefix) {
            let _ = std::fs::remove_file(entry.path());
        }
    }
}

fn serve(p: &Paths) -> (Broker, BrokerHandle) {
    let broker = Broker::open(&p.log).unwrap();
    let handle = broker.serve(&p.sock).unwrap();
    (broker, handle)
}

/// THE CROSS-FACE RETRY. The library acks input offset `R`; the CLI's derivation of the
/// very same ack — `ACK_SEQ_BASE | R`, spelled out here exactly as `asb ack` spells it —
/// must be deduped against it, append nothing, and leave the head where it was.
///
/// Before the fix the library used the bare `R` as its `producer_seq`, so these were two
/// different dedup keys and the second call appended a SECOND answer record.
#[test]
fn an_ack_retried_through_the_other_face_is_the_same_record() {
    let p = fresh("retry");
    let (_b, _h) = serve(&p);
    let mut c = Client::connect(&p.sock).unwrap();

    // The record being acknowledged, so `R` is a real log offset and not a bare guess.
    let (r, _) = c.publish(1, 1, "/f/F/in/n1/s1/h-a/ask", b"q").unwrap();

    // Face one: the library helper.
    let (first, deduped) = ack(&mut c, 7, GROUP, r, OUT, b"a").unwrap();
    assert!(!deduped, "the first ack is a genuine append");
    let head_after_first = c.publish(1, 2, "/f/F/in/n1/s1/h-a/ask", b"q2").unwrap().0;

    // Face two: the CLI's derivation of the SAME ack, written the way `asb ack` writes
    // it. `process_and_produce` is the verb `ack` is a helper over, so this is the CLI's
    // exact frame, not an approximation of it.
    let (second, deduped_again) = c
        .process_and_produce(7, ACK_SEQ_BASE | r, OUT, b"a", GROUP, r)
        .unwrap();

    assert!(
        deduped_again,
        "the CLI's derivation of the same ack was NOT recognised as a retry: the two \
         faces disagree about an ack's dedup key, so a bridge that shells out on one \
         path and links the crate on another double-acks whenever it retries"
    );
    assert_eq!(
        second, first,
        "a deduped ack must report the ORIGINAL record's offset"
    );

    // And nothing was appended: the only record after the first ack is the publish the
    // test made itself, so the head has not moved past it.
    let (third, _) = c.publish(1, 3, "/f/F/in/n1/s1/h-a/ask", b"q3").unwrap();
    assert_eq!(
        third,
        head_after_first + 1,
        "the retried ack appended a record: the head moved by more than the one publish \
         between the two acks"
    );
}

/// THE COLLISION THE RESERVATION EXISTS TO PREVENT. A producer that both publishes and
/// acks under ONE id — which is what a bound grant forces, since it permits no other —
/// has a dense publish sequence (1, 2, 3, …) and a dense supply of input offsets (0, 1,
/// 2, …). Under the OLD bare-offset derivation those two spaces overlapped exactly where
/// both are dense, and the loser of a collision was silently deduped away: the answer
/// never appended, `deduped = true` returned, nothing anywhere reporting a loss.
///
/// So this test arranges the collision on purpose. Producer 9 publishes sequences 1..=6,
/// and the ack's INPUT OFFSET is 5 — a number that is also one of those sequences. Under
/// the bare derivation the ack's key is `(9, 5)`, already burned by the fifth publish, so
/// the ack is swallowed. Under `ACK_SEQ_BASE | 5` it cannot be.
#[test]
fn an_ack_cannot_be_swallowed_by_a_publish_sequence_under_one_id() {
    let p = fresh("disjoint");
    let (_b, _h) = serve(&p);
    let mut c = Client::connect(&p.sock).unwrap();

    // Sequences 1..=6 under producer 9, landing at offsets 0..=5.
    let mut offsets = Vec::new();
    for seq in 1..=6u64 {
        let (off, _) = c
            .publish(
                9,
                seq,
                "/f/F/in/n1/s1/h-a/ask",
                format!("q{seq}").as_bytes(),
            )
            .unwrap();
        offsets.push(off);
    }

    // The offset being acknowledged is 5, which is ALSO a sequence this producer has
    // already used — the overlap made real rather than assumed.
    let r = *offsets.last().unwrap();
    assert_eq!(r, 5, "the fixture assumes offsets 0..=5");

    let (_, ack_deduped) = ack(&mut c, 9, GROUP, r, OUT, b"a").unwrap();
    assert!(
        !ack_deduped,
        "the ack was DEDUPED against this producer's own publish sequence {r}: the two \
         spaces are overlapping, so an answer is silently swallowed and nothing reports \
         the loss"
    );

    // A real log offset stays in the lower half — which is what keeps the derivation
    // injective, so two different offsets can never derive one key.
    assert!(
        r < ACK_SEQ_BASE,
        "a real log offset must stay in the lower half, or the derivation would alias"
    );
}
