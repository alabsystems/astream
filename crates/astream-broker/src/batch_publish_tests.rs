// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A BATCH PUBLISH IS ONE WRITE AND HANDS BACK A DIGEST FOR EACH RECORD (aterm tracker
//! LT-E30; aterm `docs/design-commons-at-scale/journal.md` 2.12, change A2).
//!
//! [`BrokerLog::publish_checked`] is one device write and one flush a record, so a caller
//! with a group of records to make durable together (aterm's journal, appending the group
//! one machine's writers share) paid a write and a flush for each, and then read the log
//! back to hash what it had written. [`BrokerLog::publish_batch_checked`] stages every
//! record, commits the batch once, and hands back [`record_digest`] of each record as
//! staged, so the caller chains from the digests it is handed.
//!
//! The writes are counted on the simulated device ([`Sim::log_writes`]: one per write call
//! the log file takes, whatever its length), and the flushes both there
//! ([`Sim::log_flushes`]) and by the log's own counts ([`BrokerLog::flush_counts`]). The digests are held to the formula computed here another
//! way (one hash of the assembled bytes, where the product feeds three pieces) and to an
//! answer `hashlib` gave, so the formula is pinned by something that is not this crate.

use std::collections::HashSet;
use std::sync::Arc;

use astream_digest::Sha256;
use astream_wire::Offset;

use crate::brecord::BrokerRecord;
use crate::sim_device::Sim;
use crate::store::{
    record_digest, BatchPublished, BatchRecord, Boot, BrokerLog, CheckedPublishError, Durability,
    FlushCounts, InjectedFaults, OpenOptions, Volume, COMMIT_SUBJECT, MAX_SUBJECTS_PER_PRODUCER,
};
use crate::test_scratch::Scratch;
use crate::{Escalate, Escalation, SimDevice, MAX_RECORD_PAYLOAD};

/// The records of the batch the row names.
const BATCH: usize = 4096;
/// The producer every record of a batch is published under, at sequence `i + 1`.
const PRODUCER: u64 = 1;

fn subject(i: usize) -> String {
    // Seven subjects of three lengths, so the digest's length prefix is not one value.
    format!(
        "/f/journal/{}",
        "s".repeat(1 + i % 3) + &(i % 7).to_string()
    )
}

fn body(i: usize) -> Vec<u8> {
    // Lengths 8 to 96 and one empty body; the index leads the others, so no two are alike.
    let mut out = (i as u64).to_le_bytes().to_vec();
    out.extend((0..(i * 31) % 89).map(|k| (i as u8).wrapping_mul(17).wrapping_add(k as u8)));
    if i == 5 {
        out.clear();
    }
    out
}

fn record(i: usize) -> BatchRecord {
    BatchRecord {
        producer_id: PRODUCER,
        producer_seq: i as u64 + 1,
        subject: subject(i),
        body: body(i),
    }
}

fn batch(n: usize) -> Vec<BatchRecord> {
    (0..n).map(record).collect()
}

/// The digest's formula, computed another way than the product does: the bytes assembled,
/// then hashed once.
fn digest_by_hand(subject: &str, body: &[u8]) -> [u8; 32] {
    let len = u16::try_from(subject.len()).expect("a test subject fits the prefix");
    let mut bytes = len.to_le_bytes().to_vec();
    bytes.extend_from_slice(subject.as_bytes());
    bytes.extend_from_slice(body);
    Sha256::digest(&bytes)
}

fn hex(digest: &[u8; 32]) -> String {
    digest.iter().map(|b| format!("{b:02x}")).collect()
}

fn options(durability: Durability) -> OpenOptions {
    let mut opts = OpenOptions::new(durability);
    // A weak tier is served as asked only where the boot and the volume are known.
    opts.boot = Boot::Known([0x0A; 16]);
    opts.volume = Volume::Boot;
    opts
}

fn open(sim: &Sim, opts: OpenOptions) -> BrokerLog {
    BrokerLog::open_sim(&SimDevice::on(sim.clone()), opts).expect("the simulated log opens")
}

/// The flushes issued between two readings.
fn since(before: FlushCounts, after: FlushCounts) -> FlushCounts {
    FlushCounts {
        barrier: after.barrier - before.barrier,
        full: after.full - before.full,
        skipped: after.skipped - before.skipped,
        failed: after.failed - before.failed,
    }
}

/// Whether the log's records from `first` are `records`, at consecutive offsets, under
/// their keys.
fn holds(log: &BrokerLog, first: Offset, records: &[BatchRecord]) -> Result<(), String> {
    let read: Vec<Arc<BrokerRecord>> = log.read_range(first, records.len());
    if read.len() != records.len() {
        return Err(format!(
            "{} records read from {}, {} published",
            read.len(),
            first.0,
            records.len()
        ));
    }
    for (i, (got, want)) in read.iter().zip(records).enumerate() {
        let same = got.seq.0 == first.0 + i as u64
            && got.producer_id == want.producer_id
            && got.producer_seq == want.producer_seq
            && got.subject == want.subject
            && got.body == want.body
            && got.commit.is_none();
        if !same {
            return Err(format!(
                "record {i} of the batch reads back as seq {} key ({}, {}) subject {:?} ({} \
                 body bytes)",
                got.seq.0,
                got.producer_id,
                got.producer_seq,
                got.subject,
                got.body.len()
            ));
        }
    }
    Ok(())
}

/// THE ROW'S EXIT TEST (LT-E30). A Strict log holding one record takes a batch of 4096:
///
/// - ONE WRITE: the device's write count rises by exactly 1 and the log issues exactly 1
///   full flush, where the same 4096 records through `publish_checked` on a log beside it
///   cost 4096 writes and 4096 full flushes (so the counter counts, and the batch is what
///   made it one);
/// - 4096 RECORD DIGESTS: one for each record, in order, each
///   `SHA-256(u16le(len(subject)) || subject || body)` by a second computation and by a
///   `hashlib` answer, all distinct;
/// - the records stand at consecutive offsets from the one handed back, under their keys,
///   and are durable: the only image a power loss can leave holds every one, and what an
///   open of it reads back hashes to the digests handed out, so a chain built from those
///   digests is the chain a re-read would build;
/// - a retry of the batch appends nothing and answers the same offset and digests, on the
///   log that wrote it and on one reopened after the power loss.
///
/// NEGATIVE CONTROLS, each run once against this test and restored (2026-11-18):
///
/// 1. `publish_batch_checked` committing after each staged record (`commit_batch` inside
///    its staging loop) fails here with "a batch of 4096 records took 4096 device writes"
///    (left 4096, right 1).
/// 2. `record_digest` hashing `subject || body` with no length prefix fails here with
///    "the digest of a known record".
#[test]
fn a_batch_of_4096_records_is_one_write_and_returns_4096_record_digests() {
    let records = batch(BATCH);

    // The formula, against an answer this crate did not compute:
    // hashlib.sha256(struct.pack('<H', 12) + b"/f/journal/0" + b"body").hexdigest().
    assert_eq!(
        record_digest("/f/journal/0", b"body").as_ref().map(hex),
        Some("c3eb5609e893cbec4c632b7c84385e09cf2a8267dd407bf3ef17f077603ec1bf".to_string()),
        "the digest of a known record"
    );
    // A subject past one byte of length and one hash block, not ASCII:
    // hashlib.sha256(struct.pack('<H', 300) + ('é' * 150).encode() + bytes(range(100))).
    assert_eq!(
        record_digest(&"é".repeat(150), &(0u8..100).collect::<Vec<u8>>())
            .as_ref()
            .map(hex),
        Some("610412b502ba2754c335f9047ace48a5b653efd77696be4150314ae6f150d745".to_string()),
        "the digest of a known record with a 300-byte subject"
    );
    assert_eq!(
        record_digest(&"x".repeat(65_536), b""),
        None,
        "a subject the prefix cannot state"
    );

    let sim = Sim::fresh();
    let mut log = open(&sim, options(Durability::Strict));
    // One record first, so the batch's first offset is not the empty log's zero.
    assert_eq!(
        log.publish_checked(9, 1, "/f/before".into(), b"x".to_vec())
            .unwrap(),
        (Offset(0), false)
    );
    let writes_before = sim.log_writes();
    let flushes_before = log.flush_counts();
    let device_before = sim.log_flushes();

    let published = log
        .publish_batch_checked(records.clone())
        .unwrap_or_else(|e| panic!("the batch is refused: {e}"));

    let writes = sim.log_writes() - writes_before;
    assert_eq!(
        writes, 1,
        "a batch of {BATCH} records took {writes} device writes"
    );
    assert_eq!(
        since(flushes_before, log.flush_counts()),
        FlushCounts {
            full: 1,
            ..FlushCounts::default()
        },
        "a Strict batch is one full flush and nothing else"
    );
    let device = sim.log_flushes();
    assert_eq!(
        (device.0 - device_before.0, device.1 - device_before.1),
        (1, 0),
        "the device took one full flush and no barrier"
    );

    assert_eq!(published.first, Offset(1), "the batch starts at the head");
    assert!(!published.deduped, "a new batch is appended");
    assert_eq!(published.digests.len(), BATCH, "a digest for each record");
    for (i, (digest, rec)) in published.digests.iter().zip(&records).enumerate() {
        assert_eq!(
            hex(digest),
            hex(&digest_by_hand(&rec.subject, &rec.body)),
            "the digest of record {i}"
        );
    }
    let distinct: HashSet<&[u8; 32]> = published.digests.iter().collect();
    assert_eq!(distinct.len(), BATCH, "no two records share a digest");

    assert_eq!(log.head(), Offset(1 + BATCH as u64));
    assert_eq!(log.durable_head(), log.head(), "the batch is durable");
    holds(&log, published.first, &records).unwrap();

    // A retry: nothing appended, the same answer.
    let writes_before = sim.log_writes();
    let retried = log.publish_batch_checked(records.clone()).unwrap();
    assert_eq!(
        retried,
        BatchPublished {
            deduped: true,
            ..published.clone()
        },
        "a retry answers as the batch did"
    );
    assert_eq!(sim.log_writes(), writes_before, "a retry writes nothing");
    assert_eq!(log.head(), Offset(1 + BATCH as u64));
    drop(log);

    // Durable: a power loss now leaves one image, and it holds the whole batch.
    let (images, every) = SimDevice::on(sim.clone()).power_loss_images(64, 7);
    assert!(every && !images.is_empty(), "every image, and at least one");
    for image in &images {
        let mut reopened = BrokerLog::open_sim(image, options(Durability::Strict)).unwrap();
        assert_eq!(reopened.head(), Offset(1 + BATCH as u64));
        holds(&reopened, published.first, &records).unwrap();
        let read = reopened.read_range(published.first, BATCH);
        for (i, (rec, digest)) in read.iter().zip(&published.digests).enumerate() {
            assert_eq!(
                record_digest(&rec.subject, &rec.body).as_ref(),
                Some(digest),
                "record {i} read back hashes to the digest handed out"
            );
        }
        // The retry a caller makes after a crash meets the keys the open's scan rebuilt.
        assert_eq!(
            reopened.publish_batch_checked(records.clone()).unwrap(),
            BatchPublished {
                deduped: true,
                ..published.clone()
            },
            "a retry after a power loss and a reopen answers as the batch did"
        );
        assert_eq!(reopened.head(), Offset(1 + BATCH as u64));
    }

    // The contrast: the same records one publish at a time are a write and a flush each.
    let beside = Sim::fresh();
    let mut one_at_a_time = open(&beside, options(Durability::Strict));
    for rec in records {
        one_at_a_time
            .publish_checked(rec.producer_id, rec.producer_seq, rec.subject, rec.body)
            .unwrap();
    }
    assert_eq!(beside.log_writes(), BATCH as u64);
    assert_eq!(one_at_a_time.flush_counts().full, BATCH as u64);
}

/// Every refusal leaves the log as it was: no record of the batch appended, no byte
/// written, nothing left staged, and the next batch lands at the unchanged head.
///
/// NEGATIVE CONTROL, run once and restored (2026-11-18): with the "retains N of the
/// batch's keys" refusal removed, a part-retained batch is answered as a retry and the
/// case "some keys retained" fails here ("was not refused").
#[test]
fn a_refused_batch_appends_nothing() {
    let sim = Sim::fresh();
    let mut log = open(&sim, options(Durability::Strict));
    // Three records held, published one at a time, the third with another's between.
    log.publish_checked(9, 1, "/f/held".into(), b"one".to_vec())
        .unwrap();
    log.publish_checked(9, 2, "/f/held".into(), b"two".to_vec())
        .unwrap();
    log.publish_checked(8, 1, "/f/between".into(), b"x".to_vec())
        .unwrap();
    log.publish_checked(9, 3, "/f/held".into(), b"three".to_vec())
        .unwrap();
    // Producer 4 continues producer 3's sequences.
    log.set_producer_lineage([(4, vec![3])]);
    let successor = |seq: u64| BatchRecord {
        producer_id: 4,
        producer_seq: seq,
        subject: "/f/ok".into(),
        body: b"new".to_vec(),
    };
    let held = |seq: u64, body: &[u8]| BatchRecord {
        producer_id: 9,
        producer_seq: seq,
        subject: "/f/held".into(),
        body: body.to_vec(),
    };
    let fresh = |seq: u64, subject: &str| BatchRecord {
        producer_id: 3,
        producer_seq: seq,
        subject: subject.into(),
        body: b"new".to_vec(),
    };
    let over_bound: Vec<BatchRecord> = (0..=MAX_SUBJECTS_PER_PRODUCER)
        .map(|i| fresh(i as u64 + 1, &format!("/f/bound/{i}")))
        .collect();
    let mut too_large = fresh(2, "/f/large");
    too_large.body = vec![0u8; MAX_RECORD_PAYLOAD + 1];

    let cases: Vec<(&str, Vec<BatchRecord>, std::io::ErrorKind)> = vec![
        (
            "a hidden subject",
            vec![fresh(1, "/f/ok"), fresh(2, COMMIT_SUBJECT)],
            std::io::ErrorKind::InvalidInput,
        ),
        (
            "a subject with no digest",
            vec![
                fresh(1, "/f/ok"),
                fresh(2, &format!("/f/{}", "x".repeat(65_536))),
            ],
            std::io::ErrorKind::InvalidInput,
        ),
        (
            "a key named twice",
            vec![fresh(1, "/f/ok"), fresh(2, "/f/ok"), fresh(1, "/f/ok")],
            std::io::ErrorKind::InvalidInput,
        ),
        (
            "some keys retained",
            vec![held(1, b"one"), held(2, b"two"), fresh(1, "/f/ok")],
            std::io::ErrorKind::InvalidInput,
        ),
        (
            "some keys retained, the new ones first",
            vec![fresh(1, "/f/ok"), held(1, b"one")],
            std::io::ErrorKind::InvalidInput,
        ),
        (
            "retained keys out of their order",
            vec![held(2, b"two"), held(1, b"one")],
            std::io::ErrorKind::InvalidInput,
        ),
        (
            "retained keys in order with another's record between them",
            vec![held(2, b"two"), held(3, b"three")],
            std::io::ErrorKind::InvalidInput,
        ),
        (
            "a key its producer's predecessor took earlier in the batch",
            vec![fresh(1, "/f/ok"), successor(1)],
            std::io::ErrorKind::InvalidInput,
        ),
        (
            "a record too large for a frame",
            vec![fresh(1, "/f/ok"), too_large],
            std::io::ErrorKind::InvalidData,
        ),
        (
            "a producer past its distinct subjects",
            over_bound,
            std::io::ErrorKind::InvalidInput,
        ),
    ];
    let head = log.head();
    let bytes = log.stats().retained_bytes;
    let writes = sim.log_writes();
    for (what, records, kind) in cases {
        match log.publish_batch_checked(records) {
            Err(CheckedPublishError::Io(e)) => assert_eq!(e.kind(), kind, "{what}: {e}"),
            Err(CheckedPublishError::Conflict(_)) => panic!("{what}: answered as a conflict"),
            Ok(published) => panic!("{what}: was not refused: {published:?}"),
        }
        assert_eq!(log.head(), head, "{what}: the head moved");
        assert_eq!(log.stats().retained_bytes, bytes, "{what}: bytes appended");
        assert_eq!(sim.log_writes(), writes, "{what}: the device was written");
        assert_eq!(log.poisoned(), None, "{what}: the log is poisoned");
    }

    // A retained key that names other bytes: the original comes back as evidence.
    match log.publish_batch_checked(vec![held(1, b"one"), held(2, b"other")]) {
        Err(CheckedPublishError::Conflict(original)) => {
            assert_eq!(
                (original.seq, original.body.as_slice()),
                (Offset(1), &b"two"[..])
            );
        }
        other => panic!("a conflicting key: {other:?}"),
    }
    assert_eq!((log.head(), sim.log_writes()), (head, writes));

    // The retry of two records that landed apart but stand together is a retry.
    let retried = log
        .publish_batch_checked(vec![held(1, b"one"), held(2, b"two")])
        .unwrap();
    assert_eq!((retried.first, retried.deduped), (Offset(0), true));
    assert_eq!((log.head(), sim.log_writes()), (head, writes));

    // An empty batch writes nothing and answers the head.
    let empty = log.publish_batch_checked(Vec::new()).unwrap();
    assert_eq!(
        empty,
        BatchPublished {
            first: head,
            digests: Vec::new(),
            deduped: false
        }
    );
    assert_eq!((log.head(), sim.log_writes()), (head, writes));

    // Nothing was left staged by any of it: the next batch lands whole at the head.
    let next = vec![fresh(1, "/f/ok"), fresh(2, "/f/ok")];
    let published = log.publish_batch_checked(next.clone()).unwrap();
    assert_eq!((published.first, published.deduped), (head, false));
    assert_eq!(sim.log_writes(), writes + 1);
    holds(&log, head, &next).unwrap();
}

/// The flush a batch owes is its tier's, once: nothing on Relaxed, one barrier on Ordered.
/// And a batch with an escalated record anywhere in it takes one FULL flush in its place,
/// as a record published alone does, so the durable head stands at the log's head when the
/// call returns; the retry of that batch then owes nothing more.
#[test]
fn a_batch_issues_the_one_flush_its_tier_owes_and_a_full_one_for_an_escalated_record() {
    let ordered = Durability::Ordered { horizon: None };
    let records = batch(64);

    let sim = Sim::fresh();
    let mut log = open(&sim, options(Durability::Relaxed));
    let device_before = sim.log_flushes();
    log.publish_batch_checked(records.clone()).unwrap();
    assert_eq!(sim.log_writes(), 1);
    assert_eq!(log.flush_counts(), FlushCounts::default(), "Relaxed");
    assert_eq!(sim.log_flushes(), device_before, "Relaxed: no flush");

    let sim = Sim::fresh();
    let mut opts = options(ordered);
    opts.escalation = Escalation::new([Escalate::Subject("/e/>".into())]);
    let mut log = open(&sim, opts);
    let device_before = sim.log_flushes();
    log.publish_batch_checked(records.clone()).unwrap();
    assert_eq!(sim.log_writes(), 1);
    assert_eq!(
        log.flush_counts(),
        FlushCounts {
            barrier: 1,
            ..FlushCounts::default()
        },
        "Ordered: one barrier"
    );
    let device = sim.log_flushes();
    assert_eq!(
        (device.0 - device_before.0, device.1 - device_before.1),
        (0, 1),
        "Ordered: the device took one barrier"
    );
    assert!(log.durable_head() < log.head(), "a barrier is not durable");

    let mut escalated: Vec<BatchRecord> = (64..72).map(record).collect();
    escalated[5].subject = "/e/page".into();
    let before = log.flush_counts();
    let device_before = sim.log_flushes();
    let published = log.publish_batch_checked(escalated.clone()).unwrap();
    assert_eq!(sim.log_writes(), 2);
    assert_eq!(
        since(before, log.flush_counts()),
        FlushCounts {
            full: 1,
            ..FlushCounts::default()
        },
        "an escalated batch's one flush is full, with no barrier before it"
    );
    let device = sim.log_flushes();
    assert_eq!(
        (device.0 - device_before.0, device.1 - device_before.1),
        (1, 0),
        "the device took one full flush and no barrier"
    );
    assert_eq!(
        log.durable_head(),
        log.head(),
        "the escalated batch is durable"
    );
    holds(&log, published.first, &escalated).unwrap();

    let before = log.flush_counts();
    let retried = log.publish_batch_checked(escalated).unwrap();
    assert!(retried.deduped && retried.first == published.first);
    assert_eq!(
        since(before, log.flush_counts()),
        FlushCounts::default(),
        "a full flush already covers the retried batch"
    );
}

/// A log written only by batches keeps its checkpoint as one written a record at a time
/// does: the batch that makes one due (`OpenOptions::checkpoint_every`) writes it.
///
/// NEGATIVE CONTROL, run once and restored (2026-11-18): without the `checkpoint_if_due`
/// call in `publish_batch_checked` this fails with "no checkpoint was written".
#[test]
fn a_log_written_by_batches_writes_the_checkpoint_that_comes_due() {
    let root = Scratch::new("batch-ckpt");
    let path = root.path().join("log");
    let mut ckpt = path.clone().into_os_string();
    ckpt.push(".ckpt");
    let opts = || {
        options(Durability::Relaxed)
            .with_resident_budget(512)
            .with_checkpoint_every(4_000)
    };
    let mut log = BrokerLog::open_opts(&path, opts(), BrokerLog::prepare_nothing).unwrap();
    assert!(
        !std::path::Path::new(&ckpt).exists(),
        "an empty log has none"
    );
    for round in 0..8 {
        let records: Vec<BatchRecord> = (round * 64..(round + 1) * 64).map(record).collect();
        log.publish_batch_checked(records).unwrap();
    }
    assert!(
        log.stats().retained_bytes > 8_000,
        "too few bytes for one to come due"
    );
    assert!(
        std::path::Path::new(&ckpt).exists(),
        "no checkpoint was written"
    );
    drop(log);
    let reopened = BrokerLog::open_opts(&path, opts(), BrokerLog::prepare_nothing).unwrap();
    assert_eq!(reopened.head(), Offset(8 * 64));
    holds(&reopened, Offset(0), &batch(8 * 64)).unwrap();
}

/// A batch whose write or flush fails is rolled back whole: the call is an error, no record
/// of the batch is in the log or on the device, nothing is left staged, and once the device
/// answers again the same batch lands at the unchanged head. On a weak tier that holds for
/// the FULL flush an escalated record makes the batch's own, too; where that flush fails
/// above records only a barrier covered, the batch is rolled back and the log is poisoned,
/// as by any full flush that fails there.
///
/// NEGATIVE CONTROL, run once and restored (2026-11-18): with the batch's flush left the
/// tier's when it holds an escalated record (the `write.flush = Flush::Full` line removed,
/// so the full flush is the owed one issued after the commit), the Ordered arm fails here
/// with "an escalated batch whose flush failed is in the log".
#[test]
fn a_batch_whose_write_or_flush_fails_is_rolled_back_whole() {
    let write = InjectedFaults {
        write: true,
        ..InjectedFaults::default()
    };
    let sync = InjectedFaults {
        sync: true,
        ..InjectedFaults::default()
    };
    let records = batch(8);
    for (what, faults) in [("a failed write", write), ("a failed full flush", sync)] {
        let sim = Sim::fresh();
        let mut log = open(&sim, options(Durability::Strict));
        log.publish_checked(9, 1, "/f/before".into(), b"x".to_vec())
            .unwrap();
        let (head, len) = (log.head(), sim.log_len());
        log.inject_faults(faults);
        match log.publish_batch_checked(records.clone()) {
            Err(CheckedPublishError::Io(_)) => {}
            other => panic!("{what}: {other:?}"),
        }
        assert_eq!(log.head(), head, "{what}: the head moved");
        assert_eq!(sim.log_len(), len, "{what}: bytes left on the device");
        assert_eq!(
            log.poisoned(),
            None,
            "{what}: a rolled-back batch poisons nothing"
        );
        log.inject_faults(InjectedFaults::default());
        let published = log.publish_batch_checked(records.clone()).unwrap();
        assert_eq!(
            (published.first, published.deduped),
            (head, false),
            "{what}"
        );
        holds(&log, head, &records).unwrap();
    }

    // Ordered, an escalated record in the batch, and the full flush it makes the batch's
    // own fails. First on a log whose head is durable: rolled back, and the log goes on.
    let mut escalated = records.clone();
    escalated[3].subject = "/e/page".into();
    let ordered = || {
        let mut opts = options(Durability::Ordered { horizon: None });
        opts.escalation = Escalation::new([Escalate::Subject("/e/>".into())]);
        opts
    };
    let sim = Sim::fresh();
    let mut log = open(&sim, ordered());
    let (head, len) = (log.head(), sim.log_len());
    log.inject_faults(sync);
    assert!(log.publish_batch_checked(escalated.clone()).is_err());
    assert_eq!(
        (log.head(), sim.log_len()),
        (head, len),
        "an escalated batch whose flush failed is in the log"
    );
    assert_eq!(log.poisoned(), None, "nothing earlier was at risk");
    log.inject_faults(InjectedFaults::default());
    let published = log.publish_batch_checked(escalated.clone()).unwrap();
    assert_eq!((published.first, published.deduped), (head, false));
    assert_eq!(log.durable_head(), log.head());

    // Then above records only a barrier covers: the batch is rolled back all the same, and
    // the log refuses every write until it is reopened, since the device that failed the
    // flush may have dropped those earlier records.
    let sim = Sim::fresh();
    let mut log = open(&sim, ordered());
    log.publish_batch_checked((100..104).map(record).collect())
        .unwrap();
    assert!(log.durable_head() < log.head(), "a barrier is not durable");
    let (head, len) = (log.head(), sim.log_len());
    log.inject_faults(sync);
    assert!(log.publish_batch_checked(escalated.clone()).is_err());
    assert_eq!(
        (log.head(), sim.log_len()),
        (head, len),
        "an escalated batch whose flush failed is in the log"
    );
    assert!(log.poisoned().is_some(), "earlier records were at risk");
    log.inject_faults(InjectedFaults::default());
    assert!(
        log.publish_batch_checked(escalated).is_err(),
        "a poisoned log refuses the batch"
    );
    assert_eq!(log.head(), head);
}
