// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The open from a checkpoint (`ckpt.rs`) against the full scan it stands in for (aterm
//! tracker LT-A7).
//!
//! - The exit test: a log of 1,000,000 records reopens decoding only the frames written
//!   after its checkpoint, and answers as the open that scanned them all; with a byte of
//!   the checkpoint flipped it scans them all, and answers the same.
//! - The stream: random logs written through the real writer (as `open_scan_tests.rs`
//!   writes them: re-sent keys, batches, group commits, wills, bindings, retirements,
//!   retention cuts, clean and unclean stops), sealed and plain, checkpointed by the commit
//!   that made one due, by the open and by hand, each reopened as two copies of the same
//!   files after a random tear: one with its checkpoint removed, which is the full scan,
//!   and one with it. The two answer every query alike.
//! - What a checkpoint is bound to: one of another log, of an earlier generation or of an
//!   earlier base is not taken up; nor is one with any byte flipped, cut short or added to.
//! - NEGATIVE CONTROL: a checkpoint taken up unbound (`ReadOpen::unbound_checkpoint`) makes
//!   the two differ.

use super::open_scan_tests::{
    answers, answers_over, copy_log, first_difference, open_as, options, tear_from, Rng, Shape,
    PENDINGS, WINDOWS,
};
use super::*;
use crate::storage::Dir;
use crate::test_scratch::Scratch;

/// A plain Relaxed log that keeps `budget` bytes of records decoded.
const fn plain(budget: usize) -> Shape {
    Shape {
        sealed: false,
        verified: false,
        strict: false,
        budget,
    }
}

/// Open the log at `path` as `shape` holds it, reading it as `read` says, with a checkpoint
/// kept every `every` bytes.
fn open(path: &Path, shape: Shape, read: ReadOpen, every: Option<u64>) -> io::Result<BrokerLog> {
    let mut opts = options(shape, read);
    opts.checkpoint_every = every;
    open_as(path, shape, &opts, false)
}

/// What an open on this thread decoded and whether it served from a checkpoint.
#[derive(Clone, Copy, Debug)]
struct Counted {
    decoded: open_scan::Decodes,
    /// Served from a checkpoint.
    taken: usize,
    /// Took one up, failed, and was judged again by the full scan.
    retried: usize,
}

/// Run `f`, counting what the opens in it decoded.
fn counting<T>(f: impl FnOnce() -> T) -> (T, Counted) {
    open_scan::DECODED.with(|n| n.set(open_scan::Decodes::default()));
    ckpt::OPENS.with(|n| n.set((0, 0)));
    let out = f();
    let (taken, retried) = ckpt::OPENS.with(std::cell::Cell::get);
    let counted = Counted {
        decoded: open_scan::DECODED.with(std::cell::Cell::get),
        taken,
        retried,
    };
    (out, counted)
}

fn ckpt_of(path: &Path) -> std::path::PathBuf {
    ckpt::checkpoint_path(path)
}

/// The identity `<log>.id` names at `path`, if any.
fn recorded_id(path: &Path) -> Option<[u8; 16]> {
    match logid::read(&Dir::Os(path.to_path_buf())) {
        Ok(Prior::Recorded(s)) => Some(s.identity.id),
        _ => None,
    }
}

/// What one open of `path` answers ([`answers`]), or its refusal with the copy's own folder
/// taken out of the message.
fn opened(path: &Path, shape: Shape, read: ReadOpen, every: Option<u64>) -> Vec<String> {
    let prior_id = recorded_id(path);
    match open(path, shape, read, every) {
        Ok(log) => answers(&log, path, prior_id),
        Err(e) => {
            let folder = path.parent().unwrap().display().to_string();
            vec![format!(
                "refused {:?}: {}",
                e.kind(),
                e.to_string().replace(&folder, "<dir>")
            )]
        }
    }
}

/// Publish `n` more records to `log` in batches of 500: eight producers by turns, each with
/// its own next sequence, over thirteen subjects, the bodies of 16 to 47 bytes.
fn publish_mixed(log: &mut BrokerLog, n: u64, next_seq: &mut [u64; 8]) {
    let from = log.head().0;
    for i in from..from + n {
        let p = ((i / 500) % 8) as usize;
        next_seq[p] += 1;
        let body = vec![(i % 251) as u8; 16 + (i % 32) as usize];
        log.stage_publish(
            p as u64 + 1,
            next_seq[p],
            format!("/f/ckpt/s{}", i % 13),
            body,
        )
        .unwrap_or_else(|e| panic!("stage {i}: {e:?}"));
        if (i + 1) % 500 == 0 {
            log.commit_batch()
                .unwrap_or_else(|e| panic!("batch at {i}: {e}"));
        }
    }
    log.commit_batch()
        .unwrap_or_else(|e| panic!("the last batch: {e}"));
}

/// A will, a binding and a group commit, each its own unit.
fn publish_state(log: &mut BrokerLog, round: u64, next_seq: &[u64; 8]) {
    let pid = 1 + round % 8;
    let will = WillRecord {
        producer_id: pid,
        producer_seq: next_seq[(pid - 1) as usize] + 1_000_000,
        subject: format!("/f/ckpt/will{}", round % 3),
        body: vec![9u8; 24],
    };
    log.stage_will_register(&will)
        .unwrap_or_else(|e| panic!("will {round}: {e:?}"));
    log.commit_batch()
        .unwrap_or_else(|e| panic!("will {round}: {e}"));
    if log.stage_bind(pid, format!("principal-{pid}")).is_ok() {
        log.commit_batch()
            .unwrap_or_else(|e| panic!("bind {round}: {e}"));
    }
    log.commit(format!("g{}", round % 4), log.head().0 / 2)
        .unwrap_or_else(|e| panic!("group commit {round}: {e}"));
}

/// THE EXIT TEST (aterm tracker LT-A7). A log of 1,000,000 records, written with a will, a
/// binding and a group commit every 50,000, checkpointed with 10,000 records still to come:
///
/// - reopened, it decodes the 10,000 frames after the checkpoint and the one the checkpoint
///   is bound to, where the open with no checkpoint decodes all 1,000,000;
/// - the two answer alike: every record's summary, place and time, the resident window,
///   every index, the identity, and the records read back;
/// - with one byte of the checkpoint flipped the open scans all 1,000,000 frames, answers
///   the same, and leaves no checkpoint behind.
#[test]
fn open_from_checkpoint_scans_only_tail() {
    const RECORDS: u64 = 1_000_000;
    const TAIL: u64 = 10_000;
    let root = Scratch::new("ckpt-exit");
    let path = root.path().join("log");
    // 64 KiB of records stay decoded: a window well inside the tail.
    let shape = plain(64 << 10);
    let shipped = ReadOpen::default();
    let mut log = open(&path, shape, shipped, None).unwrap_or_else(|e| panic!("create: {e}"));
    let mut next_seq = [0u64; 8];
    let mut round = 0u64;
    while log.head().0 < RECORDS - TAIL {
        let left = RECORDS - TAIL - log.head().0;
        publish_mixed(&mut log, left.min(50_000 - 3), &mut next_seq);
        if left > 50_000 {
            publish_state(&mut log, round, &next_seq);
            round += 1;
        }
    }
    assert_eq!(log.head().0, RECORDS - TAIL, "the head at the checkpoint");
    assert!(
        log.checkpoint()
            .unwrap_or_else(|e| panic!("checkpoint: {e}")),
        "the log wrote no checkpoint at record {}",
        log.head().0
    );
    let header = ckpt::header_of(&path, None).expect("the checkpoint reads back");
    assert_eq!(header.count, RECORDS - TAIL, "the checkpoint's records");
    publish_state(&mut log, round, &next_seq);
    let left = RECORDS - log.head().0;
    publish_mixed(&mut log, left, &mut next_seq);
    assert_eq!(log.head().0, RECORDS, "the head at the close");
    log.close_clean().unwrap_or_else(|e| panic!("close: {e}"));
    drop(log);
    let checkpoint = std::fs::read(ckpt_of(&path)).unwrap();
    let id = recorded_id(&path);
    // The first line names the identity sidecar as the open left it, which is each open's
    // own; the identity itself is compared apart.
    let read_back = |log: &BrokerLog| answers_over(log, &path, id, 4_099).split_off(1);

    // The full scan: the same files with the checkpoint taken away.
    std::fs::remove_file(ckpt_of(&path)).unwrap();
    let (full, scanned) = counting(|| {
        let mut log = open(&path, shape, shipped, None).unwrap_or_else(|e| panic!("full: {e}"));
        let said = (log.identity.identity, read_back(&log));
        log.close_clean().unwrap();
        said
    });
    assert_eq!(
        scanned.decoded.scanned as u64, RECORDS,
        "the full scan's frames"
    );
    assert_eq!(
        (scanned.taken, scanned.decoded.bound),
        (0, 0),
        "no checkpoint was there"
    );
    let resident = scanned.decoded.reread;
    assert!(
        resident > 100 && (resident as u64) < TAIL,
        "the window holds {resident} records, which is not inside the tail"
    );

    // From the checkpoint: only the tail's frames.
    std::fs::write(ckpt_of(&path), &checkpoint).unwrap();
    let (tail, from_checkpoint) = counting(|| {
        let mut log = open(&path, shape, shipped, None).unwrap_or_else(|e| panic!("tail: {e}"));
        let said = (log.identity.identity, read_back(&log));
        log.close_clean().unwrap();
        said
    });
    assert_eq!(from_checkpoint.taken, 1, "the open took no checkpoint up");
    assert_eq!(
        from_checkpoint.decoded,
        open_scan::Decodes {
            scanned: TAIL as usize,
            reread: resident,
            bound: 1,
        },
        "the open from the checkpoint decoded more than the tail after it"
    );
    assert_eq!(
        tail.0, full.0,
        "the identity after the open from the checkpoint"
    );
    if let Some(d) = first_difference(&full.1, &tail.1) {
        panic!("the open from the checkpoint differs from the full scan: {d}");
    }
    assert!(
        std::fs::read(ckpt_of(&path)).is_ok_and(|now| now == checkpoint),
        "an open that asked for no checkpoint rewrote the one it took up"
    );

    // A corrupted checkpoint: the full scan again.
    let mut corrupt = checkpoint.clone();
    let middle = corrupt.len() / 2;
    corrupt[middle] ^= 0x10;
    std::fs::write(ckpt_of(&path), &corrupt).unwrap();
    let (fell_back, rescanned) = counting(|| {
        let mut log = open(&path, shape, shipped, None).unwrap_or_else(|e| panic!("corrupt: {e}"));
        let said = (log.identity.identity, read_back(&log));
        log.close_clean().unwrap();
        said
    });
    assert_eq!(
        (rescanned.taken, rescanned.retried, rescanned.decoded.bound),
        (0, 0, 0),
        "a corrupted checkpoint was taken up"
    );
    assert_eq!(
        rescanned.decoded.scanned as u64, RECORDS,
        "the open beside a corrupted checkpoint did not scan the whole log"
    );
    assert_eq!(fell_back.0, full.0, "the identity after the fallback");
    if let Some(d) = first_difference(&full.1, &fell_back.1) {
        panic!("the open beside a corrupted checkpoint differs from the full scan: {d}");
    }
    assert!(
        !ckpt_of(&path).exists(),
        "the open left the corrupted checkpoint beside the log"
    );
    println!(
        "open_from_checkpoint_scans_only_tail: {RECORDS} records, checkpoint of {} bytes at \
         record {}; frames decoded: full scan {} (+{} for the window), from the checkpoint {} \
         (+{} for the window, +{} bound), beside a corrupted checkpoint {}",
        checkpoint.len(),
        header.count,
        scanned.decoded.scanned,
        scanned.decoded.reread,
        from_checkpoint.decoded.scanned,
        from_checkpoint.decoded.reread,
        from_checkpoint.decoded.bound,
        rescanned.decoded.scanned,
    );
}

// ---------------------------------------------------------------------------------------
// The stream.
// ---------------------------------------------------------------------------------------

/// What the comparisons of a run of seeds met.
#[derive(Debug, Default)]
struct Met {
    /// Opens compared that served, and that refused.
    served: usize,
    refused: usize,
    /// Of them, the opens that served from a checkpoint, and those that took one up, failed
    /// and were judged again by the full scan.
    taken: usize,
    retried: usize,
    /// Frames the opens from a checkpoint did not scan.
    skipped: usize,
}

/// Remove the checkpoint beside the log at `path`: what is left opens by the full scan.
fn without_checkpoint(path: &Path) {
    let _ = std::fs::remove_file(ckpt_of(path));
}

/// The full scan (a copy of the log at `path` with its checkpoint removed) and the open with
/// it (`stream`, `every`), compared: the first difference, if any; whether they refused.
fn compare(
    root: &Path,
    path: &Path,
    shape: Shape,
    (stream, every): (ReadOpen, Option<u64>),
    tag: &str,
    met: &mut Met,
) -> Result<bool, String> {
    let a = copy_log(path, &root.join(format!("{tag}-full")));
    let b = copy_log(path, &root.join(format!("{tag}-ckpt")));
    without_checkpoint(&a);
    let ra = opened(&a, shape, ReadOpen::default(), None);
    let (rb, counted) = counting(|| opened(&b, shape, stream, every));
    if let Some(d) = first_difference(&ra, &rb) {
        return Err(format!("{d}\n  ({counted:?})"));
    }
    let refused = ra.first().is_some_and(|l| l.starts_with("refused"));
    if refused {
        met.refused += 1;
    } else {
        met.served += 1;
    }
    met.taken += counted.taken;
    met.retried += counted.retried;
    if counted.taken > 0 {
        let full = ra.iter().filter(|l| l.starts_with("summary ")).count();
        met.skipped += full.saturating_sub(counted.decoded.scanned);
    }
    Ok(refused)
}

/// One seeded stream: the real writer's records into a log held as `shape` says and
/// checkpointed as it goes, and at every reopen, after a random tear, the full scan and the
/// open from the checkpoint of its copies compared ([`compare`]). The checkpointed side
/// reads through `mutant`'s negative control when one is set. `Err`: the first difference.
fn stream_differs(seed: u64, shape: Shape, mutant: ReadOpen, met: &mut Met) -> Result<(), String> {
    let root = Scratch::new(&format!("ckpt-stream-{seed}"));
    let path = root.path().join("log");
    let mut rng = Rng::new(seed);
    let shipped = ReadOpen::default();
    // The bytes between checkpoints: at every commit, a few a stream, and by hand alone.
    let every = [Some(300), Some(2_500), Some(9_000), None][(seed / 2 % 4) as usize];
    // The seed's own clock: a checkpoint's bytes, and so where the next falls due, follow the
    // steps between its records' broker times.
    let clock = Arc::new(std::sync::atomic::AtomicU64::new(1_700_000_000_000));
    let mut log = open(&path, shape, shipped, every).unwrap_or_else(|e| panic!("first open: {e}"));
    log.clock_override_ms = Some(Arc::clone(&clock));
    let mut next_seq = [0u64; 4];
    let mut reopen = 0usize;
    for step in 0..160 {
        clock.fetch_add(rng.below(40), std::sync::atomic::Ordering::Relaxed);
        let roll = rng.below(100);
        if roll < 40 {
            let pid = 1 + rng.below(4);
            let slot = &mut next_seq[pid as usize - 1];
            let pseq = if rng.below(6) == 0 && *slot > 0 {
                rng.below(*slot)
            } else {
                *slot += 1 + rng.below(2);
                *slot
            };
            let body = vec![(step % 251) as u8; rng.below(300) as usize];
            log.publish(pid, pseq, format!("/f/open/s{}", rng.below(7)), body)
                .unwrap_or_else(|e| panic!("step {step}: publish: {e}"));
        } else if roll < 55 {
            for _ in 0..1 + rng.below(30) {
                let pid = 1 + rng.below(4);
                next_seq[pid as usize - 1] += 1;
                let pseq = next_seq[pid as usize - 1];
                let body = vec![7u8; rng.below(200) as usize];
                let _ = log.stage_publish(pid, pseq, format!("/f/open/b{}", rng.below(4)), body);
            }
            log.commit_batch()
                .unwrap_or_else(|e| panic!("step {step}: batch: {e}"));
        } else if roll < 61 {
            let upto = rng.below(log.head().0 + 1);
            log.commit(format!("g{}", rng.below(3)), upto)
                .unwrap_or_else(|e| panic!("step {step}: commit: {e}"));
        } else if roll < 66 {
            let pid = 1 + rng.below(4);
            let will = WillRecord {
                producer_id: pid,
                producer_seq: next_seq[pid as usize - 1] + 1 + rng.below(3),
                subject: format!("/f/open/will{}", rng.below(3)),
                body: vec![9u8; rng.below(40) as usize],
            };
            if log.stage_will_register(&will).is_ok() {
                log.commit_batch()
                    .unwrap_or_else(|e| panic!("step {step}: will: {e}"));
            }
        } else if roll < 69 {
            let pid = 1 + rng.below(4);
            if log.stage_bind(pid, format!("principal-{pid}")).is_ok() {
                log.commit_batch()
                    .unwrap_or_else(|e| panic!("step {step}: bind: {e}"));
            }
        } else if roll < 72 {
            let pid = 1 + rng.below(4);
            let _ = log.retire_subject(pid, &format!("/f/open/s{}", rng.below(7)));
        } else if roll < 76 {
            #[cfg(feature = "retention")]
            {
                let span = log.head().0 - log.base().0;
                let cut = Offset(log.base().0 + rng.below(span / 2 + 1));
                if rng.below(2) == 0 {
                    let _ = log.retain_before(cut);
                } else {
                    log.retain_before_carrying_state(cut)
                        .unwrap_or_else(|e| panic!("step {step}: retention: {e}"));
                }
            }
        } else if roll < 81 {
            // A checkpoint by hand, wherever the stream stands.
            log.checkpoint()
                .unwrap_or_else(|e| panic!("step {step}: checkpoint: {e}"));
        } else if roll < 93 {
            // Stop (cleanly or not), tear, and hold the two opens of the copies to each other.
            if rng.below(3) == 0 {
                log.close_clean()
                    .unwrap_or_else(|e| panic!("step {step}: close: {e}"));
            }
            // A checkpoint is trusted for the frames below its last record, which a full
            // flush covered before it was written: the tear's flipped byte lands at that
            // record or after it.
            let flips_from = ckpt::header_of(&path, log.at_rest_ref()).map_or(0, |h| h.newest_at);
            drop(log);
            let (torn, before) = tear_from(&mut rng, &path, flips_from as usize);
            let stream = ReadOpen {
                window: Some(rng.pick(&WINDOWS)),
                pending: Some(rng.pick(&PENDINGS)),
                ..mutant
            };
            let reopened_every = rng.pick(&[None, Some(1), Some(2_000)]);
            // (An open's own checkpoint costs it no flush of the log: its recovery made one.)
            compare(
                root.path(),
                &path,
                shape,
                (stream, reopened_every),
                &format!("r{reopen}"),
                met,
            )
            .map_err(|e| format!("step {step}, reopen {reopen} after {torn}, {stream:?}: {e}"))?;
            reopen += 1;
            log = match open(&path, shape, shipped, every) {
                Ok(log) => log,
                Err(_) => {
                    // A tear the open refuses is undone, and the log goes on from what it
                    // held.
                    std::fs::write(&path, &before).unwrap();
                    open(&path, shape, shipped, every)
                        .unwrap_or_else(|e| panic!("step {step}: the reopen after {torn}: {e}"))
                }
            };
            log.clock_override_ms = Some(Arc::clone(&clock));
        } else {
            log.publish(0, 0, "/f/open/zero".to_string(), Vec::new())
                .unwrap_or_else(|e| panic!("step {step}: publish: {e}"));
        }
    }
    drop(log);
    compare(root.path(), &path, shape, (shipped, None), "last", met).map(|_| ())
}

/// A seed's shape: sealed one seed in three (and verified against its watermark every other
/// one of those), the residency budget 512 B, nothing and 16 MiB by threes, so each is met
/// sealed and plain.
fn shape_of(seed: u64) -> Shape {
    let sealed = cfg!(feature = "at-rest") && seed % 3 == 1;
    Shape {
        sealed,
        verified: cfg!(feature = "anti-rollback") && sealed && seed % 2 == 0,
        strict: false,
        budget: [512, 0, 16 << 20][(seed / 3 % 3) as usize],
    }
}

/// Over 24 seeded streams, each reopened about a dozen times, the open from a checkpoint
/// answers every query as the full scan of the same files does; and the test met what it is
/// about: opens served from a checkpoint by the hundred, frames they did not scan, opens
/// with no checkpoint to take up, opens that refused, and opens that failed from a
/// checkpoint and were judged again.
#[test]
fn an_open_from_a_checkpoint_answers_every_query_as_the_full_scan() {
    let mut met = Met::default();
    for seed in 0..24u64 {
        let shape = shape_of(seed);
        if let Err(e) = stream_differs(seed, shape, ReadOpen::default(), &mut met) {
            panic!("seed {seed} ({shape:?}): the open from a checkpoint differs: {e}");
        }
    }
    println!("an open from a checkpoint against the full scan: {met:?}");
    assert!(
        met.taken >= 100 && met.skipped >= 10_000,
        "too few opens served from a checkpoint for the comparison to mean much: {met:?}"
    );
    assert!(
        met.served > met.taken && met.refused > 0 && met.retried > 0,
        "the seeds met too little: {met:?}"
    );
}

/// Two logs of the same shape, frame for frame, whose records differ: `n` records each, in
/// batches of ten, closed cleanly, the first with a checkpoint at its head.
fn twins(root: &Path, shape: Shape, n: u64) -> (std::path::PathBuf, std::path::PathBuf) {
    let build = |name: &str, salt: u64| {
        let path = root.join(name).join("log");
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        let mut log = open(&path, shape, ReadOpen::default(), None)
            .unwrap_or_else(|e| panic!("create {name}: {e}"));
        log.clock_override_ms = Some(Arc::new(std::sync::atomic::AtomicU64::new(
            1_700_000_000_000,
        )));
        for i in 0..n {
            let pid = 1 + (i + salt) % 3;
            log.stage_publish(
                pid,
                i + 1,
                format!("/f/twin/{}", (i * (salt + 1)) % 5),
                vec![3u8; 40],
            )
            .unwrap_or_else(|e| panic!("stage {i}: {e:?}"));
            if (i + 1) % 10 == 0 {
                log.commit_batch().unwrap();
            }
        }
        log.commit_batch().unwrap();
        (path, log)
    };
    let (a, mut log_a) = build("a", 0);
    let (b, mut log_b) = build("b", 1);
    assert!(
        log_a.checkpoint().unwrap(),
        "the first twin wrote no checkpoint"
    );
    assert_eq!(log_a.durable_len, log_b.durable_len, "the twins' lengths");
    log_a.close_clean().unwrap();
    log_b.close_clean().unwrap();
    (a, b)
}

/// The binding, and the NEGATIVE CONTROL of every comparison here: a checkpoint of another
/// log of the same shape, put beside this one, is not taken up, and the open answers as its
/// full scan; taken up unbound (`ReadOpen::unbound_checkpoint`), it answers with the other
/// log's indices, and the comparison says so.
#[test]
fn a_checkpoint_of_another_log_is_not_taken_up_and_one_taken_up_unbound_is_caught() {
    let root = Scratch::new("ckpt-twins");
    let shape = plain(512);
    let (a, b) = twins(root.path(), shape, 200);
    std::fs::copy(ckpt_of(&a), ckpt_of(&b)).unwrap();
    let full = copy_log(&b, &root.path().join("full"));
    without_checkpoint(&full);
    let reference = opened(&full, shape, ReadOpen::default(), None);

    let bound = copy_log(&b, &root.path().join("bound"));
    let (said, counted) = counting(|| opened(&bound, shape, ReadOpen::default(), None));
    assert_eq!(counted.taken, 0, "another log's checkpoint was taken up");
    assert_eq!(counted.decoded.scanned, 200, "the frames scanned beside it");
    assert_eq!(first_difference(&reference, &said), None);
    assert!(
        !ckpt_of(&bound).exists(),
        "another log's checkpoint was left there"
    );

    let unbound = copy_log(&b, &root.path().join("unbound"));
    let mutant = ReadOpen {
        unbound_checkpoint: true,
        ..ReadOpen::default()
    };
    let (said, counted) = counting(|| opened(&unbound, shape, mutant, None));
    assert_eq!(counted.taken, 1, "the unbound open took no checkpoint up");
    assert!(
        first_difference(&reference, &said).is_some(),
        "an open from another log's checkpoint answered as this log's full scan: the \
         comparison sees nothing"
    );
}

/// One small log with a checkpoint 60 records below its head, closed cleanly: its path, and
/// what its full scan answers.
fn small(root: &Path, shape: Shape) -> (std::path::PathBuf, Vec<String>) {
    let path = root.join("src").join("log");
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    let mut log =
        open(&path, shape, ReadOpen::default(), None).unwrap_or_else(|e| panic!("create: {e}"));
    let mut next_seq = [0u64; 8];
    publish_mixed(&mut log, 140, &mut next_seq);
    publish_state(&mut log, 0, &next_seq);
    assert!(log.checkpoint().unwrap(), "the log wrote no checkpoint");
    publish_mixed(&mut log, 60, &mut next_seq);
    log.close_clean().unwrap();
    drop(log);
    let full = copy_log(&path, &root.join("full"));
    without_checkpoint(&full);
    let reference = opened(&full, shape, ReadOpen::default(), None);
    (path, reference)
}

/// A checkpoint with any one bit flipped, cut short anywhere, or added to, is not taken up
/// ([`ckpt::load`], asked as the open asks it, of a plain log and a sealed one): every bit of
/// every byte, every length. The whole one is taken up. (What an open does beside one that
/// is not: the exit test, and the stream's stale ones.)
#[test]
fn a_damaged_checkpoint_is_never_taken_up() {
    let shapes = [plain(512), shape_of(1)];
    for (s, shape) in shapes.into_iter().enumerate() {
        let root = Scratch::new(&format!("ckpt-damaged-{s}"));
        let (path, _) = small(root.path(), shape);
        let whole = std::fs::read(ckpt_of(&path)).unwrap();
        let log = open(&path, shape, ReadOpen::default(), None).unwrap();
        let bound = ckpt::Bound {
            base: log.base.0,
            identity: log.identity.identity,
            first: log.log_id,
            len: log.durable_len,
            key: log.at_rest_ref(),
            mutation: Mutation::Off,
            unbound: false,
        };
        let taken_up = |bytes: &[u8]| {
            std::fs::write(ckpt_of(&path), bytes).unwrap();
            ckpt::load(&log.file, &path, &bound, |records| {
                let expect = crate::tier::Expect {
                    records,
                    exact: true,
                    end: log.durable_len,
                };
                crate::tier::Tier::opening(512, expect)
            })
            .map(|seed| seed.header.count)
        };
        let records = ckpt::header_of(&path, log.at_rest_ref()).map(|h| h.count);
        assert!(
            records.is_some_and(|n| n > 100),
            "{shape:?}: the checkpoint: {records:?}"
        );
        assert_eq!(taken_up(&whole), records, "{shape:?}: the whole checkpoint");
        for at in 0..whole.len() {
            for bit in 0..8 {
                let mut bytes = whole.clone();
                bytes[at] ^= 1 << bit;
                assert_eq!(
                    taken_up(&bytes),
                    None,
                    "{shape:?}: the checkpoint with bit {bit} of byte {at} flipped was taken up"
                );
            }
        }
        for cut in 0..whole.len() {
            assert_eq!(
                taken_up(&whole[..cut]),
                None,
                "{shape:?}: the checkpoint cut to {cut} bytes was taken up"
            );
        }
        let mut longer = whole.clone();
        longer.push(0);
        assert_eq!(taken_up(&longer), None, "{shape:?}: with a byte added");
        longer.pop();
        longer.extend_from_slice(&whole);
        assert_eq!(taken_up(&longer), None, "{shape:?}: written twice over");
    }
}

/// A checkpoint is bound to the generation and the base it was taken at. Put back beside the
/// log after a repair cut its tail (the generation moved) and after a retention cut (the
/// base moved), it is not taken up, and each open answers as its full scan.
#[test]
fn a_checkpoint_of_an_earlier_generation_or_base_is_not_taken_up() {
    let root = Scratch::new("ckpt-stale");
    let shape = plain(512);
    let (path, _) = small(root.path(), shape);
    let earlier = std::fs::read(ckpt_of(&path)).unwrap();
    let check = |tag: &str| {
        let full = copy_log(&path, &root.path().join(format!("{tag}-full")));
        without_checkpoint(&full);
        let reference = opened(&full, shape, ReadOpen::default(), None);
        let stale = copy_log(&path, &root.path().join(format!("{tag}-stale")));
        std::fs::write(ckpt_of(&stale), &earlier).unwrap();
        let (said, counted) = counting(|| opened(&stale, shape, ReadOpen::default(), None));
        assert_eq!(
            counted.taken, 0,
            "{tag}: the earlier checkpoint was taken up"
        );
        assert_eq!(first_difference(&reference, &said), None, "{tag}");
    };

    // The generation: a byte flipped in the newest record, which only the explicit repair
    // cuts, above the checkpoint.
    let mut bytes = std::fs::read(&path).unwrap();
    let intact = bytes.len();
    bytes[intact - 5] ^= 0x20;
    std::fs::write(&path, &bytes).unwrap();
    let before = ckpt::header_of(&path, None).expect("the checkpoint");
    let opts = options(shape, ReadOpen::default());
    let mut log = open_as(&path, shape, &opts, true).unwrap_or_else(|e| panic!("repair: {e}"));
    assert!(
        log.durable_len < intact as u64 && log.durable_len > before.len,
        "the repair cut to byte {}, not between the checkpoint's {} and the log's {intact}",
        log.durable_len,
        before.len
    );
    let before = before.identity;
    assert_eq!(log.identity.identity.id, before.id, "the repaired log's id");
    assert_ne!(
        log.identity.identity.generation, before.generation,
        "the repair moved no generation"
    );
    assert!(!ckpt_of(&path).exists(), "the repair left the checkpoint");
    // The repair cut inside the last batch, whose unit never ended: no checkpoint stands
    // there, and one does once a record ends a unit after it.
    assert!(
        !log.checkpoint().unwrap(),
        "a checkpoint where no unit ended"
    );
    log.publish(1, 900_000, "/f/ckpt/after".to_string(), vec![2u8; 8])
        .unwrap_or_else(|e| panic!("publish after the repair: {e}"));
    log.close_clean().unwrap();
    drop(log);
    check("generation");

    // The base.
    #[cfg(feature = "retention")]
    {
        let mut log = open(&path, shape, ReadOpen::default(), None).unwrap();
        assert!(log.checkpoint().unwrap());
        let at_base_0 = std::fs::read(ckpt_of(&path)).unwrap();
        log.retain_before_carrying_state(Offset(50))
            .unwrap_or_else(|e| panic!("retention: {e}"));
        assert_eq!(log.base().0, 50, "the base after the cut");
        assert!(!ckpt_of(&path).exists(), "the cut left the checkpoint");
        log.close_clean().unwrap();
        drop(log);
        check("base");
        // The checkpoint of this very generation at base 0 as well.
        let stale = copy_log(&path, &root.path().join("base-0"));
        std::fs::write(ckpt_of(&stale), &at_base_0).unwrap();
        let (_, counted) = counting(|| opened(&stale, shape, ReadOpen::default(), None));
        assert_eq!(
            counted.taken, 0,
            "the checkpoint at base 0 was taken up at base 50"
        );
    }
}

/// `checkpoint_every`: the append that makes one due writes it, an interval of the bytes
/// asked or of the last checkpoint's own bytes when that is more; an open after an unclean
/// stop that moved the generation leaves one bound to the new one; an open writes the one
/// its fold left when none stands, and the next open scans nothing.
#[test]
fn a_commit_and_an_open_write_the_checkpoint_checkpoint_every_makes_due() {
    let stands = |at: u64, size: u64| ckpt::Standing { at, size };
    assert!(
        !ckpt::due(100, stands(0, 0), 99) && ckpt::due(100, stands(0, 0), 100),
        "the first interval"
    );
    assert!(
        !ckpt::due(100, stands(1_000, 250), 1_249) && ckpt::due(100, stands(1_000, 250), 1_250),
        "an interval of the last checkpoint's own bytes"
    );
    assert!(!ckpt::due(1, stands(500, 0), 500), "nothing written since");

    let root = Scratch::new("ckpt-every");
    let path = root.path().join("log");
    let shape = plain(512);
    let every = 4_000u64;
    let mut log = open(&path, shape, ReadOpen::default(), Some(every)).unwrap();
    let mut written = Vec::new();
    for i in 0..600u64 {
        log.publish(
            1 + i % 3,
            i + 1,
            format!("/f/every/{}", i % 4),
            vec![1u8; 50],
        )
        .unwrap_or_else(|e| panic!("publish {i}: {e}"));
        let at = ckpt::header_of(&path, None).map_or(0, |h| h.len);
        assert_eq!(at, log.checkpoint.at, "the checkpoint the log counts from");
        let size = std::fs::metadata(ckpt_of(&path)).map_or(0, |m| m.len());
        if written.last().map(|&(at, _)| at) != Some(at) && at > 0 {
            // The file is the state's stream and a 12-byte header a frame.
            assert_eq!(
                size,
                log.checkpoint.size + 12,
                "the checkpoint's bytes at {at}"
            );
            written.push((at, size));
        }
    }
    assert!(
        written.len() >= 5,
        "too few checkpoints to judge: {written:?}"
    );
    let (mut last, mut last_size) = (0u64, 0u64);
    for &(at, size) in &written {
        let since = at - last;
        let due = every.max(last_size.saturating_sub(12));
        assert!(
            since >= due && since < due + 200,
            "a checkpoint at byte {at}, {since} after the last, where {due} made one due: \
             {written:?}"
        );
        (last, last_size) = (at, size);
    }
    assert!(
        last_size > every,
        "the state never outgrew the interval asked, so nothing stretched it: {written:?}"
    );
    // An unclean stop, reopened where the boot cannot be named, so the generation moves on
    // every host. The open takes the last checkpoint up, and leaves one of every record
    // bound to the identity it settled.
    let head = log.head().0;
    let before = log.identity.identity;
    drop(log);
    let mut opts = options(shape, ReadOpen::default());
    opts.checkpoint_every = Some(every);
    opts.boot = Boot::Unknown;
    let (mut log, counted) = counting(|| open_as(&path, shape, &opts, false).unwrap());
    assert_eq!(counted.taken, 1, "the open after the stop");
    assert_eq!(log.head().0, head, "the head after the stop");
    assert_ne!(
        log.identity.identity.generation, before.generation,
        "the unclean stop moved no generation"
    );
    let standing = ckpt::header_of(&path, None).expect("a checkpoint stands");
    assert_eq!(standing.count, head, "the checkpoint the open wrote");
    assert_eq!(
        standing.identity, log.identity.identity,
        "what the checkpoint is bound to"
    );
    assert_eq!(log.checkpoint.at, standing.len);
    log.close_clean().unwrap();
    drop(log);

    // No checkpoint: an open that keeps one writes it at its end, and the next scans nothing.
    without_checkpoint(&path);
    let (mut log, counted) =
        counting(|| open(&path, shape, ReadOpen::default(), Some(every)).unwrap());
    assert_eq!((counted.taken, counted.decoded.scanned as u64), (0, head));
    let standing = ckpt::header_of(&path, None).expect("the open wrote a checkpoint");
    assert_eq!((standing.count, standing.len), (head, log.durable_len));
    log.close_clean().unwrap();
    drop(log);
    let full = copy_log(&path, &root.path().join("full"));
    without_checkpoint(&full);
    let reference = opened(&full, shape, ReadOpen::default(), None);
    let copy = copy_log(&path, &root.path().join("copy"));
    let (said, counted) = counting(|| opened(&copy, shape, ReadOpen::default(), None));
    assert_eq!(
        (
            counted.taken,
            counted.decoded.scanned,
            counted.decoded.bound
        ),
        (1, 0, 1),
        "the open after the open that wrote the checkpoint"
    );
    assert_eq!(first_difference(&reference, &said), None);
}

/// Damage below a checkpoint is not the open's to find, but for the frames it reads again
/// for its resident window: an open from a checkpoint that fails there is judged again by
/// the full scan, and answers as the open with no checkpoint does.
#[test]
fn an_open_that_fails_from_a_checkpoint_is_judged_again_by_the_full_scan() {
    let root = Scratch::new("ckpt-retried");
    // The whole log stays resident: every frame below the checkpoint is read again.
    let shape = plain(16 << 20);
    let (path, _) = small(root.path(), shape);
    let header = ckpt::header_of(&path, None).expect("the checkpoint");
    let mut bytes = std::fs::read(&path).unwrap();
    let at = (header.newest_at / 2) as usize;
    bytes[at] ^= 0x04;
    std::fs::write(&path, &bytes).unwrap();
    let full = copy_log(&path, &root.path().join("full"));
    without_checkpoint(&full);
    let reference = opened(&full, shape, ReadOpen::default(), None);
    assert!(
        reference.first().is_some_and(|l| l.starts_with("refused")),
        "the full scan served a log with a flipped byte: {:?}",
        reference.first()
    );
    let copy = copy_log(&path, &root.path().join("copy"));
    let (said, counted) = counting(|| opened(&copy, shape, ReadOpen::default(), None));
    assert_eq!(
        (counted.taken, counted.retried),
        (0, 1),
        "the open from the checkpoint above the damage"
    );
    assert_eq!(first_difference(&reference, &said), None);
}

/// What takes no checkpoint: an empty log, a log with a batch staged (refused by name), an
/// open with no residency budget (it writes one when asked, and takes none up), and a
/// replica.
#[test]
fn what_takes_no_checkpoint() {
    let root = Scratch::new("ckpt-none");
    let path = root.path().join("log");
    let shape = plain(512);
    let mut log = open(&path, shape, ReadOpen::default(), None).unwrap();
    assert!(
        !log.checkpoint().unwrap(),
        "an empty log wrote a checkpoint"
    );
    log.stage_publish(1, 1, "/f/none/a".to_string(), vec![1u8; 8])
        .unwrap_or_else(|e| panic!("stage: {e:?}"));
    let staged = log.checkpoint().unwrap_err();
    assert_eq!(staged.kind(), io::ErrorKind::InvalidInput, "{staged}");
    log.commit_batch().unwrap();
    let mut next_seq = [1u64, 0, 0, 0, 0, 0, 0, 0];
    publish_mixed(&mut log, 99, &mut next_seq);
    assert!(log.checkpoint().unwrap());
    log.close_clean().unwrap();
    drop(log);

    // No residency budget: every record is decoded for the window, which is the scan.
    let all = plain(crate::tier::Tier::RESIDENT_ALL);
    let mut opts = options(all, ReadOpen::default());
    opts.resident_budget = None;
    let (mut log, counted) = counting(|| open_as(&path, all, &opts, false).unwrap());
    assert_eq!((counted.taken, counted.decoded.scanned), (0, 100));
    assert!(
        ckpt_of(&path).exists(),
        "an open that did not look removed the checkpoint"
    );
    log.close_clean().unwrap();
    drop(log);
    without_checkpoint(&path);
    opts.checkpoint_every = Some(1);
    let (mut log, counted) = counting(|| open_as(&path, all, &opts, false).unwrap());
    assert_eq!((counted.taken, counted.decoded.scanned), (0, 100));
    assert_eq!(
        ckpt::header_of(&path, None).map(|h| h.count),
        Some(100),
        "an open with no residency budget, asked for a checkpoint, wrote none"
    );
    log.close_clean().unwrap();
    drop(log);

    // A replica: the checkpoint goes at the open that finds the marker.
    let replica = copy_log(&path, &root.path().join("replica"));
    std::fs::write(replica_marker_path(&replica), b"replica\n").unwrap();
    let (log, counted) = counting(|| open(&replica, shape, ReadOpen::default(), Some(1)).unwrap());
    assert!(log.replica, "the marker made no replica");
    assert_eq!((counted.taken, counted.decoded.scanned), (0, 100));
    assert!(!ckpt_of(&replica).exists(), "a replica kept a checkpoint");
    assert_eq!(log.checkpoint_every, None, "a replica keeps checkpoints");
}
