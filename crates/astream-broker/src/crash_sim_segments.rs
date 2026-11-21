// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! THE CRASH SIMULATION OVER A SEGMENTED LOG'S ROLL AND CUT (`segments.rs`, aterm tracker
//! LT-A8): the power-loss law of the crash simulation, held where a segmented log adds what
//! a one-file log never does, which is files made and unlinked.
//!
//! # The model
//!
//! The directory's power-loss model (`power_loss.rs`), TRACED: every file's content survives
//! as of its last full flush (a segment's, the anchor's, each sidecar's), and of the name
//! changes since the last directory flush (a segment created at a roll, the base renamed in,
//! a segment unlinked, the intent removed) any PREFIX survives. After EVERY event the real
//! code makes (a creation, a rename, an unlink, a file's flush, a directory's flush) the
//! sweep keeps every directory a power loss then can leave, tagged with the records acked by
//! then; a process that stopped dead (what the kernel holds survives) is the directory as it
//! stands. The byte-level law inside one file (barriers, torn and short writes, rot) is the
//! simulated device's (`crash_sim.rs`, `sim_device.rs`): a segment is written exactly as a
//! one-file log is, and only a full flush of it ever reaches this model, so the sweep here
//! runs the Strict tier, whose every ack is one.
//!
//! # What is checked, on every image
//!
//! | id | property |
//! |----|----------|
//! | S1 | The open never refuses (P1). |
//! | S2 | The records it reads are byte-for-byte the first `k` written (P2), at least every one acked before the loss (P3). |
//! | S3 | A cut interrupted anywhere reads as the log before it or as the finished cut, never anything else: no acked record lost, none read twice, every `Last` row, binding, will and group commit as on that side; and the process that stopped dead reads the side its last durable step says. |
//! | S4 | What an interrupted cut leaves is cleared by the open: no intent, no staged state, no segment below the base. |
//! | S5 | A second open reads the same, and the log takes appends, rolls and cuts again. |
//!
//! NEGATIVE CONTROLS, each a planted break run once and restored (2026-11-19): a roll that
//! does not flush the directory after it creates the next segment fails
//! `the_power_loss_law_holds_over_segment_roll` ("a power loss #11, 5 acked: S2: 3 records
//! read, 5 acked": the new segment's name was lost with acked records in it); a cut that
//! unlinks the segments below the floor BEFORE the base names it fails both cut laws ("Base,
//! a power loss #5: S1: the open refused: ... no segment starts at the base 0"); a cut that
//! does not flush the active segment before its intent fails
//! `the_power_loss_law_holds_over_a_relaxed_cut_at_the_active_segment` ("Base, a power loss
//! #6: S3: the kept segment lost its records").

use crate::compact::{intent_path, staged_state_path, Seam, Step};
use crate::power_loss::{self, Image};
use crate::segments::{list, SegmentBytes};
use crate::segments_tests::{open_segmented, seed, snap, Fixture, Snap, SEGMENT};
use crate::store::{BrokerLog, Durability, OpenOptions};
use astream_wire::Offset;
use std::io;

/// Every image a traced arm kept, with the records acked when it could be left.
fn traced() -> Vec<(u64, Image)> {
    power_loss::disarm()
        .expect("the power-loss model was armed")
        .traced()
}

/// The open each image is tried with: Strict, with no segment size, which an open of a
/// segmented log reads from its anchor.
fn open(fx: &Fixture) -> io::Result<BrokerLog> {
    BrokerLog::open_opts(
        &fx.path,
        OpenOptions::new(Durability::Strict),
        BrokerLog::prepare_nothing,
    )
}

/// THE ROLL: a segmented Strict log written record by record and batch by batch across a
/// dozen rolls, a power loss after every event the writes, flushes, segment creations and
/// directory flushes make. Every image opens (S1), reads a prefix of what was written that
/// holds every acked record (S2), and takes an append and a reopen after it (S5).
#[test]
fn the_power_loss_law_holds_over_segment_roll() {
    let fx = Fixture::new("crash-seg-roll");
    power_loss::arm_traced(fx.dir());
    let mut log = open_segmented(&fx.path).unwrap();
    let mut written: Vec<(String, Vec<u8>)> = Vec::new();
    let mut acked = 0u64;
    let mut stood: Vec<(u64, Image)> = Vec::new();
    for i in 0..40u64 {
        let subject = format!("/a/r/{}", i % 5);
        if i % 4 == 3 {
            let second = format!("/a/r/b{i}");
            log.stage_publish(7, 2 * i, subject.clone(), format!("r{i}").into_bytes())
                .unwrap();
            log.stage_publish(7, 2 * i + 1, second.clone(), format!("s{i}").into_bytes())
                .unwrap();
            written.push((subject, format!("r{i}").into_bytes()));
            written.push((second, format!("s{i}").into_bytes()));
            log.commit_batch().unwrap();
            acked += 2;
        } else {
            log.publish(7, 2 * i, subject.clone(), format!("r{i}").into_bytes())
                .unwrap();
            written.push((subject, format!("r{i}").into_bytes()));
            acked += 1;
        }
        power_loss::note(acked);
        stood.push((acked, power_loss::capture(fx.dir())));
    }
    let rolled = list(&fx.path).unwrap().len();
    assert!(rolled >= 10, "the run rolls: {rolled} segments");
    drop(log);
    let lost = traced();
    println!(
        "crash_sim segments roll: {} power-loss images and {} process-crash images over {} \
         records in {rolled} segments",
        lost.len(),
        stood.len(),
        written.len()
    );
    assert!(lost.len() > written.len(), "every event left images");
    let cases = lost
        .into_iter()
        .map(|c| ("a power loss", c))
        .chain(stood.into_iter().map(|c| ("a process crash", c)));
    for (n, (how, (acked, image))) in cases.enumerate() {
        power_loss::apply(fx.dir(), &image);
        let at = format!("{how} #{n}, {acked} acked");
        let mut log = open(&fx).unwrap_or_else(|e| panic!("{at}: S1: the open refused: {e}"));
        let got: Vec<(String, Vec<u8>)> = log
            .read_from(Offset(0))
            .iter()
            .map(|r| (r.subject.clone(), r.body.clone()))
            .collect();
        assert_eq!(log.base(), Offset(0), "{at}");
        assert!(
            written.starts_with(&got),
            "{at}: S2: the records read are not what was written"
        );
        assert!(
            got.len() as u64 >= acked,
            "{at}: S2: {} records read, {acked} acked",
            got.len()
        );
        let head = log.head();
        log.publish(9, 1, "/a/r/after".into(), b"after".to_vec())
            .unwrap_or_else(|e| panic!("{at}: S5: the append after refused: {e}"));
        drop(log);
        let log = open(&fx).unwrap_or_else(|e| panic!("{at}: S5: the second open refused: {e}"));
        assert_eq!(log.head().0, head.0 + 1, "{at}: S5");
    }
}

/// The cut every case takes: to offset 13, which the seed's segments floor to a base below.
const CUT: u64 = 13;

/// The durable steps of a segmented cut, in order (`segments.rs`, "Cut").
const CUT_STEPS: [Step; 6] = [
    Step::State,
    Step::Intent,
    Step::Base,
    Step::StateInstalled,
    Step::Unlink,
    Step::IntentRemoved,
];

/// Whether the base (the switch) is durable once `step` is.
const fn switched(step: Step) -> bool {
    matches!(
        step,
        Step::Base | Step::StateInstalled | Step::Unlink | Step::IntentRemoved
    )
}

/// The seeded log as a reopen reads it before the cut, and after an uninterrupted one.
fn reference(carry: bool) -> (Snap, Snap) {
    let fx = Fixture::new("crash-seg-ref");
    let mut log = open_segmented(&fx.path).unwrap();
    seed(&mut log, carry);
    drop(log);
    let mut log = open(&fx).unwrap();
    let before = snap(&mut log);
    cut(&mut log, carry, CUT).unwrap();
    drop(log);
    let mut log = open(&fx).unwrap();
    let after = snap(&mut log);
    assert!(after.base > 0 && after.base <= CUT, "{after:?}");
    (before, after)
}

fn cut(log: &mut BrokerLog, carry: bool, min: u64) -> io::Result<u64> {
    if carry {
        log.retain_before_carrying_state(Offset(min))
    } else {
        log.retain_before(Offset(min))
    }
}

/// THE CUT: a crash after every durable step of a segmented cut, carrying state and not,
/// and at every event inside each, whether the process stopped dead or the power went (every
/// directory that can leave): S1, S3, S4 and S5.
fn cut_law(carry: bool) {
    let (before, after) = reference(carry);
    let mut images = 0usize;
    for step in CUT_STEPS {
        if !carry && matches!(step, Step::State | Step::StateInstalled) {
            continue;
        }
        let fx = Fixture::new("crash-seg-cut");
        let mut log = open_segmented(&fx.path).unwrap();
        seed(&mut log, carry);
        drop(log);
        let mut log = open(&fx).unwrap();
        log.arm_compact_seam(Seam {
            crash_after: Some(step),
            ..Seam::default()
        });
        power_loss::arm_traced(fx.dir());
        let err = cut(&mut log, carry, CUT).expect_err("the armed crash");
        assert!(
            err.to_string().contains("injected crash"),
            "{step:?}: {err}"
        );
        let lost = traced();
        drop(log);
        let stood = power_loss::capture(fx.dir());
        let exact = if switched(step) { &after } else { &before };
        images = images.saturating_add(lost.len()).saturating_add(1);
        let cases = std::iter::once(("a process crash", Some(exact), stood)).chain(
            lost.into_iter()
                .map(|(_, image)| ("a power loss", None, image)),
        );
        for (n, (how, want, image)) in cases.enumerate() {
            power_loss::apply(fx.dir(), &image);
            let at = format!("{step:?}, {how} #{n}");
            let mut log = open(&fx).unwrap_or_else(|e| panic!("{at}: S1: the open refused: {e}"));
            let got = snap(&mut log);
            match want {
                Some(want) => assert_eq!(&got, want, "{at}: S3"),
                None => assert!(
                    got == before || got == after,
                    "{at}: S3: neither the log before the cut nor after it: {got:?}"
                ),
            }
            drop(log);
            for p in [intent_path(&fx.path), staged_state_path(&fx.path)] {
                assert!(!p.exists(), "{at}: S4: left {}", p.display());
            }
            assert!(
                list(&fx.path).unwrap().iter().all(|&b| b >= got.base),
                "{at}: S4: a segment below the base {}",
                got.base
            );
            let mut log = open(&fx).unwrap_or_else(|e| panic!("{at}: S5: reopen refused: {e}"));
            assert_eq!(snap(&mut log), got, "{at}: S5: the second open");
            log.publish(7, 99, "/a/s/late".into(), b"late".to_vec())
                .unwrap();
            cut(&mut log, carry, 22).unwrap();
            let base = log.base().0;
            assert!(
                base > after.base && base <= 22,
                "{at}: S5: cuts again to {base}"
            );
            drop(log);
            let log = open(&fx).unwrap();
            assert_eq!((log.base().0, log.head().0), (base, 31), "{at}: S5");
        }
    }
    println!(
        "crash_sim segments cut (carry {carry}): {images} images over {} steps",
        CUT_STEPS.len()
    );
}

#[test]
fn the_power_loss_law_holds_over_a_carrying_segment_cut() {
    cut_law(true);
}

#[test]
fn the_power_loss_law_holds_over_a_plain_segment_cut() {
    cut_law(false);
}

/// A RELAXED log's cut at its ACTIVE segment, whose records no full flush covered (a Relaxed
/// ack is the page cache): a power loss at every event of the cut, crashed after each of its
/// durable steps, always opens (S1), on one side of the cut (S3: the base is the old one or
/// the active segment's, and a moved base keeps that segment's records, which the cut flushed
/// before its intent named them), and leaves nothing of the cut behind (S4).
#[test]
fn the_power_loss_law_holds_over_a_relaxed_cut_at_the_active_segment() {
    let relaxed =
        || OpenOptions::new(Durability::Relaxed).with_segment_bytes(SegmentBytes::exactly(SEGMENT));
    let mut images = 0usize;
    for step in [Step::Intent, Step::Base, Step::Unlink, Step::IntentRemoved] {
        let fx = Fixture::new("crash-seg-relaxed");
        power_loss::arm_traced(fx.dir());
        let mut log =
            BrokerLog::open_opts(&fx.path, relaxed(), BrokerLog::prepare_nothing).unwrap();
        seed(&mut log, false);
        let active = *list(&fx.path).unwrap().last().unwrap();
        power_loss::note(1);
        log.arm_compact_seam(Seam {
            crash_after: Some(step),
            ..Seam::default()
        });
        let err = log.retain_before(Offset(30)).expect_err("the armed crash");
        assert!(
            err.to_string().contains("injected crash"),
            "{step:?}: {err}"
        );
        let lost: Vec<Image> = traced()
            .into_iter()
            .filter(|(n, _)| *n == 1)
            .map(|(_, image)| image)
            .collect();
        drop(log);
        assert!(!lost.is_empty(), "{step:?}: the cut left images");
        images = images.saturating_add(lost.len());
        for (n, image) in lost.iter().enumerate() {
            power_loss::apply(fx.dir(), image);
            let at = format!("{step:?}, a power loss #{n}");
            let mut log = open(&fx).unwrap_or_else(|e| panic!("{at}: S1: the open refused: {e}"));
            let got = snap(&mut log);
            assert!(
                got.base == 0 || got.base == active,
                "{at}: S3: the base {} is neither side's",
                got.base
            );
            if got.base == active {
                assert!(
                    got.head > active,
                    "{at}: S3: the kept segment lost its records"
                );
            }
            drop(log);
            for p in [intent_path(&fx.path), staged_state_path(&fx.path)] {
                assert!(!p.exists(), "{at}: S4: left {}", p.display());
            }
            assert!(
                list(&fx.path).unwrap().iter().all(|&b| b >= got.base),
                "{at}: S4: a segment below the base {}",
                got.base
            );
        }
    }
    println!("crash_sim segments relaxed cut at the active segment: {images} images");
}
