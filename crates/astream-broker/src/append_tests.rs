// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! EVERY APPEND LANDS AT THE LOG'S END, WHATEVER A READ DID TO THE FILE CURSOR (aterm
//! F24). A cold read (`BrokerLog::record_arc`, at a residency budget of 0 every record
//! but the newest) reads by position, and on Windows that read leaves the file cursor at
//! the end of what it read. The appends write by position at the log's durable length
//! (`storage::write_all_at` says why), so neither an un-batched append after a cold read
//! nor a batch written with the log's lock released while a reader reads cold lands
//! anywhere but the end.
//!
//! The interleaving runs a reader on its own thread, handed the log after every step a
//! writer takes: after each un-batched append, after a batch's locked begin (so the
//! reader reads cold in the window where the writer writes with the lock released, as
//! the broker's writer thread does), after its unlocked write and after its locked end.
//! Each hand-off waits for the reader's pass, so the order is the same on every run, and
//! each pass reads every retained record and checks it is the record written there.
//! Then every record must read back, the file must be exactly the concatenation of its
//! records' frames, and a reopen must recover all of them.
//!
//! Two arms. A real file, where on Unix (`pread`) a read leaves the cursor alone and on
//! Windows (`seek_read`) moves it; and the simulated device, whose reads move its cursor
//! the way Windows' do on every OS. The NEGATIVE CONTROL writes every append at the
//! cursor instead ([`BrokerLog::cursor_appends`]), the append as it was before it was
//! positional: it fails the simulated arm on every OS, with un-batched appends and with
//! batches alone, and the real file on Windows.

use std::sync::mpsc;
use std::sync::{Arc, Mutex, MutexGuard};
use std::time::Duration;

use astream_wire::{Frame, Offset};

use crate::brecord::BrokerRecord;
use crate::store::{BrokerLog, Durability, OpenOptions};
use crate::test_scratch::Scratch;
use crate::SimDevice;

/// The one producer every record is published under, at a seq equal to its offset.
const PRODUCER: u64 = 7;
/// Rounds of one un-batched append and one batch of 1 to 4 records.
const ROUNDS: u64 = 24;
/// A hang detector, not a latency budget: the reader answers each hand-off at once.
const HANG: Duration = Duration::from_secs(60);

fn subject(i: u64) -> String {
    format!("/f/append/s{}", i % 5)
}

fn body(i: u64) -> Vec<u8> {
    // Bodies of varying length, so a frame written over another cannot read back as it.
    let n = 1 + (i as usize * 53) % 211;
    (0..n)
        .map(|k| (i as u8).wrapping_mul(29).wrapping_add(k as u8))
        .collect()
}

/// Whether `rec` is the record written at offset `i`.
fn check(rec: &BrokerRecord, i: u64) -> Result<(), String> {
    if rec.seq == Offset(i) && rec.subject == subject(i) && rec.body == body(i) {
        Ok(())
    } else {
        Err(format!(
            "offset {i} reads back as seq {} subject {:?} ({} body bytes)",
            rec.seq.0,
            rec.subject,
            rec.body.len()
        ))
    }
}

/// Where the log lives.
enum Arm {
    File(Scratch),
    Sim(SimDevice),
}

impl Arm {
    fn open(&self) -> std::io::Result<BrokerLog> {
        let opts = OpenOptions::new(Durability::Relaxed).with_resident_budget(0);
        match self {
            Arm::File(root) => {
                BrokerLog::open_opts(root.path().join("log"), opts, BrokerLog::prepare_nothing)
            }
            Arm::Sim(dev) => BrokerLog::open_sim(dev, opts),
        }
    }

    /// Every byte of the log file as stored.
    fn stored(&self) -> Vec<u8> {
        match self {
            Arm::File(root) => std::fs::read(root.path().join("log")).unwrap_or_default(),
            Arm::Sim(dev) => {
                let mut out = Vec::new();
                dev.sim().read_log(&mut out);
                out
            }
        }
    }
}

fn lock(log: &Mutex<BrokerLog>) -> MutexGuard<'_, BrokerLog> {
    log.lock().unwrap_or_else(|p| p.into_inner())
}

/// One reader pass: every retained record, each read back (cold but for the newest) and
/// checked.
fn read_all(log: &BrokerLog) -> Result<(), String> {
    let (base, head) = (log.base().0, log.head().0);
    for i in base..head {
        let index = usize::try_from(i - base).map_err(|e| e.to_string())?;
        let rec = log
            .record_arc(index)
            .ok_or_else(|| format!("offset {i} of {head} does not read back"))?;
        check(&rec, i)?;
    }
    Ok(())
}

/// The records the file holds, frame after frame from its first byte to its last.
fn frames(stored: &[u8]) -> Result<Vec<BrokerRecord>, String> {
    let mut at = 0usize;
    let mut out = Vec::new();
    while at < stored.len() {
        let rest = stored.get(at..).unwrap_or(&[]);
        let decoded = match Frame::decode(rest) {
            Ok(Some(d)) => d,
            other => {
                return Err(format!(
                    "no whole frame at byte {at} of {}: {other:?}",
                    stored.len()
                ))
            }
        };
        let (rec, _, _) = BrokerRecord::from_payload_marked_bt(&decoded.frame.payload)
            .ok_or_else(|| format!("the frame at byte {at} holds no record"))?;
        out.push(rec);
        at += decoded.consumed;
    }
    Ok(out)
}

/// The interleaving on `arm`, each round an un-batched append (when `unbatched`) and a
/// batch, its appends at the file cursor when `cursor_appends` (the negative control):
/// `Ok` with the number of records written when every check held.
fn interleave(arm: &Arm, unbatched: bool, cursor_appends: bool) -> Result<u64, String> {
    let mut log = arm.open().map_err(|e| format!("open: {e}"))?;
    log.cursor_appends = cursor_appends;
    let log = Arc::new(Mutex::new(log));

    let (go, go_rx) = mpsc::channel::<()>();
    let (done_tx, done) = mpsc::channel::<Result<(), String>>();
    let reader = {
        let log = Arc::clone(&log);
        std::thread::spawn(move || {
            for () in go_rx {
                let pass = read_all(&lock(&log));
                if done_tx.send(pass).is_err() {
                    return;
                }
            }
        })
    };
    let read = || -> Result<(), String> {
        go.send(()).map_err(|_| "the reader is gone".to_string())?;
        done.recv_timeout(HANG)
            .map_err(|e| format!("the reader did not answer: {e}"))?
    };

    let mut next = 0u64;
    let run = (|| -> Result<(), String> {
        for round in 0..ROUNDS {
            if unbatched {
                let (off, dup) = lock(&log)
                    .publish(PRODUCER, next, subject(next), body(next))
                    .map_err(|e| format!("append {next}: {e}"))?;
                if (off, dup) != (Offset(next), false) {
                    return Err(format!("append {next} landed at {} (dup {dup})", off.0));
                }
                next += 1;
                read()?;
            }

            let write = {
                let mut held = lock(&log);
                for _ in 0..=round % 4 {
                    held.stage_publish(PRODUCER, next, subject(next), body(next))
                        .map_err(|e| format!("stage {next}: {e:?}"))?;
                    next += 1;
                }
                match held.commit_begin().map_err(|e| format!("begin: {e}"))? {
                    crate::store::Begun::Write(w) => w,
                    crate::store::Begun::Empty(_) => return Err("an empty batch".into()),
                }
            };
            // The lock is free: the reader reads cold while the batch is unwritten,
            // then while it is written but not yet settled, as beside the writer thread.
            read()?;
            let mut write = write;
            let res = write.run();
            read()?;
            lock(&log)
                .commit_end(write, res)
                .map_err(|e| format!("batch ending at {next}: {e}"))?;
            read()?;
        }
        Ok(())
    })();
    drop(go);
    reader
        .join()
        .map_err(|_| "the reader panicked".to_string())?;
    run?;

    let log = Arc::try_unwrap(log)
        .map_err(|_| "the log is still shared".to_string())?
        .into_inner()
        .unwrap_or_else(|p| p.into_inner());
    if log.head() != Offset(next) {
        return Err(format!("head {} after {next} records", log.head().0));
    }
    if log.cold_reads() == 0 {
        return Err("no read was cold: the interleaving tested nothing".into());
    }
    read_all(&log)?;
    let durable = log.durable_len();
    drop(log);

    let stored = arm.stored();
    if stored.len() as u64 != durable {
        return Err(format!(
            "the file holds {} bytes, the log {durable}",
            stored.len()
        ));
    }
    let on_disk = frames(&stored)?;
    if on_disk.len() as u64 != next {
        return Err(format!("the file holds {} frames of {next}", on_disk.len()));
    }
    for (i, rec) in (0u64..).zip(&on_disk) {
        check(rec, i)?;
    }

    let reopened = arm.open().map_err(|e| format!("reopen: {e}"))?;
    if reopened.head() != Offset(next) {
        return Err(format!(
            "the reopen recovered {} of {next} records",
            reopened.head().0
        ));
    }
    read_all(&reopened)?;
    Ok(next)
}

#[test]
fn appends_land_at_the_log_end_between_cold_reads_on_a_real_file() {
    let arm = Arm::File(Scratch::new("append-file"));
    let written = interleave(&arm, true, false).unwrap();
    assert!(written > ROUNDS * 2, "{written} records");
}

#[test]
fn appends_land_at_the_log_end_between_cold_reads_on_a_device_whose_reads_move_its_cursor() {
    let arm = Arm::Sim(SimDevice::new(16));
    let written = interleave(&arm, true, false).unwrap();
    assert!(written > ROUNDS * 2, "{written} records");
}

#[test]
fn appends_at_the_cursor_fail_the_interleaving_where_a_read_moves_the_cursor() {
    // With un-batched appends the first one after a cold read is caught; with batches
    // alone, a batch written after a reader's pass.
    for unbatched in [true, false] {
        let sim = interleave(&Arm::Sim(SimDevice::new(16)), unbatched, true);
        assert!(
            sim.is_err(),
            "cursor appends (un-batched too: {unbatched}) on a device whose reads move its \
             cursor passed: {sim:?}"
        );
        // A real file's cursor moves under a positional read only on Windows
        // (`seek_read`); `pread` leaves it, so there the cursor append was safe and passes.
        let file = interleave(
            &Arm::File(Scratch::new("append-file-control")),
            unbatched,
            true,
        );
        assert_eq!(
            file.is_err(),
            cfg!(windows),
            "un-batched too: {unbatched}: {file:?}"
        );
    }
}
