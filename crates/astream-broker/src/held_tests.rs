// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! The held store's tests (`held.rs`), on real logs under hand clocks: R4's acceptance,
//! RAM bounded by the rules while one mail waits a week, a hold class past its bytes, an
//! age rule, the mail hold, a restart, a crash after every durable step (the held store's
//! own first, process crash and power loss, plaintext and sealed under anti-rollback), torn
//! and damaged held stores, the rewrite, the reads below a base, and every record's age
//! across restarts, a crash that loses stamped records, and a rewrite.
//!
//! Every clock is a hand clock handed to [`BrokerLog::retain_by_rules`]; nothing sleeps.
//!
//! NEGATIVE CONTROLS (each a planted break, scratch-reverted, that fails the test named): a
//! cut that is the minimum over every rule's floor
//! (`ram_follows_the_rules_while_one_unread_mail_waits_a_week`); a drop that raises no floor
//! (`a_hold_class_past_its_bytes_gives_up_its_oldest_and_tells_the_reader`); a cut that
//! carries nothing (`mail_is_held_until_its_reader_reads_it`,
//! `a_restart_reads_the_held_store_the_floors_and_the_rules_back`); frames of a compaction
//! that never landed applied at the open (`a_crash_after_any_durable_step_*`); a fetch
//! below the oldest that clamps (`r4_acceptance_*`); a class past its bytes cut back to
//! exactly them (`a_log_at_its_bounds_is_copied_a_bounded_share_of_what_it_takes`); and a
//! wake counted by the log's bytes, not each class's own
//! (`a_class_at_its_bytes_asks_for_nothing_while_another_class_takes_records`); and every
//! class reset to the base by a rules change (`a_rules_change_keeps_the_held_mail_readable`);
//! an open that restamps the retained suffix
//! (`an_age_rule_cuts_by_when_a_record_was_first_seen_across_restarts`); stamps read back
//! that are not cut to the head recovered, or cut in memory only
//! (`a_crash_that_loses_stamped_records_never_ages_the_ones_after_it`); a rewrite's
//! snapshot without the stamps (`a_rewritten_store_keeps_the_ticks_stamps`); a prune that
//! drops every stamp at or below the base
//! (`a_carried_cut_after_a_cut_to_the_head_ages_nothing_at_once`); and, for the
//! gap notice a tail below the base is owed (R4's addendum, A9), a count that skips its
//! checks (`a_tail_below_what_the_rules_gave_up_is_told_the_range_and_the_count`,
//! `a_cut_no_rules_planned_is_told_by_its_range_alone`), a planning that ledgers nothing
//! (`a_tail_below_what_the_rules_gave_up_is_told_the_range_and_the_count`), no count of
//! what was given up since the tail last looked
//! (`a_later_give_up_inside_a_told_range_is_told_again_and_counted_once`), a compaction no
//! rules planned that leaves the ledger whole or the floors where they were
//! (`a_cut_no_rules_planned_is_told_by_its_range_alone`), or that raises the spill in memory
//! only (`a_cut_no_rules_planned_is_told_after_a_restart`), a ledger that never drops
//! (`the_ledger_is_bounded_and_whole_only_above_what_it_dropped`), a range told again only
//! when it grows, and a ledger that takes a planning's give-ups as if it were whole below
//! them (`a_give_up_the_ledger_can_no_longer_count_is_told_by_its_range_again`), and a look
//! that moves the range told while it tells nothing
//! (`a_look_that_tells_nothing_leaves_the_range_still_owed`); and, for a fetch told of gaps
//! (BUS-1), one that refuses below the oldest as a reader not told is refused, and one that
//! reads below it whenever the page holds a record, at or above the oldest too
//! (`a_wide_fetch_reads_the_mail_retention_still_holds_below_its_oldest`), and one that
//! refuses a scan that ran out below the oldest having matched nothing
//! (`a_told_fetch_whose_scan_runs_out_below_the_oldest_reads_on_to_the_held_mail`).

use super::*;
use crate::compact::{intent_path, kept_path, staged_state_path, Meter, Seam, Step};
use crate::retention::record_bytes;
use crate::store::{BrokerLog, RetentionTick};
use crate::test_scratch::Scratch;
use crate::Rule;
use astream_wire::Offset;
use std::time::Duration;

const EV: &str = "/f/F/pub/n1/s1/ev";
const PRESENCE: &str = "/f/F/pub/n1/s1/presence";
const MAIL: &str = "/f/F/in/n1/from/a";
const MAIL2: &str = "/f/F/in/n2/from/a";
const INBOX: &str = "/f/F/cur/n1/node/inbox";
const BODY: &[u8] = b"0123456789abcdef";
const MINUTE: u64 = 60_000;
const HOUR: u64 = 60 * MINUTE;
const DAY: u64 = 24 * HOUR;
/// The hand clock's start (unix ms).
const T0: u64 = 1_800_000_000_000;

#[cfg(feature = "anti-rollback")]
const KEY: [u8; 32] = [0x5e; 32];

fn filter(f: &str) -> Filter {
    Filter::new(f).unwrap()
}

fn rec_of(subject: &str, body: &[u8]) -> BrokerRecord {
    BrokerRecord {
        seq: Offset(0),
        producer_id: 1,
        producer_seq: 1,
        subject: subject.to_string(),
        body: body.to_vec(),
        commit: None,
    }
}

/// The bytes one test record of `subject` takes ([`record_bytes`]).
fn rb(subject: &str) -> u64 {
    record_bytes(&rec_of(subject, BODY))
}

/// The bulk stream the prefix (by `ev_bytes`, `ev_age`), mail held until its node's inbox
/// group reads it (when `readers`) or for 7 days, within `mail_bytes`; presence by its last
/// value; the default rule by its last value.
fn rules(
    ev_bytes: Option<u64>,
    ev_age: Option<u64>,
    mail_bytes: Option<u64>,
    mail_age: u64,
    readers: bool,
) -> Retention {
    let mut ev = Rule::prefix("/f/F/pub/*/*/ev").unwrap();
    if let Some(b) = ev_bytes {
        ev = ev.max_bytes(b);
    }
    if let Some(a) = ev_age {
        ev = ev.max_age(Duration::from_millis(a));
    }
    let mut mail = Rule::hold("/f/F/in/>")
        .unwrap()
        .max_age(Duration::from_millis(mail_age));
    if let Some(b) = mail_bytes {
        mail = mail.max_bytes(b);
    }
    if readers {
        mail = mail.until_read("/f/{2}/cur/{4}/node/inbox").unwrap();
    }
    Retention::new(
        vec![
            ev,
            mail,
            Rule::hold("/f/F/pub/*/*/presence").unwrap().last_only(),
        ],
        Rule::default_hold(),
    )
    .unwrap()
}

/// One log in its own scratch directory, plaintext or sealed under anti-rollback.
struct Fx {
    root: Scratch,
    path: PathBuf,
    sealed: bool,
    /// The producer sequence the next publish takes.
    seq: u64,
}

impl Fx {
    fn new(tag: &str, sealed: bool) -> Fx {
        let root = Scratch::new(tag);
        let path = root.path().join("log");
        Fx {
            root,
            path,
            sealed,
            seq: 0,
        }
    }

    fn create(&self) -> BrokerLog {
        #[cfg(feature = "anti-rollback")]
        if self.sealed {
            return BrokerLog::open_encrypted_verified_init(&self.path, KEY).unwrap();
        }
        assert!(!self.sealed, "a sealed fixture needs anti-rollback");
        BrokerLog::open(&self.path).unwrap()
    }

    fn try_open(&self) -> io::Result<BrokerLog> {
        #[cfg(feature = "anti-rollback")]
        if self.sealed {
            return BrokerLog::open_encrypted_verified(&self.path, KEY);
        }
        BrokerLog::open(&self.path)
    }

    fn open(&self) -> BrokerLog {
        self.try_open().unwrap()
    }

    fn dir(&self) -> &Path {
        self.root.path()
    }

    /// Publish `subjects` as one batch; their offsets.
    fn batch(&mut self, log: &mut BrokerLog, subjects: &[&str]) -> Vec<u64> {
        let mut offs = Vec::new();
        for s in subjects {
            self.seq += 1;
            let (off, _) = log
                .stage_publish(1, self.seq, s.to_string(), BODY.to_vec())
                .unwrap();
            offs.push(off.0);
        }
        log.commit_batch().unwrap();
        offs
    }

    /// The compaction's and the held store's own files beside the log that are present.
    fn leftovers(&self) -> Vec<PathBuf> {
        [
            intent_path(&self.path),
            kept_path(&self.path),
            staged_state_path(&self.path),
            held_tmp_path(&self.path),
        ]
        .into_iter()
        .filter(|p| std::fs::symlink_metadata(p).is_ok())
        .collect()
    }
}

/// Every retained record's bytes and every held one's: what the log keeps in RAM.
fn ram(log: &BrokerLog) -> u64 {
    let retained: u64 = log
        .read_from(Offset(0))
        .iter()
        .map(|r| record_bytes(r))
        .sum();
    retained + log.stats().held_bytes
}

/// The offsets a read of `f` from the start returns (it starts at the filter's oldest).
fn read(log: &BrokerLog, f: &str) -> Vec<u64> {
    let (page, _) = log.fetch(0, &filter(f), 10_000, 100_000, log.head().0);
    page.iter().map(|r| r.seq.0).collect()
}

/// `Last` of `f` at the log's head, one bounded step, through an owned view as every
/// reader of `Last` now takes one (the head published visible first).
fn last_of(log: &mut BrokerLog, f: &Filter, max: usize, scan_max: usize) -> Vec<Arc<BrokerRecord>> {
    let head = log.head().0;
    drop(log.publish_last_visible(head).unwrap());
    let mut view = log.last_view_at(head).unwrap();
    let (page, _) = log
        .last_matching(f, "", max, scan_max, &mut view)
        .unwrap()
        .into_page()
        .expect("the fixture fits one bounded step");
    page
}

/// R4's ACCEPTANCE: retention of the bulk stream set to 100 records, 250 published beside a
/// presence record at offset 3 (251 records, offsets 0 to 250, in batches of ten): the
/// oldest the stream reads is 151 — the record itself, not rounded to its batch (150 to 159):
/// offsets are absolute and an open scans a log that starts inside a batch — a `Fetch` from
/// 5 is told `retained-from=151` (NC: one that clamps), and `Last` of the presence subject
/// still answers its record at 3, across a restart too.
#[test]
fn r4_acceptance_retaining_100_of_250_reads_oldest_151_and_last_still_answers() {
    let mut fx = Fx::new("held-r4", false);
    let mut log = fx.create();
    log.set_retention(rules(Some(100 * rb(EV)), None, None, 7 * DAY, true))
        .unwrap();
    let subjects: Vec<&str> = (0..=250u64)
        .map(|i| if i == 3 { PRESENCE } else { EV })
        .collect();
    for chunk in subjects.chunks(10) {
        fx.batch(&mut log, chunk);
    }
    assert_eq!(log.head(), Offset(251));
    let tick = log.retain_by_rules(T0).unwrap();
    assert_eq!((tick.base_before, tick.base, tick.dropped), (0, 151, 151));
    let ev = filter("/f/F/pub/*/*/ev");
    let presence = filter("/f/F/pub/*/*/presence");
    for pass in ["live", "after a restart"] {
        assert_eq!(log.oldest(&ev), Offset(151), "{pass}");
        let head = log.head().0;
        match log.fetch_checked(5, &ev, 10, 1000, head) {
            Err(o) => assert_eq!(o, Offset(151), "{pass}"),
            Ok((page, _)) => panic!("{pass}: a fetch from 5 answered {} records", page.len()),
        }
        let (page, _) = log.fetch_checked(151, &ev, 1, 1000, head).unwrap();
        assert_eq!(page[0].seq, Offset(151), "{pass}");
        let last = last_of(&mut log, &presence, 10, 100);
        assert_eq!(last.len(), 1, "{pass}");
        assert_eq!(
            last[0].seq,
            Offset(3),
            "{pass}: Last of the presence subject"
        );
        drop(log);
        log = fx.open();
    }
}

/// RAM FOLLOWS THE RULES: one unread mail at offset 1 waits a week while the bulk stream
/// floods past its bytes, a batch an hour, a tick an hour on the hand clock. After every
/// tick the retained and held bytes are within the sum of the rules' bytes (plus what the
/// log took since the planning: nothing, here), and the mail still reads at offset 1 until
/// its 7 days are up; then it is given up, told (`lost`, and a read below it is refused with
/// its floor), and gone. NC: a cut that is the minimum over every rule's floor keeps every
/// record since the mail, past the bound.
#[test]
fn ram_follows_the_rules_while_one_unread_mail_waits_a_week() {
    let mut fx = Fx::new("held-ram", false);
    let mut log = fx.create();
    let (ev_max, mail_max) = (40 * rb(EV), 4 * rb(MAIL));
    log.set_retention(rules(Some(ev_max), None, Some(mail_max), 7 * DAY, true))
        .unwrap();
    assert_eq!(fx.batch(&mut log, &[EV, MAIL]), vec![0, 1]);
    let batch = [EV; 10];
    let mut told = false;
    for hour in 0..(7 * 24 + 3) {
        fx.batch(&mut log, &batch);
        let now = T0 + hour * HOUR;
        let tick = log.retain_by_rules(now).unwrap();
        assert!(
            ram(&log) <= ev_max + mail_max,
            "hour {hour}: {} bytes in RAM, the rules allow {}",
            ram(&log),
            ev_max + mail_max
        );
        if now - T0 <= 7 * DAY {
            assert_eq!(
                read(&log, "/f/F/in/>"),
                vec![1],
                "hour {hour}: the mail reads"
            );
        } else {
            if !tick.lost.is_empty() {
                assert_eq!(tick.lost, vec![(MAIL.to_string(), 1)], "hour {hour}");
                told = true;
            }
            assert!(
                read(&log, "/f/F/in/>").is_empty(),
                "hour {hour}: the mail is gone"
            );
            let head = log.head().0;
            assert_eq!(
                log.fetch_checked(0, &filter("/f/F/in/n1/>"), 10, 100, head)
                    .map(|(p, n)| (p.len(), n)),
                Err(Offset(2)),
                "hour {hour}: a read below it is told"
            );
        }
    }
    assert!(told, "the mail's drop was told once");
    assert!(log.base().0 > 1, "the cut went past the mail");
}

/// A LOG AT ITS BOUNDS IS COPIED A BOUNDED SHARE OF WHAT IT TAKES: the bulk stream at its 20
/// records' bytes takes 200 more, one a batch, each batch ticked when the log is due one (as
/// the broker's writer asks). Every cut gives up a quarter of the class, so the bytes the
/// compactions copy stay within four times the bytes the log took, and the class within its
/// bytes after every tick. NC: a class cut back to exactly its bytes is due a cut, which
/// copies the whole kept log, for every batch: about twenty times what the log took.
#[test]
fn a_log_at_its_bounds_is_copied_a_bounded_share_of_what_it_takes() {
    let mut fx = Fx::new("held-steady", false);
    let mut log = fx.create();
    let max = 20 * rb(EV);
    log.set_retention(rules(Some(max), None, None, 7 * DAY, true))
        .unwrap();
    for _ in 0..20 {
        fx.batch(&mut log, &[EV]);
    }
    let meter = Arc::new(Meter::default());
    log.arm_compact_seam(Seam {
        meter: Some(Arc::clone(&meter)),
        ..Seam::default()
    });
    let (mut took, mut ticks) = (0u64, 0u64);
    for i in 0..200u64 {
        let before = log.durable_len();
        fx.batch(&mut log, &[EV]);
        took += log.durable_len() - before;
        if log.retention_due() {
            log.retain_by_rules(T0 + i).unwrap();
            ticks += 1;
        }
        assert!(ram(&log) <= max + rb(EV), "batch {i}: {} bytes", ram(&log));
    }
    let copied: u64 = meter.flushes.lock().unwrap().iter().sum();
    assert!(
        log.base().0 >= 200,
        "PRECONDITION: the stream was cut ({ticks} ticks)"
    );
    assert!(
        copied <= 4 * took,
        "{copied} bytes copied for {took} taken, in {ticks} ticks"
    );
}

/// A CLASS AT ITS BYTES ASKS FOR NOTHING WHILE ANOTHER CLASS TAKES RECORDS: the mail class at
/// exactly its three mails' bytes, the bulk stream far from its own, fifty stream batches
/// leave the log due no tick; the next mail does. NC: a wake counted by the log's bytes, the
/// tightest class's room against every record, is due a tick, which plans the whole log,
/// after the first stream batch and every one after it.
#[test]
fn a_class_at_its_bytes_asks_for_nothing_while_another_class_takes_records() {
    let mut fx = Fx::new("held-quiet", false);
    let mut log = fx.create();
    log.set_retention(rules(
        Some(1000 * rb(EV)),
        None,
        Some(3 * rb(MAIL)),
        7 * DAY,
        false,
    ))
    .unwrap();
    fx.batch(&mut log, &[MAIL, MAIL, MAIL]);
    assert!(log.retention_due(), "before the first planning, any record");
    assert_eq!(log.retain_by_rules(T0).unwrap().base, 0);
    assert!(!log.retention_due(), "planned");
    for i in 0..50 {
        fx.batch(&mut log, &[EV]);
        assert!(!log.retention_due(), "stream batch {i}");
    }
    fx.batch(&mut log, &[MAIL]);
    assert!(log.retention_due(), "the mail class is past its bytes");
}

/// A HOLD CLASS PAST ITS BYTES GIVES UP ITS OLDEST, AND TELLS: five mails below the cut, the
/// class's bytes three mails'; the two oldest are given up (logged, counted in `lost`), and a
/// read of the mail from the start is refused `retained-from` the third (NC: a drop that
/// raises no floor reads the three silently), which reads on, across a restart too.
#[test]
fn a_hold_class_past_its_bytes_gives_up_its_oldest_and_tells_the_reader() {
    let mut fx = Fx::new("held-bytes", false);
    let mut log = fx.create();
    log.set_retention(rules(
        Some(2 * rb(EV)),
        None,
        Some(3 * rb(MAIL)),
        7 * DAY,
        false,
    ))
    .unwrap();
    fx.batch(&mut log, &[MAIL, MAIL, MAIL, MAIL, MAIL, EV, EV, EV]);
    let tick = log.retain_by_rules(T0).unwrap();
    assert_eq!(tick.base, 6);
    assert_eq!(tick.carried, 3);
    assert_eq!(tick.lost, vec![(MAIL.to_string(), 2)]);
    let mail = filter("/f/F/in/>");
    for pass in ["live", "after a restart"] {
        let head = log.head().0;
        assert_eq!(
            log.fetch_checked(0, &mail, 10, 100, head)
                .map(|(p, _)| p.len()),
            Err(Offset(2)),
            "{pass}: told where the class's records start"
        );
        let (page, next) = log.fetch_checked(2, &mail, 10, 100, head).unwrap();
        assert_eq!(
            page.iter().map(|r| r.seq.0).collect::<Vec<_>>(),
            vec![2, 3, 4],
            "{pass}"
        );
        assert_eq!(
            next, 8,
            "{pass}: the scan went on through the retained suffix"
        );
        assert_eq!(log.stats().held_records, 3, "{pass}");
        drop(log);
        log = fx.open();
    }
}

/// A CUT A CALLER ASKS FOR BETWEEN TICKS PLANS ON THE LAST TICK'S CLOCK, NEVER AT 0: a tick
/// whose cut reaches the head leaves its stamp (`retention::prune_stamps` keeps the newest),
/// so the mail that lands after it and that `retain_before_carrying_state` carries is
/// stamped at that tick's time, and the next tick, a minute on, keeps it and tells no loss.
/// NC: a prune that drops every stamp at or below the base leaves none; the carried cut then
/// stamps the mail at 0, and the next tick gives it up as a week old (aterm sim item B05).
#[test]
fn a_carried_cut_after_a_cut_to_the_head_ages_nothing_at_once() {
    let mut fx = Fx::new("held-carried-clock", false);
    let mut log = fx.create();
    log.set_retention(rules(None, Some(HOUR), None, 7 * DAY, false))
        .unwrap();
    fx.batch(&mut log, &[EV, EV]);
    assert_eq!(
        log.retain_by_rules(T0).unwrap().base,
        0,
        "nothing is an hour old"
    );
    assert_eq!(
        log.retain_by_rules(T0 + 2 * HOUR).unwrap().base,
        2,
        "the stream is past its hour: the cut reaches the head"
    );
    fx.batch(&mut log, &[MAIL, EV]);
    log.retain_before_carrying_state(Offset(4)).unwrap();
    assert_eq!(read(&log, "/f/F/in/>"), vec![2], "the cut carries the mail");
    let tick = log.retain_by_rules(T0 + 2 * HOUR + MINUTE).unwrap();
    assert!(
        tick.lost.is_empty(),
        "nothing is a week old: {:?}",
        tick.lost
    );
    assert_eq!(read(&log, "/f/F/in/>"), vec![2], "the mail is still held");
}

/// AN AGE RULE under the hand clock: the bulk stream keeps an hour, mail a day. Nothing is
/// cut before its age; at an hour and a minute the records the first tick stamped go; at a
/// day and two minutes the rest go, and the mail the cut carried is given up by its age and
/// told.
#[test]
fn an_age_rule_cuts_by_the_hand_clock() {
    let mut fx = Fx::new("held-age", false);
    let mut log = fx.create();
    log.set_retention(rules(None, Some(HOUR), None, DAY, false))
        .unwrap();
    fx.batch(&mut log, &[EV, EV, MAIL]);
    assert_eq!(
        log.retain_by_rules(T0).unwrap().base,
        0,
        "nothing is an hour old"
    );
    fx.batch(&mut log, &[EV, EV]);
    assert_eq!(log.retain_by_rules(T0 + 30 * MINUTE).unwrap().base, 0);
    let tick = log.retain_by_rules(T0 + HOUR + MINUTE).unwrap();
    assert_eq!(
        tick.base, 2,
        "the first tick's ev records are past the hour"
    );
    assert_eq!(
        read(&log, "/f/F/in/>"),
        vec![2],
        "the mail is retained above the cut"
    );
    let tick = log.retain_by_rules(T0 + DAY + 2 * MINUTE).unwrap();
    assert_eq!(tick.base, 5, "every ev record is past the hour");
    assert_eq!(
        tick.lost,
        vec![(MAIL.to_string(), 1)],
        "the mail is a day old"
    );
    let head = log.head().0;
    assert_eq!(
        log.fetch_checked(0, &filter("/f/F/in/>"), 10, 100, head)
            .map(|(p, _)| p.len()),
        Err(Offset(3))
    );
}

/// THE MAIL HOLD: an in/ mail below the cut is carried while its node's inbox group has not
/// read it (it reads at its own offset, below the base), and released once the group's
/// commit passes it — not told as lost: its reader has it. NC: a cut that carries nothing
/// drops the unread mail.
#[test]
fn mail_is_held_until_its_reader_reads_it() {
    let mut fx = Fx::new("held-mail", false);
    let mut log = fx.create();
    log.set_retention(rules(Some(rb(EV)), None, None, 7 * DAY, true))
        .unwrap();
    fx.batch(&mut log, &[EV, MAIL, MAIL2, EV, EV]);
    let tick = log.retain_by_rules(T0).unwrap();
    assert_eq!((tick.base, tick.carried), (4, 2));
    assert_eq!(read(&log, "/f/F/in/>"), vec![1, 2], "the unread mail reads");
    assert_eq!(log.oldest(&filter("/f/F/in/>")), Offset(0));
    log.commit(INBOX.into(), 1).unwrap();
    let tick = log.retain_by_rules(T0 + MINUTE).unwrap();
    assert_eq!(tick.released, 1, "n1's reader read its mail");
    assert!(tick.lost.is_empty(), "a read mail is not lost");
    assert_eq!(read(&log, "/f/F/in/>"), vec![2], "n2's is still held");
    assert_eq!(log.oldest(&filter("/f/F/in/n1/>")), Offset(2));
    assert_eq!(log.oldest(&filter("/f/F/in/n2/>")), Offset(0));
}

/// A WIDE FETCH READS THE MAIL RETENTION STILL HOLDS BELOW ITS OLDEST (BUS-1; R4's addendum
/// A9 on the fetch path): n2's mail is published before n1's, n1's inbox group reads its own,
/// and the tick releases it. The mail filter's oldest is then n1's floor, 3, the greatest of
/// its subjects' floors, above n2's unread mail at 1 (n2's own filter is whole from 0). A
/// reader that did not ask for notices is refused below 3, as before (`fetch_checked`). A
/// reader told of gaps reads from 0 and from 1 and gets n2's held mail, told `..3` with the
/// one record given up (n1's, read) counted; from 2, where the filter holds nothing below 3,
/// it is refused 3; from 3 it reads on with nothing told. `/f/F/>`, whose oldest is the base
/// (it reaches the prefix rule), reads n2's mail held below the base and the stream's record
/// at 4, told `0..4` with no count (the prefix rule's records go as a range). Once n1 has
/// another mail above the cut, a read from 2 is still refused 3: what it finds is at or above
/// the oldest, so nothing of the filter is held in `2..3`. NC: a `fetch_told` that refuses
/// below the oldest, as `fetch_checked` does, reads none of it; one that takes any record on
/// the page for a held one (`Some(_) => true`) reads n1's later mail from 2, told `2..3`.
#[test]
fn a_wide_fetch_reads_the_mail_retention_still_holds_below_its_oldest() {
    let mut fx = Fx::new("held-wide-fetch", false);
    let mut log = fx.create();
    log.set_retention(rules(Some(rb(EV)), None, None, 7 * DAY, true))
        .unwrap();
    fx.batch(&mut log, &[EV, MAIL2, MAIL, EV, EV]);
    let tick = log.retain_by_rules(T0).unwrap();
    assert_eq!((tick.base, tick.carried), (4, 2));
    log.commit(INBOX.into(), 2).unwrap();
    let tick = log.retain_by_rules(T0 + MINUTE).unwrap();
    assert_eq!(tick.released, 1, "n1's reader read its mail");
    assert!(tick.lost.is_empty(), "a read mail is not lost");
    let mails = filter("/f/F/in/>");
    let all = filter("/f/F/>");
    assert_eq!(log.oldest(&mails), Offset(3), "n1's floor, the greatest");
    assert_eq!(log.oldest(&filter("/f/F/in/n2/>")), Offset(0));
    assert_eq!(
        log.oldest(&all),
        Offset(4),
        "the base: it reaches the prefix rule"
    );
    let head = log.head().0;
    let told = |from: u64, f: &Filter| {
        log.fetch_told(from, f, 10, 100, head)
            .map(|(page, _, gap)| {
                let offs: Vec<u64> = page.iter().map(|r| r.seq.0).collect();
                (offs, gap)
            })
    };
    let gap = |from, to, records| Some(crate::proto::Gap { from, to, records });
    assert_eq!(
        log.fetch_checked(0, &mails, 10, 100, head)
            .map(|(p, _)| p.len()),
        Err(Offset(3)),
        "a reader not told is refused, as before"
    );
    assert_eq!(told(0, &mails), Ok((vec![1], gap(0, 3, Some(1)))));
    assert_eq!(told(1, &mails), Ok((vec![1], gap(1, 3, Some(1)))));
    assert_eq!(
        told(2, &mails),
        Err(Offset(3)),
        "nothing of it held in 2..3"
    );
    assert_eq!(told(3, &mails), Ok((vec![], None)));
    assert_eq!(told(0, &all), Ok((vec![1, 4], gap(0, 4, None))));

    fx.batch(&mut log, &[MAIL]);
    let head = log.head().0;
    let told = |from: u64| {
        log.fetch_told(from, &mails, 10, 100, head)
            .map(|(page, _, gap)| (page.iter().map(|r| r.seq.0).collect::<Vec<_>>(), gap))
    };
    assert_eq!(
        log.oldest(&mails),
        Offset(3),
        "the later mail is above the cut"
    );
    assert_eq!(
        told(2),
        Err(Offset(3)),
        "what the read finds is at or above the oldest: nothing held in 2..3"
    );
    assert_eq!(
        told(0),
        Ok((vec![1, 6], gap(0, 3, Some(1)))),
        "n1's group commit is at 5"
    );
}

/// A TOLD FETCH WHOSE SCAN RUNS OUT BELOW THE OLDEST READS ON TO THE HELD MAIL (BUS-1): the
/// page's own bounded scan decides whether the filter holds anything below its oldest, and a
/// scan that ends there having matched nothing cannot say. n2's mail from b, held below the
/// base and not of the filter (`/f/F/in/*/from/a`), comes before n2's mail from a; with a
/// scan of one record a told read of the filter from 0 scans n2's mail from b alone. It is
/// answered as holding: an empty page, its `next` below the oldest (n1's floor, 4), told
/// `0..4` with n1's read mail counted; the read on from that `next` reaches n2's held mail
/// from a, told the rest of the range again. NC: a `fetch_told` that refuses a scan that ran
/// out (`None => false`) refuses the read from 0, and a reader that follows the refusal
/// skips n2's mail.
#[test]
fn a_told_fetch_whose_scan_runs_out_below_the_oldest_reads_on_to_the_held_mail() {
    const FROM_B: &str = "/f/F/in/n2/from/b";
    let mut fx = Fx::new("held-told-scan", false);
    let mut log = fx.create();
    log.set_retention(rules(Some(rb(EV)), None, None, 7 * DAY, true))
        .unwrap();
    fx.batch(&mut log, &[EV, FROM_B, MAIL2, MAIL, EV, EV]);
    let tick = log.retain_by_rules(T0).unwrap();
    assert_eq!((tick.base, tick.carried), (5, 3), "the three mails");
    log.commit(INBOX.into(), 3).unwrap();
    let tick = log.retain_by_rules(T0 + MINUTE).unwrap();
    assert_eq!(tick.released, 1, "n1's reader read its mail");
    let mails = filter("/f/F/in/*/from/a");
    assert_eq!(log.oldest(&mails), Offset(4), "n1's floor");
    let head = log.head().0;
    let told = |from: u64| {
        log.fetch_told(from, &mails, 10, 1, head)
            .map(|(page, next, gap)| {
                let offs: Vec<u64> = page.iter().map(|r| r.seq.0).collect();
                (offs, next, gap)
            })
    };
    let gap = |from, to, records| Some(crate::proto::Gap { from, to, records });
    assert_eq!(
        told(0),
        Ok((vec![], 2, gap(0, 4, Some(1)))),
        "the scan ran out on n2's mail from b: answered as holding"
    );
    assert_eq!(
        told(2),
        Ok((vec![2], 5, gap(2, 4, Some(1)))),
        "the read on reaches n2's held mail"
    );
}

/// A RESTART reads back the held store, its floors, its rules and the carried state: the
/// mail held below the base reads at its offset, the floor still refuses a read below it,
/// `Last` answers, and the same rules set again keep the store whole and tick on. NC: a cut
/// that carries nothing leaves no mail to read back.
/// `r` with its mail rule (`/f/F/in/>`) forgetting (`Rule::forgetting`), the rest as they are.
fn forgetting_mail(r: &Retention) -> Retention {
    let rules = r
        .rules()
        .iter()
        .map(|rule| match rule.filter() {
            Some("/f/F/in/>") => rule.clone().forgetting(),
            _ => rule.clone(),
        })
        .collect();
    Retention::new(rules, r.default_rule().clone()).unwrap()
}

/// The subjects `Last` answers of `f`, in its order.
fn last_subjects(log: &mut BrokerLog, f: &str) -> Vec<String> {
    last_of(log, &filter(f), 64, 1_000)
        .iter()
        .map(|r| r.subject.clone())
        .collect()
}

/// A FORGETTING RULE LETS A LANE GO once retention has given up every record of it, live and
/// across reopens, on a log's own tick (`BrokerLog::retain_by_rules`, no writer thread, so
/// every count is the tick's). Four mail lanes and a presence row, all producer 1's, then the
/// bulk stream past its bytes, so the tick's cut passes every one: n1's mail its inbox read
/// (given up at the cut), n2's unread (held), n3's read but the target of producer 7's
/// pending will (registered before the cut, carried by it), n4's read once and then
/// written again above the cut. The tick forgets n1's lane alone: `RetentionTick::forgotten`
/// is 1, `Last` of the mail no longer answers it, producer 1's distinct subjects are one
/// fewer. Once n2's inbox reads its mail, the next tick gives it up and forgets that lane too.
/// The will's lane, the rewritten lane and the presence row stay, charged. A reopen reads
/// the same `Last` and the same count (the marked retires replay over the rows the cut
/// carried), and so does one after a later cut that passes the retire records themselves
/// (the carried charges drop the forgotten lanes), where a tick forgets nothing more.
///
/// LIVE CONTROL (the same run, the rule not forgetting): every tick forgets nothing, every
/// lane stays in `Last` and the count never falls, across both reopens.
#[test]
fn a_forgetting_rule_lets_a_lane_go_once_retention_gave_up_all_its_records() {
    const MAIL3: &str = "/f/F/in/n3/from/a";
    const MAIL4: &str = "/f/F/in/n4/from/a";
    for forget in [true, false] {
        let what = format!("forget {forget}");
        let mut fx = Fx::new("held-forget", false);
        let mut log = fx.create();
        let plain = rules(Some(4 * rb(EV)), None, None, 7 * DAY, true);
        let r = if forget {
            forgetting_mail(&plain)
        } else {
            plain
        };
        log.set_retention(r).unwrap();
        fx.batch(&mut log, &[MAIL, MAIL2, MAIL3, MAIL4, PRESENCE]);
        let will = crate::store::WillRecord {
            producer_id: 7,
            producer_seq: crate::store::will_seq(1).unwrap(),
            subject: MAIL3.to_string(),
            body: b"gone".to_vec(),
        };
        log.stage_will_register(&will).unwrap();
        log.commit_batch().unwrap();
        for (group, upto) in [
            (INBOX, 0),
            ("/f/F/cur/n3/node/inbox", 2),
            ("/f/F/cur/n4/node/inbox", 3),
        ] {
            log.commit(group.into(), upto).unwrap();
        }
        fx.batch(&mut log, &[EV; 8]);
        let mail4_again = fx.batch(&mut log, &[MAIL4])[0];
        let all = log.subjects_per_producer(1);
        assert_eq!(all, 6, "{what}: four lanes, presence and the stream");
        let tick = log.retain_by_rules(T0).unwrap();
        assert!(tick.base > 9, "{what}: the cut passes every lane: {tick:?}");
        assert!(tick.base <= mail4_again, "{what}: {tick:?}");
        assert_eq!(
            read(&log, "/f/F/in/n2/>"),
            vec![1],
            "{what}: n2's unread is held"
        );
        let lanes = |log: &mut BrokerLog| last_subjects(log, "/f/F/in/>");
        let every = vec![MAIL, MAIL2, MAIL3, MAIL4];
        let (want, count) = if forget {
            assert_eq!(tick.forgotten, 1, "{what}: n1's lane alone: {tick:?}");
            (vec![MAIL2, MAIL3, MAIL4], all - 1)
        } else {
            assert_eq!(tick.forgotten, 0, "{what}: {tick:?}");
            (every.clone(), all)
        };
        assert_eq!(lanes(&mut log), want, "{what}");
        assert_eq!(log.subjects_per_producer(1), count, "{what}");

        log.commit("/f/F/cur/n2/node/inbox".into(), 1).unwrap();
        let tick = log.retain_by_rules(T0 + MINUTE).unwrap();
        assert_eq!(tick.released, 1, "{what}: n2's inbox read its mail");
        let (want, count) = if forget {
            assert_eq!(tick.forgotten, 1, "{what}: n2's lane, once its mail went");
            (vec![MAIL3, MAIL4], all - 2)
        } else {
            assert_eq!(tick.forgotten, 0, "{what}");
            (every, all)
        };
        assert_eq!(lanes(&mut log), want, "{what}");
        assert_eq!(log.subjects_per_producer(1), count, "{what}");
        assert_eq!(
            last_subjects(&mut log, "/f/F/pub/*/*/presence"),
            vec![PRESENCE],
            "{what}: the presence row stays"
        );

        drop(log);
        let mut log = fx.open();
        let back = log.retention().unwrap().clone();
        assert_eq!(
            back.rules()[1].forgets(),
            forget,
            "{what}: the held store's rules frame reads the rule back"
        );
        log.set_retention(back).unwrap();
        assert_eq!(lanes(&mut log), want, "{what}: after a reopen");
        assert_eq!(
            log.subjects_per_producer(1),
            count,
            "{what}: after a reopen"
        );
        // A later cut past the retire records the forgets appended, then a reopen: the
        // carried charges no longer hold the forgotten lanes.
        let head = log.head().0;
        fx.batch(&mut log, &[EV; 8]);
        let tick = log.retain_by_rules(T0 + 2 * MINUTE).unwrap();
        assert!(tick.base > head, "{what}: past the retires: {tick:?}");
        assert_eq!(
            tick.forgotten, 0,
            "{what}: nothing more to forget: {tick:?}"
        );
        drop(log);
        let mut log = fx.open();
        assert_eq!(
            lanes(&mut log),
            want,
            "{what}: after a cut past the retires"
        );
        assert_eq!(log.subjects_per_producer(1), count, "{what}: and its count");
    }
}

#[test]
fn a_restart_reads_the_held_store_the_floors_and_the_rules_back() {
    let mut fx = Fx::new("held-restart", false);
    let mut log = fx.create();
    let r = rules(Some(rb(EV)), None, Some(3 * rb(MAIL)), 7 * DAY, false);
    log.set_retention(r.clone()).unwrap();
    fx.batch(&mut log, &[MAIL, PRESENCE, MAIL, MAIL, MAIL, EV, EV]);
    let tick = log.retain_by_rules(T0).unwrap();
    assert_eq!((tick.base, tick.carried, tick.lost.len()), (6, 3, 1));
    drop(log);
    let mut log = fx.open();
    assert_eq!(log.retention(), Some(&r), "the rules are read back");
    assert_eq!(log.base(), Offset(6));
    assert_eq!(read(&log, "/f/F/in/>"), vec![2, 3, 4]);
    assert_eq!(log.oldest(&filter("/f/F/in/>")), Offset(1));
    let last = last_of(&mut log, &filter("/f/F/pub/*/*/presence"), 10, 100);
    assert_eq!(last.iter().map(|r| r.seq.0).collect::<Vec<_>>(), vec![1]);
    assert_eq!(
        log.retain_by_rules(T0 + MINUTE).unwrap(),
        RetentionTick {
            base_before: 6,
            base: 6,
            ..RetentionTick::default()
        },
        "rules read back are not set: no tick runs on them"
    );
    log.set_retention(r).unwrap();
    assert_eq!(fx.batch(&mut log, &[MAIL, EV]), vec![7, 8]);
    let tick = log.retain_by_rules(T0 + 2 * MINUTE).unwrap();
    assert_eq!(tick.base, 7, "the mail at 7 is retained above the cut");
    assert_eq!(
        tick.lost,
        vec![(MAIL.to_string(), 1)],
        "the class keeps three"
    );
    assert_eq!(read(&log, "/f/F/in/>"), vec![3, 4, 7]);
    drop(log);
    let log = fx.open();
    assert_eq!(read(&log, "/f/F/in/>"), vec![3, 4, 7]);
    assert_eq!(log.oldest(&filter("/f/F/in/>")), Offset(3));
}

/// What a reader can see of the crash law's log: the records, the mail held and retained,
/// the floors, `Last`, the inbox group's resume point, the store's counts, and the subject
/// budget its one producer is charged (`Last`'s carried charges: what a `Retire` credits
/// back).
#[derive(Debug, PartialEq, Eq)]
struct Snap {
    base: u64,
    head: u64,
    retained: Vec<(u64, String)>,
    mail: Vec<u64>,
    oldest: [u64; 3],
    last: Vec<(String, u64)>,
    group: u64,
    held: (usize, u64),
    budget: (usize, usize),
}

fn snap(log: &mut BrokerLog) -> Snap {
    let head = log.head().0;
    let last = last_of(log, &filter("/>"), 1000, 100_000);
    let stats = log.stats();
    Snap {
        base: log.base().0,
        head,
        retained: log
            .read_from(Offset(0))
            .iter()
            .map(|r| (r.seq.0, r.subject.clone()))
            .collect(),
        mail: read(log, "/f/F/in/>"),
        oldest: [
            log.oldest(&filter("/f/F/in/n1/>")).0,
            log.oldest(&filter("/f/F/in/n2/>")).0,
            log.oldest(&filter("/f/F/pub/*/*/ev")).0,
        ],
        last: last.iter().map(|r| (r.subject.clone(), r.seq.0)).collect(),
        group: log.group_start(INBOX).0,
        held: (stats.held_records, stats.held_bytes),
        budget: (log.subjects_per_producer(1), log.will_reserved_subjects(1)),
    }
}

/// The crash law's rules: three ev records kept, mail until read or 7 days.
fn crash_rules() -> Retention {
    rules(Some(3 * rb(EV)), None, None, 7 * DAY, true)
}

/// The log every crash case starts from: a first tick carried two mails (n1's at 1, n2's
/// at 4); n1's reader then read its mail; and more was published, n2 mail at 13 among it.
/// Reopened, its rules set again: the next tick at `T0 + HOUR` releases n1's mail (a floor
/// rises) and carries the mail at 13, cutting at 15.
fn seed(fx: &mut Fx) -> BrokerLog {
    let mut log = fx.create();
    log.set_retention(crash_rules()).unwrap();
    fx.batch(&mut log, &[EV, MAIL, EV, PRESENCE, MAIL2]);
    fx.batch(&mut log, &[EV; 6]);
    let tick = log.retain_by_rules(T0).unwrap();
    assert_eq!((tick.base, tick.carried), (8, 2));
    log.commit(INBOX.into(), 1).unwrap();
    fx.batch(&mut log, &[EV, MAIL2, EV, EV, EV, EV]);
    drop(log);
    let mut log = fx.open();
    log.set_retention(crash_rules()).unwrap();
    log
}

/// The reference: the seeded log as a reopen reads it before the tick, and after an
/// uninterrupted one.
fn reference(sealed: bool) -> (Snap, Snap) {
    let mut fx = Fx::new("held-ref", sealed);
    let mut log = seed(&mut fx);
    let before = snap(&mut log);
    drop(log);
    assert_eq!(snap(&mut fx.open()), before, "a reopen reads the seed back");
    let mut log = fx.open();
    log.set_retention(crash_rules()).unwrap();
    let tick = log.retain_by_rules(T0 + HOUR).unwrap();
    assert_eq!(
        (tick.base, tick.carried, tick.released),
        (15, 1, 1),
        "the tick both carries and releases"
    );
    drop(log);
    let after = snap(&mut fx.open());
    assert_eq!(after.base, 15);
    assert_eq!(after.mail, vec![4, 13]);
    assert_eq!(after.oldest, [2, 0, 15]);
    assert_eq!(
        after.budget,
        (4, 0),
        "ev, mail, presence and the second mail stay charged to their producer"
    );
    assert!(fx.leftovers().is_empty(), "{:?}", fx.leftovers());
    (before, after)
}

const STEPS: [Step; 9] = [
    Step::Held,
    Step::Copy,
    Step::State,
    Step::Intent,
    Step::Rename,
    Step::StateInstalled,
    Step::Base,
    Step::Watermark,
    Step::IntentRemoved,
];

/// Whether the log on disk is the kept suffix once `step` is durable.
const fn switched(step: Step) -> bool {
    !matches!(step, Step::Held | Step::Copy | Step::State | Step::Intent)
}

/// THE CRASH LAW WITH A HELD STORE: after a crash following any durable step of a tick's
/// compaction — the held store's frames first — whether the process stopped dead or the
/// power went (every directory that can leave), the next open reads the log, its held
/// store and its floors either as they were or as the uninterrupted tick leaves them, never
/// anything else: no carried mail lost, no released one back, no frame of a compaction that
/// did not land applied. It leaves none of the compaction's files behind, a second open
/// reads the same, and the log ticks on.
fn held_crash_law(sealed: bool) {
    let (before, after) = reference(sealed);
    for step in STEPS {
        if step == Step::Watermark && !sealed {
            continue;
        }
        let mut fx = Fx::new("held-crash", sealed);
        let mut log = seed(&mut fx);
        log.arm_compact_seam(Seam {
            crash_after: Some(step),
            ..Seam::default()
        });
        #[cfg(unix)]
        crate::power_loss::arm(fx.dir());
        let err = log.retain_by_rules(T0 + HOUR).expect_err("the armed crash");
        #[cfg(unix)]
        let lost = crate::power_loss::disarm().unwrap().images();
        #[cfg(not(unix))]
        let lost: Vec<()> = Vec::new();
        assert!(
            err.to_string().contains("injected crash"),
            "{step:?}: {err}"
        );
        drop(log);
        #[cfg(unix)]
        let stood = crate::power_loss::capture(fx.dir());
        let want = if switched(step) { &after } else { &before };
        #[cfg(unix)]
        {
            let left = std::iter::once(("a process crash", stood))
                .chain(lost.into_iter().map(|image| ("a power loss", image)));
            for (how, image) in left {
                crate::power_loss::apply(fx.dir(), &image);
                reopens_whole(&fx, &format!("{step:?}, {how}"), want);
            }
        }
        #[cfg(not(unix))]
        {
            let _ = lost;
            reopens_whole(&fx, &format!("{step:?}"), want);
        }
    }
}

fn reopens_whole(fx: &Fx, at: &str, want: &Snap) {
    let mut log = fx
        .try_open()
        .unwrap_or_else(|e| panic!("{at}: the open after the crash refused: {e}"));
    assert_eq!(&snap(&mut log), want, "{at}");
    drop(log);
    assert!(
        fx.leftovers().is_empty(),
        "{at}: left behind {:?}",
        fx.leftovers()
    );
    let mut log = fx
        .try_open()
        .unwrap_or_else(|e| panic!("{at}: the second open refused: {e}"));
    assert_eq!(&snap(&mut log), want, "{at}: the second open");
    log.set_retention(crash_rules()).unwrap();
    let tick = log.retain_by_rules(T0 + HOUR).unwrap();
    assert_eq!(tick.base, 15, "{at}: ticks on to the same cut");
    drop(log);
    let log = fx.open();
    assert_eq!(
        read(&log, "/f/F/in/>"),
        vec![4, 13],
        "{at}: and reads it back"
    );
}

#[test]
fn a_crash_after_any_durable_step_of_a_ticks_compaction_reopens_whole() {
    held_crash_law(false);
}

/// The same law on a log sealed at rest under anti-rollback, reopened verified: the held
/// store is sealed under the log's key, frame by frame.
#[cfg(feature = "anti-rollback")]
#[test]
fn a_crash_after_any_durable_step_under_anti_rollback_reopens_whole() {
    held_crash_law(true);
}

/// A SEALED HELD STORE does not open under another key, and holds no record's bytes in the
/// clear.
#[cfg(feature = "anti-rollback")]
#[test]
fn a_sealed_held_store_is_sealed() {
    let mut fx = Fx::new("held-sealed", true);
    let log = seed(&mut fx);
    drop(log);
    let bytes = std::fs::read(held_path(&fx.path)).unwrap();
    assert!(
        !bytes.windows(BODY.len()).any(|w| w == BODY),
        "a held record's body in the clear"
    );
    let err = HeldStore::load(
        &fx.path,
        Some(crate::store::AtRestRef::v1(&[0x11; 32])),
        8,
        false,
    )
    .err()
    .expect("another key");
    assert!(err.to_string().contains("authenticate"), "{err}");
}

/// AGES SURVIVE A RESTART: the bulk stream kept 7 days by age; ten records first seen by a
/// tick at T0, the log reopened and its rules set again (as `asb serve --retain-file` does at
/// every start), ten more first seen at T0 + 3 days, reopened again: a tick at T0 + 7 days and
/// a minute cuts the first ten, by when they were first seen, and after one more restart a
/// tick at T0 + 10 days and a minute the next ten. NC: an open that restamps the retained
/// suffix (the stamps read back left out) cuts nothing until 7 days after the last restart.
#[test]
fn an_age_rule_cuts_by_when_a_record_was_first_seen_across_restarts() {
    let mut fx = Fx::new("held-ages", false);
    let r = rules(None, Some(7 * DAY), None, 7 * DAY, false);
    let mut log = fx.create();
    log.set_retention(r.clone()).unwrap();
    fx.batch(&mut log, &[EV; 10]);
    assert_eq!(log.retain_by_rules(T0).unwrap().base, 0);
    drop(log);
    let mut log = fx.open();
    log.set_retention(r.clone()).unwrap();
    fx.batch(&mut log, &[EV; 10]);
    assert_eq!(log.retain_by_rules(T0 + 3 * DAY).unwrap().base, 0);
    drop(log);
    let mut log = fx.open();
    log.set_retention(r.clone()).unwrap();
    assert_eq!(
        log.retain_by_rules(T0 + 6 * DAY).unwrap().base,
        0,
        "nothing is 7 days old"
    );
    let tick = log.retain_by_rules(T0 + 7 * DAY + MINUTE).unwrap();
    assert_eq!(
        (tick.base_before, tick.base),
        (0, 10),
        "the ten first seen at T0, whatever the restarts since"
    );
    drop(log);
    let mut log = fx.open();
    log.set_retention(r).unwrap();
    assert_eq!(log.retain_by_rules(T0 + 9 * DAY).unwrap().base, 10);
    assert_eq!(
        log.retain_by_rules(T0 + 10 * DAY + MINUTE).unwrap().base,
        20,
        "the ten first seen at T0 + 3 days"
    );
}

/// A CRASH THAT LOSES STAMPED RECORDS NEVER AGES THE ONES AFTER IT: a tick at T0 stamps
/// twenty records, the second batch of which (15 to 19) a crash then tears away; the log
/// reopened takes five new records at those offsets, and is reopened again before any tick
/// sees them. A tick at T0 + 7 days and a minute cuts the fifteen first seen at T0, never
/// the five no tick had seen. NC: stamps read back that are not cut to the head recovered
/// (and, with the cut kept in memory only, the second open's) age the new five 7 days and
/// cut them too.
#[test]
fn a_crash_that_loses_stamped_records_never_ages_the_ones_after_it() {
    let mut fx = Fx::new("held-stamps-lost", false);
    let r = rules(None, Some(7 * DAY), None, 7 * DAY, false);
    let mut log = fx.create();
    log.set_retention(r.clone()).unwrap();
    fx.batch(&mut log, &[EV; 15]);
    fx.batch(&mut log, &[EV; 5]);
    assert_eq!(log.retain_by_rules(T0).unwrap().base, 0);
    drop(log);
    // The power went before the second batch's bytes were all on the disk: its sealing
    // record is torn, so the open cuts the batch at its start.
    let len = std::fs::metadata(&fx.path).unwrap().len();
    std::fs::OpenOptions::new()
        .write(true)
        .open(&fx.path)
        .unwrap()
        .set_len(len - 3)
        .unwrap();
    let mut log = fx.open();
    assert_eq!(
        log.head(),
        Offset(15),
        "PRECONDITION: the torn batch is cut"
    );
    assert_eq!(fx.batch(&mut log, &[EV; 5]), vec![15, 16, 17, 18, 19]);
    drop(log);
    let mut log = fx.open();
    log.set_retention(r).unwrap();
    let tick = log.retain_by_rules(T0 + 7 * DAY + MINUTE).unwrap();
    assert_eq!(tick.base, 15, "only the records first seen at T0");
    assert_eq!(
        log.read_from(Offset(0))
            .iter()
            .map(|r| r.seq.0)
            .collect::<Vec<_>>(),
        vec![15, 16, 17, 18, 19],
        "the five no tick had seen are kept"
    );
}

/// A REWRITE KEEPS THE STAMPS: a store due a rewrite (its length set past the bound by
/// hand) is written whole at the next tick, the tick's stamps in its snapshot, and the open
/// after it reads every record's age back: a tick at T0 + 7 days and a minute cuts the four
/// first seen at T0, at T0 + 8 days and a minute the next four. NC: a snapshot without the
/// stamps reads back none, and nothing is cut until 7 days after the restart.
#[test]
fn a_rewritten_store_keeps_the_ticks_stamps() {
    let mut fx = Fx::new("held-rewrite-stamps", false);
    let r = rules(None, Some(7 * DAY), None, 7 * DAY, false);
    let mut log = fx.create();
    log.set_retention(r.clone()).unwrap();
    for day in 0..3 {
        fx.batch(&mut log, &[EV; 4]);
        if day == 2 {
            log.held_store_mut().len += 16 << 20;
            assert!(log.held_store_mut().rewrite_due(), "PRECONDITION");
        }
        assert_eq!(log.retain_by_rules(T0 + day * DAY).unwrap().base, 0);
    }
    assert!(
        std::fs::metadata(held_path(&fx.path)).unwrap().len() < 1 << 20,
        "PRECONDITION: the store was rewritten"
    );
    drop(log);
    let mut log = fx.open();
    log.set_retention(r).unwrap();
    assert_eq!(log.retain_by_rules(T0 + 7 * DAY + MINUTE).unwrap().base, 4);
    assert_eq!(log.retain_by_rules(T0 + 8 * DAY + MINUTE).unwrap().base, 8);
}

/// A TORN OR ZEROED TAIL is cut at its frame (an append a crash interrupted holds nothing a
/// landed compaction needs); damage inside the store refuses the open, naming the file.
#[test]
fn a_torn_held_tail_is_cut_and_damage_refuses_naming_the_file() {
    let mut fx = Fx::new("held-torn", false);
    let mut log = seed(&mut fx);
    let want = snap(&mut log);
    drop(log);
    let held = held_path(&fx.path);
    let whole = std::fs::read(&held).unwrap();
    let frame = Frame::new(b"Tsomething long enough".to_vec())
        .encode()
        .unwrap();
    for (how, tail) in [
        (
            "a frame cut short",
            frame.get(..frame.len() - 3).unwrap().to_vec(),
        ),
        ("a header cut short", frame.get(..5).unwrap().to_vec()),
        ("zeros", vec![0u8; 40]),
    ] {
        let mut b = whole.clone();
        b.extend_from_slice(&tail);
        std::fs::write(&held, &b).unwrap();
        let mut log = fx
            .try_open()
            .unwrap_or_else(|e| panic!("{how}: the open refused: {e}"));
        assert_eq!(snap(&mut log), want, "{how}");
        drop(log);
        assert_eq!(
            std::fs::read(&held).unwrap(),
            whole,
            "{how}: cut at the frame"
        );
    }
    let mut b = whole.clone();
    let mid = HEADER_SIZE + 4;
    b[mid] ^= 0xff;
    std::fs::write(&held, &b).unwrap();
    let err = fx.try_open().err().expect("damage refuses");
    assert!(err.to_string().contains(".held"), "{err}");
    std::fs::write(&held, &whole).unwrap();
    assert_eq!(snap(&mut fx.open()), want, "the store put back opens");
}

/// A RULES CHANGE KEEPS THE HELD MAIL READABLE: a tick carried an unread mail at 1 below a
/// cut at 3; the rules set again with the stream's bytes doubled and a new hold class beside
/// them, the mail still reads from 0 with no `retained-from=`, its class whole from where it
/// was, while a read of the new class below the base is told where it starts — live, and
/// across a restart (the rules set again). NC: every class reset to the base by the change
/// refuses the mail's read `retained-from=3`.
#[test]
fn a_rules_change_keeps_the_held_mail_readable() {
    let mut fx = Fx::new("held-retune", false);
    let mut log = fx.create();
    log.set_retention(rules(Some(rb(EV)), None, None, 7 * DAY, false))
        .unwrap();
    fx.batch(&mut log, &[EV, MAIL, EV, EV]);
    assert_eq!(log.retain_by_rules(T0).unwrap().base, 3);
    let retuned = || {
        let mut r: Vec<Rule> = rules(Some(2 * rb(EV)), None, None, 7 * DAY, false)
            .rules()
            .to_vec();
        r.push(Rule::hold("/f/F/x/>").unwrap());
        Retention::new(r, Rule::default_hold()).unwrap()
    };
    log.set_retention(retuned()).unwrap();
    let mail = filter("/f/F/in/>");
    for pass in ["live", "after a restart"] {
        let head = log.head().0;
        let got = log
            .fetch_checked(0, &mail, 10, 100, head)
            .map(|(p, _)| p.iter().map(|r| r.seq.0).collect::<Vec<_>>());
        assert_eq!(got, Ok(vec![1]), "{pass}: the held mail reads from 0");
        assert_eq!(log.oldest(&filter("/f/F/x/>")), Offset(3), "{pass}");
        drop(log);
        log = fx.open();
        log.set_retention(retuned()).unwrap();
    }
}

/// THE REWRITE: a hold class that churns (each tick carries a large mail and gives up the
/// oldest) grows the file past twice what it carries, and the next tick writes it whole:
/// the file stays within a small multiple of what it holds, and reads back the same.
#[test]
fn a_churning_store_is_rewritten_and_reads_back_the_same() {
    let mut fx = Fx::new("held-rewrite", false);
    let mut log = fx.create();
    let big = vec![7u8; 64 * 1024];
    let mail_bytes = 2 * record_bytes(&rec_of(MAIL, &big));
    log.set_retention(rules(Some(rb(EV)), None, Some(mail_bytes), 7 * DAY, false))
        .unwrap();
    let mut largest = 0u64;
    for i in 0..48u64 {
        fx.seq += 1;
        log.stage_publish(1, fx.seq, MAIL.into(), big.clone())
            .unwrap();
        fx.seq += 1;
        log.stage_publish(1, fx.seq, EV.into(), BODY.to_vec())
            .unwrap();
        fx.seq += 1;
        log.stage_publish(1, fx.seq, EV.into(), BODY.to_vec())
            .unwrap();
        log.commit_batch().unwrap();
        log.retain_by_rules(T0 + i * MINUTE).unwrap();
        largest = largest.max(std::fs::metadata(held_path(&fx.path)).unwrap().len());
    }
    assert_eq!(log.stats().held_records, 2);
    let live = log.stats().held_bytes;
    assert!(
        largest <= 2 * (live + 64 * 1024) + (1 << 20) + 2 * 70 * 1024,
        "the file grew to {largest} bytes for {live} held"
    );
    assert!(
        largest > 1 << 20,
        "PRECONDITION: the churn passed the slack"
    );
    let want = snap(&mut log);
    drop(log);
    assert_eq!(snap(&mut fx.open()), want);
}

/// WITHOUT RULES nothing changes but the refusal: no held store is written, a tick does
/// nothing, and a read below a base a caller compacted to is clamped by `fetch` and refused
/// by `fetch_checked` with the base.
#[test]
fn a_log_without_rules_keeps_no_held_store() {
    let mut fx = Fx::new("held-none", false);
    let mut log = fx.create();
    fx.batch(&mut log, &[MAIL, EV, EV]);
    assert_eq!(log.retain_by_rules(T0).unwrap().base, 0);
    assert_eq!(log.retain_before(Offset(2)).unwrap(), 2);
    assert!(std::fs::symlink_metadata(held_path(&fx.path)).is_err());
    let all = filter("/>");
    assert_eq!(log.oldest(&all), Offset(2));
    let (page, _) = log.fetch(0, &all, 10, 100, 3);
    assert_eq!(page[0].seq, Offset(2), "fetch clamps");
    assert_eq!(
        log.fetch_checked(0, &all, 10, 100, 3).map(|(p, _)| p.len()),
        Err(Offset(2))
    );
    assert_eq!(
        log.fetch_checked(0, &all, 0, 100, 3).unwrap().1,
        0,
        "the head query"
    );
}

/// A COMPACTION A CALLER ASKS FOR on a log its rules retain carries what they hold below
/// the floor it names, and its state, as a tick's does.
#[test]
fn a_callers_compaction_carries_what_the_rules_hold() {
    let mut fx = Fx::new("held-caller", false);
    let mut log = fx.create();
    log.set_retention(rules(None, None, None, 7 * DAY, true))
        .unwrap();
    fx.batch(&mut log, &[MAIL, PRESENCE, EV, EV]);
    assert_eq!(log.retain_before(Offset(3)).unwrap(), 3);
    assert_eq!(read(&log, "/f/F/in/>"), vec![0]);
    let last = last_of(&mut log, &filter("/f/F/pub/*/*/presence"), 10, 100);
    assert_eq!(last.len(), 1, "its state carried");
}

/// A LOG CREATED where one with a held store was deleted carries none of it.
#[test]
fn a_created_log_carries_no_predecessors_held_store() {
    let mut fx = Fx::new("held-created", false);
    let log = seed(&mut fx);
    drop(log);
    assert!(std::fs::symlink_metadata(held_path(&fx.path)).is_ok());
    std::fs::remove_file(&fx.path).unwrap();
    let log = fx.open();
    assert_eq!(log.retention(), None);
    assert_eq!(log.stats().held_records, 0);
    assert!(std::fs::symlink_metadata(held_path(&fx.path)).is_err());
}

/// `Some` gap notice from `from` to `to`, counting `records`.
fn gap(from: u64, to: u64, records: Option<u64>) -> Option<crate::proto::Gap> {
    Some(crate::proto::Gap { from, to, records })
}

/// A TAIL IS TOLD WHAT THE RULES GAVE UP BELOW IT (R4's addendum, A9): with the mail class
/// past its bytes, the two oldest of five mails go. A tail on the mail from 0 is owed the
/// range up to the class's oldest, 2, and the count, 2, once. A tail that looked before the
/// cut is told at its next look. A tail from the held mail or above the base is owed
/// nothing, and one subject's tail counts only its own records. A filter that reaches the
/// prefix rule is told the range to the base and no count, because the cut dropped those
/// records as a range. After a restart the counts are not known, so the range alone is
/// told. Mail aged out past that range then widens it, and the wider range is told again.
/// NC: a count that skips its checks (a guess) counts the prefix filter's range. A planning
/// that ledgers nothing reads `Some(0)` and tells nothing.
#[test]
fn a_tail_below_what_the_rules_gave_up_is_told_the_range_and_the_count() {
    use crate::store::Told;
    let mut fx = Fx::new("held-gap", false);
    let mut log = fx.create();
    let ruled = || rules(Some(2 * rb(EV)), None, Some(3 * rb(MAIL)), 7 * DAY, false);
    log.set_retention(ruled()).unwrap();
    fx.batch(&mut log, &[MAIL, MAIL, MAIL, MAIL, MAIL, EV, EV, EV]);
    let mail = filter("/f/F/in/>");
    let mut early = Told::at(0);
    assert_eq!(
        log.gap_notice(&mail, 0, &mut early),
        None,
        "nothing given up yet"
    );
    let tick = log.retain_by_rules(T0).unwrap();
    assert_eq!((tick.base, tick.carried), (6, 3));
    assert_eq!(tick.lost, vec![(MAIL.to_string(), 2)]);

    let mut told = Told::at(0);
    assert_eq!(
        log.gap_notice(&mail, 0, &mut told),
        gap(0, 2, Some(2)),
        "the two mails past the class's bytes"
    );
    assert_eq!(log.gap_notice(&mail, 0, &mut told), None, "told once");
    assert_eq!(
        log.gap_notice(&mail, 0, &mut early),
        gap(0, 2, Some(2)),
        "a tail that looked before the cut is told at its next look"
    );
    assert_eq!(
        log.gap_notice(&mail, 2, &mut Told::at(2)),
        None,
        "from the held mail"
    );
    assert_eq!(
        log.gap_notice(&mail, 6, &mut Told::at(6)),
        None,
        "above the base"
    );
    assert_eq!(
        log.gap_notice(&filter("/f/F/in/n1/>"), 1, &mut Told::at(1)),
        gap(1, 2, Some(1)),
        "a tail from 1 lost only the mail at 1"
    );
    assert_eq!(
        log.gap_notice(&filter("/f/F/>"), 0, &mut Told::at(0)),
        gap(0, 6, None),
        "the prefix rule's records went as a range: no count"
    );

    drop(log);
    let mut log = fx.open();
    let mut after = Told::at(0);
    assert_eq!(
        log.gap_notice(&mail, 0, &mut after),
        gap(0, 2, None),
        "after a restart: the range, never a guessed count"
    );
    assert_eq!(log.gap_notice(&mail, 0, &mut after), None, "told once");
    // The same rules again, and a day past the mail's age: the three held mails go too.
    log.set_retention(ruled()).unwrap();
    let tick = log.retain_by_rules(T0 + 8 * DAY).unwrap();
    assert_eq!(tick.released, 3);
    assert_eq!(
        log.gap_notice(&mail, 0, &mut after),
        gap(0, 5, None),
        "the range grew: told again"
    );
}

/// A LATER GIVE-UP INSIDE A RANGE ALREADY TOLD IS TOLD AGAIN, counted once. n2's mail at 0
/// and n1's at 1 are held below the base at 4. When n1's reader reads its mail, that mail
/// goes, and a tail on all mail from 0 is told `0..2`, counting 1: n1's mail. n2's mail at
/// 0 is still held, so the tail is still delivered it (a `Fetch` of all mail that did not
/// ask for gap notices is refused below the oldest, 2, and one that asked reads it; of n2's
/// mail any `Fetch` reads it). When n2's mail ages out, inside the
/// range already told, the tail is told `0..2` again, counting 1: n2's mail, and not n1's a
/// second time. NC: a count of only what lies at or above the range told (no `seq > seen`)
/// reads `Some(0)` for n2's mail and tells nothing.
#[test]
fn a_later_give_up_inside_a_told_range_is_told_again_and_counted_once() {
    use crate::store::Told;
    let mut fx = Fx::new("held-gap-again", false);
    let mut log = fx.create();
    log.set_retention(rules(Some(rb(EV)), None, None, 7 * DAY, true))
        .unwrap();
    fx.batch(&mut log, &[MAIL2, MAIL, EV, EV, EV]);
    let tick = log.retain_by_rules(T0).unwrap();
    assert_eq!((tick.base, tick.carried), (4, 2));
    let mail = filter("/f/F/in/>");
    let mut told = Told::at(0);
    assert_eq!(
        log.gap_notice(&mail, 0, &mut told),
        None,
        "every mail is held"
    );

    log.commit(INBOX.into(), 1).unwrap();
    let tick = log.retain_by_rules(T0 + MINUTE).unwrap();
    assert_eq!(tick.released, 1, "n1's reader read its mail");
    assert_eq!(
        log.gap_notice(&mail, 0, &mut told),
        gap(0, 2, Some(1)),
        "n1's read mail: not this tail's to have read"
    );
    assert_eq!(read(&log, "/f/F/in/n2/>"), vec![0], "n2's is still held");

    let tick = log.retain_by_rules(T0 + 8 * DAY).unwrap();
    assert_eq!(
        tick.lost,
        vec![(MAIL2.to_string(), 1)],
        "n2's mail aged out"
    );
    assert_eq!(
        log.gap_notice(&mail, 0, &mut told),
        gap(0, 2, Some(1)),
        "told again inside the range, its own count"
    );
    assert_eq!(log.gap_notice(&mail, 0, &mut told), None);
}

/// A COMPACTION NO RULES PLANNED is told by its range alone: it drops records the ledger
/// never names, so a count would be a guess. On a log no rules ever held, the range runs to
/// the base. On one whose rules were read back from the held store and not set again (they
/// answer reads and plan no cut), the mail it dropped unnamed is told too: every hold class
/// reads from at least the cut (`HeldStore::cut_unplanned`). NC: a cut that leaves the
/// ledger whole from the open counts the mail filter's range at `Some(0)` and tells
/// nothing; one that leaves the hold classes' floors where they were tells nothing either.
#[test]
fn a_cut_no_rules_planned_is_told_by_its_range_alone() {
    use crate::store::Told;
    let mut fx = Fx::new("held-gap-norules", false);
    let mut log = fx.create();
    fx.batch(&mut log, &[MAIL, EV, EV]);
    let all = filter("/>");
    let mut told = Told::at(0);
    assert_eq!(log.gap_notice(&all, 0, &mut told), None);
    assert_eq!(log.retain_before(Offset(2)).unwrap(), 2);
    assert_eq!(log.gap_notice(&all, 0, &mut told), gap(0, 2, None));
    assert_eq!(log.gap_notice(&all, 0, &mut told), None, "told once");
    assert_eq!(log.gap_notice(&all, 2, &mut Told::at(2)), None);

    let mut fx = Fx::new("held-gap-readback", false);
    let mut log = fx.create();
    log.set_retention(rules(None, None, None, 7 * DAY, false))
        .unwrap();
    fx.batch(&mut log, &[MAIL, EV, EV]);
    drop(log);
    let mut log = fx.open();
    assert!(log.retention_active().is_none(), "read back, not set again");
    let mail = filter("/f/F/in/>");
    let mut told = Told::at(0);
    assert_eq!(log.gap_notice(&mail, 0, &mut told), None);
    assert_eq!(log.retain_before(Offset(2)).unwrap(), 2);
    assert_eq!(
        log.oldest(&mail),
        Offset(2),
        "the hold class reads from the cut"
    );
    assert_eq!(
        log.gap_notice(&mail, 0, &mut told),
        gap(0, 2, None),
        "the mail the cut dropped unnamed"
    );
    assert_eq!(log.gap_notice(&mail, 0, &mut told), None, "told once");
}

/// A COMPACTION NO RULES PLANNED IS TOLD AFTER A RESTART TOO: on a log whose rules were read
/// back and not set again, `retain_before(2)` drops the mail at 0 unnamed. Its held-store
/// job writes the spill before the copy (`HeldStore::unplanned_job`), so a reopen reads the
/// mail from 2 and tells a tail from 0 the range `0..2`, with no count. A crash after that
/// frame, before the compaction landed, cuts it away at the open: the mail reads from 0
/// again, still in the log. NC: a cut that raises the spill in memory only (no job) reads
/// the mail from 0 after the restart and tells nothing.
#[test]
fn a_cut_no_rules_planned_is_told_after_a_restart() {
    use crate::store::Told;
    let mail = filter("/f/F/in/>");
    let ruled = || rules(None, None, None, 7 * DAY, false);
    let mut fx = Fx::new("held-gap-unplanned-restart", false);
    let mut log = fx.create();
    log.set_retention(ruled()).unwrap();
    fx.batch(&mut log, &[MAIL, EV, EV]);
    drop(log);
    let mut log = fx.open();
    assert!(log.retention_active().is_none(), "read back, not set again");
    assert_eq!(log.retain_before(Offset(2)).unwrap(), 2);
    drop(log);
    let log = fx.open();
    assert_eq!(
        log.oldest(&mail),
        Offset(2),
        "the spill the cut's frame raised, read back"
    );
    assert_eq!(
        log.gap_notice(&mail, 0, &mut Told::at(0)),
        gap(0, 2, None),
        "after a restart: the mail the cut dropped unnamed"
    );
    drop(log);

    let mut fx = Fx::new("held-gap-unplanned-crash", false);
    let mut log = fx.create();
    log.set_retention(ruled()).unwrap();
    fx.batch(&mut log, &[MAIL, EV, EV]);
    drop(log);
    let mut log = fx.open();
    log.arm_compact_seam(Seam {
        crash_after: Some(Step::Held),
        ..Seam::default()
    });
    let err = log.retain_before(Offset(2)).expect_err("the armed crash");
    assert!(err.to_string().contains("injected crash"), "{err}");
    drop(log);
    let log = fx.open();
    assert_eq!(
        (log.base(), log.oldest(&mail)),
        (Offset(0), Offset(0)),
        "the frame of a cut that never landed is cut away"
    );
    assert_eq!(read(&log, "/f/F/in/>"), vec![0]);
    assert!(fx.leftovers().is_empty(), "{:?}", fx.leftovers());
}

/// THE LEDGER IS BOUNDED as the floors are, and is whole only above what its bound dropped:
/// past [`retention::LEDGER_MAX`] records the lowest goes; past
/// [`retention::LEDGER_BYTES_MAX`] bytes of names the lowest go too; a record below where
/// it is whole is not taken; and `whole_from` forgets what is below. NC: a ledger that
/// never drops holds every record it was handed.
#[test]
fn the_ledger_is_bounded_and_whole_only_above_what_it_dropped() {
    use crate::retention::{Ledger, LEDGER_BYTES_MAX, LEDGER_MAX};
    let mail = filter("/f/F/in/>");
    let mut l = Ledger::default();
    let max = LEDGER_MAX as u64;
    for off in 0..=max {
        l.note(off, MAIL);
    }
    assert_eq!(l.len(), LEDGER_MAX);
    assert_eq!(
        l.whole(),
        1,
        "the lowest went, and it is whole only above it"
    );
    assert_eq!(l.seq(), max + 1);
    assert_eq!(l.count(&mail, 0, u64::MAX, 0, 0), max);
    l.note(0, MAIL);
    assert_eq!(
        (l.len(), l.seq()),
        (LEDGER_MAX, max + 1),
        "below where it is whole"
    );
    l.whole_from(max - 1);
    assert_eq!((l.len(), l.whole()), (2, max - 1));
    assert_eq!(l.count(&mail, 0, u64::MAX, 0, 0), 2);

    let long = format!("/f/F/in/n1/{}", "x".repeat(1 << 20));
    let fit = LEDGER_BYTES_MAX / long.len();
    let mut l = Ledger::default();
    for off in 0..=fit as u64 {
        l.note(off, &long);
    }
    assert_eq!(l.len(), fit, "past the bytes of names, the lowest went");
    assert_eq!(l.whole(), 1);
}

/// [`rules`]'s stream, kept by one record's bytes, and its mail, held a week (and, when
/// `readers`, until its node's inbox group reads it), beside a class of its own, `box`, that
/// holds its records a day.
fn boxed_rules(readers: bool) -> Retention {
    let mut mail = Rule::hold("/f/F/in/>")
        .unwrap()
        .max_age(Duration::from_millis(7 * DAY));
    if readers {
        mail = mail.until_read("/f/{2}/cur/{4}/node/inbox").unwrap();
    }
    Retention::new(
        vec![
            Rule::prefix("/f/F/pub/*/*/ev").unwrap().max_bytes(rb(EV)),
            mail,
            Rule::hold("/f/F/box/>")
                .unwrap()
                .max_age(Duration::from_millis(DAY)),
        ],
        Rule::default_hold(),
    )
    .unwrap()
}

/// A `box` subject of a mebibyte, the `i`th: a few of them give up more names than the
/// ledger and the floors take ([`retention::LEDGER_BYTES_MAX`], [`FLOOR_BYTES_MAX`]).
fn big_box(i: usize) -> String {
    format!("/f/F/box/{i:02}{}", "x".repeat(1 << 20))
}

/// A GIVE-UP THE LEDGER CAN NO LONGER COUNT, inside a range a counted notice told, is told
/// by the range again. n2's mail at 0 and n1's at 1 are held. n1's reader reads its mail,
/// and a tail on all mail from 0 is told `0..2`, counting 1. Then, in one planning, n2's
/// mail ages out beside nine `box` records of a mebibyte's name: more names than the ledger
/// takes, so it drops its lowest, n2's mail and n1's among them, and is whole only above
/// them. The range has not grown, and its count is no longer known: the tail is told `0..2`
/// with no count, once. NC: a range told again only when it grows (no `|| told.counted`)
/// tells nothing; a ledger that takes a planning's give-ups without being whole only from
/// where the planning's was (no `whole_from` in `Ledger::take`) counts none, and tells
/// nothing.
#[test]
fn a_give_up_the_ledger_can_no_longer_count_is_told_by_its_range_again() {
    use crate::store::Told;
    let mut fx = Fx::new("held-gap-uncounted", false);
    let mut log = fx.create();
    log.set_retention(boxed_rules(true)).unwrap();
    fx.batch(&mut log, &[MAIL2, MAIL]);
    let big = big_box(0);
    for _ in 0..9 {
        fx.batch(&mut log, &[big.as_str()]);
    }
    fx.batch(&mut log, &[EV, EV, EV]);
    let tick = log.retain_by_rules(T0).unwrap();
    assert_eq!((tick.base, tick.carried), (13, 11));
    let mail = filter("/f/F/in/>");
    let mut told = Told::at(0);
    assert_eq!(
        log.gap_notice(&mail, 0, &mut told),
        None,
        "every mail is held"
    );

    log.commit(INBOX.into(), 1).unwrap();
    let tick = log.retain_by_rules(T0 + MINUTE).unwrap();
    assert_eq!(tick.released, 1, "n1's reader read its mail");
    assert_eq!(log.gap_notice(&mail, 0, &mut told), gap(0, 2, Some(1)));

    let tick = log.retain_by_rules(T0 + 8 * DAY).unwrap();
    assert!(
        tick.lost.iter().any(|(s, n)| s == MAIL2 && *n == 1),
        "n2's mail aged out"
    );
    assert_eq!(
        log.gap_notice(&mail, 0, &mut told),
        gap(0, 2, None),
        "told again by its range: its count is not known"
    );
    assert_eq!(log.gap_notice(&mail, 0, &mut told), None, "told once");
    assert!(
        log.held_store_mut().ledger.whole() > 1,
        "the ledger names neither mail now"
    );
}

/// A LOOK THAT TELLS NOTHING LEAVES THE RANGE STILL OWED. A tail on all mail from n2's mail
/// at `M` is owed nothing while it is held. Then the `box` records age out, one more of
/// them, each of its own subject, than the floors take ([`FLOORS_MAX`]): half below the mail
/// and the rest above it. The floors fold into the spill (`HeldStore::raise`) past the first
/// above it, so the mail reads from `M + 2`; the ledger drops only its lowest, below the
/// mail, so it is whole there and names no mail in `M..M + 2`: the look counts none, and
/// tells nothing. When the mail ages out beside eight `box` records of a mebibyte's name
/// (more names than the ledger takes, [`retention::LEDGER_BYTES_MAX`]), the ledger drops it,
/// and is whole only above it: the range is the same, and no count can be given, so the
/// tail is told the range, once. NC: a look that moves the range told as it tells nothing
/// never tells it.
#[test]
fn a_look_that_tells_nothing_leaves_the_range_still_owed() {
    use crate::store::Told;
    const HALF: u64 = (FLOORS_MAX / 2) as u64;
    const M: u64 = HALF;
    let mut fx = Fx::new("held-gap-owed", false);
    let mut log = fx.create();
    log.set_retention(boxed_rules(false)).unwrap();
    // Each `box` record a subject of its own, so each raises a floor. A producer creates at
    // most `MAX_SUBJECTS_PER_PRODUCER` subjects: a fresh one every 4096 records.
    let mut staged = 0u64;
    let mut boxes = |log: &mut BrokerLog, from: u64, to: u64| {
        for i in from..to {
            staged += 1;
            log.stage_publish(
                100 + staged / 4096,
                staged,
                format!("/f/F/box/{i:05}"),
                BODY.to_vec(),
            )
            .unwrap();
            if staged.is_multiple_of(4096) || i + 1 == to {
                log.commit_batch().unwrap();
            }
        }
    };
    boxes(&mut log, 0, HALF);
    assert_eq!(fx.batch(&mut log, &[MAIL2]), vec![M]);
    boxes(&mut log, HALF, 2 * HALF + 1);
    fx.batch(&mut log, &[EV, EV, EV]);
    let base = 2 * HALF + 4;
    let tick = log.retain_by_rules(T0).unwrap();
    assert_eq!((tick.base, tick.carried), (base, 2 * HALF as usize + 2));
    let mail = filter("/f/F/in/>");
    let mut told = Told::at(M);
    assert_eq!(
        log.gap_notice(&mail, M, &mut told),
        None,
        "the mail is held"
    );

    let tick = log.retain_by_rules(T0 + 2 * DAY).unwrap();
    assert_eq!(
        tick.released,
        2 * HALF as usize + 1,
        "every box record aged out"
    );
    assert_eq!(
        log.oldest(&mail),
        Offset(M + 2),
        "the spill the folded floors raised"
    );
    assert!(log.held_store_mut().ledger.whole() <= M);
    assert_eq!(
        log.gap_notice(&mail, M, &mut told),
        None,
        "no mail was given up: nothing to tell"
    );

    let big = big_box(0);
    for _ in 0..8 {
        fx.batch(&mut log, &[big.as_str()]);
    }
    fx.batch(&mut log, &[EV, EV, EV]);
    let tick = log.retain_by_rules(T0 + 3 * DAY).unwrap();
    assert_eq!((tick.base, tick.carried), (base + 11, 8));
    assert_eq!(log.gap_notice(&mail, M, &mut told), None);

    let tick = log.retain_by_rules(T0 + 8 * DAY).unwrap();
    assert!(
        tick.lost.iter().any(|(s, n)| s == MAIL2 && *n == 1),
        "the mail aged out"
    );
    assert!(
        log.held_store_mut().ledger.whole() > M,
        "the ledger dropped it"
    );
    assert_eq!(log.oldest(&mail), Offset(M + 2), "the range is the same");
    assert_eq!(
        log.gap_notice(&mail, M, &mut told),
        gap(M, M + 2, None),
        "the range still owed, told"
    );
    assert_eq!(log.gap_notice(&mail, M, &mut told), None, "told once");
}
