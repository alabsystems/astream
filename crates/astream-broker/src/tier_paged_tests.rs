// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! THE PAGES AGAINST THE SLOT VECTOR (`broker.paged-tier`): random streams of pushes, cuts,
//! truncations, budget changes, rebuilds and repagings, over every page size from one record
//! to [`PAGE`], with frame starts and broker times that sometimes leave their page's column
//! range, and after every step each answer the pages give (every record's summary, frame
//! start, broker time and residency, the page-by-page walks, a filtered read's passes, the
//! counts, the subjects named, and with `retention` the retention planning over them) is the
//! slot vector's. The negative controls: a page entry off by one record, its base or its
//! index, a walk that keeps a name across a page, and a pass that drops a page it wants, are
//! caught.

use std::sync::Arc;

use astream_wire::Offset;

use super::{Met, PageMutant, Tier, PAGE, PAGE_SHIFT};
use crate::brecord::BrokerRecord;

/// xorshift64*: the streams' deterministic PRNG.
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Rng {
        Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1)
    }

    fn below(&mut self, n: u64) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D) % n.max(1)
    }
}

/// The subjects the streams name: a fabric's stream, presence and mail, and a hidden one.
const SUBJECTS: [&str; 6] = [
    "/f/F/pub/a/b/ev",
    "/f/F/pub/a/c/ev",
    "/f/F/pub/a/b/presence",
    "/f/F/in/n/x",
    "/f/F/in/n/y",
    crate::store::COMMIT_SUBJECT,
];

/// The next records of a stream: offsets from `next`, frame starts contiguous by each
/// record's plaintext bytes and a marker, broker times rising, and (with `wide`) now and
/// then a frame start or broker time no page column holds.
struct Gen {
    rng: Rng,
    next: u64,
    at: u64,
    bt: u64,
    wide: bool,
}

impl Gen {
    fn new(seed: u64, wide: bool) -> Gen {
        Gen {
            rng: Rng::new(seed),
            next: 1_000,
            at: 0,
            bt: 1_793_000_000_000,
            wide,
        }
    }

    fn record(&mut self) -> (BrokerRecord, Option<u64>, u64) {
        let subject = SUBJECTS[self.rng.below(SUBJECTS.len() as u64) as usize];
        let body = vec![(self.next % 251) as u8; self.rng.below(300) as usize];
        let rec = BrokerRecord {
            seq: Offset(self.next),
            producer_id: 1 + self.rng.below(3),
            producer_seq: self.next,
            subject: subject.to_string(),
            body,
            commit: None,
        };
        self.next += 1;
        let at = self.at;
        let roll = self.rng.below(100);
        self.at += crate::brecord::plaintext_frame_bytes(&rec) + 9;
        if self.wide && roll < 3 {
            // A frame start past a page's `u32` range from its first.
            self.at += 1 << 32;
        }
        let bt = match self.rng.below(100) {
            0..=9 => None,
            10..=12 if self.wide => Some(self.bt + (1 << 33)),
            13..=15 if self.wide => Some(self.bt.saturating_sub(1 + self.rng.below(1 << 20))),
            _ => {
                self.bt += self.rng.below(2_000);
                Some(self.bt)
            }
        };
        (rec, bt, at)
    }
}

/// The retention rules the planning runs over both: the stream as the prefix, by bytes and
/// age, presence by its last value, mail held.
#[cfg(feature = "retention")]
fn rules() -> crate::retention::Retention {
    use crate::retention::{Retention, Rule};
    use std::time::Duration;
    Retention::new(
        vec![
            Rule::prefix("/f/F/pub/*/*/ev")
                .unwrap()
                .max_bytes(20_000)
                .max_age(Duration::from_secs(600)),
            Rule::hold("/f/F/pub/*/*/presence").unwrap().last_only(),
            Rule::hold("/f/F/in/>")
                .unwrap()
                .max_bytes(8_000)
                .max_age(Duration::from_secs(900)),
        ],
        crate::retention::Rule::default_hold(),
    )
    .unwrap()
}

/// The retention planning over the pages and over the slot vector, at `now`, the same.
#[cfg(feature = "retention")]
fn check_plans(t: &Tier, now: u64) -> Result<(), String> {
    t.check_plans(&rules(), now)
}

/// Without `retention` there is no planning to compare.
#[cfg(not(feature = "retention"))]
fn check_plans(_t: &Tier, _now: u64) -> Result<(), String> {
    Ok(())
}

/// The budgets the streams set: none resident, a few records, a few pages, everything.
const BUDGETS: [usize; 5] = [0, 400, 9_000, 120_000, Tier::RESIDENT_ALL];

/// One seeded stream of `steps` steps over pages of `1 << shift` records, each step checked
/// against the slot vector; returns the tier it ends with.
fn stream(seed: u64, shift: u32, wide: bool, steps: usize) -> Tier {
    stream_seen(seed, shift, wide, steps).0
}

/// [`stream`], and how many of its steps ended with a frame start and with a broker time in
/// the wide maps.
fn stream_seen(seed: u64, shift: u32, wide: bool, steps: usize) -> (Tier, usize, usize) {
    let mut seen = (0, 0);
    let mut rng = Rng::new(seed ^ 0x51ED);
    let mut gen = Gen::new(seed, wide);
    let mut t = Tier::paged(BUDGETS[rng.below(5) as usize], shift);
    for step in 0..steps {
        let roll = rng.below(100);
        if roll < 55 {
            for _ in 0..1 + rng.below(24) {
                let (rec, bt, at) = gen.record();
                t.push(Arc::new(rec), bt, at);
            }
        } else if roll < 70 {
            let n = rng.below(t.len() as u64 + 1) as usize;
            // The bytes the cut removed: the first kept frame's start, or (now and then) a
            // shift past some page's first frame start, which saturates.
            let shift = match (t.at(n), rng.below(5)) {
                (Some(at), 0) => at.saturating_add(rng.below(1 << 12)),
                (Some(at), _) => at,
                (None, _) => rng.below(1 << 16),
            };
            t.drain_front(n, shift);
            gen.at = gen.at.saturating_sub(shift);
        } else if roll < 76 {
            let keep = rng.below(t.len() as u64 + 1) as usize;
            t.truncate(keep);
            gen.next = t.base.saturating_add(t.len() as u64);
            if t.len() == 0 {
                gen.next = 1_000 + rng.below(1 << 20);
            }
        } else if roll < 84 {
            t.set_budget(BUDGETS[rng.below(5) as usize]);
        } else if roll < 90 {
            let s = rng.below(u64::from(PAGE_SHIFT) + 1) as u32;
            t.repage(s);
        } else if roll < 95 {
            // A rebuild (an open, a replica's truncation): fresh records, from_parts.
            let n = rng.below(600) as usize;
            gen.next = 1_000 + rng.below(1 << 20);
            let mut records = Vec::new();
            let mut bts = Vec::new();
            let mut ats = Vec::new();
            for _ in 0..n {
                let (rec, bt, at) = gen.record();
                records.push(rec);
                bts.push(bt);
                ats.push(at);
            }
            let budget = BUDGETS[rng.below(5) as usize];
            t = if rng.below(2) == 0 {
                Tier::paged(budget, t.shift).rebuilt(records, bts, ats)
            } else {
                let mut fresh = Tier::paged(budget, t.shift);
                fresh.fill(records, bts, ats);
                fresh
            };
        } else {
            // A planning long after the newest record, past every rule's age.
            let now = gen.bt.saturating_add(3_600_000 + rng.below(1 << 20));
            if let Err(e) = check_plans(&t, now) {
                panic!("seed {seed} shift {shift} step {step}: {e}");
            }
        }
        if let Err(e) = t.check_shadow() {
            panic!("seed {seed} shift {shift} step {step}: {e}");
        }
        // The planning after every step, at a time within the rules' ages of the newest.
        let now = gen.bt.saturating_add(rng.below(1_200_000));
        if let Err(e) = check_plans(&t, now) {
            panic!("seed {seed} shift {shift} step {step}: {e}");
        }
        seen.0 += usize::from(!t.wide_at.is_empty());
        seen.1 += usize::from(!t.wide_bt.is_empty());
    }
    (t, seen.0, seen.1)
}

#[test]
fn the_pages_answer_every_query_as_the_slot_vector_does() {
    for shift in 0..=PAGE_SHIFT {
        let mut seen = (0, 0);
        for seed in 0..6 {
            let (t, at, bt) = stream_seen(u64::from(shift) * 100 + seed, shift, true, 160);
            drop(t);
            seen = (seen.0 + at, seen.1 + bt);
        }
        // Not vacuous: values no column holds were held, and answered, at this page size.
        assert!(
            seen.0 > 0 && seen.1 > 0,
            "shift {shift}: steps with wide frame starts and broker times {seen:?}"
        );
    }
}

#[test]
fn a_rebuilt_tier_keeps_its_budget_and_page_size() {
    let mut gen = Gen::new(9, false);
    let t = Tier::paged(400, 2);
    let (mut records, mut bts, mut ats) = (Vec::new(), Vec::new(), Vec::new());
    for _ in 0..40 {
        let (rec, bt, at) = gen.record();
        records.push(rec);
        bts.push(bt);
        ats.push(at);
    }
    let r = t.rebuilt(records, bts, ats);
    assert_eq!((r.budget, r.shift, r.len()), (400, 2, 40));
    assert_eq!(r.pages.len(), 10, "40 records in pages of 4");
    assert_eq!(r.check_shadow(), Ok(()));
}

#[test]
fn a_full_page_of_distinct_subjects_and_a_production_page_fill_hold() {
    // 256 distinct subjects in one page: every `u8` index is used.
    let mut t = Tier::with_budget(0);
    for i in 0..(PAGE as u64 * 3) {
        let rec = BrokerRecord {
            seq: Offset(i),
            producer_id: 1,
            producer_seq: i,
            subject: format!("/f/s{}", i % PAGE as u64),
            body: vec![1; (i % 17) as usize],
            commit: None,
        };
        t.push(Arc::new(rec), Some(i * 3), i * 100);
    }
    assert_eq!(t.pages.len(), 3);
    assert_eq!(t.pages[0].subjects.len(), PAGE);
    assert_eq!(t.check_shadow(), Ok(()));
    // A cut inside the second page leaves its tail and the third page, every frame start
    // moved down by the bytes cut.
    t.drain_front(PAGE + 7, (PAGE as u64 + 7) * 100);
    assert_eq!((t.pages.len(), t.head, t.len()), (2, 7, 2 * PAGE - 7));
    assert_eq!(t.at(0), Some(0));
    assert!(
        t.wide_at.is_empty(),
        "a real log's frame starts fit their columns"
    );
    assert_eq!(t.check_shadow(), Ok(()));
}

/// A tier with at least two pages of at least two records each and no wide values.
fn mutable_tier(seed: u64, shift: u32) -> Tier {
    let mut gen = Gen::new(seed, false);
    let mut t = stream(seed, shift, false, 40);
    // The stream repages now and then: back to the page size asked for.
    t.repage(shift);
    for _ in 0..(3usize << shift) + 1 {
        let (rec, bt, at) = gen.record();
        let rec = BrokerRecord {
            seq: Offset(t.base + t.len() as u64),
            ..rec
        };
        let at = t
            .len()
            .checked_sub(1)
            .and_then(|i| t.at(i))
            .map_or(at, |a| a + 4_096);
        t.push(Arc::new(rec), bt, at);
    }
    t
}

/// The negative controls: a page whose first frame start and broker time are its second
/// record's, or pages that begin one record late, answer differently and are caught.
#[test]
fn a_page_entry_off_by_one_record_is_caught() {
    for shift in 1..=PAGE_SHIFT {
        for seed in 0..3 {
            let mut t = mutable_tier(700 + u64::from(shift) * 10 + seed, shift);
            assert_eq!(t.check_shadow(), Ok(()), "shift {shift} seed {seed}");
            let pages = t.pages.len();
            assert!(
                pages >= 2,
                "shift {shift} seed {seed}: two pages to mutate, {pages} for {} records from head {}",
                t.len(),
                t.head
            );
            t.mutate(PageMutant::Base(pages - 2));
            assert!(
                t.check_shadow().is_err(),
                "shift {shift} seed {seed}: a page based one record late answers the same"
            );
            let mut t = mutable_tier(700 + u64::from(shift) * 10 + seed, shift);
            t.mutate(PageMutant::Index);
            assert!(
                t.check_shadow().is_err(),
                "shift {shift} seed {seed}: pages indexed one record late answer the same"
            );
        }
    }
}

/// Two pages of `1 << shift` records, the first naming `SUBJECTS[0]` alone and the second
/// `SUBJECTS[1]`.
fn two_pages(shift: u32) -> Tier {
    let page = 1u64 << shift;
    let mut t = Tier::paged(0, shift);
    for i in 0..2 * page {
        let rec = BrokerRecord {
            seq: Offset(i),
            producer_id: 1,
            producer_seq: i,
            subject: SUBJECTS[(i / page) as usize].to_string(),
            body: vec![3; 8],
            commit: None,
        };
        t.push(Arc::new(rec), Some(i), i * 64);
    }
    t
}

/// The negative control of the page-by-page walk: a walk that keeps the subject name its last
/// record read across a page boundary reads the next page's records under the last page's
/// name, and is caught, at every page size. A filtered read's pass names a page's records by
/// the page's own ids, so it meets what it met before.
#[test]
fn a_walk_that_keeps_a_name_across_a_page_is_caught() {
    for shift in 0..=PAGE_SHIFT {
        let page = 1usize << shift;
        let mut t = two_pages(shift);
        assert_eq!(t.check_shadow(), Ok(()), "shift {shift}");
        // Each page names one subject: the walk for it reads that page's records alone.
        let len = t.len();
        let second: Vec<usize> = t.naming(SUBJECTS[1], 0, len).collect();
        assert_eq!(second, (page..len).collect::<Vec<_>>(), "shift {shift}");
        assert_eq!(t.naming(SUBJECTS[0], 1, len).count(), page - 1);
        assert_eq!(t.naming(SUBJECTS[2], 0, len).count(), 0, "shift {shift}");
        t.mutate(PageMutant::StaleName);
        assert!(
            t.check_shadow().is_err(),
            "shift {shift}: a walk keeping the last page's name answers the same"
        );
        let met: Vec<usize> = t
            .passing(0, len, |s| s == SUBJECTS[1])
            .map(Met::index)
            .collect();
        assert_eq!(met, (page..len).collect::<Vec<_>>(), "shift {shift}");
    }
}

/// The negative control of a filtered read's page skip (aterm F11c): a pass that passes whole a
/// page it wants a record of answers differently from the slot vector and is caught, at every
/// page size, on two pages of one subject each and on the streams' tiers.
#[test]
fn a_pass_that_drops_a_wanted_page_is_caught() {
    for shift in 0..=PAGE_SHIFT {
        let page = 1usize << shift;
        let mut t = two_pages(shift);
        let len = t.len();
        // The pass wanting the second page's subject passes the first page whole.
        let met: Vec<Met> = t.passing(0, len, |s| s == SUBJECTS[1]).collect();
        assert_eq!(
            met,
            (page..len).map(Met::Wanted).collect::<Vec<_>>(),
            "shift {shift}"
        );
        t.mutate(PageMutant::DropWanted);
        assert!(
            t.check_shadow().is_err(),
            "shift {shift}: a pass dropping a page it wants answers the same"
        );
        for seed in 0..3 {
            let mut t = mutable_tier(900 + u64::from(shift) * 10 + seed, shift);
            assert_eq!(t.check_shadow(), Ok(()), "shift {shift} seed {seed}");
            t.mutate(PageMutant::DropWanted);
            assert!(
                t.check_shadow().is_err(),
                "shift {shift} seed {seed}: a pass dropping a page it wants answers the same"
            );
        }
    }
}
