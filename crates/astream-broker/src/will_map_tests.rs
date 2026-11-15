// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The latest-will map (`BrokerLog::durable_latest_wills`, aterm F19) held to the read-back it
//! replaced (`BrokerLog::latest_wills_read_back`: the wills `<log>.state` carried, then every
//! retained `/a/will` record read back from the tier, in offset order).
//!
//! - Over random logs written through the real writer (wills registered, replaced by a later
//!   registration, fired, deduped by a publish under their own key and fenced by a later one,
//!   a few aimed at a hidden subject; publishes and batches; retirements; plain cuts and cuts
//!   that carry state; clean and unclean stops), sealed and plain, at residency budgets of 0
//!   and 16 MiB, the map answers what the read-back answers after every step, `stats` counts
//!   the pending wills the read-back holds, and every reopen's map holds the wills the live
//!   log's held.
//! - At a budget of 0, `stats` and the will queries read no record back, while the read-back
//!   reads every retained will.
//! - NEGATIVE CONTROL: a cut that leaves the map as it was (`WILLS_UNCUT`) is caught on
//!   every seed.

use super::*;
use crate::test_scratch::Scratch;

/// xorshift64*: the tests' deterministic PRNG.
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

const KEY: [u8; 32] = [0x6b; 32];
/// The residency budgets: the newest record alone, and the 16 MiB aterm's broker opens with.
const BUDGETS: [usize; 2] = [0, 16 << 20];
const SEEDS: u64 = 16;
const STEPS: usize = 150;
/// The producers the random logs write under.
const PRODUCERS: u64 = 4;

/// How a seed's log is held.
#[derive(Clone, Copy, Debug)]
struct Shape {
    sealed: bool,
    budget: usize,
}

fn shape_of(seed: u64) -> Shape {
    Shape {
        sealed: cfg!(feature = "at-rest") && seed % 4 >= 2,
        budget: BUDGETS[(seed % 2) as usize],
    }
}

fn open(path: &Path, shape: Shape) -> BrokerLog {
    let mut opts = OpenOptions::new(Durability::Relaxed);
    opts.resident_budget = Some(shape.budget);
    let key = if shape.sealed { Some(KEY) } else { None };
    BrokerLog::open_core(
        Storage::Os(path),
        &opts,
        false,
        key,
        AntiRollbackMode::Off,
        BrokerLog::prepare_nothing,
    )
    .map(|(log, _)| log)
    .unwrap_or_else(|e| panic!("open {shape:?}: {e}"))
}

/// One producer's latest will as the map holds it, and its settled flag where an open
/// derives it from retained records alone (`None` for a will carried below the base, whose
/// flag a live log took from records a cut has since dropped).
type Held = (u64, Offset, WillRecord, Option<bool>);

/// The map's wills by producer, and the producers each visible target's set names.
fn held(log: &BrokerLog) -> (Vec<Held>, Vec<(String, Vec<u64>)>) {
    let mut wills: Vec<Held> = Vec::new();
    for (&pid, e) in &log.durable_latest_wills {
        let settled = if e.offset.0 >= log.base.0 {
            Some(e.settled_above)
        } else {
            None
        };
        wills.push((pid, e.offset, e.will.clone(), settled));
    }
    wills.sort_unstable_by_key(|h| h.0);
    let mut targets: Vec<(String, Vec<u64>)> = Vec::new();
    for (subject, pids) in &log.durable_wills_by_subject {
        let mut pids: Vec<u64> = pids.iter().copied().collect();
        pids.sort_unstable();
        targets.push((subject.clone(), pids));
    }
    targets.sort_unstable();
    (wills, targets)
}

/// Where the map and the read-back part on `log`, if they do.
fn differs(log: &BrokerLog) -> Option<String> {
    let map = log.latest_wills();
    let back = log.latest_wills_read_back();
    if map != back {
        return Some(format!("the map holds {map:?}\nthe read-back {back:?}"));
    }
    let mut pending = 0usize;
    for (_, w) in &back {
        if log.will_unsettled(w) {
            pending += 1;
        }
    }
    let counted = log.stats().pending_wills;
    if counted != pending {
        return Some(format!(
            "stats counts {counted} pending wills, the read-back {pending}"
        ));
    }
    None
}

/// What a seed's run met.
#[derive(Debug, Default)]
struct Met {
    reopens: usize,
    cuts: usize,
    /// Cuts after which the map held fewer wills than before.
    dropping_cuts: usize,
    /// Cuts after which a producer's latest will was an older one, which an earlier cut
    /// carried and a plain cut, which rewrites no `<log>.state`, left in it.
    older_back: usize,
}

/// Producer `pid`'s latest will, as the log answers it.
fn latest_of(log: &BrokerLog, pid: u64) -> Option<WillRecord> {
    log.pending_wills()
        .into_iter()
        .find(|w| w.producer_id == pid)
}

/// A cut to a random floor (the head's when `to_head`), plain (which a will or binding below
/// it may refuse) or carrying state, counted in `met`.
#[cfg(feature = "retention")]
fn cut(log: &mut BrokerLog, rng: &mut Rng, to_head: bool, met: &mut Met) -> Result<(), String> {
    let before: HashMap<u64, Offset> = log
        .durable_latest_wills
        .iter()
        .map(|(&pid, e)| (pid, e.offset))
        .collect();
    let span = log.head().0 - log.base().0;
    let floor = if to_head {
        log.head()
    } else {
        Offset(log.base().0 + rng.below(span + 1))
    };
    if !to_head && rng.below(2) == 0 {
        let _ = log.retain_before(floor);
    } else {
        log.retain_before_carrying_state(floor)
            .map_err(|e| format!("a carrying cut to {}: {e}", floor.0))?;
    }
    met.cuts += 1;
    if log.durable_latest_wills.len() < before.len() {
        met.dropping_cuts += 1;
    }
    let older = log
        .durable_latest_wills
        .iter()
        .any(|(pid, e)| match before.get(pid) {
            Some(was) => e.offset < *was,
            None => false,
        });
    if older {
        met.older_back += 1;
    }
    Ok(())
}

/// Runs seed `seed`'s log; `Err` names the first step after which the map and the read-back
/// part, or a reopen's map differs from the live log's.
fn run(seed: u64, shape: Shape) -> Result<Met, String> {
    let root = Scratch::new(&format!("will-map-{seed}"));
    let path = root.path().join("log");
    let mut rng = Rng::new(seed);
    let mut log = open(&path, shape);
    let mut next_seq = [0u64; PRODUCERS as usize];
    let mut met = Met::default();
    for step in 0..STEPS {
        let roll = rng.below(100);
        let pid = 1 + rng.below(PRODUCERS);
        let slot = (pid - 1) as usize;
        let what = if roll < 22 {
            next_seq[slot] += 1 + rng.below(2);
            let body = vec![step as u8; rng.below(200) as usize];
            log.publish(
                pid,
                next_seq[slot],
                format!("/f/will/s{}", rng.below(4)),
                body,
            )
            .map_err(|e| format!("step {step}: publish: {e}"))?;
            "publish"
        } else if roll < 30 {
            for _ in 0..1 + rng.below(8) {
                let p = 1 + rng.below(PRODUCERS);
                let s = (p - 1) as usize;
                next_seq[s] += 1;
                let _ = log.stage_publish(
                    p,
                    next_seq[s],
                    format!("/f/will/b{}", rng.below(3)),
                    vec![3u8; 40],
                );
            }
            log.commit_batch()
                .map_err(|e| format!("step {step}: batch: {e}"))?;
            "batch"
        } else if roll < 48 {
            // Its key lies above every seq its producer published, so a later publish may
            // land on it (a dedup) or past it (a fence); a second registration replaces it.
            let subject = if rng.below(12) == 0 {
                COMMIT_SUBJECT.to_string()
            } else {
                format!("/f/will/t{}", rng.below(3))
            };
            let will = WillRecord {
                producer_id: pid,
                producer_seq: next_seq[slot] + 1 + rng.below(3),
                subject,
                body: vec![9u8; rng.below(40) as usize],
            };
            if log.stage_will_register(&will).is_ok() {
                log.commit_batch()
                    .map_err(|e| format!("step {step}: will: {e}"))?;
            }
            "register"
        } else if roll < 55 {
            if let Some(w) = latest_of(&log, pid) {
                if log.stage_will_fire(w).is_ok() {
                    log.commit_batch()
                        .map_err(|e| format!("step {step}: fire: {e}"))?;
                }
            }
            "fire"
        } else if roll < 60 {
            if let Some(w) = latest_of(&log, pid) {
                next_seq[slot] = next_seq[slot].max(w.producer_seq);
                log.publish(pid, w.producer_seq, "/f/will/key".to_string(), vec![1u8; 8])
                    .map_err(|e| format!("step {step}: publish under a will's key: {e}"))?;
            }
            "publish under a will's key"
        } else if roll < 65 {
            let kind = if rng.below(2) == 0 { 's' } else { 't' };
            let _ = log.retire_subject(pid, &format!("/f/will/{kind}{}", rng.below(4)));
            "retire"
        } else if roll < 78 {
            #[cfg(feature = "retention")]
            {
                cut(&mut log, &mut rng, false, &mut met)
                    .map_err(|e| format!("step {step}: {e}"))?;
            }
            "cut"
        } else if roll < 88 {
            let live = held(&log);
            if rng.below(2) == 0 {
                log.close_clean()
                    .map_err(|e| format!("step {step}: close: {e}"))?;
            }
            drop(log);
            log = open(&path, shape);
            met.reopens += 1;
            let reopened = held(&log);
            if reopened != live {
                return Err(format!(
                    "step {step}: the reopen holds {reopened:?}\nthe live log held {live:?}"
                ));
            }
            "reopen"
        } else {
            next_seq[slot] += 1;
            log.publish(
                pid,
                next_seq[slot],
                format!("/f/will/t{}", rng.below(3)),
                vec![2u8; 16],
            )
            .map_err(|e| format!("step {step}: publish on a will's target: {e}"))?;
            "publish on a target"
        };
        if let Some(d) = differs(&log) {
            return Err(format!("step {step} ({what}): {d}"));
        }
    }
    // Every seed ends with a will its own key settles, cut away under a carrying cut: the
    // map must lose it, as the read-back does.
    #[cfg(feature = "retention")]
    {
        let pid = PRODUCERS;
        let slot = (pid - 1) as usize;
        let will = WillRecord {
            producer_id: pid,
            producer_seq: next_seq[slot] + 1,
            subject: "/f/will/last".to_string(),
            body: b"gone".to_vec(),
        };
        log.stage_will_register(&will)
            .map_err(|e| format!("the last will: {e:?}"))?;
        log.commit_batch()
            .map_err(|e| format!("the last will: {e}"))?;
        log.publish(
            pid,
            will.producer_seq,
            "/f/will/key".to_string(),
            vec![1u8; 8],
        )
        .map_err(|e| format!("the last will's key: {e}"))?;
        cut(&mut log, &mut rng, true, &mut met)?;
        if let Some(d) = differs(&log) {
            return Err(format!("the last cut: {d}"));
        }
    }
    let live = held(&log);
    drop(log);
    let log = open(&path, shape);
    let reopened = held(&log);
    if reopened != live {
        return Err(format!(
            "the last reopen holds {reopened:?}\nthe live log held {live:?}"
        ));
    }
    differs(&log).map_or(Ok(met), |d| Err(format!("the last reopen: {d}")))
}

#[test]
fn the_latest_will_map_answers_as_the_read_back_over_random_logs() {
    let mut total = Met::default();
    for seed in 0..SEEDS {
        let shape = shape_of(seed);
        match run(seed, shape) {
            Ok(met) => {
                total.reopens += met.reopens;
                total.cuts += met.cuts;
                total.dropping_cuts += met.dropping_cuts;
                total.older_back += met.older_back;
            }
            Err(e) => panic!("seed {seed} {shape:?}: {e}"),
        }
    }
    // The seeds met what the map is maintained across: reopens and, with retention, cuts
    // that dropped wills from it besides each seed's last, and plain cuts that left a
    // producer an older will an earlier cut carried.
    assert!(total.reopens > 0, "the seeds met too little: {total:?}");
    if cfg!(feature = "retention") {
        assert!(
            total.dropping_cuts > SEEDS as usize && total.older_back > 0,
            "the seeds met too little: {total:?}"
        );
    }
}

/// NEGATIVE CONTROL: a cut that leaves the map as it was holds, after it, a will the log no
/// longer has, which the read-back does not; every seed catches it.
#[cfg(feature = "retention")]
#[test]
fn a_map_a_cut_leaves_as_it_was_is_caught_on_every_seed() {
    WILLS_UNCUT.with(|m| m.set(true));
    let mut caught = 0u64;
    for seed in 0..SEEDS {
        if run(seed, shape_of(seed)).is_err() {
            caught += 1;
        }
    }
    WILLS_UNCUT.with(|m| m.set(false));
    assert_eq!(caught, SEEDS, "every seed catches a map no cut updates");
}

/// At a budget of 0, every retained will cold, `stats` and the will queries read none of them
/// back, where the read-back reads each (the counter's own control).
#[test]
fn stats_and_the_will_queries_read_no_will_back_at_a_budget_of_zero() {
    const WILLS: u64 = 40;
    let root = Scratch::new("will-map-cold");
    let path = root.path().join("log");
    let shape = Shape {
        sealed: false,
        budget: 0,
    };
    let mut log = open(&path, shape);
    for k in 0..WILLS {
        let pid = 100 + k;
        let will = WillRecord {
            producer_id: pid,
            producer_seq: 10,
            subject: format!("/f/will/cold/{k}"),
            body: b"gone".to_vec(),
        };
        log.stage_will_register(&will).unwrap();
        log.commit_batch().unwrap();
        // Every other will is settled by a publish under its key.
        if k % 2 == 0 {
            log.publish(pid, 10, "/f/will/cold/key".to_string(), vec![1u8; 8])
                .unwrap();
        }
        for i in 0..50u64 {
            log.publish(
                1,
                k * 50 + i + 1,
                "/f/will/cold/filler".to_string(),
                vec![7u8; 64],
            )
            .unwrap();
        }
    }
    log.close_clean().unwrap();
    drop(log);
    let log = open(&path, shape);
    assert_eq!(log.residency().0, 1, "the newest record alone is resident");
    log.reset_cold_reads();
    let stats = log.stats();
    assert_eq!(stats.pending_wills, (WILLS / 2) as usize);
    assert_eq!(log.pending_wills().len(), WILLS as usize);
    #[cfg(feature = "retention")]
    assert_eq!(
        log.retention_blocker(log.head().0).map(|(off, _)| off),
        Some(log.latest_wills()[1].0 .0),
        "the lowest pending will holds the floor"
    );
    assert_eq!(
        log.cold_reads(),
        0,
        "stats and the will queries read a record back"
    );
    let back = log.latest_wills_read_back();
    assert_eq!(back, log.latest_wills());
    assert_eq!(
        log.cold_reads(),
        WILLS,
        "the read-back reads every retained will"
    );
}
