// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Evidence for `broker.retention-rules`' exported planning: in a test or debug build
//! `retention::plan`, its `View` and `Plan`, the held record, `oldest`, `stamp`,
//! `prune_stamps`, `clamp_stamps`, `carried_since` and the `Ledger` are pub, so a simulation of the broker
//! plans every cut as the broker's tick does (aterm's deterministic fabric simulation).
//! Never a cargo feature: the gate is `debug_assertions`, so this file is empty in a
//! release build.
//!
//! The test plans each tick by the export, on the records the log itself holds and a held
//! store applied as the broker's applies a plan (records carried and given up, floors
//! raised), and requires the log's own tick (`BrokerLog::retain_by_rules`) to take the same
//! cut, carry and give up as many records, lose the same records of the same subjects, and
//! leave every filter's oldest offset and every fetch where the export's plan says.
//!
//! NEGATIVE CONTROL: a plan taken at an earlier clock than the tick's (here the day before
//! the age rules bite) differs from what the tick did, so the comparison is not vacuous; and
//! the ticks are required to cut, carry, release read mail and give up records by age and
//! by bytes, so a fixture that exercised none of it fails.
#![cfg(all(feature = "retention", debug_assertions))]

use super::aterm_fixture::{scaled, ATERM_RETAIN};
use astream_broker::retention::{self, Held, Plan, Stamps, View};
use astream_broker::{BrokerLog, BrokerRecord, Retention};
use astream_wire::{Filter, Offset};
use std::collections::{BTreeMap, HashMap};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

static CTR: AtomicU64 = AtomicU64::new(0);

const DAY_MS: u64 = 24 * 60 * 60 * 1000;
const EV: &str = "/f/F/pub/n1/s1/ev";
const PRESENCE: &str = "/f/F/pub/n1/s1/presence";
const NODE_MAIL: &str = "/f/F/in/n1/s1/n2/note";
const PERSON_MAIL: &str = "/f/F/in/p/h-x/n1/ask";
const HALT: &str = "/f/F/halt/h-x";
const INBOX: &str = "/f/F/cur/n1/node/inbox";

/// Removes the log and every `<log>.*` sidecar when dropped.
struct Cleanup(std::path::PathBuf);

impl Drop for Cleanup {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
        let (Some(dir), Some(name)) = (self.0.parent(), self.0.file_name()) else {
            return;
        };
        let prefix = format!("{}.", name.to_string_lossy());
        for entry in std::fs::read_dir(dir).into_iter().flatten().flatten() {
            if entry.file_name().to_string_lossy().starts_with(&prefix) {
                let _ = std::fs::remove_file(entry.path());
            }
        }
    }
}

/// aterm's four rules (aterm-link `broker_rules::default_rules`, read from
/// `tests/fixtures/aterm-broker.retain`), at bytes a few records reach.
fn rules() -> Retention {
    scaled(ATERM_RETAIN, 900, 700, 4096)
}

/// THE HELD STORE AS A SIMULATION KEEPS IT: what the broker's applies of each plan (its
/// records carried and given up, its subjects' floors raised), and the stamps.
struct Mirror {
    base: u64,
    held: BTreeMap<u64, Held>,
    floors: BTreeMap<String, u64>,
    floor_max: u64,
    since: Vec<u64>,
    stamps: Stamps,
    groups: HashMap<String, u64>,
}

impl Mirror {
    fn new(rules: &Retention) -> Mirror {
        Mirror {
            base: 0,
            held: BTreeMap::new(),
            floors: BTreeMap::new(),
            floor_max: 0,
            since: retention::carried_since(None, &[], rules, 0),
            stamps: Stamps::new(),
            groups: HashMap::new(),
        }
    }

    /// The export's plan of the tick at `now` on `log`: its stamps taken first, as the
    /// tick takes them. `stamped` keeps them (the tick's own), else they are put back.
    fn plan(&mut self, log: &BrokerLog, rules: &Retention, now: u64, stamped: bool) -> Plan {
        let before = self.stamps.clone();
        retention::stamp(&mut self.stamps, log.head().0, now);
        let records: Vec<Arc<BrokerRecord>> = log.read_range(Offset(self.base), usize::MAX);
        let record_bts: Vec<Option<u64>> =
            records.iter().map(|r| log.record_bt_ms(r.seq)).collect();
        let view = View {
            base: self.base,
            ceiling: log.head().0,
            records: &records,
            record_bts: &record_bts,
            stamps: &self.stamps,
            groups: &self.groups,
            held: &self.held,
            now,
        };
        let plan = retention::plan(rules, &view, None);
        if !stamped {
            self.stamps = before;
        }
        plan
    }

    /// Apply `plan` as the held store does when its job lands.
    fn apply(&mut self, plan: Plan) {
        for off in &plan.remove {
            self.held.remove(off);
        }
        for h in plan.carry {
            self.held.insert(h.rec.seq.0, h);
        }
        for (subject, floor) in plan.floors {
            let f = self.floors.entry(subject).or_insert(0);
            *f = (*f).max(floor);
            self.floor_max = self.floor_max.max(*f);
        }
        self.base = self.base.max(plan.cut);
        retention::prune_stamps(&mut self.stamps, self.base);
    }

    fn oldest(&self, rules: &Retention, filter: &Filter) -> u64 {
        retention::oldest(
            Some(rules),
            self.base,
            &self.since,
            &self.floors,
            0,
            self.floor_max,
            filter,
        )
    }
}

/// What each tick did, summed, so a fixture that exercised nothing fails.
#[derive(Default)]
struct Seen {
    cuts: u32,
    carried: usize,
    released: usize,
    lost: u64,
    aged: u64,
    bytes: u64,
}

/// One tick at `now`: the export's plan, then the log's own tick, compared.
fn tick(log: &mut BrokerLog, m: &mut Mirror, rules: &Retention, now: u64, seen: &mut Seen) {
    let plan = m.plan(log, rules, now, true);
    let base_before = log.base().0;
    let t = log.retain_by_rules(now).unwrap();
    assert_eq!(t.base_before, base_before);
    assert_eq!(t.base, plan.cut, "the tick's cut is the plan's (now={now})");
    assert_eq!(t.carried, plan.carry.len(), "carried (now={now})");
    assert_eq!(t.released, plan.remove.len(), "released (now={now})");
    let mut lost: BTreeMap<String, u64> = BTreeMap::new();
    for ((subject, why), n) in &plan.lost {
        *lost.entry(subject.clone()).or_insert(0) += n;
        match why {
            retention::Why::Read => {}
            retention::Why::Aged => seen.aged += n,
            retention::Why::Bytes => seen.bytes += n,
        }
    }
    let lost: Vec<(String, u64)> = lost.into_iter().collect();
    assert_eq!(t.lost, lost, "lost (now={now})");
    if plan.cut > base_before {
        seen.cuts += 1;
    }
    seen.carried += plan.carry.len();
    seen.released += plan.remove.len();
    seen.lost += lost.iter().map(|(_, n)| n).sum::<u64>();
    m.apply(plan);
    assert_eq!(log.base().0, m.base);
    for f in [
        EV,
        PRESENCE,
        NODE_MAIL,
        PERSON_MAIL,
        HALT,
        "/f/F/in/>",
        "/f/>",
    ] {
        let filter = Filter::new(f).unwrap();
        let oldest = m.oldest(rules, &filter);
        assert_eq!(log.oldest(&filter).0, oldest, "{f}'s oldest (now={now})");
        // What a fetch from the oldest reads: the held records the filter matches, then the
        // retained ones.
        let (page, _) = log.fetch(oldest, &filter, usize::MAX, usize::MAX, log.head().0);
        let got: Vec<u64> = page.iter().map(|r| r.seq.0).collect();
        let retained = log.read_range(Offset(m.base), usize::MAX);
        let want: Vec<u64> = m
            .held
            .range(oldest..)
            .map(|(&o, h)| (o, &h.rec))
            .chain(retained.iter().map(|r| (r.seq.0, r)))
            .filter(|(o, r)| {
                *o >= oldest
                    && !astream_broker::store::is_hidden_subject(&r.subject)
                    && filter.matches_str(&r.subject)
            })
            .map(|(o, _)| o)
            .collect();
        assert_eq!(got, want, "{f}'s fetch from {oldest} (now={now})");
    }
}

fn publish(log: &mut BrokerLog, seq: &mut u64, subject: &str, body: &str) -> u64 {
    *seq += 1;
    log.publish(7, *seq, subject.to_string(), body.as_bytes().to_vec())
        .unwrap()
        .0
         .0
}

#[test]
fn the_exported_plan_is_the_ticks() {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!("asret_planner_{}_{n}.log", std::process::id()));
    let _cleanup = Cleanup(path.clone());
    let rules = rules();
    let mut log = BrokerLog::open(&path).unwrap();
    log.set_retention(rules.clone()).unwrap();
    let mut m = Mirror::new(&rules);
    let mut seen = Seen::default();
    let mut seq = 0u64;
    let t0 = 1_000_000;

    // Day 0: a stream, presence, a halt, a node's mail and a person's.
    let mut node_mail = Vec::new();
    for i in 0..6 {
        publish(
            &mut log,
            &mut seq,
            EV,
            &format!("ev {i} {}", "x".repeat(60)),
        );
        publish(&mut log, &mut seq, PRESENCE, &format!("live {i}"));
        node_mail.push(publish(&mut log, &mut seq, NODE_MAIL, &format!("note {i}")));
    }
    publish(&mut log, &mut seq, HALT, "state=on");
    publish(&mut log, &mut seq, PERSON_MAIL, "ask 0");
    tick(&mut log, &mut m, &rules, t0, &mut seen);

    // Day 2: the node reads its first three mails; more stream and mail.
    let upto = node_mail[2];
    log.commit(INBOX.to_string(), upto).unwrap();
    m.groups.insert(INBOX.to_string(), upto);
    for i in 6..14 {
        publish(
            &mut log,
            &mut seq,
            EV,
            &format!("ev {i} {}", "y".repeat(60)),
        );
        node_mail.push(publish(&mut log, &mut seq, NODE_MAIL, &format!("note {i}")));
    }
    tick(&mut log, &mut m, &rules, t0 + 2 * DAY_MS, &mut seen);

    // Day 3: more mail than the mail class's bytes hold, unread.
    for i in 14..30 {
        node_mail.push(publish(
            &mut log,
            &mut seq,
            NODE_MAIL,
            &format!("note {i} {}", "z".repeat(20)),
        ));
        publish(&mut log, &mut seq, EV, &format!("ev {i}"));
    }
    tick(&mut log, &mut m, &rules, t0 + 3 * DAY_MS, &mut seen);

    // NEGATIVE CONTROL: the plan of day 6, where no age rule bites, is not what the tick of
    // day 8 does.
    publish(&mut log, &mut seq, EV, "ev late");
    let early = m.plan(&log, &rules, t0 + 6 * DAY_MS, false);

    // Day 8: past the week, the day-0 records age out.
    let late = m.plan(&log, &rules, t0 + 8 * DAY_MS, false);
    assert!(
        early.cut != late.cut || early.remove != late.remove || early.lost.len() != late.lost.len(),
        "the day-6 plan is the day-8 one: the comparison would hold for any clock"
    );
    tick(&mut log, &mut m, &rules, t0 + 8 * DAY_MS, &mut seen);

    // Day 9: the node reads everything; what it read goes.
    let upto = *node_mail.last().unwrap();
    log.commit(INBOX.to_string(), upto).unwrap();
    m.groups.insert(INBOX.to_string(), upto);
    publish(&mut log, &mut seq, EV, "ev last");
    tick(&mut log, &mut m, &rules, t0 + 9 * DAY_MS, &mut seen);

    assert!(seen.cuts >= 2, "the ticks cut {} times", seen.cuts);
    assert!(seen.carried > 0, "nothing carried");
    assert!(seen.released > 0, "no held record released");
    assert!(seen.aged > 0, "nothing aged out");
    assert!(seen.bytes > 0, "nothing given up for its class's bytes");
    assert!(seen.lost > 0, "no unread record lost");
}
