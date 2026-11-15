// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! The retention rules' own tests (`retention.rs`): the rules and their checks, Hello's
//! encoding of them, the rules file's lines, the filter overlap a floor is found by, the
//! reader templates, the stamps, and the planning on hand-built views — no file, no clock.
//!
//! NEGATIVE CONTROLS (each a planted break, scratch-reverted, that fails the test named):
//! an overlap that answers `false` for two filters sharing a subject
//! (`filters_overlap_is_sound`); a cut that a hold rule's records hold back
//! (`a_hold_rule_never_holds_the_cut`); a class's bytes not counted from its newest record
//! (`the_cut_keeps_the_newest_records_within_the_prefix_bytes`); a read that does not
//! expand the template (`a_record_every_reader_read_is_released_and_one_unread_is_carried`);
//! a class past its bytes cut back to exactly them
//! (`a_class_past_its_bytes_gives_up_at_least_a_quarter_of_them`); every class reset to the
//! base by a rules change (`a_rules_change_keeps_each_class_whole_from_where_it_was`).

use super::*;
use crate::brecord::GroupCommit;
use astream_wire::Offset;
use std::collections::BTreeMap;
use std::sync::Arc;

const EV: &str = "/f/F/pub/n1/s1/ev";
const MAIL: &str = "/f/F/in/n1/from/a";
const PRESENCE: &str = "/f/F/pub/n1/s1/presence";

fn rec(seq: u64, subject: &str, body: &[u8]) -> Arc<BrokerRecord> {
    Arc::new(BrokerRecord {
        seq: Offset(seq),
        producer_id: 1,
        producer_seq: seq,
        subject: subject.to_string(),
        body: body.to_vec(),
        commit: None,
    })
}

/// A fabric's rules: the bulk stream the prefix, mail held until its node's inbox group
/// reads it or for a day, presence by its last value, everything else by its last value.
fn fabric(ev_bytes: Option<u64>, mail_bytes: Option<u64>) -> Retention {
    let mut ev = Rule::prefix("/f/F/pub/*/*/ev").unwrap();
    if let Some(b) = ev_bytes {
        ev = ev.max_bytes(b);
    }
    let mut mail = Rule::hold("/f/F/in/>")
        .unwrap()
        .max_age(Duration::from_secs(86_400))
        .until_read("/f/{2}/cur/{4}/node/inbox")
        .unwrap();
    if let Some(b) = mail_bytes {
        mail = mail.max_bytes(b);
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

struct V {
    records: Vec<Arc<BrokerRecord>>,
    stamps: Stamps,
    groups: HashMap<String, u64>,
    held: BTreeMap<u64, Held>,
}

impl V {
    fn new(subjects: &[&str]) -> V {
        let records = subjects
            .iter()
            .enumerate()
            .map(|(i, s)| rec(i as u64, s, b"body"))
            .collect();
        V {
            records,
            stamps: Vec::new(),
            groups: HashMap::new(),
            held: BTreeMap::new(),
        }
    }

    fn view(&self, now: u64) -> View<'_> {
        View {
            base: 0,
            ceiling: self.records.len() as u64,
            records: &self.records,
            record_bts: &[],
            stamps: &self.stamps,
            groups: &self.groups,
            held: &self.held,
            now,
        }
    }
}

#[test]
fn filters_overlap_is_sound() {
    for (a, b, want) in [
        ("/f/F/pub/*/*/ev", "/f/F/pub/n1/s1/ev", true),
        ("/f/F/pub/*/*/ev", "/f/F/>", true),
        ("/f/F/pub/*/*/ev", "/f/F/in/>", false),
        ("/f/F/in/>", "/f/F/in/n1/from/a", true),
        ("/f/F/in/>", "/f/F/in", false),
        ("/f/F/pub/*/*/ev", "/f/F/pub/*/*/presence", false),
        ("/>", "/x", true),
        ("/a/*", "/a/b/c", false),
        ("/a/>", "/a/*/c", true),
    ] {
        assert_eq!(filters_overlap(a, b), want, "{a} vs {b}");
        assert_eq!(filters_overlap(b, a), want, "{b} vs {a}");
    }
    // SOUND: every pair of filters that share a subject overlaps.
    let subjects = ["/f/F/pub/n1/s1/ev", "/f/F/in/n1/from/a", "/x", "/a/b/c"];
    let filters = [
        "/f/F/pub/*/*/ev",
        "/f/F/>",
        "/f/F/in/>",
        "/>",
        "/a/*/c",
        "/a/b/>",
        "/x",
        "/f/*/in/*/from/a",
    ];
    for s in subjects {
        for a in filters {
            for b in filters {
                let fa = Filter::new(a).unwrap();
                let fb = Filter::new(b).unwrap();
                if fa.matches_str(s) && fb.matches_str(s) {
                    assert!(filters_overlap(a, b), "{a} and {b} share {s}");
                }
            }
        }
    }
}

#[test]
fn a_reader_template_names_the_subjects_segments() {
    assert_eq!(
        expand("/f/{2}/cur/{4}/node/inbox", MAIL).as_deref(),
        Some("/f/F/cur/n1/node/inbox")
    );
    assert_eq!(expand("/g/{9}", MAIL), None, "too few segments: no group");
    assert!(Rule::hold("/f/F/in/>")
        .unwrap()
        .until_read("/f/{0}")
        .is_err());
    assert!(Rule::hold("/f/F/in/>")
        .unwrap()
        .until_read("/f/{x}")
        .is_err());
    assert!(Rule::hold("/f/F/in/>")
        .unwrap()
        .until_read("no-slash")
        .is_err());
}

#[test]
fn the_rules_are_checked() {
    let ev = || Rule::prefix("/f/F/pub/*/*/ev").unwrap();
    assert!(
        Retention::new(vec![], Rule::default_hold()).is_err(),
        "no prefix"
    );
    assert!(
        Retention::new(vec![ev(), ev()], Rule::default_hold()).is_err(),
        "two prefixes"
    );
    assert!(
        Retention::new(vec![ev().last_only()], Rule::default_hold()).is_err(),
        "a prefix that keeps the last value only"
    );
    assert!(
        Retention::new(vec![ev()], Rule::hold("/x").unwrap()).is_err(),
        "a default with a filter"
    );
    assert!(Rule::prefix("not a filter").is_err());
    let r = Retention::new(vec![ev()], Rule::default_hold()).unwrap();
    assert_eq!(r.class_of(EV), 0);
    assert_eq!(r.class_of(MAIL), 1, "the default class");
    assert_eq!(
        r.class_of("/a/commit"),
        1,
        "a hidden subject is the default's"
    );
}

#[test]
fn hellos_entry_round_trips_the_rules() {
    let r = fabric(Some(1 << 28), Some(64 << 20));
    let b = r.encode();
    assert_eq!(Retention::decode(&b), Some(r.clone()));
    let mut cut = b.clone();
    cut.pop();
    assert_eq!(Retention::decode(&cut), None, "cut short");
    let mut long = b;
    long.push(0);
    assert_eq!(Retention::decode(&long), None, "a byte past the rules");
}

#[test]
fn a_rules_file_line_reads_as_its_rule() {
    let (d, r) = parse_rule_line("prefix age=7d bytes=256MiB /f/F/pub/*/*/ev").unwrap();
    assert!(!d);
    assert_eq!(
        r,
        Rule::prefix("/f/F/pub/*/*/ev")
            .unwrap()
            .max_age(Duration::from_secs(7 * 86_400))
            .max_bytes(256 << 20)
    );
    let (_, r) =
        parse_rule_line("hold age=7d bytes=64MiB read=/f/{2}/cur/{4}/node/inbox /f/F/in/>")
            .unwrap();
    assert_eq!(r.readers(), ["/f/{2}/cur/{4}/node/inbox".to_string()]);
    let (_, r) = parse_rule_line("hold last /f/F/pub/*/*/presence").unwrap();
    assert_eq!(r.keep(), Keep::Last);
    let (d, r) = parse_rule_line("default age=7d bytes=32MiB").unwrap();
    assert!(d && r.filter().is_none() && r.bytes() == Some(32 << 20));
    for bad in [
        "",
        "prefix",
        "keep /x",
        "hold age=7y /x",
        "hold bytes=1TB /x",
        "hold size=1 /x",
    ] {
        assert!(parse_rule_line(bad).is_err(), "{bad:?}");
    }
}

/// A RULES FILE reads as its retention: comments and blank lines skipped, the default line
/// taken wherever it stands, the default rule's last value without one; a second default,
/// a bad line (named by its number), a file with no prefix rule, and one past
/// [`MAX_RULES`] are refused.
#[test]
fn a_rules_file_reads_as_its_retention() {
    let r = parse_rules(
        "# the fabric's rules\n\
         prefix age=7d bytes=256MiB /f/F/pub/*/*/ev\n\
         \n\
         default age=7d bytes=32MiB\n\
         \thold age=7d bytes=64MiB read=/f/{2}/cur/{4}/node/inbox /f/F/in/>  \n\
         hold last /f/F/pub/*/*/presence\n",
    )
    .unwrap();
    assert_eq!(r.rules().len(), 3);
    assert_eq!(r.rules()[1].filter(), Some("/f/F/in/>"));
    assert_eq!(r.default_rule().bytes(), Some(32 << 20));
    let r = parse_rules("prefix /f/F/pub/*/*/ev\n").unwrap();
    assert_eq!(r.default_rule(), &Rule::default_hold());
    let two = "prefix /x/>\ndefault\ndefault last\n";
    assert_eq!(
        parse_rules(two).unwrap_err(),
        "line 3: a second default rule"
    );
    assert!(parse_rules("prefix /x/>\nhold size=1 /y\n")
        .unwrap_err()
        .starts_with("line 2: "));
    assert!(parse_rules("hold /y\n").is_err(), "no prefix rule");
    let mut long = String::from("prefix /x/>\n");
    for i in 0..MAX_RULES {
        long.push_str(&format!("hold /y{i}\n"));
    }
    assert_eq!(
        parse_rules(&long).unwrap_err(),
        format!("line {}: more than {MAX_RULES} rules", MAX_RULES + 1)
    );
}

/// THE HEADROOM a planning leaves: the least, over the classes that bound bytes, of what
/// the class may still take — its retained records above the cut and its held ones both —
/// so a broker's writer can ask for a tick the moment some class may be past its bytes,
/// and not before. No bounded class: none.
#[test]
fn the_planning_says_what_the_tightest_class_has_left() {
    let rb = record_bytes(&rec(0, EV, b"body"));
    let mb = record_bytes(&rec(0, MAIL, b"body"));
    // The prefix keeps 3 of its 4 ev records, and has room for none more.
    let rules = fabric(Some(3 * rb), Some(5 * mb));
    let v = V::new(&[EV, MAIL, EV, EV, MAIL, EV]);
    let p = plan(&rules, &v.view(0), None);
    assert_eq!(p.cut, 1);
    assert_eq!(p.headroom, 0, "the prefix is at its bytes");
    assert_eq!(p.room[..2], [0, 3 * mb], "each class's own room");
    assert_eq!(p.room[2..], [u64::MAX, u64::MAX], "no bytes bound: no room");
    let rules = fabric(Some(10 * rb), Some(5 * mb));
    let p = plan(&rules, &v.view(0), None);
    assert_eq!(p.cut, 0);
    assert_eq!(p.headroom, 3 * mb, "the mail class: 2 of 5 in the suffix");
    assert_eq!(p.room[0], 6 * rb, "the prefix: 4 of 10");
    // Two mails held below a base of 2, three ev records retained above it.
    let mut v = V::new(&[]);
    v.records = (2..5u64).map(|off| rec(off, EV, b"body")).collect();
    for off in [0u64, 1] {
        v.held.insert(
            off,
            Held {
                rec: rec(off, MAIL, b"body"),
                at_ms: 0,
                bt_ms: None,
            },
        );
    }
    let mut view = v.view(0);
    view.base = 2;
    view.ceiling = 5;
    let p = plan(&rules, &view, None);
    assert_eq!(p.cut, 2);
    assert_eq!(p.headroom, 3 * mb, "held mail counts against its class");
    let p = plan(&fabric(None, None), &view, None);
    assert_eq!(p.headroom, u64::MAX, "no class bounds bytes");
}

#[test]
fn a_stamp_never_makes_a_record_older_than_it_is() {
    let mut s = Stamps::new();
    stamp(&mut s, 10, 1_000);
    stamp(&mut s, 20, 2_000);
    stamp(&mut s, 20, 3_000);
    stamp(&mut s, 25, 500);
    assert_eq!(s, vec![(10, 1_000), (20, 2_000), (25, 2_000)], "never back");
    assert_eq!(stamped_at(&s, 9, 9_999), 1_000);
    assert_eq!(stamped_at(&s, 10, 9_999), 2_000);
    assert_eq!(stamped_at(&s, 30, 9_999), 9_999, "not yet seen: now");
    for i in 0..(STAMPS_MAX as u64 * 2) {
        stamp(&mut s, 100 + i, 10_000 + i);
    }
    assert!(s.len() <= STAMPS_MAX);
    // Merged into the LATER stamp: a record reads younger, never older.
    for w in s.windows(2) {
        assert!(w[0].0 < w[1].0 && w[0].1 <= w[1].1);
    }
    prune_stamps(&mut s, 5_000);
    assert!(s.first().unwrap().0 > 5_000);
}

/// THE CUT: walking from the newest, the record that takes the prefix class past its bytes
/// puts the cut just above it, whatever the other classes hold.
#[test]
fn the_cut_keeps_the_newest_records_within_the_prefix_bytes() {
    let rb = record_bytes(&rec(0, EV, b"body"));
    let rules = fabric(Some(3 * rb), None);
    let v = V::new(&[EV, EV, PRESENCE, EV, EV, EV, EV]);
    let p = plan(&rules, &v.view(0), None);
    assert_eq!(p.cut, 4, "the newest three ev records are 4, 5 and 6");
    assert_eq!(p.kept[0], 3 * rb);
    assert!(
        p.carry.is_empty(),
        "presence is carried by its Last row only"
    );
}

/// A CLASS PAST ITS BYTES GIVES UP AT LEAST A QUARTER OF THEM, so it has that much room,
/// less what it was past them by, before it asks for the next cut: the bulk stream one
/// record past its 20 records' bytes keeps 16 and has 4 of room; far past them (250) it
/// keeps exactly its 20; and a hold class one mail past its 8 mails' bytes gives up its two
/// oldest. NC: a class cut back to exactly its bytes keeps 20 of the 21 with no room left.
#[test]
fn a_class_past_its_bytes_gives_up_at_least_a_quarter_of_them() {
    let rb = record_bytes(&rec(0, EV, b"body"));
    let mb = record_bytes(&rec(0, MAIL, b"body"));
    let rules = fabric(Some(20 * rb), Some(8 * mb));
    let v = V::new(&[EV; 21]);
    let p = plan(&rules, &v.view(0), None);
    assert_eq!((p.cut, p.kept[0], p.room[0]), (5, 16 * rb, 4 * rb));
    let v = V::new(&[EV; 250]);
    let p = plan(&rules, &v.view(0), None);
    assert_eq!((p.cut, p.kept[0], p.room[0]), (230, 20 * rb, 0));
    let mut v = V::new(&[EV]);
    v.records = vec![rec(20, EV, b"body")];
    for off in 0..9u64 {
        v.held.insert(
            off,
            Held {
                rec: rec(off, MAIL, b"body"),
                at_ms: 0,
                bt_ms: None,
            },
        );
    }
    let mut view = v.view(0);
    view.base = 20;
    view.ceiling = 21;
    let p = plan(&rules, &view, None);
    assert_eq!(p.remove, vec![0, 1], "the two oldest mails");
    assert_eq!(
        p.room[1], mb,
        "a quarter, less the mail it was past them by"
    );
}

/// A HOLD RULE NEVER HOLDS THE CUT: one unread mail below the bulk stream's cut is carried
/// in the held store, and the cut goes past it.
#[test]
fn a_hold_rule_never_holds_the_cut() {
    let rb = record_bytes(&rec(0, EV, b"body"));
    let rules = fabric(Some(2 * rb), None);
    let v = V::new(&[EV, MAIL, EV, EV, EV, EV]);
    let p = plan(&rules, &v.view(0), None);
    assert_eq!(p.cut, 4);
    assert_eq!(
        p.carry.iter().map(|h| h.rec.seq.0).collect::<Vec<_>>(),
        vec![1],
        "the mail is carried"
    );
}

/// A record every reader its rule names has read is released (and its subject's floor
/// rises past it, untold); one some reader has not read is carried.
#[test]
fn a_record_every_reader_read_is_released_and_one_unread_is_carried() {
    let rb = record_bytes(&rec(0, EV, b"body"));
    let rules = fabric(Some(rb), None);
    let mut v = V::new(&[MAIL, "/f/F/in/n2/from/a", EV, EV]);
    v.groups.insert("/f/F/cur/n1/node/inbox".into(), 0);
    v.groups.insert("/f/F/cur/n2/node/inbox".into(), 0);
    let p = plan(&rules, &v.view(0), None);
    assert_eq!(p.cut, 3);
    assert_eq!(
        p.carry.iter().map(|h| h.rec.seq.0).collect::<Vec<_>>(),
        vec![1],
        "n2's group has not read its mail at 1"
    );
    assert_eq!(
        p.floors.get(MAIL),
        Some(&1),
        "n1's read mail: the floor past it"
    );
    assert!(p.lost.is_empty(), "a read record is not lost");
}

/// A held record past its age is given up and told; one past the class's bytes, the
/// oldest first, likewise.
#[test]
fn a_held_class_gives_up_its_oldest_by_age_and_by_bytes() {
    let mb = record_bytes(&rec(0, MAIL, b"body"));
    let rules = fabric(None, Some(2 * mb));
    let mut v = V::new(&[EV]);
    for (off, at) in [(10u64, 0u64), (11, 50), (12, 60), (13, 70)] {
        v.held.insert(
            off,
            Held {
                rec: rec(off, MAIL, b"body"),
                at_ms: at,
                bt_ms: None,
            },
        );
    }
    let mut v_base = v.view(86_400_000 + 10);
    v_base.base = 20;
    v_base.ceiling = 20;
    v_base.records = &[];
    let p = plan(&rules, &v_base, None);
    assert_eq!(
        p.remove,
        vec![10, 11],
        "10 aged; 11 the oldest past the bytes"
    );
    assert_eq!(p.floors.get(MAIL), Some(&12));
    assert_eq!(p.lost.get(&(MAIL.to_string(), Why::Aged)), Some(&1));
    assert_eq!(p.lost.get(&(MAIL.to_string(), Why::Bytes)), Some(&1));
}

/// The floor a read of a filter answers: the base for what the prefix rule can match, the
/// matching subjects' floors for a hold class, the greatest across what a filter reaches.
#[test]
fn oldest_is_the_floor_of_what_the_filter_reaches() {
    let rules = fabric(None, None);
    let mut floors = BTreeMap::new();
    floors.insert(MAIL.to_string(), 7u64);
    let o = |f: &str| {
        oldest(
            Some(&rules),
            100,
            &[0; 4],
            &floors,
            0,
            7,
            &Filter::new(f).unwrap(),
        )
    };
    assert_eq!(o("/f/F/pub/*/*/ev"), 100);
    assert_eq!(o("/f/F/in/n1/>"), 7);
    assert_eq!(o("/f/F/in/n2/>"), 0, "no floor of n2's");
    assert_eq!(o("/f/F/>"), 100, "the greatest of what it reaches");
    assert_eq!(
        o("/f/F/pub/*/*/presence"),
        100,
        "a last-value class: the base"
    );
    assert_eq!(
        oldest(
            None,
            100,
            &[],
            &floors,
            0,
            7,
            &Filter::new("/f/F/in/>").unwrap()
        ),
        100,
        "no rules: the base"
    );
    assert_eq!(
        oldest(
            Some(&rules),
            100,
            &[40; 4],
            &floors,
            0,
            7,
            &Filter::new("/f/F/in/n2/>").unwrap()
        ),
        40,
        "from where the rules took effect"
    );
    assert_eq!(
        oldest(
            Some(&rules),
            100,
            &[0; 4],
            &floors,
            9,
            9,
            &Filter::new("/f/F/in/n2/>").unwrap()
        ),
        9,
        "the spill"
    );
}

/// A RULES CHANGE KEEPS EACH CLASS WHOLE FROM WHERE IT WAS: the mail class with only its
/// bounds retuned keeps its old start; a hold class new to the rules, or one over subjects
/// the old prefix or a last-value rule kept (dropped below the base, not carried), starts at
/// the base; a keep-all default whose old rules all stay named keeps its start (its subjects
/// are a subset of the old default's); and with no old rules everything starts at the base.
/// NC: every class reset to the base fails the first.
#[test]
fn a_rules_change_keeps_each_class_whole_from_where_it_was() {
    let old = fabric(Some(1 << 20), Some(1 << 20));
    let since = [2u64, 5, 2, 2];
    let retuned = fabric(Some(2 << 20), Some(4 << 20));
    assert_eq!(
        carried_since(Some(&old), &since, &retuned, 9)[1],
        5,
        "the mail class, its bounds retuned"
    );
    let mut rules: Vec<Rule> = old.rules().to_vec();
    rules.push(Rule::hold("/f/F/x/>").unwrap());
    rules.push(Rule::hold("/f/F/pub/>").unwrap());
    let added = Retention::new(rules, Rule::default_keeping_all()).unwrap();
    let got = carried_since(Some(&old), &since, &added, 9);
    assert_eq!(got[1], 5);
    assert_eq!(got[3], 9, "a class new to the rules");
    assert_eq!(
        got[4], 9,
        "over what the prefix and a last-value rule dropped"
    );
    assert_eq!(got[5], 9, "the default: the old one kept only last values");
    let all = |default: Rule| {
        let mut rules: Vec<Rule> = old.rules().to_vec();
        rules.truncate(2);
        Retention::new(rules, default).unwrap()
    };
    let before = all(Rule::default_keeping_all());
    let mut rules: Vec<Rule> = before.rules().to_vec();
    rules.push(Rule::hold("/f/F/x/>").unwrap());
    let after = Retention::new(rules, Rule::default_keeping_all()).unwrap();
    assert_eq!(
        carried_since(Some(&before), &[0, 4, 6], &after, 9)[3],
        6,
        "a keep-all default whose old rules all stay named"
    );
    assert_eq!(carried_since(None, &[], &retuned, 9), vec![9; 4]);
}

/// Where each rule's `keep` byte stands in Hello's entry `b` (`Retention::encode`'s layout).
fn keep_bytes_at(b: &[u8]) -> Vec<usize> {
    let u16_at = |at: usize| usize::from(u16::from_le_bytes([b[at], b[at + 1]]));
    let mut out = Vec::new();
    let mut at = 1usize;
    for _ in 0..b[0] {
        out.push(at + 1);
        at += 2 + 8 + 8;
        at += 2 + u16_at(at);
        let readers = b[at];
        at += 1;
        for _ in 0..readers {
            at += 2 + u16_at(at);
        }
    }
    assert_eq!(at, b.len(), "the walk read the whole entry");
    out
}

/// A FORGETTING RULE (`Rule::forgetting`) in each form a rule takes: the rules file's
/// `forget` word, wherever it stands among the options, reads as the builder's rule; Hello's
/// entry (and the held store's `R` frame, which is the same encoding) carries it and reads
/// it back, the default rule's too, as bit 1 of the `keep` byte; rules that forget nothing
/// encode as before the bit (`keep` 0 or 1), so an older decoder reads them, and one byte
/// that names a bit no build writes, or keeps the last value and forgets, is refused. A
/// rule that keeps the last value only and forgets is refused by `Retention::new`, by a
/// rules file's line (named) and by a decoder.
#[test]
fn a_forgetting_rule_reads_encodes_and_decodes_and_never_keeps_the_last_value() {
    let mail = Rule::hold("/f/*/in/>")
        .unwrap()
        .until_read("/f/{2}/cur/{4}/node/inbox")
        .unwrap()
        .until_read("/f/{2}/cur/n-carry/node/carry")
        .unwrap()
        .forgetting()
        .max_age(Duration::from_secs(7 * 86_400))
        .max_bytes(64 << 20);
    assert!(mail.forgets() && mail.keep() == Keep::All);
    assert!(
        !Rule::hold("/f/*/in/>").unwrap().forgets(),
        "off by default"
    );
    let (_, r) = parse_rule_line(
        "hold read=/f/{2}/cur/{4}/node/inbox read=/f/{2}/cur/n-carry/node/carry forget \
         age=7d bytes=64MiB /f/*/in/>",
    )
    .unwrap();
    assert_eq!(r, mail);
    let (_, r) = parse_rule_line(
        "hold forget age=7d bytes=64MiB read=/f/{2}/cur/{4}/node/inbox \
         read=/f/{2}/cur/n-carry/node/carry /f/*/in/>",
    )
    .unwrap();
    assert_eq!(r, mail, "the word stands anywhere among the options");
    let (d, r) = parse_rule_line("default forget age=7d").unwrap();
    assert!(d && r.forgets() && r.keep() == Keep::All);

    let ev = || Rule::prefix("/f/*/pub/*/*/ev").unwrap();
    let presence = || Rule::hold("/f/*/pub/*/*/presence").unwrap().last_only();
    let forgetting = Retention::new(
        vec![ev(), presence(), mail.clone()],
        Rule::default_keeping_all().forgetting(),
    )
    .unwrap();
    let b = forgetting.encode();
    let back = Retention::decode(&b).expect("rules that forget read back");
    assert_eq!(back, forgetting);
    assert!(back.rules()[2].forgets() && back.default_rule().forgets());
    assert!(!back.rules()[0].forgets() && !back.rules()[1].forgets());
    assert!(back.forgets("/f/F/in/n1/s1/n2/task") && !back.forgets("/f/F/pub/n/s/presence"));
    assert!(back.forgets_any());

    // The keep bytes, rule by rule: ev keeps all (0), presence its last value (1), the mail
    // and the default rule keep all and forget (2).
    let plain = Retention::new(
        vec![
            ev(),
            presence(),
            Rule::hold("/f/*/in/>")
                .unwrap()
                .until_read("/f/{2}/cur/{4}/node/inbox")
                .unwrap(),
        ],
        Rule::default_keeping_all(),
    )
    .unwrap();
    assert!(!plain.forgets_any());
    let keeps = |r: &Retention| -> Vec<u8> {
        let b = r.encode();
        keep_bytes_at(&b).into_iter().map(|at| b[at]).collect()
    };
    assert_eq!(
        keeps(&plain),
        vec![0, 1, 0, 0],
        "no rule forgets: as before"
    );
    assert_eq!(keeps(&forgetting), vec![0, 1, 2, 2]);

    // The mail rule's keep byte, rewritten: last and forget (3), and bits no build writes.
    let at = keep_bytes_at(&b)[2];
    assert_eq!(b[at], 2, "the mail rule's keep byte");
    for bad in [3u8, 4, 6, 0x80] {
        let mut x = b.clone();
        x[at] = bad;
        assert_eq!(Retention::decode(&x), None, "keep byte {bad:#x}");
    }
    let mut x = b;
    x[at] = 0;
    let unforgetting = Retention::decode(&x).unwrap();
    assert!(
        !unforgetting.rules()[2].forgets(),
        "bit 1 is the whole flag"
    );

    // Last and forget, refused everywhere a rule is checked.
    let both = Rule::hold("/f/*/pub/*/*/presence")
        .unwrap()
        .last_only()
        .forgetting();
    let e = Retention::new(vec![ev(), both], Rule::default_hold()).unwrap_err();
    assert!(
        e.to_string()
            .contains("keeps the last value only and forgets"),
        "{e}"
    );
    assert!(
        Retention::new(vec![ev()], Rule::default_hold().forgetting()).is_err(),
        "the default rule that keeps the last value only"
    );
    for line in [
        "hold last forget /f/*/pub/*/*/presence",
        "hold forget last /f/*/pub/*/*/presence",
        "default last forget",
    ] {
        assert!(parse_rule_line(line).is_err(), "{line:?}");
    }
    assert_eq!(
        parse_rules("prefix /x/>\nhold last forget /y\n").unwrap_err(),
        "line 2: retention: the rule over \"/y\" keeps the last value only and forgets: a \
         subject's `Last` row is what it keeps, so only a rule that keeps every record forgets"
    );
}

/// A commit a record carries is counted in its bytes, as the frame holds it.
#[test]
fn record_bytes_is_the_plaintext_frame() {
    let mut r = (*rec(3, EV, b"body")).clone();
    let plain = record_bytes(&r);
    assert_eq!(
        plain as usize,
        astream_wire::HEADER_SIZE + r.encode_payload().unwrap().len()
    );
    r.commit = Some(GroupCommit {
        group: "g".into(),
        upto: 1,
    });
    assert_eq!(
        record_bytes(&r) as usize,
        astream_wire::HEADER_SIZE + r.encode_payload().unwrap().len()
    );
}

/// Summary-only planning (`plan_with` over `Planned` entries whose `whole()` is `None`)
/// calls `load(i)` ONLY for cold records a hold rule carries below `cut` — never for
/// prefix records, superseded last-value records, records at or above `cut`, read mail,
/// or aged mail — and fails closed (`cut == base`) if a carried record cannot be read.
#[test]
fn plan_with_reads_only_the_cold_records_a_cut_carries_and_refuses_an_unreadable_one() {
    struct ColdSum {
        off: u64,
        subject: String,
        bytes: u64,
    }
    impl Planned for ColdSum {
        fn offset(&self) -> u64 {
            self.off
        }
        fn subject(&self) -> &str {
            &self.subject
        }
        fn bytes(&self) -> u64 {
            self.bytes
        }
        fn whole(&self) -> Option<Arc<BrokerRecord>> {
            None
        }
    }

    let mail_n2 = "/f/F/in/n2/from/a";
    let pres_b = "/f/F/pub/n1/s2/presence";
    // Offsets 0..9:
    // 0: PRESENCE (last_only -> not held in <log>.held)
    // 1: MAIL n1 (read: group committed through 1 -> released without loading)
    // 2: PRESENCE (last_only -> not held in <log>.held)
    // 3: mail_n2 (aged -> given up without loading)
    // 4: mail_n2 (unread, fresh -> carried into <log>.held!)
    // 5: EV (pushes prefix past 1 EV's bytes -> cut lands just above it at 6)
    // 6: mail_n2 (at cut -> stays in retained suffix without loading)
    // 7: EV (newest EV -> kept in retained suffix)
    // 8: pres_b (above cut -> stays in retained suffix)
    let subjects = [
        PRESENCE, MAIL, PRESENCE, mail_n2, mail_n2, EV, mail_n2, EV, pres_b,
    ];
    let mut full = V::new(&subjects);
    let ev_one = record_bytes(&full.records[7]);
    let rules = fabric(Some(ev_one), None);
    let day_ms: u64 = 86_400 * 1_000;
    let now: u64 = 10 * day_ms;
    // Stamp offsets 0..4 at t=0 (so mail at offset 3 is aged past 1 day at `now`),
    // leaving offsets 4.. unstamped (`stamped_at` = `now`, fresh).
    stamp(&mut full.stamps, 4, 0);
    full.groups.insert("/f/F/cur/n1/node/inbox".into(), 1);

    let sums: Vec<ColdSum> = full
        .records
        .iter()
        .map(|r| ColdSum {
            off: r.seq.0,
            subject: r.subject.clone(),
            bytes: record_bytes(r),
        })
        .collect();

    let whole_plan = plan(&rules, &full.view(now), None);
    assert_eq!(
        whole_plan.cut, 6,
        "EV at 5 exceeds 1-record prefix budget, placing cut just above it at 6"
    );

    let cold_view = View {
        base: 0,
        ceiling: sums.len() as u64,
        records: &sums,
        record_bts: &[],
        stamps: &full.stamps,
        groups: &full.groups,
        held: &full.held,
        now,
    };
    let loaded = std::cell::RefCell::new(Vec::new());
    let cold_plan = plan_with(&rules, &cold_view, None, |i| {
        loaded.borrow_mut().push(i);
        full.records.get(i).cloned()
    });
    let mut loaded = loaded.into_inner();
    loaded.sort_unstable();
    assert_eq!(
        loaded,
        vec![4],
        "loads only the unread fresh Keep::All record below cut (offset 4)"
    );
    assert_eq!(cold_plan.cut, whole_plan.cut);
    fn carry_tup(p: &Plan) -> Vec<(&BrokerRecord, u64, Option<u64>)> {
        p.carry
            .iter()
            .map(|h| (&*h.rec, h.at_ms, h.bt_ms))
            .collect()
    }
    assert_eq!(carry_tup(&cold_plan), carry_tup(&whole_plan));
    assert_eq!(cold_plan.remove, whole_plan.remove);
    assert_eq!(cold_plan.floors, whole_plan.floors);
    assert_eq!(cold_plan.lost, whole_plan.lost);
    assert_eq!(cold_plan.kept, whole_plan.kept);
    assert_eq!(cold_plan.room, whole_plan.room);
    assert_eq!(cold_plan.headroom, whole_plan.headroom);

    // Byte-capped hold class: offset 6 (in the kept suffix) already fills a 1-record
    // mail budget, so offset 4 is given up by `Why::Bytes` without ever loading it.
    let byte_capped = fabric(Some(ev_one), Some(record_bytes(&full.records[6])));
    let bytes_loaded = std::cell::RefCell::new(Vec::new());
    let bytes_plan = plan_with(&byte_capped, &cold_view, None, |i| {
        bytes_loaded.borrow_mut().push(i);
        full.records.get(i).cloned()
    });
    assert!(bytes_loaded.into_inner().is_empty());
    assert!(bytes_plan.carry.is_empty());
    assert_eq!(
        bytes_plan.lost.get(&(mail_n2.to_string(), Why::Bytes)),
        Some(&1)
    );

    // NC: if a cold record a hold rule wants to carry cannot be read back, `plan_with`
    // refuses the cut (`cut == base`) rather than compacting past an unreadable hold.
    let refused = plan_with(&rules, &cold_view, None, |i| {
        if i == 4 {
            None
        } else {
            full.records.get(i).cloned()
        }
    });
    assert_eq!(refused.cut, 0, "unreadable carried record refuses cut");
    assert!(refused.carry.is_empty());
    assert!(refused.remove.is_empty());
    assert!(refused.lost.is_empty());
}
