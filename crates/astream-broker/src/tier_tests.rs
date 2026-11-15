// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The residency tier against the real log: with a budget that keeps only the newest
//! record decoded, every record read back from its frame equals the record written —
//! through the single-append path and the batch path, sealed at rest or not, across a
//! reopen, and across a retention cut that moves every kept frame.

use std::sync::Arc;

use astream_wire::Offset;

use crate::brecord::BrokerRecord;
use crate::store::{BrokerLog, Durability};

fn body(i: u64) -> Vec<u8> {
    // Bodies of varying length, so a wrong frame boundary cannot decode by luck.
    let n = 1 + (i as usize * 37) % 300;
    (0..n)
        .map(|k| (i as u8).wrapping_mul(31).wrapping_add(k as u8))
        .collect()
}

fn subject(i: u64) -> String {
    format!("/f/tier/s{}", i % 7)
}

fn check_all(log: &BrokerLog, from: u64, to: u64) {
    let got: Vec<Arc<BrokerRecord>> = log.read_from(Offset(from));
    assert_eq!(
        got.len() as u64,
        to - from,
        "every retained record reads back"
    );
    for (k, rec) in got.iter().enumerate() {
        let i = from + k as u64;
        assert_eq!(rec.seq, Offset(i));
        assert_eq!(rec.subject, subject(i));
        assert_eq!(rec.body, body(i));
    }
}

#[test]
fn cold_records_read_back_exactly_through_single_appends_and_reopen() {
    let root = crate::test_scratch::Scratch::new("tier-single");
    let path = root.path().join("log");
    {
        let mut log = BrokerLog::open_with(&path, Durability::Relaxed).unwrap();
        log.set_resident_budget(0);
        for i in 0..200u64 {
            log.publish(1, i, subject(i), body(i)).unwrap();
        }
        let (resident, _, retained) = log.residency();
        assert_eq!((resident, retained), (1, 200));
        check_all(&log, 0, 200);
        check_all(&log, 150, 200);
    }
    let mut log = BrokerLog::open_with(&path, Durability::Relaxed).unwrap();
    log.set_resident_budget(0);
    check_all(&log, 0, 200);
    // Appends after a reopen land at positions after the recovered prefix.
    for i in 200..230u64 {
        log.publish(1, i, subject(i), body(i)).unwrap();
    }
    check_all(&log, 0, 230);
}

#[test]
fn cold_records_read_back_exactly_through_the_batch_path() {
    let root = crate::test_scratch::Scratch::new("tier-batch");
    let path = root.path().join("log");
    let mut log = BrokerLog::open_with(&path, Durability::Relaxed).unwrap();
    log.set_resident_budget(1);
    let mut i = 0u64;
    for batch in 1..=12u64 {
        for _ in 0..batch {
            log.stage_publish(2, i, subject(i), body(i)).unwrap();
            i += 1;
        }
        log.commit_batch().unwrap();
    }
    check_all(&log, 0, i);
}

#[cfg(feature = "at-rest")]
#[test]
fn cold_records_read_back_exactly_when_sealed_at_rest() {
    const KEY: [u8; 32] = [0x5a; 32];
    let root = crate::test_scratch::Scratch::new("tier-sealed");
    let path = root.path().join("log");
    {
        let mut log = BrokerLog::open_encrypted(&path, KEY).unwrap();
        log.set_resident_budget(0);
        for i in 0..64u64 {
            log.publish(3, i, subject(i), body(i)).unwrap();
        }
        check_all(&log, 0, 64);
    }
    let mut log = BrokerLog::open_encrypted(&path, KEY).unwrap();
    log.set_resident_budget(0);
    check_all(&log, 0, 64);
}

#[cfg(feature = "retention")]
#[test]
fn cold_records_read_back_exactly_after_a_retention_cut() {
    let root = crate::test_scratch::Scratch::new("tier-retain");
    let path = root.path().join("log");
    let mut log = BrokerLog::open_with(&path, Durability::Strict).unwrap();
    log.set_resident_budget(0);
    for i in 0..120u64 {
        log.publish(4, i, subject(i), body(i)).unwrap();
    }
    log.retain_before(Offset(50)).unwrap();
    check_all(&log, 50, 120);
    for i in 120..140u64 {
        log.publish(4, i, subject(i), body(i)).unwrap();
    }
    check_all(&log, 50, 140);
    drop(log);
    let mut log = BrokerLog::open_with(&path, Durability::Strict).unwrap();
    log.set_resident_budget(0);
    check_all(&log, 50, 140);
}

#[test]
fn a_bounded_log_answers_last_and_fetch_like_an_unbounded_one() {
    let root = crate::test_scratch::Scratch::new("tier-parity");
    let (a, b) = (root.path().join("a"), root.path().join("b"));
    let mut bounded = BrokerLog::open_with(&a, Durability::Relaxed).unwrap();
    let mut full = BrokerLog::open_with(&b, Durability::Relaxed).unwrap();
    bounded.set_resident_budget(0);
    for i in 0..90u64 {
        bounded.publish(5, i, subject(i), body(i)).unwrap();
        full.publish(5, i, subject(i), body(i)).unwrap();
    }
    let filter = astream_wire::Filter::new("/f/tier/>").unwrap();
    let head = bounded.stats().head.0;
    for from in [0u64, 13, 44, 89] {
        let (pa, na) = bounded.fetch(from, &filter, 10, 100, head);
        let (pb, nb) = full.fetch(from, &filter, 10, 100, head);
        assert_eq!(na, nb);
        assert_eq!(pa, pb);
    }
    assert_eq!(bounded.read_from(Offset(0)), full.read_from(Offset(0)));
    for log in [&mut bounded, &mut full] {
        drop(log.publish_last_visible(head).unwrap());
    }
    let mut bounded_view = bounded.last_view_at(head).unwrap();
    let mut full_view = full.last_view_at(head).unwrap();
    assert_eq!(
        bounded
            .last_matching(&filter, "", 10, 100, &mut bounded_view)
            .unwrap()
            .into_page(),
        full.last_matching(&filter, "", 10, 100, &mut full_view)
            .unwrap()
            .into_page(),
    );
}

#[cfg(unix)]
#[test]
fn last_refuses_an_unreadable_retained_value_in_plain_and_retirement_overlay_views() {
    use std::os::unix::fs::FileExt as _;

    for overlay in [false, true] {
        let root = crate::test_scratch::Scratch::new("tier-last-unreadable");
        eprintln!(
            "Last unreadable overlay={overlay} world={}",
            root.path().display()
        );
        let path = root.path().join("log");
        let mut log = BrokerLog::open_with(&path, Durability::Strict).unwrap();
        log.set_resident_budget(0);
        for (seq, subject) in ["/f/tier/target", "/f/tier/retired", "/f/tier/newest"]
            .into_iter()
            .enumerate()
        {
            log.publish(7, seq as u64, subject.into(), body(seq as u64))
                .unwrap();
        }
        let head = log.head().0;
        drop(log.publish_last_visible(head).unwrap());
        let mut view = log.last_view_at(head).unwrap();
        if overlay {
            assert!(log.retire_subject(7, "/f/tier/retired").unwrap().is_some());
        }
        let filter = astream_wire::Filter::new("/f/tier/>").unwrap();
        let expected = log
            .last_matching(&filter, "", 10, 100, &mut view)
            .unwrap()
            .into_page()
            .unwrap();
        assert_eq!(
            expected.0.len(),
            3,
            "the old view includes the subsequently retired row"
        );
        assert_eq!(
            expected
                .0
                .iter()
                .find(|rec| rec.subject == "/f/tier/target")
                .unwrap()
                .seq,
            Offset(0)
        );
        assert_eq!(
            !view.overlay.is_empty(),
            overlay,
            "exercise both actual index branches"
        );
        assert_eq!(log.residency().0, 1);

        let at = log.frame_at_for_test(0).unwrap() + 16;
        let file = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .open(&path)
            .unwrap();
        let mut original = [0; 4];
        file.read_exact_at(&mut original, at).unwrap();
        let changed = original.map(|byte| byte ^ 0xff);
        file.write_all_at(&changed, at).unwrap();
        file.sync_all().unwrap();
        let error = match log.last_matching(&filter, "", 10, 100, &mut view) {
            Err(error) => error,
            Ok(_) => panic!("unreadable retained Last record was answered successfully"),
        };
        assert_eq!(
            error,
            crate::LastViewError::UnreadableRetained { offset: 0 },
            "retained damage cannot become an empty page or an older carried value"
        );
        file.write_all_at(&original, at).unwrap();
        file.sync_all().unwrap();
        let recovered = log
            .last_matching(&filter, "", 10, 100, &mut view)
            .unwrap()
            .into_page()
            .unwrap();
        assert_eq!(
            recovered, expected,
            "the same owned view recovers only after the actual frame is readable"
        );
    }
}

#[cfg(unix)]
#[test]
fn last_wire_refuses_cold_damage_and_recovers_the_actual_retained_value() {
    use std::os::unix::fs::FileExt as _;

    let root = crate::test_scratch::Scratch::new("tier-last-wire-unreadable");
    eprintln!("Last wire unreadable world={}", root.path().display());
    let path = root.path().join("log");
    let sock = root.path().join("sock");
    let mut opts = crate::OpenOptions::new(Durability::Strict);
    opts.resident_budget = Some(0);
    let broker = crate::Broker::open_opts(&path, opts, || Ok(crate::Prepared::Nothing)).unwrap();
    let mut handle = broker.serve(&sock).unwrap();
    let mut client = crate::Client::connect(&sock).unwrap();
    let subject = "/f/F/pub/n-1/presence";
    client.publish(7, 0, subject, b"inc=41").unwrap();
    client.publish(7, 1, "/f/other", b"newest hot row").unwrap();
    assert_eq!(broker.residency().0, 1);
    let expected = client.last(subject, "", 8).unwrap().0;
    assert_eq!(expected, vec![(0, subject.into(), b"inc=41".to_vec())]);
    let at = broker.shared_log_frame_at_for_test(0).unwrap() + 16;
    let file = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .open(&path)
        .unwrap();
    let mut original = [0; 4];
    file.read_exact_at(&mut original, at).unwrap();
    file.write_all_at(&original.map(|byte| byte ^ 0xff), at)
        .unwrap();
    file.sync_all().unwrap();
    assert!(
        client.last(subject, "", 8).is_err(),
        "Last must refuse, not report missing presence"
    );
    let mut stamped = crate::Client::connect(&sock).unwrap();
    assert!(
        stamped.last_stamped(subject, "", 8).is_err(),
        "stamped Last cannot certify absence either"
    );
    file.write_all_at(&original, at).unwrap();
    file.sync_all().unwrap();
    let mut recovered = crate::Client::connect(&sock).unwrap();
    assert_eq!(recovered.last(subject, "", 8).unwrap().0, expected);
    drop(recovered);
    drop(stamped);
    drop(client);
    handle.shutdown();
}

#[cfg(all(unix, feature = "retention"))]
#[test]
fn a_known_pruned_last_value_remains_readable_from_carried_state_and_reopen() {
    use std::os::unix::fs::FileExt as _;
    let root = crate::test_scratch::Scratch::new("tier-last-carried");
    eprintln!("Last carried world={}", root.path().display());
    let path = root.path().join("log");
    let subject = "/f/tier/quiet";
    let mut log = BrokerLog::open_with(&path, Durability::Strict).unwrap();
    log.set_resident_budget(0);
    log.publish(7, 0, subject.into(), b"quiet retained state".to_vec())
        .unwrap();
    log.publish(7, 1, "/f/tier/newest".into(), b"newest".to_vec())
        .unwrap();
    assert_eq!(log.retain_before_carrying_state(Offset(1)).unwrap(), 1);
    for reopen in [false, true] {
        if reopen {
            drop(log);
            log = BrokerLog::open_with(&path, Durability::Strict).unwrap();
            log.set_resident_budget(0);
        }
        let head = log.head().0;
        drop(log.publish_last_visible(head).unwrap());
        let mut view = log.last_view_at(head).unwrap();
        let filter = astream_wire::Filter::new(subject).unwrap();
        let (rows, resume) = log
            .last_matching(&filter, "", 8, 100, &mut view)
            .unwrap()
            .into_page()
            .unwrap();
        assert_eq!(resume, None);
        assert_eq!(rows.len(), 1);
        assert_eq!(
            (
                rows[0].seq,
                rows[0].subject.as_str(),
                rows[0].body.as_slice()
            ),
            (Offset(0), subject, b"quiet retained state".as_slice())
        );
    }

    // A newer retained value supersedes the old carried value. Damage must not revive
    // that old value as if it were still current, including after physical compaction.
    log.publish(7, 2, subject.into(), b"newer retained state".to_vec())
        .unwrap();
    log.publish(
        7,
        3,
        "/f/tier/newest".into(),
        b"make the new value cold".to_vec(),
    )
    .unwrap();
    let head = log.head().0;
    drop(log.publish_last_visible(head).unwrap());
    let mut view = log.last_view_at(head).unwrap();
    let filter = astream_wire::Filter::new(subject).unwrap();
    let expected = log
        .last_matching(&filter, "", 8, 100, &mut view)
        .unwrap()
        .into_page()
        .unwrap();
    assert_eq!(expected.0.len(), 1);
    assert_eq!(expected.0[0].seq, Offset(2));
    let at = log.frame_at_for_test(1).unwrap() + 16; // base1: retained offset2 is index1.
    let file = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .open(&path)
        .unwrap();
    let mut original = [0; 4];
    file.read_exact_at(&mut original, at).unwrap();
    file.write_all_at(&original.map(|byte| byte ^ 0xff), at)
        .unwrap();
    file.sync_all().unwrap();
    match log.last_matching(&filter, "", 8, 100, &mut view) {
        Err(error) => assert_eq!(
            error,
            crate::LastViewError::UnreadableRetained { offset: 2 }
        ),
        Ok(_) => panic!("damaged newer retained value revived old carried state"),
    }
    file.write_all_at(&original, at).unwrap();
    file.sync_all().unwrap();
    assert_eq!(
        log.last_matching(&filter, "", 8, 100, &mut view)
            .unwrap()
            .into_page()
            .unwrap(),
        expected
    );
}

#[cfg(unix)]
#[test]
fn summary_filters_keep_fetch_stats_and_subscribe_from_reading_cold_non_matches() {
    let root = crate::test_scratch::Scratch::new("tier-summary-filter");
    let path = root.path().join("log");
    let sock = root.path().join("sock");
    let mut opts = crate::OpenOptions::new(Durability::Relaxed);
    opts.resident_budget = Some(0);
    let broker = crate::Broker::open_opts(&path, opts, || Ok(crate::Prepared::Nothing)).unwrap();
    let mut handle = broker.serve(&sock).unwrap();
    let mut cli = crate::Client::connect(&sock).unwrap();
    let needle = "/f/tier/needle";
    let needle_offsets = [17u64, 130, 289, 391];
    for i in 0..400u64 {
        let subj = if needle_offsets.contains(&i) {
            needle.to_string()
        } else {
            format!("/f/tier/noise/{}", i % 6)
        };
        let (off, deduped) = cli.publish(1, i + 1, &subj, &body(i)).unwrap();
        assert_eq!((off, deduped), (i, false));
    }
    // Append one hidden consumer-group commit at offset 400 so offset 391 is cold too.
    assert_eq!(cli.commit("/f/tier/grp", 10).unwrap(), 400);
    let (resident, _, retained) = broker.residency();
    assert_eq!((resident, retained), (1, 401));

    // 1) `Broker::stats` and wire `Client::stats` read summaries alone (0 cold reads).
    broker.reset_cold_reads();
    let st = broker.stats();
    assert_eq!(st.log.head, Offset(401));
    assert_eq!(st.visible_head, 401);
    let wire_st = cli.stats("/f/tier/>").unwrap();
    assert_eq!(wire_st.head, 401);
    assert_eq!(
        wire_st.faces.iter().map(|f| f.records).sum::<u64>(),
        400,
        "all 400 non-hidden records counted by face"
    );
    assert_eq!(
        broker.cold_reads(),
        0,
        "Broker::stats and wire Stats must decode zero cold frames"
    );

    // 2) `Fetch` on a narrow filter decodes only the 4 matching cold records.
    broker.reset_cold_reads();
    let (records, (next, head)) = cli.fetch(0, needle, 10).unwrap();
    assert_eq!((next, head), (401, 401));
    let got_offs: Vec<u64> = records.iter().map(|(o, _, _)| *o).collect();
    assert_eq!(got_offs, needle_offsets);
    for (o, s, b) in &records {
        assert_eq!(s, needle);
        assert_eq!(b, &body(*o));
    }
    assert_eq!(
        broker.cold_reads(),
        needle_offsets.len() as u64,
        "Fetch decoded only matching cold frames"
    );

    // 3) Multi-chunk `Subscribe` (`401 > TAIL_CHUNK = 256`) decodes only the 4 matching
    //    cold records and emits its caught-up mark only after reaching the head (401).
    broker.reset_cold_reads();
    let mut sub_cli = crate::Client::connect(&sock).unwrap();
    assert!(sub_cli.idle_marks().unwrap());
    let mut sub = sub_cli.subscribe(0, needle).unwrap();
    let mut delivered = Vec::new();
    let caught_up_next = loop {
        match sub.recv_event().unwrap().expect("open subscription") {
            crate::Event::Delivery {
                offset,
                subject: s,
                body: b,
            } => {
                assert_eq!(s, needle);
                assert_eq!(b, body(offset));
                delivered.push(offset);
            }
            crate::Event::Mark { next, head, .. } => {
                assert_eq!(
                    delivered, needle_offsets,
                    "caught-up mark must not fire before scanning all chunks to head"
                );
                assert_eq!(head, 401);
                break next;
            }
            crate::Event::Gap(g) => panic!("unexpected gap: {g:?}"),
        }
    };
    assert_eq!(caught_up_next, 401);
    assert_eq!(
        broker.cold_reads(),
        needle_offsets.len() as u64,
        "Subscribe decoded only matching cold frames across chunks"
    );
    drop(sub);

    // NC: a broad filter matching every non-hidden cold record DOES perform cold reads.
    broker.reset_cold_reads();
    let (broad_records, _) = cli.fetch(0, "/f/tier/>", 10).unwrap();
    assert_eq!(broad_records.len(), 10);
    assert_eq!(broker.cold_reads(), 10);

    drop(cli);
    handle.shutdown();
}

/// `Broker::stats` and `Broker::health`, which aterm's broker takes every 30 s under the log
/// lock, read no will back at a budget of 0: they count the pending wills from the log's
/// latest-will map, not from its `/a/will` records, every one of them cold here (aterm F19).
#[cfg(unix)]
#[test]
fn stats_and_health_read_no_retained_will_back_at_a_budget_of_zero() {
    let root = crate::test_scratch::Scratch::new("tier-stats-wills");
    let path = root.path().join("log");
    let sock = root.path().join("sock");
    let mut opts = crate::OpenOptions::new(Durability::Relaxed);
    opts.resident_budget = Some(0);
    let broker = crate::Broker::open_opts(&path, opts, || Ok(crate::Prepared::Nothing)).unwrap();
    let mut handle = broker.serve(&sock).unwrap();
    let mut wills = Vec::new();
    for k in 0..6u64 {
        let mut c = crate::Client::connect(&sock).unwrap();
        let seq = crate::will_seq(1).unwrap();
        c.will(100 + k, seq, &format!("/f/tier/will/{k}"), b"gone")
            .unwrap();
        wills.push(c);
    }
    // Three of the connections end, and their wills fire.
    wills.truncate(3);
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
    while broker.head() < 9 {
        assert!(
            std::time::Instant::now() < deadline,
            "three wills fired within a minute (head {})",
            broker.head()
        );
        std::thread::sleep(std::time::Duration::from_millis(1));
    }
    let mut cli = crate::Client::connect(&sock).unwrap();
    for i in 0..300u64 {
        cli.publish(1, i + 1, "/f/tier/noise", &body(i)).unwrap();
    }
    let (resident, _, retained) = broker.residency();
    assert_eq!((resident, retained), (1, 309));

    broker.reset_cold_reads();
    let st = broker.stats();
    assert_eq!(st.log.pending_wills, 3, "the three live connections' wills");
    let health = broker.health();
    assert_eq!((health.head, health.pending_wills), (309, 3));
    assert_eq!(
        broker.cold_reads(),
        0,
        "Broker::stats and Broker::health read a retained will back"
    );

    drop(cli);
    drop(wills);
    handle.shutdown();
}

#[cfg(feature = "retention")]
fn assert_rule_retention_parity(at_rest: Option<[u8; 32]>) {
    let tag = if at_rest.is_some() {
        "tier-rules-sealed"
    } else {
        "tier-rules-plain"
    };
    let root = crate::test_scratch::Scratch::new(tag);
    let (a, b) = (root.path().join("bounded"), root.path().join("full"));
    let open = |p: &std::path::Path, budget: Option<usize>| -> BrokerLog {
        let mut opts = crate::OpenOptions::new(Durability::Strict);
        opts.resident_budget = budget;
        #[cfg(feature = "at-rest")]
        if let Some(k) = at_rest {
            opts.at_rest_key = Some(k);
        }
        #[cfg(not(feature = "at-rest"))]
        let _ = at_rest;
        BrokerLog::open_opts(p, opts, || Ok(crate::Prepared::Nothing)).unwrap()
    };

    let mut bounded = open(&a, Some(0));
    let mut full = open(&b, None);

    let rules_of = || {
        crate::Retention::new(
            vec![
                crate::Rule::prefix("/f/F/pub/*/*/ev")
                    .unwrap()
                    .max_bytes(450),
                crate::Rule::hold("/f/F/in/>")
                    .unwrap()
                    .max_age(std::time::Duration::from_secs(86_400))
                    .until_read("/f/{2}/cur/{4}/node/inbox")
                    .unwrap(),
                crate::Rule::hold("/f/F/pub/*/*/presence")
                    .unwrap()
                    .last_only(),
            ],
            crate::Rule::default_hold(),
        )
        .unwrap()
    };
    bounded.set_retention(rules_of()).unwrap();
    full.set_retention(rules_of()).unwrap();

    let push_both =
        |bounded: &mut BrokerLog, full: &mut BrokerLog, seq: u64, s: &str, n: usize| -> Offset {
            let payload = vec![(seq as u8).wrapping_add(11); n];
            let (ob, fb) = bounded
                .publish(9, seq + 1, s.to_string(), payload.clone())
                .unwrap();
            let (of, ff) = full.publish(9, seq + 1, s.to_string(), payload).unwrap();
            assert_eq!((ob, fb), (of, ff));
            ob
        };

    // Under the prefix byte cap (`cut == base`): planning + tick read 0 cold frames.
    push_both(&mut bounded, &mut full, 0, "/f/F/pub/n1/s1/presence", 24);
    let n1_mail = push_both(&mut bounded, &mut full, 1, "/f/F/in/n1/from/a", 24);
    push_both(&mut bounded, &mut full, 2, "/f/F/pub/n1/s1/ev", 64);
    bounded.reset_cold_reads();
    let t_b = bounded.retain_by_rules(1_000).unwrap();
    let t_f = full.retain_by_rules(1_000).unwrap();
    assert_eq!((t_b.base, t_b.carried), (0, 0));
    assert_eq!(t_b.base, t_f.base);
    assert_eq!(
        bounded.cold_reads(),
        0,
        "tick with cut == base must read 0 cold frames"
    );

    // Commit n1's mail as read, add unread n2 mail, supersede presence, and push EV past
    // 450 bytes so the cut advances above them.
    bounded
        .commit("/f/F/cur/n1/node/inbox".to_string(), n1_mail.0)
        .unwrap();
    full.commit("/f/F/cur/n1/node/inbox".to_string(), n1_mail.0)
        .unwrap();
    let n2_mail = push_both(&mut bounded, &mut full, 3, "/f/F/in/n2/from/a", 32);
    push_both(&mut bounded, &mut full, 4, "/f/F/pub/n1/s1/presence", 28);
    for seq in 5..12u64 {
        push_both(&mut bounded, &mut full, seq, "/f/F/pub/n1/s1/ev", 90);
    }
    let tb1 = bounded.retain_by_rules(2_000).unwrap();
    let tf1 = full.retain_by_rules(2_000).unwrap();
    assert!(tb1.base > 5, "cut advanced into EV burst: {}", tb1.base);
    assert_eq!(
        (tb1.base, tb1.carried, tb1.released),
        (tf1.base, tf1.carried, tf1.released)
    );
    assert_eq!(
        tb1.carried, 1,
        "Keep::All carried unread n2 mail into <log>.held (presence carried in <log>.state)"
    );
    let pres_f = astream_wire::Filter::new("/f/F/pub/*/*/presence").unwrap();
    let hb = bounded.stats().head.0;
    let hf = full.stats().head.0;
    let _ = bounded.publish_last_visible(hb).unwrap();
    let _ = full.publish_last_visible(hf).unwrap();
    let mut vb = bounded.last_view_at(hb).unwrap();
    let mut vf = full.last_view_at(hf).unwrap();
    let crate::LastStep::Page(lb, None) =
        bounded.last_matching(&pres_f, "", 16, 64, &mut vb).unwrap()
    else {
        panic!("expected single LastStep::Page from bounded");
    };
    let crate::LastStep::Page(lf, None) = full.last_matching(&pres_f, "", 16, 64, &mut vf).unwrap()
    else {
        panic!("expected single LastStep::Page from full");
    };
    assert_eq!(lb.len(), 1, "latest presence carried below cut");
    assert_eq!(lb, lf);

    // Second tick after n2 reads its mail + another EV burst.
    bounded
        .commit("/f/F/cur/n2/node/inbox".to_string(), n2_mail.0)
        .unwrap();
    full.commit("/f/F/cur/n2/node/inbox".to_string(), n2_mail.0)
        .unwrap();
    for seq in 12..18u64 {
        push_both(&mut bounded, &mut full, seq, "/f/F/pub/n1/s1/ev", 90);
    }
    bounded.reset_cold_reads();
    let tb2 = bounded.retain_by_rules(3_000).unwrap();
    let tf2 = full.retain_by_rules(3_000).unwrap();
    assert!(tb2.dropped >= 6, "tb2 dropped EV prefix: {}", tb2.dropped);
    assert_eq!(
        bounded.cold_reads(),
        0,
        "steady-state prefix compaction with no newly carried records must decode 0 cold frames"
    );
    assert_eq!(
        (tb2.base, tb2.carried, tb2.released),
        (tf2.base, tf2.carried, tf2.released)
    );
    assert_eq!(tb2.released, 1, "read n2 mail released from <log>.held");

    for pat in [
        "/f/F/>",
        "/f/F/in/>",
        "/f/F/pub/*/*/presence",
        "/f/F/pub/*/*/ev",
    ] {
        let f = astream_wire::Filter::new(pat).unwrap();
        assert_eq!(bounded.oldest(&f), full.oldest(&f), "oldest({pat})");
        let head = bounded.stats().head.0;
        assert_eq!(
            bounded.fetch(0, &f, 64, 1024, head),
            full.fetch(0, &f, 64, 1024, head),
            "fetch({pat})"
        );
    }
    assert_eq!(bounded.read_from(Offset(0)), full.read_from(Offset(0)));

    drop(bounded);
    drop(full);
    let reopened = open(&a, Some(0));
    assert!(
        reopened.hot_capacity_for_test() <= 16,
        "reopened zero-budget log must not grow hot ring across recovered history"
    );
    let reopened_full = open(&b, None);
    let all = astream_wire::Filter::new("/f/F/>").unwrap();
    let head = reopened.stats().head.0;
    assert_eq!(reopened.base(), reopened_full.base());
    assert_eq!(
        reopened.fetch(0, &all, 64, 1024, head),
        reopened_full.fetch(0, &all, 64, 1024, head)
    );
    assert_eq!(
        reopened.read_from(Offset(0)),
        reopened_full.read_from(Offset(0))
    );
}

#[cfg(feature = "retention")]
#[test]
fn rule_retention_on_zero_resident_budget_matches_unbounded_and_reads_only_carried_records() {
    assert_rule_retention_parity(None);
    #[cfg(feature = "at-rest")]
    assert_rule_retention_parity(Some([0x3c; 32]));
}

#[cfg(unix)]
#[test]
fn unreadable_cold_record_stops_fetch_and_refuses_subscribe_and_fork_without_spinning() {
    use std::io::{Seek, SeekFrom, Write};

    let root = crate::test_scratch::Scratch::new("tier-unreadable");
    let path = root.path().join("log");
    let sock = root.path().join("sock");
    let mut opts = crate::OpenOptions::new(Durability::Strict);
    opts.resident_budget = Some(0);
    let broker = crate::Broker::open_opts(&path, opts, || Ok(crate::Prepared::Nothing)).unwrap();
    let mut handle = broker.serve(&sock).unwrap();
    let mut cli = crate::Client::connect(&sock).unwrap();

    // Offsets 0, 1, 3, 4, 5 match `/f/match`; offset 2 is `/f/other` (non-matching cold).
    let subjects = [
        "/f/match", "/f/match", "/f/other", "/f/match", "/f/match", "/f/match",
    ];
    for (i, s) in subjects.iter().enumerate() {
        let payload = vec![b'a' + i as u8; 48];
        cli.publish(7, i as u64, s, &payload).unwrap();
    }
    assert_eq!(broker.residency(), (1, broker.residency().1, 6));

    // Locate offset 3's frame start.
    let frame3_at = broker
        .shared_log_frame_at_for_test(3)
        .expect("frame 3 recorded");

    // Positive control before corruption: `ForkSubscribe` at cold non-matching offset 2
    // replaces `/f/other` with `/f/match` and delivers [0, 1, 2, 3, 4, 5].
    {
        let mut fork = crate::Client::connect(&sock)
            .unwrap()
            .fork_subscribe(2, "/f/match", b"swapped", "/f/match")
            .unwrap();
        let mut seen = Vec::new();
        while let Some((off, _s, b)) = fork.recv().unwrap() {
            seen.push((off, b));
        }
        let offs: Vec<u64> = seen.iter().map(|(o, _)| *o).collect();
        assert_eq!(offs, vec![0, 1, 2, 3, 4, 5]);
        assert_eq!(seen[2].1, b"swapped");
    }

    // Corrupt cold frame 3's payload bytes in place on disk after open.
    {
        let mut f = std::fs::OpenOptions::new().write(true).open(&path).unwrap();
        f.seek(SeekFrom::Start(frame3_at + 16)).unwrap();
        f.write_all(&[0xff, 0x00, 0xaa, 0x55]).unwrap();
        f.sync_all().unwrap();
    }

    // 1) `Fetch` delivers [0, 1] and stops with `next == 3` (never skips damaged 3 to 4, 5).
    let (records, (next, _head)) = cli.fetch(0, "/f/match", 10).unwrap();
    let fetch_offs: Vec<u64> = records.iter().map(|(o, _, _)| *o).collect();
    assert_eq!(fetch_offs, vec![0, 1]);
    assert_eq!(next, 3, "Fetch must stop before unreadable cold offset 3");

    // 2) `Subscribe` delivers [0, 1], emits NO false caught-up mark, and returns an
    //    explicit refusal naming offset 3 rather than spinning.
    let mut sub_cli = crate::Client::connect(&sock).unwrap();
    assert!(sub_cli.idle_marks().unwrap());
    let mut sub = sub_cli.subscribe(0, "/f/match").unwrap();
    let mut sub_offs = Vec::new();
    let sub_err = loop {
        match sub.recv_event() {
            Ok(Some(crate::Event::Delivery { offset, .. })) => sub_offs.push(offset),
            Ok(Some(crate::Event::Mark { next, head, .. })) => {
                panic!("premature caught-up mark ({next}/{head}) before unreadable cold frame")
            }
            Ok(Some(crate::Event::Gap(g))) => panic!("unexpected gap: {g:?}"),
            Ok(None) => panic!("unexpected clean EOF without refusal"),
            Err(e) => break e,
        }
    };
    assert_eq!(sub_offs, vec![0, 1]);
    let msg = sub_err.to_string();
    assert!(
        msg.contains("cold record at offset 3"),
        "expected refusal naming cold offset 3, got: {msg:?}"
    );
    drop(sub);

    // 3) `ForkSubscribe` delivers [0, 1] and refuses at offset 3 instead of closing its
    //    snapshot with a Mark as if [0, 1] were the whole log.
    let mut fork = crate::Client::connect(&sock)
        .unwrap()
        .fork_subscribe(5, "/f/match", b"alt", "/f/match")
        .unwrap();
    let mut fork_offs = Vec::new();
    let fork_err = loop {
        match fork.recv() {
            Ok(Some((off, _, _))) => fork_offs.push(off),
            Ok(None) => panic!("ForkSubscribe silently truncated snapshot at unreadable frame"),
            Err(e) => break e,
        }
    };
    assert_eq!(fork_offs, vec![0, 1]);
    assert!(
        fork_err.to_string().contains("cold record at offset 3"),
        "expected ForkSubscribe refusal naming offset 3, got: {fork_err:?}"
    );
    drop(fork);
    drop(cli);

    // 4) Shutdown joins cleanly with zero stuck/spinning tail threads.
    handle.shutdown();
}

#[test]
fn open_opts_and_set_resident_budget_bound_hot_ring_and_sharded_broker_tracks_residency() {
    let root = crate::test_scratch::Scratch::new("tier-open-cap");
    let path = root.path().join("log");
    {
        let mut log = BrokerLog::open(&path).unwrap();
        for i in 0..500u64 {
            log.publish(5, i + 1, format!("/f/cap/{}", i % 8), vec![b'z'; 64])
                .unwrap();
        }
        assert_eq!(log.residency().0, 500);
        assert!(log.hot_capacity_for_test() >= 500);
        log.set_resident_budget(0);
        assert_eq!(log.residency().0, 1);
        assert!(
            log.hot_capacity_for_test() <= 16,
            "set_resident_budget(0) must shrink hot VecDeque capacity, got {}",
            log.hot_capacity_for_test()
        );
    }

    // Reopening the 500-record log with `resident_budget = Some(0)` must build only the
    // hot suffix (never growing `tier.hot` to 500 slots during open).
    let mut opts = crate::OpenOptions::new(Durability::Strict);
    opts.resident_budget = Some(0);
    let reopened = BrokerLog::open_opts(&path, opts, || Ok(crate::Prepared::Nothing)).unwrap();
    assert_eq!((reopened.residency().0, reopened.residency().2), (1, 500));
    assert!(
        reopened.hot_capacity_for_test() <= 16,
        "open_opts(resident_budget = Some(0)) must keep hot VecDeque bounded, got {}",
        reopened.hot_capacity_for_test()
    );
    let all = reopened.read_from(Offset(0));
    assert_eq!(all.len(), 500);
    assert_eq!(all[0].seq, Offset(0));
    assert_eq!(all[499].seq, Offset(499));
    drop(reopened);

    // Multi-shard `ShardedBroker::open_opts`, `residency`, and `set_resident_budget`.
    let shard_dir = root.path().join("shards");
    let mut s_opts = crate::OpenOptions::new(Durability::Relaxed);
    s_opts.resident_budget = Some(0);
    let sb = crate::ShardedBroker::open_opts(&shard_dir, 4, s_opts).unwrap();
    let mut handle = sb.serve_tcp_loopback().unwrap();
    for s in 0..4usize {
        let addr = handle.tcp_addr(s).unwrap();
        let mut cli = crate::Client::connect_tcp(addr).unwrap();
        for i in 0..8u64 {
            cli.publish(
                11,
                (s as u64) * 100 + i + 1,
                &format!("/f/sh/{s}/{i}"),
                b"v",
            )
            .unwrap();
        }
    }
    let (res_recs, _res_bytes, ret_recs) = sb.residency();
    assert_eq!((res_recs, ret_recs), (4, 32));
    sb.set_resident_budget(usize::MAX);
    assert_eq!(sb.residency().0, 4);
    handle.shutdown();
    drop(sb);

    let mut reopen_opts = crate::OpenOptions::new(Durability::Relaxed);
    reopen_opts.resident_budget = Some(0);
    let sb2 = crate::ShardedBroker::open_opts(&shard_dir, 4, reopen_opts).unwrap();
    assert_eq!((sb2.residency().0, sb2.residency().2), (4, 32));
    let mut h2 = sb2.serve_tcp_loopback().unwrap();
    for s in 0..4usize {
        let mut cli = crate::Client::connect_tcp(h2.tcp_addr(s).unwrap()).unwrap();
        let (rows, _) = cli.fetch(0, "/f/sh/>", 16).unwrap();
        assert_eq!(rows.len(), 8);
    }
    h2.shutdown();
}

#[cfg(all(unix, feature = "retention"))]
#[test]
fn compaction_prunes_dropped_dedup_keys_and_skips_damaged_cold_prefix_payloads() {
    use std::io::{Seek, SeekFrom, Write};

    let root = crate::test_scratch::Scratch::new("tier-compact-dedup");
    let path = root.path().join("log");
    let mut opts = crate::OpenOptions::new(Durability::Strict);
    opts.resident_budget = Some(0);
    let mut log = BrokerLog::open_opts(&path, opts, || Ok(crate::Prepared::Nothing)).unwrap();

    // Seed 8 records on one subject (`producer_id = 21`, `producer_seq = 1..=8`).
    for seq in 1..=8u64 {
        let (off, dup) = log
            .publish(21, seq, "/f/ev".to_string(), vec![seq as u8; 48])
            .unwrap();
        assert_eq!((off, dup), (Offset(seq - 1), false));
    }
    // First carry-compaction to 2 charges `/f/ev` into `carried_charges` and leaves
    // offsets 2..8 (`producer_seq` 3..=8) on disk, with 2..7 cold and 7 hot.
    let d1 = log.retain_before_carrying_state(Offset(2)).unwrap();
    assert_eq!(d1, 2);

    // Corrupt cold offset 3 (`index == 1` above base 2)'s payload bytes on disk; its
    // 8-byte frame header length stays intact, and retention to `Offset(6)` drops 2..6.
    let bad_at = log.frame_at_for_test(1).expect("offset 3 frame start");
    {
        let mut f = std::fs::OpenOptions::new().write(true).open(&path).unwrap();
        f.seek(SeekFrom::Start(bad_at + 16)).unwrap();
        f.write_all(&[0xde, 0xad, 0xbe, 0xef]).unwrap();
        f.sync_all().unwrap();
    }

    log.reset_cold_reads();
    let d2 = log.retain_before_carrying_state(Offset(6)).unwrap();
    assert_eq!(d2, 4);
    assert_eq!(
        log.cold_reads(),
        0,
        "carrying cut across already-charged cold prefix must decode 0 dropped frames"
    );
    assert_eq!(log.base(), Offset(6));

    // Kept key `producer_seq = 7` (offset 6) still dedups; dropped key `producer_seq = 4`
    // (offset 3, below base 6) was pruned from `dedup` and appends at the head.
    let (kept_off, kept_dup) = log
        .publish(21, 7, "/f/ev".to_string(), vec![7u8; 48])
        .unwrap();
    assert_eq!((kept_off, kept_dup), (Offset(6), true));
    let (new_off, new_dup) = log
        .publish(21, 4, "/f/ev".to_string(), vec![4u8; 48])
        .unwrap();
    assert_eq!((new_off, new_dup), (Offset(8), false));
}

/// xorshift64*: a tiny deterministic PRNG for the packed tier's random streams.
struct Rng(u64);

impl Rng {
    fn below(&mut self, n: u64) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D) % n.max(1)
    }
}

/// Every retained record of `log` against what was published (`model`, by offset): read
/// back through the tier (from its frame start where the budget left it cold) equal to the
/// record, its summary the record's own (offset, subject, plaintext-frame bytes, hidden),
/// and the pages naming exactly the retained records' subjects.
fn check_packed(
    log: &BrokerLog,
    model: &std::collections::BTreeMap<u64, BrokerRecord>,
) -> Result<(), String> {
    let tier = log.tier_for_test();
    let base = log.base().0;
    let want: Vec<&BrokerRecord> = model.range(base..).map(|(_, r)| r).collect();
    if tier.len() != want.len() || log.head().0 != base + want.len() as u64 {
        return Err(format!(
            "retained {} records from {base} to {}, published {}",
            tier.len(),
            log.head().0,
            want.len()
        ));
    }
    for (i, rec) in want.iter().enumerate() {
        let got = log.record_arc(i);
        if got.as_deref() != Some(*rec) {
            return Err(format!("record {} reads back as {got:?}", base + i as u64));
        }
        let s = tier.summary(i).ok_or(format!("no summary at {i}"))?;
        let expect = (
            base + i as u64,
            rec.subject.as_str(),
            crate::brecord::plaintext_frame_bytes(rec),
            crate::store::is_hidden_record(rec),
        );
        if (s.offset(), s.subject(), s.bytes(), s.is_hidden()) != expect {
            return Err(format!("summary {i}: {s:?}, the record's {expect:?}"));
        }
    }
    let subjects: std::collections::BTreeSet<&str> =
        want.iter().map(|r| r.subject.as_str()).collect();
    if tier.live_subjects() != subjects.len() {
        return Err(format!(
            "{} subjects named, {} retained",
            tier.live_subjects(),
            subjects.len()
        ));
    }
    Ok(())
}

/// The filters the filtered reads of a [`packed_stream`] are checked with: one subject, one
/// batch subject, every subject and one no record names.
const PACKED_FILTERS: [&str; 4] = ["/f/packed/s3", "/f/packed/b1", "/f/packed/>", "/f/none/>"];

/// A `Fetch` page of `log` from `start` as a scan of one summary an index reads it (test
/// reference, `start` at or above the base): each retained record below `scan_max` records on
/// and below `visible`, unhidden and matched, read back, up to `max` of them; the page ends
/// before a record it cannot read, and past the records held.
fn fetch_each(
    log: &BrokerLog,
    start: u64,
    filter: &astream_wire::Filter,
    max: usize,
    scan_max: usize,
    visible: u64,
) -> (Vec<Arc<BrokerRecord>>, u64) {
    let base = log.base().0;
    let tier = log.tier_for_test();
    let limit = start.saturating_add(scan_max as u64).min(visible);
    let mut out = Vec::new();
    for off in start..limit {
        let i = (off - base) as usize;
        let Some(s) = tier.summary(i) else {
            return (out, off);
        };
        if s.is_hidden() || !filter.matches_str(s.subject()) {
            continue;
        }
        let Some(rec) = log.record_arc(i) else {
            return (out, off);
        };
        out.push(rec);
        if out.len() >= max {
            return (out, off + 1);
        }
    }
    (out, limit.max(start))
}

/// A filtered tail's step of `log` from `*cursor` (at or above the base) as a scan of one
/// summary an index reads it (test reference): the records and the offset it scanned to, `Err`
/// for a record it cannot read before any other, and the cursor moved where it found none.
fn tail_each(
    log: &BrokerLog,
    cursor: &mut u64,
    filter: &astream_wire::Filter,
    also_at: Option<u64>,
    max: usize,
) -> Result<(Vec<Arc<BrokerRecord>>, u64), u64> {
    let (base, head) = (log.base().0, log.head().0);
    let tier = log.tier_for_test();
    if *cursor >= head {
        return Ok((Vec::new(), *cursor));
    }
    let from = (*cursor - base) as usize;
    let to = (from + max.max(1)).min((head - base) as usize);
    let mut out = Vec::new();
    let mut scanned_to = *cursor;
    for i in from..to {
        let off = base + i as u64;
        let want = also_at == Some(off)
            || tier
                .summary(i)
                .is_none_or(|s| !s.is_hidden() && filter.matches_str(s.subject()));
        if want {
            let Some(rec) = log.record_arc(i) else {
                if out.is_empty() {
                    return Err(off);
                }
                break;
            };
            out.push(rec);
        }
        scanned_to = off + 1;
    }
    if out.is_empty() {
        *cursor = scanned_to;
    }
    Ok((out, scanned_to))
}

/// Every filtered read of `log` against [`fetch_each`] and [`tail_each`]: for each of
/// [`PACKED_FILTERS`], a reader paging `Fetch`es from the filter's oldest to the head (one
/// record a page over 7 records a scan, and up to 1,000 over 300), and a tail stepping from the
/// base (9 and 1,000 records a step, with and without a record `also_at` a third of the way
/// in), each page and step the same records, next offset and cursor as the reference's.
fn check_fetches(log: &BrokerLog) -> Result<(), String> {
    use crate::store::TailStep;
    let (base, head) = (log.base().0, log.head().0);
    let ids = |page: &[Arc<BrokerRecord>]| page.iter().map(|r| r.seq.0).collect::<Vec<_>>();
    for pat in PACKED_FILTERS {
        let filter = astream_wire::Filter::new(pat).map_err(|e| e.to_string())?;
        for (max, scan_max) in [(1, 7), (1_000, 300)] {
            let mut from = log.oldest(&filter).0;
            while from < head {
                let mine = log.fetch(from, &filter, max, scan_max, head);
                let theirs = fetch_each(log, from, &filter, max, scan_max, head);
                if mine != theirs {
                    return Err(format!(
                        "fetch {pat:?} from {from} (max {max}, scan {scan_max}): {:?} next {}, \
                         one an index {:?} next {}",
                        ids(&mine.0),
                        mine.1,
                        ids(&theirs.0),
                        theirs.1
                    ));
                }
                if mine.1 <= from {
                    break;
                }
                from = mine.1;
            }
        }
        let third = base + (head - base) / 3;
        for (max, also_at) in [
            (9, None),
            (9, Some(third)),
            (1_000, None),
            (1_000, Some(third)),
        ] {
            let mut at = base;
            while at < head {
                let (mut mine_at, mut theirs_at) = (at, at);
                let mine = match log.read_tail_chunk(&mut mine_at, head, &filter, also_at, max) {
                    TailStep::Chunk {
                        records,
                        scanned_to,
                    } => Ok((records, scanned_to)),
                    TailStep::Unreadable(off) => Err(off),
                };
                let theirs = tail_each(log, &mut theirs_at, &filter, also_at, max);
                if mine != theirs || mine_at != theirs_at {
                    return Err(format!(
                        "tail {pat:?} step from {at} (max {max}, also {also_at:?}): {:?} cursor \
                         {mine_at}, one an index {:?} cursor {theirs_at}",
                        mine.as_ref().map(|(r, to)| (ids(r), *to)),
                        theirs.as_ref().map(|(r, to)| (ids(r), *to))
                    ));
                }
                // The tail's reader moves on past what the step scanned.
                let Ok((_, to)) = mine else { break };
                if to <= at {
                    break;
                }
                at = to;
            }
        }
    }
    Ok(())
}

/// How a [`packed_stream`] holds its log: sealed at rest or not, its residency budget, the
/// page size each open repages to (`None`: the production page), and the most records a
/// batch commits.
#[derive(Clone, Copy, Debug)]
struct StreamShape {
    sealed: bool,
    budget: usize,
    page_shift: Option<u32>,
    batch: u64,
}

impl StreamShape {
    /// Seed `seed`'s shape: one of five budgets (the newest alone resident, a few records, a
    /// few dozen, a few hundred, all), pages from one record to the production page, batches
    /// small or long enough to fill production pages.
    fn of(seed: u64, sealed: bool) -> StreamShape {
        let budgets = [
            0usize,
            512,
            4_096,
            64 << 10,
            crate::tier::Tier::RESIDENT_ALL,
        ];
        StreamShape {
            sealed,
            budget: budgets[(seed % 5) as usize],
            page_shift: match seed % 3 {
                0 => None,
                k => Some(((seed / 3 + k) % 8) as u32),
            },
            batch: if seed % 2 == 0 { 6 } else { 40 },
        }
    }
}

/// One seeded stream against a real log held as `shape` says: single publishes (a
/// re-sent key answered with its original offset and nothing appended), batches, hidden
/// commit records, reopens (each one's broker times the same as before it) and, with
/// `retention`, cuts; after every step `check_packed` (every retained record against what
/// was published, read back through the tier), the tier's pages against the slot vector
/// beside them (`Tier::check_shadow`), every fourth step the filtered reads against a scan of
/// one summary an index (`check_fetches`) and, with `retention`, the retention planning over
/// each (`Tier::check_plans`).
fn packed_stream(seed: u64, shape: StreamShape) -> (crate::test_scratch::Scratch, BrokerLog) {
    use crate::brecord::GroupCommit;
    use std::collections::BTreeMap;

    let root = crate::test_scratch::Scratch::new(&format!(
        "tier-packed-{seed}-{}",
        if shape.sealed { "sealed" } else { "plain" }
    ));
    let path = root.path().join("log");
    let open = |path: &std::path::Path| {
        let mut opts = crate::OpenOptions::new(Durability::Relaxed);
        opts.resident_budget = Some(shape.budget);
        #[cfg(feature = "at-rest")]
        if shape.sealed {
            opts.at_rest_key = Some([0x5a; 32]);
        }
        let mut log = BrokerLog::open_opts(path, opts, || Ok(crate::Prepared::Nothing)).unwrap();
        if let Some(shift) = shape.page_shift {
            log.tier_mut_for_test().repage(shift);
        }
        log
    };
    let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
    let mut log = open(&path);
    let mut model: BTreeMap<u64, BrokerRecord> = BTreeMap::new();
    let mut keys: BTreeMap<(u64, u64), u64> = BTreeMap::new();
    let mut next_seq = [0u64; 4];
    let record = |off: u64, pid: u64, pseq: u64, subject: String, body: Vec<u8>| BrokerRecord {
        seq: Offset(off),
        producer_id: pid,
        producer_seq: pseq,
        subject,
        body,
        commit: None,
    };
    for step in 0..240 {
        let roll = rng.below(100);
        if roll < 55 {
            let pid = rng.below(4);
            let resend = rng.below(6) == 0 && next_seq[pid as usize] > 0;
            let pseq = if resend {
                rng.below(next_seq[pid as usize])
            } else {
                next_seq[pid as usize] += 1 + rng.below(2);
                next_seq[pid as usize]
            };
            let subject = format!("/f/packed/s{}", rng.below(9));
            let body = vec![(step % 251) as u8; rng.below(400) as usize];
            let (off, dup) = log
                .publish(pid + 1, pseq, subject.clone(), body.clone())
                .unwrap();
            match keys.get(&(pid + 1, pseq)) {
                Some(&orig) => assert_eq!((off.0, dup), (orig, true), "seed {seed} step {step}"),
                None => {
                    assert!(!dup, "seed {seed} step {step}: a fresh key dedups");
                    keys.insert((pid + 1, pseq), off.0);
                    model.insert(off.0, record(off.0, pid + 1, pseq, subject, body));
                }
            }
        } else if roll < 70 {
            for _ in 0..1 + rng.below(shape.batch) {
                let pid = rng.below(4);
                next_seq[pid as usize] += 1;
                let pseq = next_seq[pid as usize];
                let subject = format!("/f/packed/b{}", rng.below(5));
                let body = vec![7u8; rng.below(300) as usize];
                let (off, dup) = log
                    .stage_publish(pid + 1, pseq, subject.clone(), body.clone())
                    .unwrap();
                assert!(!dup);
                keys.insert((pid + 1, pseq), off.0);
                model.insert(off.0, record(off.0, pid + 1, pseq, subject, body));
            }
            log.commit_batch().unwrap();
        } else if roll < 80 {
            let group = format!("g{}", rng.below(3));
            let upto = rng.below(log.head().0 + 1);
            let off = log.commit(group.clone(), upto).unwrap();
            let mut rec = record(off.0, 0, 0, crate::store::COMMIT_SUBJECT.into(), Vec::new());
            rec.commit = Some(GroupCommit { group, upto });
            model.insert(off.0, rec);
        } else if roll < 90 {
            let bts: Vec<Option<u64>> = (0..log.tier_for_test().len())
                .map(|i| log.tier_for_test().bt(i))
                .collect();
            drop(log);
            log = open(&path);
            let again: Vec<Option<u64>> = (0..log.tier_for_test().len())
                .map(|i| log.tier_for_test().bt(i))
                .collect();
            assert_eq!(
                again, bts,
                "seed {seed} step {step}: the reopen's broker times"
            );
        } else {
            #[cfg(feature = "retention")]
            {
                let span = log.head().0 - log.base().0;
                let cut = log.base().0 + rng.below(span / 2 + 1);
                log.retain_before(Offset(cut)).unwrap();
                keys.retain(|_, off| *off >= log.base().0);
            }
        }
        if let Err(e) = check_packed(&log, &model) {
            panic!("seed {seed} {shape:?} step {step}: {e}");
        }
        if let Err(e) = log.tier_for_test().check_shadow() {
            panic!("seed {seed} {shape:?} step {step}: {e}");
        }
        // The filtered reads every fourth step, and after the last.
        if step % 4 == 3 {
            if let Err(e) = check_fetches(&log) {
                panic!("seed {seed} {shape:?} step {step}: {e}");
            }
        }
        #[cfg(feature = "retention")]
        {
            // Within twice the prefix rule's age of the newest record's broker time.
            let tier = log.tier_for_test();
            let newest = tier.len().checked_sub(1).and_then(|i| tier.bt(i));
            let now = newest.unwrap_or(0).saturating_add(rng.below(120_000));
            if let Err(e) = tier.check_plans(&packed_rules(), now) {
                panic!("seed {seed} {shape:?} step {step}: {e}");
            }
        }
    }
    (root, log)
}

/// The retention rules a [`packed_stream`]'s planning runs over the pages and the slot vector:
/// one batch subject by its last value, another held by bytes and age, and the rest as the
/// prefix, by bytes and age.
#[cfg(feature = "retention")]
fn packed_rules() -> crate::retention::Retention {
    use crate::retention::{Retention, Rule};
    use std::time::Duration;
    Retention::new(
        vec![
            Rule::hold("/f/packed/b1").unwrap().last_only(),
            Rule::hold("/f/packed/b2")
                .unwrap()
                .max_bytes(2_000)
                .max_age(Duration::from_secs(30)),
            Rule::prefix("/f/packed/*")
                .unwrap()
                .max_bytes(12_000)
                .max_age(Duration::from_secs(60)),
        ],
        Rule::default_hold(),
    )
    .unwrap()
}

#[test]
fn every_retained_record_reads_back_through_the_paged_tier() {
    for seed in 0..18 {
        let (_root, log) = packed_stream(seed, StreamShape::of(seed, false));
        drop(log);
    }
}

#[cfg(feature = "at-rest")]
#[test]
fn every_retained_record_reads_back_through_the_paged_tier_sealed_at_rest() {
    for seed in 0..9 {
        let (_root, log) = packed_stream(seed, StreamShape::of(seed, true));
        drop(log);
    }
}

/// The record at offset `off` of the cold-read logs: subjects in a small set, bodies of 16
/// to 32 KiB, so a 16 MiB window holds about 650 and leaves the rest cold.
fn wide_record(off: u64) -> (String, Vec<u8>) {
    let n = 16_384 + ((off * 7_919) % 16_384) as usize;
    let body = (0..n)
        .map(|k| (off as u8).wrapping_mul(13).wrapping_add(k as u8))
        .collect();
    (format!("/f/wide/s{}", off % 5), body)
}

/// Every retained record read back from a log of 1,200 records reopened at a residency
/// budget of 0 and of 16 MiB (the budget aterm opens with), equal to what was published;
/// the tier's pages answer as the slot vector does.
fn cold_reads_at_both_budgets(sealed: bool) {
    let root = crate::test_scratch::Scratch::new(if sealed {
        "tier-wide-sealed"
    } else {
        "tier-wide-plain"
    });
    let path = root.path().join("log");
    let open = |budget: usize| {
        let mut opts = crate::OpenOptions::new(Durability::Relaxed);
        opts.resident_budget = Some(budget);
        #[cfg(feature = "at-rest")]
        if sealed {
            opts.at_rest_key = Some([0x6b; 32]);
        }
        BrokerLog::open_opts(&path, opts, || Ok(crate::Prepared::Nothing)).unwrap()
    };
    const N: u64 = 1_200;
    {
        let mut log = open(16 << 20);
        for off in 0..N {
            let (subject, body) = wide_record(off);
            if off % 50 == 49 {
                log.stage_publish(2, off + 1, subject, body).unwrap();
                log.commit_batch().unwrap();
            } else {
                log.publish(2, off + 1, subject, body).unwrap();
            }
        }
    }
    for budget in [0usize, 16 << 20] {
        let log = open(budget);
        let (resident, _, retained) = log.residency();
        assert_eq!(retained as u64, N, "budget {budget}");
        if budget == 0 {
            assert_eq!(resident, 1, "budget 0 keeps the newest alone");
        } else {
            assert!(
                resident > 1 && (resident as u64) < N,
                "budget {budget}: {resident} of {N} resident, some cold"
            );
        }
        let before = log.cold_reads();
        let got = log.read_from(Offset(0));
        assert_eq!(
            got.len() as u64,
            N,
            "budget {budget}: every record reads back"
        );
        for rec in &got {
            let (subject, body) = wide_record(rec.seq.0);
            assert_eq!(
                (rec.producer_id, rec.producer_seq, &rec.subject, &rec.body),
                (2, rec.seq.0 + 1, &subject, &body),
                "budget {budget}: record {}",
                rec.seq.0
            );
        }
        assert_eq!(
            log.cold_reads() - before,
            N - resident as u64,
            "budget {budget}: each record outside the window read from the file once"
        );
        assert_eq!(
            log.tier_for_test().check_shadow(),
            Ok(()),
            "budget {budget}"
        );
    }
}

#[test]
fn every_record_reads_back_at_budget_0_and_16_mib() {
    cold_reads_at_both_budgets(false);
}

#[cfg(feature = "at-rest")]
#[test]
fn every_record_reads_back_at_budget_0_and_16_mib_sealed_at_rest() {
    cold_reads_at_both_budgets(true);
}

/// The negative control: one record whose frame start is a byte off is caught.
#[test]
fn a_frame_start_one_byte_off_is_caught() {
    for seed in 0..4 {
        let (_root, mut log) = packed_stream(seed, StreamShape::of(seed, false));
        let model: std::collections::BTreeMap<u64, BrokerRecord> = (0..log.tier_for_test().len())
            .filter_map(|i| log.record_arc(i))
            .map(|r| (r.seq.0, (*r).clone()))
            .collect();
        assert_eq!(check_packed(&log, &model), Ok(()));
        assert!(
            log.tier_for_test().len() >= 2,
            "seed {seed}: a cold record to skew"
        );
        log.set_resident_budget(0);
        log.tier_mut_for_test().skew_frame_start(0);
        assert!(
            check_packed(&log, &model).is_err(),
            "seed {seed}: a skewed frame start reads back"
        );
    }
}

/// The negative control of the paged tier on a real log: a page whose first frame start and
/// broker time are its second record's, or pages that begin one record late, are caught by
/// the cold reads against what was published and by the slot vector beside the pages.
#[test]
fn a_page_entry_off_by_one_record_is_caught_on_a_real_log() {
    use crate::tier::PageMutant;
    for seed in [1u64, 4, 7] {
        let shape = StreamShape {
            budget: 0,
            page_shift: Some(2),
            ..StreamShape::of(seed, false)
        };
        for mutant in [PageMutant::Base(1), PageMutant::Index] {
            let (_root, mut log) = packed_stream(seed, shape);
            let model: std::collections::BTreeMap<u64, BrokerRecord> =
                (0..log.tier_for_test().len())
                    .filter_map(|i| log.record_arc(i))
                    .map(|r| (r.seq.0, (*r).clone()))
                    .collect();
            assert_eq!(check_packed(&log, &model), Ok(()));
            assert!(
                log.tier_for_test().len() >= 12,
                "seed {seed}: three pages of four to mutate"
            );
            log.tier_mut_for_test().mutate(mutant);
            assert!(
                check_packed(&log, &model).is_err(),
                "seed {seed}: {mutant:?} reads back what was published"
            );
            assert!(
                log.tier_for_test().check_shadow().is_err(),
                "seed {seed}: {mutant:?} answers as the slot vector"
            );
        }
    }
}

/// The negative control of the filtered reads' page skip on a real log (aterm F11c): a pass
/// that passes whole a page it wants a record of answers a `Fetch` and a tail step differently
/// from a scan of one summary an index, and the slot vector beside the pages tells it apart, at
/// every page size from one record to the production page, a stream of its own each (whose
/// cuts leave it a page or two at the larger sizes).
#[test]
fn a_pass_that_drops_a_wanted_page_is_caught_on_a_real_log() {
    use crate::tier::PageMutant;
    let shifts = (0..crate::tier::PAGE_SHIFT).map(Some).chain([None]);
    for (seed, page_shift) in (2u64..).step_by(3).zip(shifts) {
        let shift = page_shift.unwrap_or(crate::tier::PAGE_SHIFT);
        let shape = StreamShape {
            page_shift,
            ..StreamShape::of(seed, false)
        };
        let (_root, mut log) = packed_stream(seed, shape);
        assert_eq!(check_fetches(&log), Ok(()), "seed {seed} shift {shift}");
        assert!(
            log.tier_for_test().len() >= 12,
            "seed {seed} shift {shift}: a dozen records to pass"
        );
        log.tier_mut_for_test().mutate(PageMutant::DropWanted);
        assert!(
            check_fetches(&log).is_err(),
            "seed {seed} shift {shift}: a pass dropping a page it wants reads as one an index"
        );
        assert!(
            log.tier_for_test().check_shadow().is_err(),
            "seed {seed} shift {shift}: a pass dropping a page it wants answers as the slot vector"
        );
    }
}
