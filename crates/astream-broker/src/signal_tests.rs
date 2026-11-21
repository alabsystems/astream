// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! The signal table judged alone: no broker, no socket, no clock. Every instant a take
//! judges by is a number the test passes.

use super::*;

const NEVER: u64 = u64::MAX;

fn all() -> Filter {
    Filter::new("/>").unwrap()
}

/// What a take returned, as `(subject, producer, seq, body)`.
fn taken(rows: &[SignalRow]) -> Vec<(String, u64, u64, Vec<u8>)> {
    rows.iter()
        .map(|r| (r.subject.to_string(), r.producer_id, r.seq, r.body.to_vec()))
        .collect()
}

fn row(subject: &str, producer: u64, seq: u64, body: &[u8]) -> (String, u64, u64, Vec<u8>) {
    (subject.to_string(), producer, seq, body.to_vec())
}

/// CONFLATION: a reader that takes between two puts sees each value; one that takes after a
/// hundred sees the hundredth, once, and a subject it had already taken does not come again
/// until it is put again. NC: a table that queued puts per reader would hand the late
/// reader a hundred rows.
#[test]
fn a_take_between_puts_sees_each_value_and_a_late_take_sees_only_the_newest() {
    let mut t = SignalTable::new();
    let mut prompt = 0u64;
    let mut late = 0u64;
    assert!(t.caught_up(prompt));

    assert_eq!(
        t.put(1, 7, 1, NEVER, "/s/a", b"v0".to_vec()),
        Ok(Put::Changed)
    );
    assert!(!t.caught_up(prompt));
    assert_eq!(
        taken(&t.take_after(&mut prompt, &all(), usize::MAX, 0)),
        [row("/s/a", 7, 1, b"v0")]
    );
    assert!(t.caught_up(prompt));
    assert_eq!(
        t.put(1, 7, 1, NEVER, "/s/a", b"v1".to_vec()),
        Ok(Put::Changed)
    );
    assert_eq!(
        taken(&t.take_after(&mut prompt, &all(), usize::MAX, 0)),
        [row("/s/a", 7, 1, b"v1")]
    );

    for n in 2..=100u32 {
        let body = format!("v{n}").into_bytes();
        assert_eq!(t.put(1, 7, 1, NEVER, "/s/a", body), Ok(Put::Changed));
    }
    assert_eq!(
        t.put(1, 7, 1, NEVER, "/s/b", b"b".to_vec()),
        Ok(Put::Changed)
    );
    assert_eq!(t.len(), 2, "one row per subject, however often it was put");
    assert_eq!(
        taken(&t.take_after(&mut late, &all(), usize::MAX, 0)),
        [row("/s/a", 7, 1, b"v100"), row("/s/b", 7, 1, b"b")],
        "the late reader gets each subject once, at its newest value"
    );
    assert!(t.caught_up(late));
    assert!(t.take_after(&mut late, &all(), usize::MAX, 0).is_empty());

    // A filter that matches nothing still moves the reader past what it visited.
    let mut other = 0u64;
    let none = Filter::new("/elsewhere/>").unwrap();
    assert!(t.take_after(&mut other, &none, usize::MAX, 0).is_empty());
    assert!(t.caught_up(other));
    // And a narrower one takes only its own subject.
    let mut narrow = 0u64;
    let only_b = Filter::new("/s/b").unwrap();
    assert_eq!(
        taken(&t.take_after(&mut narrow, &only_b, usize::MAX, 0)),
        [row("/s/b", 7, 1, b"b")]
    );
}

/// WHOSE ROW IT IS: the owning connection replaces at any seq; another connection of the
/// same producer replaces only at a seq not below the row's, and at an equal seq only if it
/// is the newer connection; another producer wins. An accepted put with an unchanged body
/// is still a change a reader takes. NC: were an equal seq always the later arrival's, the
/// late bytes of a connection its producer left behind would take the row back from the
/// connection that replaced it, and that dead connection's end would then remove it.
#[test]
fn a_stale_seq_from_another_connection_changes_nothing_and_the_owner_always_replaces() {
    let mut t = SignalTable::new();
    let mut seen = 0u64;
    assert_eq!(
        t.put(1, 7, 5, NEVER, "/s/a", b"five".to_vec()),
        Ok(Put::Changed)
    );
    let _ = t.take_after(&mut seen, &all(), usize::MAX, 0);

    // A lower seq from another connection of the same producer: acknowledged, nothing moved.
    assert_eq!(
        t.put(2, 7, 4, NEVER, "/s/a", b"late".to_vec()),
        Ok(Put::Stale)
    );
    assert!(t.caught_up(seen), "a stale put is no change");
    assert!(!t.owns(2));

    // The owner, at the same seq and the same body: a change, redelivered.
    assert_eq!(
        t.put(1, 7, 5, NEVER, "/s/a", b"five".to_vec()),
        Ok(Put::Changed)
    );
    assert_eq!(
        taken(&t.take_after(&mut seen, &all(), usize::MAX, 0)),
        [row("/s/a", 7, 5, b"five")]
    );
    // The owner, at a LOWER seq: its own bytes arrive in the order it sent them.
    assert_eq!(
        t.put(1, 7, 3, NEVER, "/s/a", b"three".to_vec()),
        Ok(Put::Changed)
    );
    assert_eq!(
        taken(&t.take_after(&mut seen, &all(), usize::MAX, 0)),
        [row("/s/a", 7, 3, b"three")]
    );

    // A NEWER connection at an EQUAL seq takes the row: a reconnect inside one incarnation.
    assert_eq!(
        t.put(2, 7, 3, NEVER, "/s/a", b"again".to_vec()),
        Ok(Put::Changed)
    );
    assert!(t.owns(2));
    assert!(
        !t.owns(1),
        "the row moved, and connection 1 owns nothing else"
    );
    assert_eq!(t.owners(), [(2, 7)]);
    assert_eq!(
        taken(&t.take_after(&mut seen, &all(), usize::MAX, 0)),
        [row("/s/a", 7, 3, b"again")]
    );
    // So the first connection is now the stale one: at a lower seq, and at the EQUAL seq
    // too, since it is the older connection. Its late bytes do not take the row back.
    assert_eq!(
        t.put(1, 7, 2, NEVER, "/s/a", b"older".to_vec()),
        Ok(Put::Stale)
    );
    assert_eq!(
        t.put(1, 7, 3, NEVER, "/s/a", b"left behind".to_vec()),
        Ok(Put::Stale)
    );
    assert!(t.caught_up(seen), "neither stale put is a change");
    assert_eq!(t.owners(), [(2, 7)]);
    // The connection left behind then ends: the row is not its to take.
    assert_eq!(t.drop_conn(1), 0);
    let mut fresh = 0u64;
    assert_eq!(
        taken(&t.take_after(&mut fresh, &all(), usize::MAX, 0)),
        [row("/s/a", 7, 3, b"again")],
        "the newer connection's value is still held"
    );
    // A higher seq from the older connection is a later incarnation's, and replaces.
    assert_eq!(
        t.put(1, 7, 4, NEVER, "/s/a", b"four".to_vec()),
        Ok(Put::Changed)
    );
    assert_eq!(t.owners(), [(1, 7)]);
    assert_eq!(
        taken(&t.take_after(&mut seen, &all(), usize::MAX, 0)),
        [row("/s/a", 7, 4, b"four")]
    );

    // Another producer id is last writer wins, whatever its seq.
    assert_eq!(
        t.put(3, 8, 0, NEVER, "/s/a", b"other".to_vec()),
        Ok(Put::Changed)
    );
    assert_eq!(t.owners(), [(3, 8)]);
    assert_eq!(
        taken(&t.take_after(&mut seen, &all(), usize::MAX, 0)),
        [row("/s/a", 8, 0, b"other")]
    );
    assert_eq!(t.len(), 1);
    assert_eq!(t.bytes(), "/s/a".len() + b"other".len());
}

/// EVERY BOUND refuses before anything is kept, and names its class: a body too large is
/// the request's fault (7), a full table is a state a later put may find lifted (5).
#[test]
fn the_bounds_refuse_before_anything_is_kept() {
    // The body.
    let mut t = SignalTable::new();
    let too_large = vec![0u8; MAX_SIGNAL_BODY + 1];
    let refused = t.put(1, 7, 1, NEVER, "/s/a", too_large).unwrap_err();
    assert_eq!(
        refused,
        SignalRefusal::BodyTooLarge {
            len: MAX_SIGNAL_BODY + 1
        }
    );
    assert_eq!(refused.code(), crate::proto::ERR_RECORD_REFUSED);
    assert!(refused.message().contains("too large"));
    assert_eq!((t.len(), t.bytes()), (0, 0));
    assert_eq!(
        t.put(1, 7, 1, NEVER, "/s/a", vec![0u8; MAX_SIGNAL_BODY]),
        Ok(Put::Changed),
        "a body at the limit is kept"
    );

    // One connection's subjects.
    let mut t = SignalTable::new();
    for n in 0..MAX_SIGNAL_SUBJECTS_PER_CONN {
        assert_eq!(
            t.put(1, 7, 1, NEVER, &format!("/s/{n}"), Vec::new()),
            Ok(Put::Changed)
        );
    }
    let bytes = t.bytes();
    let refused = t
        .put(1, 7, 1, NEVER, "/s/one-more", Vec::new())
        .unwrap_err();
    assert_eq!(refused, SignalRefusal::ConnSubjects);
    assert_eq!(refused.code(), crate::proto::ERR_REFUSED);
    assert_eq!((t.len(), t.bytes()), (MAX_SIGNAL_SUBJECTS_PER_CONN, bytes));
    assert_eq!(
        t.put(1, 7, 1, NEVER, "/s/0", b"again".to_vec()),
        Ok(Put::Changed),
        "a subject it already owns is no new subject"
    );
    assert_eq!(
        t.put(2, 8, 1, NEVER, "/s/one-more", Vec::new()),
        Ok(Put::Changed),
        "the bound is each connection's own"
    );

    // One connection's bytes: four rows of a quarter of the bound each fill it exactly.
    let mut t = SignalTable::new();
    let quarter = MAX_SIGNAL_BYTES_PER_CONN / 4;
    let subject = |conn: u64, n: usize| format!("/b/{conn:02}/{n}");
    let fill = |t: &mut SignalTable, conn: u64| {
        for n in 0..4 {
            let s = subject(conn, n);
            let body = vec![0u8; quarter - s.len()];
            assert_eq!(t.put(conn, conn, 1, NEVER, &s, body), Ok(Put::Changed));
        }
    };
    fill(&mut t, 1);
    assert_eq!(t.bytes(), MAX_SIGNAL_BYTES_PER_CONN);
    let refused = t.put(1, 1, 1, NEVER, "/b/01/more", Vec::new()).unwrap_err();
    assert_eq!(refused, SignalRefusal::ConnBytes);
    assert_eq!(refused.code(), crate::proto::ERR_REFUSED);
    assert_eq!((t.len(), t.bytes()), (4, MAX_SIGNAL_BYTES_PER_CONN));
    // Replacing a row with a smaller one is judged by what the connection would then hold.
    assert_eq!(
        t.put(1, 1, 1, NEVER, &subject(1, 0), Vec::new()),
        Ok(Put::Changed)
    );

    // The table's bytes: sixteen connections at their own bound fill it exactly.
    let mut t = SignalTable::new();
    let conns = u64::try_from(MAX_SIGNAL_BYTES / MAX_SIGNAL_BYTES_PER_CONN).unwrap();
    for conn in 1..=conns {
        fill(&mut t, conn);
    }
    assert_eq!(t.bytes(), MAX_SIGNAL_BYTES);
    let refused = t.put(99, 99, 1, NEVER, "/b/x", Vec::new()).unwrap_err();
    assert_eq!(refused, SignalRefusal::TableBytes);
    assert_eq!(refused.code(), crate::proto::ERR_REFUSED);
    assert_eq!(t.bytes(), MAX_SIGNAL_BYTES);
    assert!(!t.owns(99));
    // A connection that goes gives its bytes back, and the refused put is then kept.
    assert_eq!(t.drop_conn(1), 4);
    assert_eq!(
        t.put(99, 99, 1, NEVER, "/b/x", Vec::new()),
        Ok(Put::Changed)
    );

    // The table's subjects.
    let mut t = SignalTable::new();
    let per = MAX_SIGNAL_SUBJECTS_PER_CONN;
    let conns = u64::try_from(MAX_SIGNAL_SUBJECTS / per).unwrap();
    for conn in 1..=conns {
        for n in 0..per {
            assert_eq!(
                t.put(conn, conn, 1, NEVER, &format!("/t/{conn}/{n}"), Vec::new()),
                Ok(Put::Changed)
            );
        }
    }
    assert_eq!(t.len(), MAX_SIGNAL_SUBJECTS);
    let refused = t.put(9999, 9999, 1, NEVER, "/t/x", Vec::new()).unwrap_err();
    assert_eq!(refused, SignalRefusal::TableSubjects);
    assert_eq!(refused.code(), crate::proto::ERR_REFUSED);
    assert_eq!(t.len(), MAX_SIGNAL_SUBJECTS);
    assert_eq!(
        t.put(9999, 9999, 1, NEVER, "/t/1/0", b"taken over".to_vec()),
        Ok(Put::Changed),
        "a subject the table already holds is no new subject"
    );
    // Every row gone, every byte is given back.
    for conn in 1..=conns {
        t.drop_conn(conn);
    }
    t.drop_conn(9999);
    assert_eq!((t.len(), t.bytes()), (0, 0));
}

/// THE SESSION: a connection that ends takes the rows it still owns and no other, and a
/// row another connection took over is that connection's to lose.
#[test]
fn dropping_a_connection_removes_only_what_it_still_owns() {
    let mut t = SignalTable::new();
    assert_eq!(
        t.put(1, 7, 1, NEVER, "/s/a", b"a".to_vec()),
        Ok(Put::Changed)
    );
    assert_eq!(
        t.put(1, 7, 1, NEVER, "/s/b", b"b".to_vec()),
        Ok(Put::Changed)
    );
    assert_eq!(
        t.put(2, 8, 1, NEVER, "/s/c", b"c".to_vec()),
        Ok(Put::Changed)
    );
    // Connection 2 takes `/s/b` over: connection 1 no longer owns it.
    assert_eq!(
        t.put(2, 8, 1, NEVER, "/s/b", b"B".to_vec()),
        Ok(Put::Changed)
    );
    let mut seen = 0u64;
    let _ = t.take_after(&mut seen, &all(), usize::MAX, 0);

    assert_eq!(t.drop_conn(1), 1);
    assert!(!t.owns(1));
    assert_eq!(
        t.drop_conn(1),
        0,
        "a connection that owns nothing drops nothing"
    );
    assert_eq!(t.len(), 2);
    assert_eq!(t.bytes(), "/s/b".len() + 1 + "/s/c".len() + 1);
    assert!(
        t.caught_up(seen),
        "a withdrawal is no change a reader is sent"
    );

    // A reader that starts now is sent what is left, and nothing of the dropped row.
    let mut fresh = 0u64;
    assert_eq!(
        taken(&t.take_after(&mut fresh, &all(), usize::MAX, 0)),
        [row("/s/c", 8, 1, b"c"), row("/s/b", 8, 1, b"B")]
    );

    // By producer, as a revocation judges.
    assert_eq!(t.drop_where(|_, producer| producer == 8), 2);
    assert_eq!((t.len(), t.bytes()), (0, 0));
    assert!(!t.owns(2));
    assert!(t.owners().is_empty());
}

/// A TAKE IS BOUNDED: one take gathers a page, the next resumes after it, and the pages
/// together are every row once, oldest change first. A subject put again between two pages
/// moves behind the reader's place and is taken at its new value.
#[test]
fn a_take_is_bounded_and_resumes_in_version_order() {
    let mut t = SignalTable::new();
    for n in 0..5u8 {
        assert_eq!(
            t.put(1, 7, 1, NEVER, &format!("/s/{n}"), vec![n; 10]),
            Ok(Put::Changed)
        );
    }
    let mut seen = 0u64;
    // Each row costs 14 bytes; a page of 20 holds two.
    let first = t.take_after(&mut seen, &all(), 20, 0);
    assert_eq!(
        taken(&first),
        [row("/s/0", 7, 1, &[0; 10]), row("/s/1", 7, 1, &[1; 10])]
    );
    assert!(!t.caught_up(seen), "a full page leaves the reader behind");

    // `/s/0`, already taken, is put again; `/s/3`, not yet taken, is put again too.
    assert_eq!(
        t.put(1, 7, 1, NEVER, "/s/0", b"zero".to_vec()),
        Ok(Put::Changed)
    );
    assert_eq!(
        t.put(1, 7, 1, NEVER, "/s/3", b"three".to_vec()),
        Ok(Put::Changed)
    );

    let mut rest = Vec::new();
    while !t.caught_up(seen) {
        let page = t.take_after(&mut seen, &all(), 20, 0);
        assert!(
            !page.is_empty(),
            "a reader behind is always handed something"
        );
        rest.extend(taken(&page));
    }
    assert_eq!(
        rest,
        [
            row("/s/2", 7, 1, &[2; 10]),
            row("/s/4", 7, 1, &[4; 10]),
            row("/s/0", 7, 1, b"zero"),
            row("/s/3", 7, 1, b"three"),
        ],
        "`/s/3` is taken once, at its newest value, and `/s/0` again"
    );
}

/// AUTHORITY THAT LAPSED: a row at or past the instant its authority ends is not taken,
/// and the take that meets it removes it. NC: a table that ignored the instant would keep
/// serving a value whose grant expired for as long as its connection stayed open.
#[test]
fn a_row_past_its_authority_is_not_taken_and_is_removed() {
    let mut t = SignalTable::new();
    assert!(!t.has_deadlines());
    assert_eq!(
        t.put(1, 7, 1, 100, "/s/dated", b"d".to_vec()),
        Ok(Put::Changed)
    );
    assert_eq!(
        t.put(1, 7, 1, NEVER, "/s/kept", b"k".to_vec()),
        Ok(Put::Changed)
    );
    assert!(t.has_deadlines());

    let mut early = 0u64;
    assert_eq!(
        taken(&t.take_after(&mut early, &all(), usize::MAX, 99)),
        [row("/s/dated", 7, 1, b"d"), row("/s/kept", 7, 1, b"k")],
        "before its instant the row is served"
    );

    let mut at = 0u64;
    assert_eq!(
        taken(&t.take_after(&mut at, &all(), usize::MAX, 100)),
        [row("/s/kept", 7, 1, b"k")],
        "at its instant it is not"
    );
    assert_eq!(t.len(), 1, "and the take that met it removed it");
    assert_eq!(t.bytes(), "/s/kept".len() + 1);
    assert!(!t.has_deadlines());
    assert_eq!(t.owners(), [(1, 7)]);

    // A put again under a later authority is served again.
    assert_eq!(
        t.put(1, 7, 1, 500, "/s/dated", b"d2".to_vec()),
        Ok(Put::Changed)
    );
    assert!(t.has_deadlines());
    assert_eq!(
        taken(&t.take_after(&mut at, &all(), usize::MAX, 100)),
        [row("/s/dated", 7, 1, b"d2")]
    );
    // Replacing it with an undated row clears the deadline count.
    assert_eq!(
        t.put(1, 7, 1, NEVER, "/s/dated", b"d3".to_vec()),
        Ok(Put::Changed)
    );
    assert!(!t.has_deadlines());
}

/// ROOM HELD BY ROWS SERVED TO NOBODY IS GIVEN BACK: a reader that is caught up never meets
/// a row whose authority has since lapsed, so no take removes it; a put that a bound would
/// refuse is told so (`at_bound`), the lapsed rows are dropped (`drop_lapsed`), and the put
/// is kept. NC: without the drop a connection whose first grant expired with 64 subjects
/// held could signal no new subject under its next grant.
#[test]
fn a_put_at_a_bound_is_given_the_room_of_rows_past_their_authority() {
    let mut t = SignalTable::new();
    for n in 0..MAX_SIGNAL_SUBJECTS_PER_CONN {
        assert_eq!(
            t.put(1, 7, 1, 100, &format!("/s/{n}"), Vec::new()),
            Ok(Put::Changed)
        );
    }
    assert_eq!(
        t.put(2, 8, 1, NEVER, "/s/undated", b"u".to_vec()),
        Ok(Put::Changed)
    );
    // The reader takes them all while their authority holds, and is caught up.
    let mut seen = 0u64;
    assert_eq!(
        t.take_after(&mut seen, &all(), usize::MAX, 99).len(),
        MAX_SIGNAL_SUBJECTS_PER_CONN + 1
    );
    assert!(t.take_after(&mut seen, &all(), usize::MAX, 100).is_empty());
    assert_eq!(
        t.len(),
        MAX_SIGNAL_SUBJECTS_PER_CONN + 1,
        "a caught-up reader meets no lapsed row, so its take removed none"
    );

    assert!(t.at_bound(1, "/s/one-more", 0));
    assert!(
        !t.at_bound(1, "/s/0", 0),
        "a subject it already owns is no new subject"
    );
    assert!(
        !t.at_bound(2, "/s/one-more", 0),
        "the bound is connection 1's"
    );
    assert_eq!(
        t.put(1, 7, 1, 500, "/s/one-more", Vec::new()),
        Err(SignalRefusal::ConnSubjects)
    );

    assert_eq!(t.drop_lapsed(99), 0, "before their instant nothing lapsed");
    assert_eq!(t.drop_lapsed(100), MAX_SIGNAL_SUBJECTS_PER_CONN);
    assert_eq!(t.len(), 1, "the undated row is no lapsed row");
    assert_eq!(t.bytes(), "/s/undated".len() + 1);
    assert!(!t.owns(1));
    assert!(!t.has_deadlines());
    assert!(
        t.caught_up(seen),
        "a withdrawal is no change a reader is sent"
    );
    assert_eq!(
        t.drop_lapsed(u64::MAX),
        0,
        "a row with no instant never lapses"
    );

    assert!(!t.at_bound(1, "/s/one-more", 0));
    assert_eq!(
        t.put(1, 7, 1, 500, "/s/one-more", Vec::new()),
        Ok(Put::Changed)
    );
    assert_eq!(
        taken(&t.take_after(&mut seen, &all(), usize::MAX, 100)),
        [row("/s/one-more", 7, 1, b"")]
    );
}
