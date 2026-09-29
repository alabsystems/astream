//! Rung 2 evidence: resume + roaming. Backs the claim `term.resume.gapless-exactly-once`.
//!
//! Resume: a `/a/state` snapshot at any offset plus the log tail reproduces the
//! exact never-dropped screen — including when an escape sequence straddles the
//! snapshot boundary (the parser state must travel with the snapshot) — and the
//! prefix is provably NOT re-folded: the resume is handed garbage in place of
//! every record the snapshot already folded and still lands on the right screen.
//! A snapshot never claims offsets it did not fold (an empty log, an over-range
//! K). Input: a proposal re-sent after a drop is applied exactly once, in-session
//! and across a reconnect that rebuilds the dedup high-water from the log; and a
//! recovered log is CONTINUED (`Session::resume_from`), so the records appended
//! after the reconnect extend the same offset axis and recover again as one
//! intact log.

use astream_engine::{
    high_water_from_log, materialize, record_session, recover, resume, try_materialize, Log,
    MemDisk, Offset, Seeded, Session, Tail,
};
use astream_term::{screen, Record};

const COLS: u16 = 80;
const ROWS: u16 = 24;
const SEED: u64 = 0x5E55;

fn out(s: &[u8]) -> Record {
    Record::Out(s.to_vec())
}

/// A session whose offset-1 output ends mid-escape ("col\x1b["), so a snapshot
/// taken there must carry the parser's CSI state to render the rest correctly.
fn session_records() -> Vec<Record> {
    vec![
        out(b"\x1b[2Jhello\r\n"),
        out(b"col\x1b["),             // escape starts, incomplete...
        out(b"33mYELLOW\x1b[0m\r\n"), // ...completes in the next record
        Record::Resize { cols: 40, rows: 10 },
        out(b"\x1b[3;5Hx"),
    ]
}

fn record_log(records: &[Record]) -> Vec<u8> {
    record_session(SEED, records)
}

fn decode(bytes: &[u8]) -> Vec<Record> {
    let disk = MemDisk::from_bytes(bytes.to_vec());
    Log::read_from(&disk, Offset::ZERO)
        .map(|r| r.unwrap().record)
        .collect()
}

#[test]
fn resume_from_state_snapshot_is_gapless_and_exact_at_every_offset() {
    let records = decode(&record_log(&session_records()));
    let golden = screen::fold(COLS, ROWS, &records);

    for k in 0..records.len() {
        let snapshot = materialize(COLS, ROWS, &records, Offset(k as u64));
        assert_eq!(snapshot.folded_through(), Some(Offset(k as u64)));
        let resumed = resume(&snapshot, &records);
        assert_eq!(
            resumed.serialize(),
            golden.serialize(),
            "resume at offset {k} diverged from the never-dropped run"
        );
    }
}

#[test]
fn resume_never_re_folds_the_prefix() {
    let records = decode(&record_log(&session_records()));
    let golden = screen::fold(COLS, ROWS, &records);
    let garbage = out(b"\x1b[2JGARBAGE\r\n");

    for k in 0..records.len() {
        let snapshot = materialize(COLS, ROWS, &records, Offset(k as u64));
        // Every record the snapshot already folded is replaced with garbage that
        // would wreck the screen if it were applied: a resume that re-folds the
        // prefix (or re-applies offset K) paints GARBAGE; one that folds only the
        // tail after K cannot tell the difference.
        let mut corrupted = records.clone();
        for r in corrupted.iter_mut().take(k + 1) {
            *r = garbage.clone();
        }
        let resumed = resume(&snapshot, &corrupted);
        assert_eq!(
            resumed.serialize(),
            golden.serialize(),
            "resume at offset {k} read the prefix"
        );
        assert!(!resumed.line_text(0).contains("GARBAGE"));
    }

    // The garbage is load-bearing: folding a log that starts with it differs.
    let mut from_scratch = records.clone();
    from_scratch[0] = garbage;
    assert_ne!(
        screen::fold(COLS, ROWS, &from_scratch).serialize(),
        golden.serialize()
    );
}

#[test]
fn snapshot_carries_parser_state_across_a_split_escape() {
    let records = decode(&record_log(&session_records()));
    let golden = screen::fold(COLS, ROWS, &records);

    // Offset 1 ends mid-escape; without carried parser state the following
    // "33m..." would paint literally instead of completing the SGR.
    let snapshot = materialize(COLS, ROWS, &records, Offset(1));
    let resumed = resume(&snapshot, &records);

    assert_eq!(resumed.serialize(), golden.serialize());
    assert!(resumed.line_text(1).contains("YELLOW"));
    assert!(!resumed.line_text(1).contains("33m"));
}

#[test]
fn a_snapshot_never_claims_offsets_it_did_not_fold() {
    let records = decode(&record_log(&session_records()));
    let golden = screen::fold(COLS, ROWS, &records);

    // A client attaches before any output: nothing is folded, so a resume over
    // the log that fills in later paints everything from offset 0.
    let empty = materialize(COLS, ROWS, &[], Offset(0));
    assert_eq!(empty.folded_through(), None);
    assert_eq!(empty.next_offset(), Offset::ZERO);
    assert_eq!(resume(&empty, &records).serialize(), golden.serialize());
    assert!(try_materialize(COLS, ROWS, &[], Offset(0)).is_none());

    // A snapshot asked for beyond the end folds what exists and says so; the
    // records that arrive later are folded on resume, not skipped.
    let partial = &records[..2];
    let over = materialize(COLS, ROWS, partial, Offset(99));
    assert_eq!(over.folded_through(), Some(Offset(1)));
    assert_eq!(over.next_offset(), Offset(2));
    assert_eq!(resume(&over, &records).serialize(), golden.serialize());
    assert!(try_materialize(COLS, ROWS, partial, Offset(99)).is_none());
    assert!(try_materialize(COLS, ROWS, partial, Offset(2)).is_none());
    assert_eq!(
        try_materialize(COLS, ROWS, partial, Offset(1))
            .unwrap()
            .folded_through(),
        Some(Offset(1))
    );
    // An offset that does not fit usize is out of range, never truncated.
    assert!(try_materialize(COLS, ROWS, partial, Offset(u64::MAX)).is_none());
    assert_eq!(
        materialize(COLS, ROWS, partial, Offset(u64::MAX)).folded_through(),
        Some(Offset(1))
    );
}

#[test]
fn input_is_applied_exactly_once_within_a_session() {
    let mut s = Session::new(Seeded::new(SEED));
    assert!(s.apply_input(7, 1, b"a".to_vec()).unwrap().is_some());
    assert!(s.apply_input(7, 2, b"b".to_vec()).unwrap().is_some());
    // A drop: unsure whether seq 2 landed, the client re-sends it, then seq 3.
    assert!(
        s.apply_input(7, 2, b"b".to_vec()).unwrap().is_none(),
        "the re-sent keystroke is deduped"
    );
    assert!(s.apply_input(7, 3, b"c".to_vec()).unwrap().is_some());

    let ins = decode(&s.log_bytes())
        .into_iter()
        .filter(|r| matches!(r, Record::In { .. }))
        .count();
    assert_eq!(ins, 3, "three keystrokes, each applied exactly once");
}

#[test]
fn dedup_high_water_is_recoverable_across_a_reconnect() {
    // Session A applies seqs 1,2 for client 7, then drops.
    let mut a = Session::new(Seeded::new(SEED));
    a.apply_input(7, 1, b"a".to_vec()).unwrap();
    a.apply_input(7, 2, b"b".to_vec()).unwrap();
    let records = decode(&a.log_bytes());

    // Reconnect: rebuild the high-water from the (recovered) log.
    let hw = high_water_from_log(&records);
    assert_eq!(hw.get(&7), Some(&2));

    // A session on a NEW offset axis (fresh disk) that inherits only the dedup map.
    let mut b = Session::with_high_water(Seeded::new(SEED), hw);
    // The keystroke in flight at the drop (seq 2) is re-sent -> still exactly once.
    assert!(
        b.apply_input(7, 2, b"b".to_vec()).unwrap().is_none(),
        "re-sent across the reconnect, deduped by the recovered high-water"
    );
    assert!(b.apply_input(7, 3, b"c".to_vec()).unwrap().is_some());
}

#[test]
fn a_recovered_log_is_continued_not_restarted() {
    // Session A: a prompt, two keystrokes, then the process dies.
    let mut a = Session::new(Seeded::new(SEED));
    a.append_output(b"\x1b[2J$ ".to_vec()).unwrap();
    a.apply_input(7, 1, b"l".to_vec()).unwrap();
    a.apply_input(7, 2, b"s".to_vec()).unwrap();
    let bytes = a.log_bytes();
    let report = recover(&bytes);
    assert_eq!((report.records, report.tail.clone()), (3, Tail::Clean));

    // Reconnect over the recovered bytes — the SAME disk, continued: the next
    // offset is 3 and the dedup map is rebuilt from the log.
    let recovered = MemDisk::from_bytes(bytes[..report.valid_len].to_vec());
    let mut b = Session::resume_from(Seeded::with_disk(SEED, recovered)).unwrap();
    assert_eq!(b.next_offset(), Offset(3));
    assert!(
        b.apply_input(7, 2, b"s".to_vec()).unwrap().is_none(),
        "the keystroke in flight at the crash, re-sent, is deduped"
    );
    assert_eq!(
        b.apply_input(7, 3, b"\n".to_vec()).unwrap(),
        Some(Offset(3))
    );
    assert_eq!(
        b.append_output(b"ls\r\nfile\r\n".to_vec()).unwrap(),
        Offset(4)
    );

    // Recover AGAIN: one intact, dense, clock-monotone log. Nothing appended
    // after the reconnect is lost to a seq or clock restart.
    let all = b.log_bytes();
    let again = recover(&all);
    assert_eq!(
        (again.records, again.tail.clone(), again.valid_len),
        (5, Tail::Clean, all.len())
    );
    let envs: Vec<_> = Log::read_bytes(&all, Offset::ZERO)
        .map(|r| r.unwrap())
        .collect();
    for (i, e) in envs.iter().enumerate() {
        assert_eq!(
            e.seq,
            Offset(i as u64),
            "dense offsets across the reconnect"
        );
        assert_eq!(
            e.ts_logical, i as u64,
            "the seam clock continued past the recovered ts_logical"
        );
    }
    // The continued log is byte-identical to a never-interrupted recording of the
    // same records: the continuation is exact, not merely monotone.
    let recs: Vec<Record> = envs.into_iter().map(|e| e.record).collect();
    assert_eq!(record_session(SEED, &recs), all);
    assert!(screen::fold(COLS, ROWS, &recs)
        .line_text(1)
        .contains("file"));
    assert_eq!(high_water_from_log(&recs).get(&7), Some(&3));

    // Resume refuses a disk whose log is not intact rather than continuing over it.
    let mut damaged = all.clone();
    let n = damaged.len();
    damaged[n - 1] ^= 0xFF;
    assert!(Session::resume_from(Seeded::with_disk(SEED, MemDisk::from_bytes(damaged))).is_err());
}
