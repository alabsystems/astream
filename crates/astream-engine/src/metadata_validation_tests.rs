//! Independent pre-change parser/consumer controls. Work counts describe owned
//! body materializations, not allocator calls (empty Vecs allocate no storage).
use crate::envelope::{legacy::OwnedEnvelopeOracle, owned_decode_work};
use crate::*;
use astream_term::{Folder, Record};
use astream_wire::{steps, Frame};

fn frame(seq: u64, record: Record) -> Vec<u8> {
    Envelope {
        seq: Offset(seq),
        ts_logical: 100u64.saturating_sub(seq),
        caused_by: Some(CausedBy {
            partition: Some(7),
            offset: seq,
        }),
        record,
    }
    .encode()
    .unwrap()
}
fn fixture() -> Vec<u8> {
    let records = [
        Record::In {
            bytes: vec![b'a'; 64],
            client_id: 9,
            client_seq: 7,
        },
        Record::Out(vec![b'b'; 128]),
        Record::In {
            bytes: Vec::new(),
            client_id: 9,
            client_seq: 3,
        },
        Record::Resize { cols: 0, rows: 0 },
        Record::Exit { code: -2 },
    ];
    records
        .into_iter()
        .enumerate()
        .flat_map(|(i, r)| frame(i as u64, r))
        .collect()
}
fn old_read(bytes: &[u8]) -> Vec<Result<Envelope, ReadError>> {
    let mut pos = 0;
    let mut expected = Offset::ZERO;
    let mut out = Vec::new();
    loop {
        let env = match Frame::decode(&bytes[pos..]) {
            Ok(None) => break,
            Err(e) => {
                out.push(Err(ReadError::Frame(e)));
                break;
            }
            Ok(Some(d)) => {
                pos += d.consumed;
                match OwnedEnvelopeOracle::from_payload(&d.frame.payload) {
                    Ok(e) => e,
                    Err(e) => {
                        out.push(Err(ReadError::Envelope(e)));
                        break;
                    }
                }
            }
        };
        if env.seq != expected {
            out.push(Err(ReadError::SeqMismatch {
                expected,
                found: env.seq,
            }));
            break;
        }
        let Some(next) = expected.checked_next() else {
            out.push(Err(ReadError::OffsetOverflow));
            break;
        };
        expected = next;
        out.push(Ok(env));
    }
    out
}

// Frozen recovery loop: the frame payload and body are independently owned.
// Classification still uses the unchanged wire resynchronization policy.
fn old_recover(bytes: &[u8]) -> RecoverReport {
    let mut pos = 0usize;
    let mut records = 0u64;
    let mut expected = Offset::ZERO;
    let tail = loop {
        match Frame::decode(&bytes[pos..]) {
            Ok(None) => break crate::store::tail_of(steps::end_without_frame(bytes, pos)),
            Err(e) => break crate::store::tail_of(steps::end_at_corrupt_frame(bytes, pos, e)),
            Ok(Some(d)) => match OwnedEnvelopeOracle::from_payload(&d.frame.payload) {
                Err(e) => {
                    break Tail::Fault {
                        at: pos,
                        kind: FaultKind::BadEnvelope(e),
                    }
                }
                Ok(e) if e.seq != expected => {
                    break Tail::Fault {
                        at: pos,
                        kind: FaultKind::OutOfOrder {
                            expected: expected.0,
                            found: e.seq.0,
                        },
                    }
                }
                Ok(_) => {
                    pos += d.consumed;
                    records += 1;
                    let Some(next) = expected.checked_next() else {
                        break crate::store::tail_of(steps::end_without_frame(bytes, pos));
                    };
                    expected = next;
                }
            },
        }
    };
    RecoverReport {
        valid_len: pos,
        records,
        torn: tail != Tail::Clean,
        tail,
    }
}
fn old_edges(logs: &[(Partition, &[u8])]) -> Vec<CrossEdge> {
    let mut out = Vec::new();
    for &(effect_partition, bytes) in logs {
        for item in old_read(bytes) {
            let Ok(env) = item else {
                break;
            };
            if let Some(CausedBy {
                partition: Some(cause_partition),
                offset,
            }) = env.caused_by
            {
                if cause_partition != effect_partition.0 {
                    out.push(CrossEdge {
                        cause: (Partition(cause_partition), Offset(offset)),
                        effect: (effect_partition, env.seq),
                    });
                }
            }
        }
    }
    out
}
fn malformed() -> Vec<u8> {
    // A bad body and wrong sequence: body validation must win, even before start.
    let mut p = vec![3, crate::envelope::TAG_OUT];
    p.extend_from_slice(&7u64.to_le_bytes());
    p.extend_from_slice(&0u64.to_le_bytes());
    p.push(0);
    p.extend_from_slice(&9u32.to_le_bytes());
    p.push(1);
    Frame::new(p).encode().unwrap()
}

#[test]
fn metadata_consumers_preserve_fault_order_and_recovery_classification() {
    let bytes = fixture();
    let mut cases = Vec::new();
    for end in 0..=bytes.len() {
        cases.push(bytes[..end].to_vec());
    }
    for at in 0..bytes.len() {
        let mut changed = bytes.clone();
        changed[at] ^= 0x80;
        cases.push(changed);
    }
    cases.push(malformed());
    let mut bad_then_good = malformed();
    bad_then_good.extend_from_slice(&bytes);
    cases.push(bad_then_good);
    let mut repeated = bytes.clone();
    repeated.extend_from_slice(&bytes);
    cases.push(repeated);
    // A CRC-valid invalid envelope at EOF is Fault, whereas incomplete/corrupt
    // frames keep the wire's Torn versus later-frame Fault distinction.
    for payload in [vec![], vec![9; 18], vec![3, 255]] {
        cases.push(Frame::new(payload).encode().unwrap());
    }
    // Valid CRCs, including changed length/body/cause fields, reach the parser.
    let decoded = Frame::decode(&bytes).unwrap().unwrap();
    for at in 0..decoded.frame.payload.len() {
        let mut p = decoded.frame.payload.clone();
        p[at] ^= 0x80;
        cases.push(Frame::new(p).encode().unwrap());
    }
    let same_log = Envelope {
        seq: Offset::ZERO,
        ts_logical: 0,
        caused_by: Some(CausedBy {
            partition: None,
            offset: u64::MAX,
        }),
        record: Record::Out(vec![1]),
    }
    .encode()
    .unwrap();
    assert!(cross_edges_from_logs(&[(Partition(7), &bytes), (Partition(0), &same_log)]).is_empty());
    for damaged in &cases {
        assert_eq!(recover(damaged), old_recover(damaged));
        let logs = [
            (Partition(1), damaged.as_slice()),
            (Partition(2), bytes.as_slice()),
            (Partition(7), bytes.as_slice()),
            (Partition(0), same_log.as_slice()),
            (Partition(1), damaged.as_slice()),
        ];
        assert_eq!(cross_edges_from_logs(&logs), old_edges(&logs));
    }
    assert_eq!(
        Log::read_bytes(&malformed(), Offset(99)).next(),
        Some(Err(ReadError::Envelope(EnvelopeError::BadBodyLen)))
    );
    assert!(matches!(
        recover(&malformed()).tail,
        Tail::Fault {
            kind: FaultKind::BadEnvelope(EnvelopeError::BadBodyLen),
            ..
        }
    ));
}

#[test]
fn session_metadata_keeps_highwater_last_input_clock_and_error_semantics() {
    let bytes = fixture();
    let mut session =
        Session::resume_from(Seeded::with_disk(4, MemDisk::from_bytes(bytes.clone()))).unwrap();
    assert_eq!(session.next_offset(), Offset(5));
    assert_eq!(session.last_in_offset(), Some(Offset(2)));
    assert!(session.is_duplicate(9, 7));
    assert!(!session.is_duplicate(9, 8));
    assert!(!session.is_duplicate(10, 0));
    session.append_output(vec![b'x']).unwrap();
    let last = Log::read_bytes(&session.log_bytes(), Offset(5))
        .next()
        .unwrap()
        .unwrap();
    assert!(last.ts_logical > 100); // maximum, not the last (96), stored timestamp
    assert_eq!(
        Session::resume_from(Seeded::with_disk(4, MemDisk::from_bytes(malformed()))).err(),
        Some(ReadError::Envelope(EnvelopeError::BadBodyLen))
    );
    let mut torn = bytes.clone();
    torn.push(1);
    assert_eq!(
        Session::resume_from(Seeded::with_disk(4, MemDisk::from_bytes(torn))).err(),
        Some(ReadError::Incomplete { at: bytes.len() })
    );
}

#[test]
fn fleet_prefix_keeps_pending_parser_state_and_validates_skipped_bodies() {
    let first = frame(0, Record::Out(b"hello\x1b[3".to_vec()));
    let mut bytes = first.clone();
    bytes.extend_from_slice(&frame(1, Record::Out(b"1mX".to_vec())));
    let cut = Cut {
        offsets: vec![(Partition(0), Offset(0)), (Partition(7), Offset(1))],
    };
    let snap = materialize_fleet_cut(&cut, &[(Partition(0), &bytes)], 10, 2).unwrap();
    let actual = resume_fleet_cut(&snap, &[(Partition(0), &bytes)]).unwrap();
    let mut folder = Folder::new(10, 2);
    for e in old_read(&bytes) {
        folder.apply(&e.unwrap().record);
    }
    assert_eq!(actual[0], (Partition(0), folder.into_screen()));
    let mut bad_prefix = malformed();
    bad_prefix.extend_from_slice(&frame(1, Record::Out(b"1mX".to_vec())));
    assert_eq!(
        resume_fleet_cut(&snap, &[(Partition(0), &bad_prefix)]).unwrap_err(),
        FleetError::Read {
            partition: Partition(0),
            err: ReadError::Envelope(EnvelopeError::BadBodyLen)
        }
    );
}

#[test]
fn metadata_and_skipped_prefix_remove_only_unreturned_owned_materializations() {
    use owned_decode_work::{capture, Work};
    let bytes = fixture();
    let (_, old) = capture(|| old_read(&bytes));
    assert_eq!(
        old,
        Work {
            materializations: 3,
            nonempty: 2,
            bytes: 192
        }
    );
    let (_, yielded) = capture(|| Log::read_bytes(&bytes, Offset::ZERO).collect::<Vec<_>>());
    assert_eq!(yielded, old);
    let (_, skipped) = capture(|| Log::read_bytes(&bytes, Offset(5)).collect::<Vec<_>>());
    assert_eq!(skipped, Work::default());
    let (_, prefix) = capture(|| Log::read_bytes(&bytes, Offset(1)).collect::<Vec<_>>());
    assert_eq!(
        prefix,
        Work {
            materializations: 2,
            nonempty: 1,
            bytes: 128
        }
    );
    let (_, recovered) = capture(|| recover(&bytes));
    let (_, edges) = capture(|| cross_edges_from_logs(&[(Partition(0), &bytes)]));
    let (_, resumed) =
        capture(|| Session::resume_from(Seeded::with_disk(1, MemDisk::from_bytes(bytes.clone()))));
    assert_eq!(
        (recovered, edges, resumed),
        (Work::default(), Work::default(), Work::default())
    );
    let cut = Cut {
        offsets: vec![(Partition(0), Offset(0)), (Partition(7), Offset(4))],
    };
    let snap = materialize_fleet_cut(&cut, &[(Partition(0), &bytes)], 2, 2).unwrap();
    let (_, fleet) = capture(|| resume_fleet_cut(&snap, &[(Partition(0), &bytes)]).unwrap());
    assert_eq!(
        fleet,
        Work {
            materializations: 2,
            nonempty: 1,
            bytes: 128
        }
    );
}

#[test]
#[ignore = "manual structural owned-body materialization audit; not allocator counts or production timing"]
fn metadata_materialization_audit() {
    use owned_decode_work::capture;
    for body in [0usize, 64, 1024, 64 * 1024] {
        let n = 256;
        let bytes: Vec<_> = (0..n)
            .flat_map(|i| frame(i, Record::Out(vec![0; body])))
            .collect();
        let (_, old) = capture(|| old_read(&bytes));
        let (_, yielded) = capture(|| Log::read_bytes(&bytes, Offset::ZERO).collect::<Vec<_>>());
        let (_, skip) = capture(|| Log::read_bytes(&bytes, Offset(n)).collect::<Vec<_>>());
        let (_, recovery) = capture(|| recover(&bytes));
        let (_, edges) = capture(|| cross_edges_from_logs(&[(Partition(0), &bytes)]));
        let (_, session) = capture(|| {
            Session::resume_from(Seeded::with_disk(1, MemDisk::from_bytes(bytes.clone())))
        });
        assert_eq!(old, yielded);
        assert_eq!((skip, recovery, edges, session), Default::default());
        println!("BODY_MATERIALIZATION records={n} body={body} old={old:?} yielded={yielded:?} skip={skip:?} recover={recovery:?} edges={edges:?} session={session:?}");
    }
}
