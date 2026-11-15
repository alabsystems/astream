// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{CausedBy, Disk, Effects, Seeded};
use astream_term::{screen, Record};
use std::cell::Cell;

thread_local! {
    static LAST_LOOKUP_HINT: Cell<Option<usize>> = const { Cell::new(None) };
}

pub(super) fn note_lookup_hint(hint: usize) {
    LAST_LOOKUP_HINT.with(|last| last.set(Some(hint)));
}

fn take_lookup_hint() -> Option<usize> {
    LAST_LOOKUP_HINT.with(|last| last.take())
}

// Retain the pre-index implementation as a behavioral oracle. In particular,
// edge rebuilding includes duplicate logs while screen replay takes the first.
fn legacy_materialize(
    cut: &Cut,
    logs: &[(Partition, &[u8])],
    cols: u16,
    rows: u16,
) -> Result<FleetSnapshot, FleetError> {
    let edges = cross_edges_from_logs(logs);
    if let Some(v) = first_violation(cut, &edges) {
        return Err(FleetError::InconsistentCut(v));
    }
    let mut partitions: Vec<FleetPartitionState> = Vec::new();
    for &(part, cut_off) in &cut.offsets {
        if partitions.iter().any(|ps| ps.partition == part) {
            continue;
        }
        let log_bytes = logs
            .iter()
            .find(|&&(p, _)| p == part)
            .map_or(&[][..], |&(_, b)| b);
        let mut folder = Folder::new(cols, rows);
        let mut folded_through = None;
        for item in Log::read_bytes(log_bytes, Offset::ZERO) {
            let env = item.map_err(|err| FleetError::Read {
                partition: part,
                err,
            })?;
            if !fleet_seq_within_cut(env.seq.0, cut_off.0) {
                break;
            }
            let seq = Offset(fleet_clamp_to_cut(env.seq.0, cut_off.0));
            folded_through = Some(seq);
            folder.apply(&env.record);
            if seq == cut_off {
                break;
            }
        }
        partitions.push(FleetPartitionState {
            partition: part,
            snapshot: StateSnapshot::from_parts(folded_through, folder),
        });
    }
    Ok(FleetSnapshot {
        cut: cut.clone(),
        edges,
        partitions,
    })
}

// The first indexed implementation used raw cut length as its lookup hint.
// Retain that complete policy as a benchmark control for duplicate-heavy cuts.
fn raw_count_materialize(
    cut: &Cut,
    logs: &[(Partition, &[u8])],
    cols: u16,
    rows: u16,
) -> Result<FleetSnapshot, FleetError> {
    let edges = cross_edges_from_logs(logs);
    if let Some(v) = first_violation(cut, &edges) {
        return Err(FleetError::InconsistentCut(v));
    }
    let mut partitions: Vec<FleetPartitionState> = Vec::new();
    let mut seen = (cut.offsets.len() >= PARTITION_INDEX_MIN).then(BTreeSet::new);
    let mut by_partition = PartitionLogs::new(logs, cut.offsets.len());
    for &(part, cut_off) in &cut.offsets {
        let repeated = match &mut seen {
            Some(seen) => !seen.insert(part),
            None => partitions.iter().any(|ps| ps.partition == part),
        };
        if repeated {
            continue;
        }
        let log_bytes = by_partition.get(part);
        let mut folder = Folder::new(cols, rows);
        let mut folded_through = None;
        for item in Log::read_bytes(log_bytes, Offset::ZERO) {
            let env = item.map_err(|err| FleetError::Read {
                partition: part,
                err,
            })?;
            if !fleet_seq_within_cut(env.seq.0, cut_off.0) {
                break;
            }
            let seq = Offset(fleet_clamp_to_cut(env.seq.0, cut_off.0));
            folded_through = Some(seq);
            folder.apply(&env.record);
            if seq == cut_off {
                break;
            }
        }
        partitions.push(FleetPartitionState {
            partition: part,
            snapshot: StateSnapshot::from_parts(folded_through, folder),
        });
    }
    Ok(FleetSnapshot {
        cut: cut.clone(),
        edges,
        partitions,
    })
}

fn legacy_resume(
    fleet: &FleetSnapshot,
    logs: &[(Partition, &[u8])],
) -> Result<Vec<(Partition, Screen)>, FleetError> {
    let mut out = Vec::new();
    for ps in &fleet.partitions {
        let log_bytes = logs
            .iter()
            .find(|&&(p, _)| p == ps.partition)
            .map_or(&[][..], |&(_, b)| b);
        let mut folder = ps.snapshot.clone_folder();
        let start_off = ps.snapshot.next_offset();
        for item in Log::read_bytes(log_bytes, Offset::ZERO) {
            let env = item.map_err(|err| FleetError::Read {
                partition: ps.partition,
                err,
            })?;
            if env.seq.0 >= start_off.0 {
                folder.apply(&env.record);
            }
        }
        out.push((ps.partition, folder.into_screen()));
    }
    Ok(out)
}

fn legacy_replay(
    cut: &Cut,
    p: Partition,
    bytes: &[u8],
    cols: u16,
    rows: u16,
) -> Result<CutReplay, ReadError> {
    let mut records = Vec::new();
    let mut folded_through = None;
    if let Some(cut_off) = cut.offset_of(p) {
        for item in Log::read_bytes(bytes, Offset::ZERO) {
            let env = item?;
            if !fleet_seq_within_cut(env.seq.0, cut_off.0) {
                break;
            }
            let seq = Offset(fleet_clamp_to_cut(env.seq.0, cut_off.0));
            folded_through = Some(seq);
            records.push(env.record);
            if seq == cut_off {
                break;
            }
        }
    }
    Ok(CutReplay {
        screen: screen::fold(cols, rows, &records),
        folded_through,
    })
}

fn log_bytes(id: u64, cause: Option<CausedBy>) -> Vec<u8> {
    let mut fx = Seeded::new(id);
    let mut log = Log::new();
    let records = [
        Record::Out(b"\x1b[3".to_vec()),
        Record::Out(format!("1m{id}\r\n\x1b]2;title").into_bytes()),
        Record::In {
            bytes: vec![b'i'; 128],
            client_id: id,
            client_seq: u64::MAX,
        },
        Record::Out(b"\x07end\xe2\x82".to_vec()),
        Record::Out(b"\xac\r\n".to_vec()),
        Record::Resize { cols: 13, rows: 4 },
    ];
    for (at, record) in records.into_iter().enumerate() {
        log.append_caused(&mut fx, record, if at == 2 { cause } else { None })
            .unwrap();
    }
    fx.disk().read_all().to_vec()
}

fn assert_materialized_equal(
    actual: Result<FleetSnapshot, FleetError>,
    expected: Result<FleetSnapshot, FleetError>,
) -> Option<FleetSnapshot> {
    match (actual, expected) {
        (Err(actual), Err(expected)) => {
            assert_eq!(actual, expected);
            None
        }
        (Ok(actual), Ok(expected)) => {
            assert_eq!(actual.cut, expected.cut);
            assert_eq!(actual.edges, expected.edges);
            assert_eq!(actual.partitions.len(), expected.partitions.len());
            for (actual, expected) in actual.partitions.iter().zip(expected.partitions) {
                assert_eq!(actual.partition, expected.partition);
                assert_eq!(
                    actual.snapshot.folded_through(),
                    expected.snapshot.folded_through()
                );
                assert_eq!(
                    actual.snapshot.clone_folder(),
                    expected.snapshot.clone_folder(),
                    "parser state and screen must match"
                );
            }
            Some(actual)
        }
        (actual, expected) => {
            panic!("different materialization outcomes: {actual:?} / {expected:?}")
        }
    }
}

fn next(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}

#[test]
fn indexed_fleet_matches_legacy_order_duplicates_missing_logs_and_errors() {
    let mut seed = 0x1d87_6e30_4a91_8bf5;
    for case in 0..512 {
        let mut owned: Vec<_> = (0..6)
            .map(|i| {
                let part = Partition(next(&mut seed) % 5);
                let cause = (next(&mut seed) % 3 == 0).then(|| CausedBy {
                    partition: Some(next(&mut seed) % 5),
                    offset: next(&mut seed) % 8,
                });
                (part, log_bytes(i + 1, cause))
            })
            .collect();
        for (_, bytes) in &mut owned {
            match next(&mut seed) % 5 {
                0 => {
                    let at = next(&mut seed) as usize % bytes.len();
                    bytes[at] ^= 0x80;
                }
                1 => bytes.truncate(next(&mut seed) as usize % bytes.len()),
                2 => bytes.extend_from_within(..), // a valid frame with a regressed seq
                _ => {}
            }
        }
        let logs: Vec<_> = owned.iter().map(|(p, b)| (*p, b.as_slice())).collect();
        let offsets = (0..next(&mut seed) % 13)
            .map(|_| {
                let part = Partition(next(&mut seed) % 7);
                let off = next(&mut seed) % 8;
                (part, Offset(if off == 7 { u64::MAX } else { off }))
            })
            .collect();
        let original = Cut { offsets };
        for indexed in [false, true] {
            let mut cut = original.clone();
            if indexed {
                // The policy now counts distinct partitions. Missing filler
                // partitions force the real indexed branch without introducing
                // causes for the original logs or changing their first offsets.
                for extra in 0..PARTITION_INDEX_MIN {
                    cut.offsets
                        .push((Partition(u64::MAX - extra as u64), Offset(0)));
                }
                cut.offsets.extend_from_within(..);
            }
            if let Some(mut fleet) = assert_materialized_equal(
                materialize_fleet_cut(&cut, &logs, 17, 5),
                legacy_materialize(&cut, &logs, 17, 5),
            ) {
                // Public snapshots may be reordered and contain duplicates.
                // Resume must preserve every entry on either lookup path.
                fleet.partitions.reverse();
                if let Some(first) = fleet.partitions.first().cloned() {
                    fleet.partitions.push(first);
                    if indexed {
                        while fleet.partitions.len() < PARTITION_INDEX_MIN {
                            let copy = fleet.partitions.clone();
                            fleet.partitions.extend(copy);
                        }
                    }
                }
                assert_eq!(
                    resume_fleet_cut(&fleet, &logs),
                    legacy_resume(&fleet, &logs),
                    "resume case {case}, indexed {indexed}"
                );
            }
        }
    }
}

#[test]
fn duplicate_heavy_public_cuts_use_distinct_lookup_count_and_preserve_first_offsets() {
    const N: usize = 16_384;
    let first = log_bytes(1, None);
    let later = log_bytes(2, None);
    let mut logs: Vec<_> = (0..N)
        .map(|i| (Partition(i as u64), b"".as_slice()))
        .collect();
    logs[N - 1].1 = first.as_slice();
    logs.push((Partition((N - 1) as u64), later.as_slice()));
    for part in [Partition((N - 1) as u64), Partition(N as u64)] {
        let mut cut = Cut {
            offsets: vec![(part, Offset(u64::MAX)); 4096],
        };
        cut.offsets[0].1 = Offset(1);
        let _ = take_lookup_hint();
        let actual = materialize_fleet_cut(&cut, &logs, 17, 5);
        assert_eq!(
            take_lookup_hint(),
            Some(1),
            "duplicates are not additional lookups"
        );
        let fleet =
            assert_materialized_equal(actual, legacy_materialize(&cut, &logs, 17, 5)).unwrap();
        assert_eq!(fleet.partitions.len(), 1);
        assert_eq!(fleet.cut, cut);
        assert_eq!(fleet.partitions[0].partition, part);
        assert_eq!(
            fleet.partitions[0].snapshot.folded_through(),
            if part.0 < N as u64 {
                Some(Offset(1))
            } else {
                None
            }
        );
        assert_eq!(
            resume_fleet_cut(&fleet, &logs),
            legacy_resume(&fleet, &logs)
        );

        // A cut with enough genuinely distinct partitions still indexes; both
        // duplicate cut offsets and duplicate supplied logs remain first-wins.
        for extra in 0..PARTITION_INDEX_MIN - 1 {
            cut.offsets.push((Partition(extra as u64), Offset(0)));
        }
        let actual = materialize_fleet_cut(&cut, &logs, 17, 5);
        assert_eq!(take_lookup_hint(), Some(PARTITION_INDEX_MIN));
        let fleet =
            assert_materialized_equal(actual, raw_count_materialize(&cut, &logs, 17, 5)).unwrap();
        assert_eq!(fleet.partitions.len(), PARTITION_INDEX_MIN);
        assert_eq!(fleet.partitions[0].partition, part);
    }
}

#[test]
fn later_duplicate_logs_still_determine_consistency_before_replay_errors() {
    let mut damaged = log_bytes(1, None);
    damaged[0] ^= 1;
    let valid = log_bytes(2, None);
    let caused = log_bytes(
        3,
        Some(CausedBy {
            partition: Some(99),
            offset: 7,
        }),
    );
    let logs = [
        (Partition(1), damaged.as_slice()),
        (Partition(2), valid.as_slice()),
        (Partition(2), caused.as_slice()),
    ];
    let cut = Cut {
        offsets: vec![(Partition(1), Offset(0)), (Partition(2), Offset(2))],
    };
    assert!(matches!(
        materialize_fleet_cut(&cut, &logs, 10, 3),
        Err(FleetError::InconsistentCut(v)) if v.edge.cause == (Partition(99), Offset(7))
    ));
    let cut = Cut {
        offsets: vec![
            (Partition(2), Offset(1)),
            (Partition(2), Offset(2)),
            (Partition(1), Offset(0)),
        ],
    };
    // The first cut occurrence excludes that edge. Replay then reports the
    // first corrupt requested log, despite another duplicate cut offset.
    assert!(matches!(
        materialize_fleet_cut(&cut, &logs, 10, 3),
        Err(FleetError::Read {
            partition: Partition(1),
            ..
        })
    ));
}

#[test]
fn replay_error_selection_follows_cut_and_snapshot_order() {
    let mut a = log_bytes(1, None);
    let mut b = log_bytes(2, None);
    a[0] ^= 1;
    b[0] ^= 1;
    let logs = [
        (Partition(1), a.as_slice()),
        (Partition(u64::MAX), b.as_slice()),
    ];
    let cut = Cut {
        offsets: vec![(Partition(u64::MAX), Offset(0)), (Partition(1), Offset(0))],
    };
    assert!(matches!(
        materialize_fleet_cut(&cut, &logs, 10, 3),
        Err(FleetError::Read {
            partition: Partition(u64::MAX),
            ..
        })
    ));
    let blank = || StateSnapshot::from_parts(None, Folder::new(10, 3));
    let mut fleet = FleetSnapshot {
        cut,
        edges: Vec::new(),
        partitions: vec![
            FleetPartitionState {
                partition: Partition(u64::MAX),
                snapshot: blank(),
            },
            FleetPartitionState {
                partition: Partition(1),
                snapshot: blank(),
            },
        ],
    };
    assert!(matches!(
        resume_fleet_cut(&fleet, &logs),
        Err(FleetError::Read {
            partition: Partition(u64::MAX),
            ..
        })
    ));
    fleet.partitions.reverse();
    assert!(matches!(
        resume_fleet_cut(&fleet, &logs),
        Err(FleetError::Read {
            partition: Partition(1),
            ..
        })
    ));
}

#[test]
fn streaming_cut_replay_matches_collected_prefix_at_every_byte_boundary() {
    let original = log_bytes(1, None);
    for end in 0..=original.len() {
        let mut bytes = original[..end].to_vec();
        for corrupt in [false, true] {
            if corrupt && !bytes.is_empty() {
                let at = bytes.len() / 2;
                bytes[at] ^= 0x40;
            }
            for off in [None, Some(0), Some(1), Some(3), Some(5), Some(u64::MAX)] {
                let cut = Cut {
                    offsets: off
                        .map(|off| vec![(Partition(1), Offset(off)), (Partition(1), Offset(0))])
                        .unwrap_or_default(),
                };
                match (
                    replay_to_cut(&cut, Partition(1), &bytes, 17, 5),
                    legacy_replay(&cut, Partition(1), &bytes, 17, 5),
                ) {
                    (Err(actual), Err(expected)) => assert_eq!(actual, expected),
                    (Ok(actual), Ok(expected)) => {
                        assert_eq!(actual.folded_through, expected.folded_through);
                        assert_eq!(actual.screen.serialize(), expected.screen.serialize());
                    }
                    (actual, expected) => panic!("replay mismatch: {actual:?} / {expected:?}"),
                }
            }
        }
    }
}

#[test]
fn partition_log_index_visits_each_directory_entry_at_most_once() {
    const N: usize = 16_384;
    let logs: Vec<_> = (0..N)
        .flat_map(|i| {
            [
                (Partition(i as u64), b"first".as_slice()),
                (Partition(i as u64), b"later"),
            ]
        })
        .collect();
    let mut index = PartitionLogs::new(&logs, N);
    assert_eq!(index.get(Partition(0)), b"first");
    assert_eq!(index.visited, 1, "do not index an unused suffix");
    assert_eq!(index.get(Partition(0)), b"first");
    assert_eq!(index.visited, 1);
    for part in (0..N as u64).rev() {
        assert_eq!(index.get(Partition(part)), b"first");
    }
    assert_eq!(index.get(Partition(u64::MAX)), b"");
    assert_eq!(index.visited, logs.len());
    for part in (0..N as u64).rev() {
        assert_eq!(index.get(Partition(part)), b"first");
    }
    assert_eq!(index.get(Partition(u64::MAX)), b"");
    assert_eq!(index.visited, logs.len());
    let empty_first = [(Partition(1), b"".as_slice()), (Partition(1), b"later")];
    let mut index = PartitionLogs::new(&empty_first, PARTITION_INDEX_MIN);
    assert_eq!(index.get(Partition(1)), b"");
    assert_eq!(index.get(Partition(0)), b"");
    assert_eq!(index.get(Partition(1)), b"");
}

#[test]
fn sparse_requests_keep_linear_scans_without_indexing_large_log_directories() {
    const N: usize = 16_384;
    let logs: Vec<_> = (0..N)
        .map(|i| (Partition(i as u64), b"bytes".as_slice()))
        .collect();
    for lookups in [1usize, 8] {
        for missing in [false, true] {
            let mut index = PartitionLogs::new(&logs, lookups);
            for at in 0..lookups {
                let part = Partition(if missing { N + at } else { N - at - 1 } as u64);
                let expected = logs
                    .iter()
                    .find(|&&(p, _)| p == part)
                    .map_or(&[][..], |&(_, b)| b);
                assert_eq!(index.get(part), expected);
            }
            assert!(!index.indexed);
            assert!(
                index.first.is_empty(),
                "do not allocate tree nodes for sparse requests"
            );
            assert_eq!(index.remaining.len(), logs.len());
        }
    }
}

#[test]
#[ignore = "manual fleet directory lookup CPU benchmark"]
fn partition_lookup_microbench() {
    use std::hint::black_box;
    use std::time::Instant;
    let force_index = std::env::var_os("FLEET_FORCE_INDEX").is_some();
    for n in [1usize, 8, 64, 128, 256, 512, 1024, 4096, 16_384] {
        let logs: Vec<_> = (0..n)
            .map(|i| (Partition(i as u64), b"bytes".as_slice()))
            .collect();
        for reverse in [false, true] {
            let queries: Vec<_> = (0..n)
                .map(|i| Partition(if reverse { n - i - 1 } else { i } as u64))
                .collect();
            let repeats = (16_384 / n).max(1);
            let mut indexed_ns = [0; 3];
            let mut legacy_ns = [0; 3];
            for run in 0..3 {
                let mut indexed = || {
                    let start = Instant::now();
                    for _ in 0..repeats {
                        let lookups = if force_index {
                            n.max(PARTITION_INDEX_MIN)
                        } else {
                            n
                        };
                        let mut index = PartitionLogs::new(black_box(&logs), lookups);
                        for &part in &queries {
                            black_box(index.get(black_box(part)));
                        }
                        assert_eq!(index.visited, if index.indexed { n } else { 0 });
                    }
                    indexed_ns[run] = start.elapsed().as_nanos();
                };
                let mut legacy = || {
                    let start = Instant::now();
                    for _ in 0..repeats {
                        let logs = black_box(&logs);
                        for &part in &queries {
                            let part = black_box(part);
                            black_box(logs.iter().find(|&&(p, _)| p == part).unwrap().1);
                        }
                    }
                    legacy_ns[run] = start.elapsed().as_nanos();
                };
                if run % 2 == 0 {
                    indexed();
                    legacy();
                } else {
                    legacy();
                    indexed();
                }
            }
            indexed_ns.sort_unstable();
            legacy_ns.sort_unstable();
            println!(
                "FLEET_LOOKUP partitions={n} reverse={reverse} batches={repeats} adaptive_ns={} legacy_ns={} speedup={:.2} adaptive_entries={} legacy_entries={} indexed={} force_index={force_index}",
                indexed_ns[1], legacy_ns[1], legacy_ns[1] as f64 / indexed_ns[1].max(1) as f64,
                if force_index || n >= PARTITION_INDEX_MIN { n } else { n * (n + 1) / 2 }, n * (n + 1) / 2, force_index || n >= PARTITION_INDEX_MIN
            );
        }
    }
}

#[test]
#[ignore = "manual sparse fleet-request CPU benchmark"]
fn sparse_request_lookup_microbench() {
    use std::hint::black_box;
    use std::time::Instant;
    const N: usize = 16_384;
    const BATCHES: usize = 128;
    let logs: Vec<_> = (0..N)
        .map(|i| (Partition(i as u64), b"bytes".as_slice()))
        .collect();
    for lookups in [1usize, 8] {
        for shape in ["first", "last", "absent"] {
            let queries: Vec<_> = (0..lookups)
                .map(|at| {
                    Partition(match shape {
                        "first" => at,
                        "last" => N - at - 1,
                        _ => N + at,
                    } as u64)
                })
                .collect();
            let mut adaptive_ns = [0; 3];
            let mut legacy_ns = [0; 3];
            for run in 0..3 {
                let mut adaptive = || {
                    let start = Instant::now();
                    for _ in 0..BATCHES {
                        let mut index = PartitionLogs::new(black_box(&logs), lookups);
                        for &part in &queries {
                            black_box(index.get(black_box(part)));
                        }
                    }
                    adaptive_ns[run] = start.elapsed().as_nanos();
                };
                let mut legacy = || {
                    let start = Instant::now();
                    for _ in 0..BATCHES {
                        let logs = black_box(&logs);
                        for &part in &queries {
                            let part = black_box(part);
                            black_box(
                                logs.iter()
                                    .find(|&&(p, _)| p == part)
                                    .map_or(&[][..], |&(_, b)| b),
                            );
                        }
                    }
                    legacy_ns[run] = start.elapsed().as_nanos();
                };
                if run % 2 == 0 {
                    adaptive();
                    legacy();
                } else {
                    legacy();
                    adaptive();
                }
            }
            adaptive_ns.sort_unstable();
            legacy_ns.sort_unstable();
            println!("SPARSE_FLEET_LOOKUP logs={N} lookups={lookups} shape={shape} batches={BATCHES} adaptive_ns={} legacy_ns={} speedup={:.2} indexed=false", adaptive_ns[1], legacy_ns[1], legacy_ns[1] as f64 / adaptive_ns[1].max(1) as f64);
        }
    }
}

#[test]
#[ignore = "manual duplicate-heavy public fleet materialization benchmark"]
fn duplicate_cut_materialization_microbench() {
    use std::hint::black_box;
    use std::time::Instant;
    let bytes = log_bytes(1, None);
    for n in [1024usize, 16_384] {
        let mut logs: Vec<_> = (0..n)
            .map(|i| (Partition(i as u64), b"".as_slice()))
            .collect();
        logs[n - 1].1 = bytes.as_slice();
        for duplicates in [128usize, 4096] {
            for shape in ["last", "absent"] {
                let part = Partition(if shape == "last" { n - 1 } else { n } as u64);
                let mut cut = Cut {
                    offsets: vec![(part, Offset(u64::MAX)); duplicates],
                };
                cut.offsets[0].1 = Offset(1);
                let mut distinct_ns = [0; 3];
                let mut raw_ns = [0; 3];
                for run in 0..3 {
                    let mut distinct = || {
                        let start = Instant::now();
                        let snapshot =
                            materialize_fleet_cut(black_box(&cut), black_box(&logs), 17, 5);
                        distinct_ns[run] = start.elapsed().as_nanos();
                        assert_eq!(take_lookup_hint(), Some(1));
                        snapshot
                    };
                    let mut raw = || {
                        let start = Instant::now();
                        let snapshot =
                            raw_count_materialize(black_box(&cut), black_box(&logs), 17, 5);
                        raw_ns[run] = start.elapsed().as_nanos();
                        assert_eq!(take_lookup_hint(), Some(duplicates));
                        snapshot
                    };
                    let (actual, previous) = if run % 2 == 0 {
                        (distinct(), raw())
                    } else {
                        let previous = raw();
                        (distinct(), previous)
                    };
                    let actual = assert_materialized_equal(actual, previous).unwrap();
                    assert_eq!(actual.partitions.len(), 1);
                    assert_eq!(actual.partitions[0].partition, part);
                    black_box(actual);
                }
                distinct_ns.sort_unstable();
                raw_ns.sort_unstable();
                println!(
                    "DUPLICATE_FLEET_MATERIALIZE logs={n} cut_entries={duplicates} distinct_partitions=1 shape={shape} distinct_hint_ns={} raw_hint_ns={} speedup={:.2} cached_directory_headers_before={n} cached_directory_headers_after=0 accounting=structural_not_allocator_peak",
                    distinct_ns[1], raw_ns[1], raw_ns[1] as f64 / distinct_ns[1].max(1) as f64
                );
            }
        }
    }
}

#[test]
#[ignore = "manual replay CPU and structural retained-body benchmark"]
fn streaming_replay_retention_microbench() {
    use std::hint::black_box;
    use std::time::Instant;
    fn body_bytes(record: &Record) -> usize {
        match record {
            Record::In { bytes, .. } | Record::Out(bytes) => bytes.len(),
            Record::Resize { .. } | Record::Exit { .. } => 0,
        }
    }
    for n in [1024usize, 16_384, 65_536] {
        let mut fx = Seeded::new(1);
        let mut log = Log::new();
        let input = Record::In {
            bytes: vec![b'x'; 1024],
            client_id: 1,
            client_seq: 1,
        };
        for at in 0..n {
            let record = if at + 1 == n {
                Record::Out(b"\x1b[31mvisible\x1b[0m".to_vec())
            } else {
                input.clone()
            };
            log.append(&mut fx, record).unwrap();
        }
        let bytes = fx.disk().read_all();
        let cut = Cut {
            offsets: vec![(Partition(1), Offset(u64::MAX))],
        };
        let mut sum_bodies = 0;
        let mut max_body = 0;
        for env in Log::read_bytes(bytes, Offset::ZERO) {
            let size = body_bytes(&env.unwrap().record);
            sum_bodies += size;
            max_body = max_body.max(size);
        }
        assert_eq!(sum_bodies, (n - 1) * 1024 + b"\x1b[31mvisible\x1b[0m".len());
        assert_eq!(max_body, 1024);
        let mut stream_ns = [0; 3];
        let mut collect_ns = [0; 3];
        for run in 0..3 {
            let mut streaming = || {
                let start = Instant::now();
                let result =
                    replay_to_cut(black_box(&cut), Partition(1), black_box(bytes), 80, 24).unwrap();
                stream_ns[run] = start.elapsed().as_nanos();
                result
            };
            let mut collected = || {
                let start = Instant::now();
                // Both variants intentionally use the new reader, isolating
                // retained-prefix storage from the separate frame-copy change.
                let result =
                    legacy_replay(black_box(&cut), Partition(1), black_box(bytes), 80, 24).unwrap();
                collect_ns[run] = start.elapsed().as_nanos();
                result
            };
            let (streamed, collected) = if run % 2 == 0 {
                (streaming(), collected())
            } else {
                let reference = collected();
                (streaming(), reference)
            };
            assert_eq!(streamed.folded_through, collected.folded_through);
            assert_eq!(streamed.screen.serialize(), collected.screen.serialize());
            assert!(streamed.screen.line_text(0).contains("visible"));
        }
        stream_ns.sort_unstable();
        collect_ns.sort_unstable();
        println!(
            "FLEET_REPLAY records={n} log_bytes={} stream_ns={} collect_ns={} collected_owned_body_bytes={sum_bodies} streaming_owned_body_upper={max_body} collected_logical_record_header_bytes={} accounting=structural_not_allocator_peak",
            bytes.len(), stream_ns[1], collect_ns[1], n * std::mem::size_of::<Record>()
        );
    }
}
