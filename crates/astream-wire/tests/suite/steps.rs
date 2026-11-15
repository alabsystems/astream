//! Claim `wire.steps.torn-vs-fault`: `astream_wire::steps` is astream's generic
//! opaque record — a dense, versioned, CRC-framed step record — and its scan
//! tells a torn tail from a fault at ANY base step, not only from step 0.
//!
//! The encoder writes exactly the documented bytes (checked against a record
//! built by hand from the layout, not from the encoder, and stamped with the
//! literal version byte every record on disk holds, 1, under which a hand-made
//! record also reads back). A run of records at an arbitrary base scans back
//! `Clean`, and each accepted record's range slices out exactly its body
//! (proptest). Cutting a run whose bodies nest no frame at ANY byte — every place
//! a writer can die in the middle of an append — is `Clean` at a record boundary
//! and `Torn` anywhere else, never a fault, with every record before the cut
//! intact (proptest). A body that nests a whole frame is the case the classifier
//! cannot tell from damage: a cut past the nested frame's last byte is a
//! `LengthPastEnd` fault at its record and a cut before it `Torn`, keeping the
//! record before it either way, and a damaged last record that nests one is
//! `CorruptFrame` (fixture and proptest). Damaging one payload byte of a record
//! that has an intact record after it is a `CorruptFrame` fault at that record's
//! offset; the same damage to the last record is a torn tail (proptest; CRC-32
//! detects every single-byte error, so the outcome is exact). A whole run followed
//! by zero bytes of any length, shorter than a frame header or not (what a ring's
//! writer leaves before its physical end), is `Torn` with `valid_len` at the last
//! record's end and every record kept, never a fault, while the same zeros with the
//! run's next record after them are a `CorruptFrame` fault at the first zero
//! (proptest). The fixtures re-run
//! the engine journal's torn and fault cases at a non-zero base: a truncated last
//! record, a corrupt middle record, a skipped, repeated or early step, a rotted
//! length, an unreadable record. The count never wraps: an intact record after
//! step `u64::MAX` is a `PastLastStep` fault, never a torn tail, while what is not
//! an intact step record there is classified as anywhere else. And a region
//! bounded by a commit word scans `Clean` below the word even while a
//! half-written record sits above it, and `Torn` past the word, keeping exactly
//! the records below it.

use astream_wire::steps::{
    decode_step, encode_step, scan_steps_from, StepEnd, StepFault, StepScan, STEP_HEADER,
    STEP_VERSION,
};
use astream_wire::{Frame, FrameError, HEADER_SIZE};
use proptest::prelude::*;

/// A base step far from zero, so nothing here passes by assuming a run starts
/// at step 0.
const K: u64 = 0x0000_7F3A_0000_0029;

/// The version byte every step record already on disk holds: every workflow
/// journal written since the record existed, and every record an embedder keeps.
/// Written as a literal, not as `STEP_VERSION`, because it is a fact about bytes
/// that exist, not about this build: a build that moved the constant would pass
/// every test that reads the constant back, and then refuse every journal on
/// disk as `BadStep` at byte 0. The hand-made records below are stamped with it.
const ON_DISK_STEP_VERSION: u8 = 1;

/// A step record built by hand from the documented layout — `version | step u64
/// LE | len u32 LE | body` inside a CRC frame — independently of the encoder.
fn step_frame(version: u8, step: u64, body: &[u8]) -> Vec<u8> {
    let mut p = vec![version];
    p.extend_from_slice(&step.to_le_bytes());
    p.extend_from_slice(&(body.len() as u32).to_le_bytes());
    p.extend_from_slice(body);
    Frame::new(p).encode().unwrap()
}

/// A run of records with steps `first, first + 1, …`, and where each record
/// starts and ends.
struct Run {
    bytes: Vec<u8>,
    starts: Vec<usize>,
    ends: Vec<usize>,
}

fn run(first: u64, bodies: &[Vec<u8>]) -> Run {
    let mut bytes = Vec::new();
    let mut starts = Vec::new();
    let mut ends = Vec::new();
    for (i, body) in bodies.iter().enumerate() {
        starts.push(bytes.len());
        bytes.extend_from_slice(&encode_step(first + i as u64, body).unwrap());
        ends.push(bytes.len());
    }
    Run {
        bytes,
        starts,
        ends,
    }
}

/// The steps a scan accepted, without their ranges.
fn step_numbers(scan: &StepScan) -> Vec<u64> {
    scan.steps.iter().map(|(step, _)| *step).collect()
}

/// The bodies a scan accepted, sliced out of the scanned bytes by their ranges.
fn bodies_of(bytes: &[u8], scan: &StepScan) -> Vec<Vec<u8>> {
    scan.steps
        .iter()
        .map(|(_, range)| bytes[range.clone()].to_vec())
        .collect()
}

/// Bodies that never hold the frame magic's first byte, so no frame can start
/// inside one: a cut or a damaged byte then has nothing decodable after it
/// unless a later record is really there. (A frame starting inside a record's
/// header would also need a CRC-32 match over bytes nobody chose.) This is the
/// precondition of "a cut is never a fault", not a way around a case: a body
/// that DOES nest a frame turns some cuts into faults, and
/// `a_body_that_nests_a_frame_turns_a_cut_past_it_into_a_fault` and the
/// `a_cut_past_a_nested_frame_is_a_fault_and_before_it_torn` property pin
/// exactly which.
fn body() -> impl Strategy<Value = Vec<u8>> {
    prop::collection::vec(
        any::<u8>().prop_filter("not the magic's first byte", |b| *b != 0xA5),
        0..48,
    )
}

#[test]
fn encode_step_writes_the_documented_bytes() {
    for (step, body) in [
        (0u64, &b""[..]),
        (3, &b"hello"[..]),
        (K, &b"a body of some length"[..]),
        (u64::MAX, &[0xA5, 0x71, 0x01, 0x00][..]),
    ] {
        let bytes = encode_step(step, body).unwrap();
        assert_eq!(
            bytes,
            step_frame(ON_DISK_STEP_VERSION, step, body),
            "step {step}"
        );
        assert_eq!(bytes.len(), HEADER_SIZE + STEP_HEADER + body.len());
        let frame = Frame::decode(&bytes).unwrap().unwrap().frame;
        assert_eq!(decode_step(&frame.payload), Some((step, body)));
    }
}

#[test]
fn a_record_already_on_disk_still_reads() {
    // The other direction of the version pin: a record built by hand with the
    // byte journals on disk hold is a step record this build reads, alone and as
    // a run, so a journal written by an earlier build opens.
    let mut bytes = step_frame(ON_DISK_STEP_VERSION, K, b"acked");
    bytes.extend_from_slice(&step_frame(ON_DISK_STEP_VERSION, K + 1, b""));
    let frame = Frame::decode(&bytes).unwrap().unwrap();
    assert_eq!(decode_step(&frame.frame.payload), Some((K, &b"acked"[..])));
    let scan = scan_steps_from(&bytes, K);
    assert_eq!(
        (step_numbers(&scan), scan.valid_len, scan.end),
        (vec![K, K + 1], bytes.len(), StepEnd::Clean)
    );
}

#[test]
fn empty_bytes_are_a_clean_empty_run_at_any_base() {
    for first in [0, K, u64::MAX] {
        let scan = scan_steps_from(&[], first);
        assert_eq!(
            scan,
            StepScan {
                steps: Vec::new(),
                valid_len: 0,
                end: StepEnd::Clean
            }
        );
    }
}

#[test]
fn a_truncated_last_record_is_torn_at_a_nonzero_base() {
    let r = run(K, &[b"a".to_vec(), b"bb".to_vec(), b"ccc".to_vec()]);
    let cut = &r.bytes[..r.bytes.len() - 1];
    let scan = scan_steps_from(cut, K);
    assert_eq!(step_numbers(&scan), vec![K, K + 1]);
    assert_eq!(bodies_of(cut, &scan), vec![b"a".to_vec(), b"bb".to_vec()]);
    assert_eq!(scan.valid_len, r.ends[1]);
    assert_eq!(scan.end, StepEnd::Torn);
}

#[test]
fn a_corrupt_middle_record_with_an_intact_one_after_it_is_a_fault_at_a_nonzero_base() {
    let r = run(K, &[b"a".to_vec(), b"bb".to_vec(), b"ccc".to_vec()]);
    let mut rot = r.bytes.clone();
    // A body byte of the middle record: its frame CRC no longer matches.
    rot[r.ends[1] - 1] ^= 0x01;
    let scan = scan_steps_from(&rot, K);
    assert_eq!(step_numbers(&scan), vec![K]);
    assert_eq!(scan.valid_len, r.starts[1]);
    assert_eq!(
        scan.end,
        StepEnd::Fault {
            at: r.starts[1],
            kind: StepFault::CorruptFrame(FrameError::ChecksumMismatch)
        }
    );
    // A broken magic in the middle record is the same fault, named for its cause.
    let mut rot = r.bytes.clone();
    rot[r.starts[1]] = 0x00;
    assert_eq!(
        scan_steps_from(&rot, K).end,
        StepEnd::Fault {
            at: r.starts[1],
            kind: StepFault::CorruptFrame(FrameError::BadMagic)
        }
    );
}

#[test]
fn a_skipped_repeated_or_early_step_is_out_of_order_at_a_nonzero_base() {
    // K, K+1, then K+3 where K+2 was expected.
    let mut bytes = encode_step(K, b"a").unwrap();
    bytes.extend_from_slice(&encode_step(K + 1, b"b").unwrap());
    let at = bytes.len();
    bytes.extend_from_slice(&encode_step(K + 3, b"c").unwrap());
    let scan = scan_steps_from(&bytes, K);
    assert_eq!(step_numbers(&scan), vec![K, K + 1]);
    assert_eq!(scan.valid_len, at);
    assert_eq!(
        scan.end,
        StepEnd::Fault {
            at,
            kind: StepFault::OutOfOrder {
                expected: K + 2,
                found: K + 3
            }
        }
    );

    // A run that starts at K+1, scanned as if it started at K.
    let early = encode_step(K + 1, b"b").unwrap();
    assert_eq!(
        scan_steps_from(&early, K).end,
        StepEnd::Fault {
            at: 0,
            kind: StepFault::OutOfOrder {
                expected: K,
                found: K + 1
            }
        }
    );

    // A repeated step.
    let mut repeat = encode_step(K, b"a").unwrap();
    let at = repeat.len();
    repeat.extend_from_slice(&encode_step(K, b"a").unwrap());
    let scan = scan_steps_from(&repeat, K);
    assert_eq!(step_numbers(&scan), vec![K]);
    assert_eq!(
        scan.end,
        StepEnd::Fault {
            at,
            kind: StepFault::OutOfOrder {
                expected: K + 1,
                found: K
            }
        }
    );
}

#[test]
fn a_run_from_zero_scanned_from_five_is_out_of_order_at_byte_zero() {
    let r = run(0, &[b"a".to_vec(), b"b".to_vec(), b"c".to_vec()]);
    assert_eq!(
        scan_steps_from(&r.bytes, 5),
        StepScan {
            steps: Vec::new(),
            valid_len: 0,
            end: StepEnd::Fault {
                at: 0,
                kind: StepFault::OutOfOrder {
                    expected: 5,
                    found: 0
                }
            }
        }
    );
}

#[test]
fn a_rotted_length_is_a_fault_mid_run_and_torn_on_the_last_record() {
    let r = run(K, &[b"a".to_vec(), b"bb".to_vec(), b"ccc".to_vec()]);
    let past_end = (2 * r.bytes.len()) as u32;

    // The middle record's length now runs past the end, but the last record is
    // intact behind it: a damaged header, not a torn write.
    let mut rot = r.bytes.clone();
    rot[r.starts[1] + 4..r.starts[1] + 8].copy_from_slice(&past_end.to_le_bytes());
    let scan = scan_steps_from(&rot, K);
    assert_eq!(
        (step_numbers(&scan), scan.valid_len),
        (vec![K], r.starts[1])
    );
    assert_eq!(
        scan.end,
        StepEnd::Fault {
            at: r.starts[1],
            kind: StepFault::LengthPastEnd
        }
    );

    // The same rot on the LAST record has nothing decodable after it: it is
    // indistinguishable from a torn write.
    let mut last = r.bytes.clone();
    last[r.starts[2] + 4..r.starts[2] + 8].copy_from_slice(&past_end.to_le_bytes());
    let scan = scan_steps_from(&last, K);
    assert_eq!(
        (step_numbers(&scan), scan.end),
        (vec![K, K + 1], StepEnd::Torn)
    );
}

#[test]
fn an_unreadable_step_record_is_bad_step_at_a_nonzero_base() {
    // Another STEP_VERSION, intact under its CRC.
    let mut bytes = encode_step(K, b"a").unwrap();
    let at = bytes.len();
    bytes.extend_from_slice(&step_frame(STEP_VERSION + 1, K + 1, b"b"));
    let scan = scan_steps_from(&bytes, K);
    assert_eq!(step_numbers(&scan), vec![K]);
    assert_eq!(
        scan.end,
        StepEnd::Fault {
            at,
            kind: StepFault::BadStep
        }
    );

    // A body length past the payload, intact under its CRC.
    let mut p = vec![STEP_VERSION];
    p.extend_from_slice(&(K + 1).to_le_bytes());
    p.extend_from_slice(&9u32.to_le_bytes());
    p.extend_from_slice(b"short");
    let mut bytes = encode_step(K, b"a").unwrap();
    bytes.extend_from_slice(&Frame::new(p).encode().unwrap());
    assert_eq!(
        scan_steps_from(&bytes, K).end,
        StepEnd::Fault {
            at,
            kind: StepFault::BadStep
        }
    );
}

#[test]
fn a_record_after_the_last_step_is_a_fault_never_a_torn_tail() {
    // u64::MAX is the last step a run can hold: the count does not wrap.
    let mut last = encode_step(u64::MAX - 1, b"a").unwrap();
    last.extend_from_slice(&encode_step(u64::MAX, b"b").unwrap());
    let at = last.len();
    let scan = scan_steps_from(&last, u64::MAX - 1);
    assert_eq!(step_numbers(&scan), vec![u64::MAX - 1, u64::MAX]);
    assert_eq!((scan.valid_len, scan.end), (at, StepEnd::Clean));

    // An intact record after it cannot be in order, whatever step it names: a
    // fault at that record, keeping the run before it. Not Torn, which a file's
    // reader may truncate away with a record that was acknowledged; not a step 0
    // accepted as the next.
    let past = |found: u64| StepEnd::Fault {
        at,
        kind: StepFault::PastLastStep { found },
    };
    for found in [0, 1, u64::MAX] {
        let mut bytes = last.clone();
        bytes.extend_from_slice(&encode_step(found, b"c").unwrap());
        let scan = scan_steps_from(&bytes, u64::MAX - 1);
        assert_eq!(step_numbers(&scan), vec![u64::MAX - 1, u64::MAX]);
        assert_eq!(scan.valid_len, at);
        assert_eq!(scan.end, past(found), "a record at step {found}");
        // With more intact records behind it the fault is the same one, at the
        // same record: not a LengthPastEnd blamed on a length that is sound.
        bytes.extend_from_slice(&encode_step(found.wrapping_add(1), b"d").unwrap());
        assert_eq!(
            scan_steps_from(&bytes, u64::MAX - 1).end,
            past(found),
            "a record at step {found}, then another"
        );
    }

    // What is not an intact step record there is classified as anywhere else:
    // an intact frame of another step version is BadStep ...
    let mut foreign = last.clone();
    foreign.extend_from_slice(&step_frame(STEP_VERSION + 1, 0, b"c"));
    assert_eq!(
        scan_steps_from(&foreign, u64::MAX - 1).end,
        StepEnd::Fault {
            at,
            kind: StepFault::BadStep
        }
    );
    // ... a record cut short is the torn tail a crash leaves ...
    let next = encode_step(0, b"c").unwrap();
    let mut torn = last.clone();
    torn.extend_from_slice(&next[..next.len() - 1]);
    let scan = scan_steps_from(&torn, u64::MAX - 1);
    assert_eq!((scan.valid_len, scan.end), (at, StepEnd::Torn));
    // ... and a corrupt record with an intact one behind it is CorruptFrame.
    let mut rot = last.clone();
    rot.extend_from_slice(&next);
    let rotted = rot.len() - 1;
    rot[rotted] ^= 0x01;
    rot.extend_from_slice(&encode_step(1, b"d").unwrap());
    assert_eq!(
        scan_steps_from(&rot, u64::MAX - 1).end,
        StepEnd::Fault {
            at,
            kind: StepFault::CorruptFrame(FrameError::ChecksumMismatch)
        }
    );
}

/// A record whose body nests an encoded frame: `prefix | inner | suffix`, where
/// `inner` is a whole step record. Returns the run (`acked` at `first`, then the
/// nesting record) and where the inner frame starts and ends in its bytes.
fn nesting_run(
    first: u64,
    prefix: &[u8],
    inner: &[u8],
    suffix: &[u8],
) -> (Run, std::ops::Range<usize>) {
    let mut nesting = prefix.to_vec();
    nesting.extend_from_slice(inner);
    nesting.extend_from_slice(suffix);
    let r = run(first, &[b"acked".to_vec(), nesting]);
    let start = r.starts[1] + HEADER_SIZE + STEP_HEADER + prefix.len();
    (r, start..start + inner.len())
}

#[test]
fn a_body_that_nests_a_frame_turns_a_cut_past_it_into_a_fault() {
    // A step whose output embeds an astream record — plausible for a workflow
    // built on astream. The classifier cannot tell the nested frame from one
    // that follows damage, so a crash's tail can read as a fault (the module doc
    // of `astream_wire::steps` says why, and what it costs).
    let inner = encode_step(0, b"inner payload").unwrap();
    let (r, nested) = nesting_run(K, b"prefix-", &inner, b"-suffix");

    // Intact, the record is accepted whole: the scan steps over it by its
    // length and never looks inside its body.
    let scan = scan_steps_from(&r.bytes, K);
    assert_eq!(
        (step_numbers(&scan), scan.valid_len, &scan.end),
        (vec![K, K + 1], r.bytes.len(), &StepEnd::Clean)
    );

    for cut in r.ends[0] + 1..r.ends[1] {
        let scan = scan_steps_from(&r.bytes[..cut], K);
        // The prefix is the acked record whatever the verdict: the nested frame
        // never costs a record anyone was told was committed.
        assert_eq!(
            (step_numbers(&scan), scan.valid_len),
            (vec![K], r.ends[0]),
            "cut at byte {cut}"
        );
        let want = if cut < nested.end {
            // Before the nested frame is whole, nothing decodes after the
            // partial record: the torn tail a crash leaves.
            StepEnd::Torn
        } else {
            // From its last byte on, a complete frame decodes behind the
            // partial record, which is what a rotted length looks like: a fault
            // where a crash left only a torn tail. A file's reader refuses here.
            StepEnd::Fault {
                at: r.starts[1],
                kind: StepFault::LengthPastEnd,
            }
        };
        assert_eq!(scan.end, want, "cut at byte {cut}");
    }

    // A damaged last record that nests a frame is CorruptFrame, where the same
    // damage to a record that nests none is a torn tail.
    let mut rot = r.bytes.clone();
    rot[r.ends[1] - 1] ^= 0x01;
    let scan = scan_steps_from(&rot, K);
    assert_eq!(
        (scan.valid_len, scan.end),
        (
            r.ends[0],
            StepEnd::Fault {
                at: r.starts[1],
                kind: StepFault::CorruptFrame(FrameError::ChecksumMismatch)
            }
        )
    );
}

#[test]
fn a_region_scanned_below_its_commit_word_is_clean_while_a_record_is_half_written() {
    // The writer copied two records and stored the word one past them, then died
    // part-way through copying a third. A reader scans below the word only.
    let r = run(
        K,
        &[b"keyframe".to_vec(), b"chunk".to_vec(), b"half".to_vec()],
    );
    let commit = r.ends[1];
    let mut region = vec![0u8; r.bytes.len() + 64];
    region[..r.bytes.len() - 3].copy_from_slice(&r.bytes[..r.bytes.len() - 3]);
    let scan = scan_steps_from(&region[..commit], K);
    assert_eq!(scan.end, StepEnd::Clean);
    assert_eq!(
        bodies_of(&region, &scan),
        vec![b"keyframe".to_vec(), b"chunk".to_vec()]
    );
    // Past the word the same bytes read as a torn tail — which is why a region
    // reader never looks there, and treats any non-Clean end below it as a fault.
    // The torn scan keeps exactly what the word admitted: the half-written record
    // and the zeros after it cost no record before them.
    let past = scan_steps_from(&region, K);
    assert_eq!(past.end, StepEnd::Torn);
    assert_eq!(past.valid_len, commit);
    assert_eq!(past.steps, scan.steps);
}

proptest! {
    /// N records encoded at a random base scan back Clean, numbered from the
    /// base, and each range slices out exactly its body.
    #[test]
    fn a_run_at_any_base_scans_clean_and_its_ranges_slice_to_the_bodies(
        first in 0u64..=u64::MAX - 16,
        bodies in prop::collection::vec(body(), 0..12),
    ) {
        let r = run(first, &bodies);
        let scan = scan_steps_from(&r.bytes, first);
        prop_assert_eq!(&scan.end, &StepEnd::Clean);
        prop_assert_eq!(scan.valid_len, r.bytes.len());
        let want: Vec<u64> = (0..bodies.len() as u64).map(|i| first + i).collect();
        prop_assert_eq!(step_numbers(&scan), want);
        prop_assert_eq!(bodies_of(&r.bytes, &scan), bodies);
    }

    /// A cut at every byte of a run — every place a writer can die in the middle
    /// of an append — is Clean at a record boundary and Torn anywhere else, never
    /// a fault, and keeps every record that ends at or before the cut. Its bodies
    /// nest no frame (see `body`); the next property is the run whose body does.
    #[test]
    fn a_cut_anywhere_is_clean_or_torn_never_a_fault(
        first in 0u64..=u64::MAX - 16,
        bodies in prop::collection::vec(body(), 1..6),
    ) {
        let r = run(first, &bodies);
        for cut in 0..=r.bytes.len() {
            let kept = r.ends.iter().filter(|end| **end <= cut).count();
            let valid_len = if kept == 0 { 0 } else { r.ends[kept - 1] };
            let scan = scan_steps_from(&r.bytes[..cut], first);
            let want_end = if cut == valid_len { StepEnd::Clean } else { StepEnd::Torn };
            prop_assert_eq!(&scan.end, &want_end, "cut at byte {}", cut);
            prop_assert_eq!(scan.valid_len, valid_len);
            prop_assert_eq!(bodies_of(&r.bytes, &scan), bodies[..kept].to_vec());
        }
    }

    /// The other side of that property: a record whose body nests a whole step
    /// record (at any step, anywhere in the body), cut at every byte from the
    /// record before it to its own end, is Torn until the nested frame is whole
    /// and a LengthPastEnd fault at the record from the nested frame's last byte
    /// on — never anything that drops the record before it — and Clean at either
    /// record boundary.
    #[test]
    fn a_cut_past_a_nested_frame_is_a_fault_and_before_it_torn(
        first in 0u64..=u64::MAX - 16,
        prefix in body(),
        inner_step in any::<u64>(),
        inner_body in body(),
        suffix in body(),
    ) {
        let inner = encode_step(inner_step, &inner_body).unwrap();
        let (r, nested) = nesting_run(first, &prefix, &inner, &suffix);
        for cut in r.ends[0]..=r.ends[1] {
            let scan = scan_steps_from(&r.bytes[..cut], first);
            let (kept, want_end) = if cut == r.ends[1] {
                (2, StepEnd::Clean)
            } else if cut == r.ends[0] {
                (1, StepEnd::Clean)
            } else if cut < nested.end {
                (1, StepEnd::Torn)
            } else {
                (
                    1,
                    StepEnd::Fault {
                        at: r.starts[1],
                        kind: StepFault::LengthPastEnd,
                    },
                )
            };
            prop_assert_eq!(&scan.end, &want_end, "cut at byte {}", cut);
            prop_assert_eq!(scan.valid_len, r.ends[kept - 1]);
            prop_assert_eq!(scan.steps.len(), kept);
        }
    }

    /// A whole run followed by zero bytes, as many as a ring's writer leaves before
    /// its physical end when the next record would straddle it (aterm-restore's
    /// history ring writes that record at the ring's start instead): any count of
    /// them, fewer than a frame header's 12, exactly 12, or more, ends Torn, with
    /// `valid_len` at the last record's end and every record kept, never a fault. So
    /// a reader that finds only zeros past `valid_len` knows the scan stopped exactly
    /// where they start. No zeros at all is Clean. NEGATIVE CONTROL: the same zeros
    /// with the run's next record after them, as a scan across the gap would read
    /// them, are a CorruptFrame fault at the first zero, the same records kept: the
    /// rule is "nothing decodable after", not "zeros".
    #[test]
    fn a_run_then_zeros_of_any_length_is_torn_at_the_last_record(
        first in 0u64..=u64::MAX - 16,
        bodies in prop::collection::vec(body(), 0..6),
        zeros in 0usize..64,
    ) {
        let r = run(first, &bodies);
        let valid_len = r.bytes.len();
        let mut gap = r.bytes.clone();
        gap.resize(valid_len + zeros, 0);
        let scan = scan_steps_from(&gap, first);
        let want_end = if zeros == 0 { StepEnd::Clean } else { StepEnd::Torn };
        prop_assert_eq!(&scan.end, &want_end, "{} zeros", zeros);
        prop_assert_eq!(scan.valid_len, valid_len);
        prop_assert_eq!(bodies_of(&gap, &scan), bodies.clone());

        let next = first + bodies.len() as u64;
        let mut across = gap.clone();
        across.extend_from_slice(&encode_step(next, b"next").unwrap());
        let scan = scan_steps_from(&across, first);
        if zeros == 0 {
            prop_assert_eq!(&scan.end, &StepEnd::Clean);
            prop_assert_eq!(scan.steps.len(), bodies.len() + 1);
        } else {
            prop_assert_eq!(
                &scan.end,
                &StepEnd::Fault {
                    at: valid_len,
                    kind: StepFault::CorruptFrame(FrameError::BadMagic),
                },
                "{} zeros, then a record",
                zeros
            );
            prop_assert_eq!(scan.valid_len, valid_len);
            prop_assert_eq!(bodies_of(&across, &scan), bodies);
        }
    }

    /// One damaged payload byte in record i is a CorruptFrame fault at record i
    /// when an intact record follows it, and a torn tail when it is the last. The
    /// records before it survive either way.
    #[test]
    fn a_damaged_payload_byte_is_a_fault_unless_nothing_follows_it(
        first in 0u64..=u64::MAX - 16,
        bodies in prop::collection::vec(body(), 1..6),
        which in any::<prop::sample::Index>(),
        at in any::<prop::sample::Index>(),
    ) {
        let r = run(first, &bodies);
        let i = which.index(bodies.len());
        // A byte of the payload (past the frame header), which the CRC covers.
        let payload_len = r.ends[i] - r.starts[i] - HEADER_SIZE;
        let byte = r.starts[i] + HEADER_SIZE + at.index(payload_len);
        let mut damaged = r.bytes.clone();
        // Never the magic's first byte, so the damage cannot start a frame.
        damaged[byte] = if damaged[byte] == 0 { 1 } else { 0 };
        let scan = scan_steps_from(&damaged, first);
        prop_assert_eq!(scan.valid_len, r.starts[i]);
        prop_assert_eq!(bodies_of(&damaged, &scan), bodies[..i].to_vec());
        let want_end = if i + 1 < bodies.len() {
            StepEnd::Fault {
                at: r.starts[i],
                kind: StepFault::CorruptFrame(FrameError::ChecksumMismatch),
            }
        } else {
            StepEnd::Torn
        };
        prop_assert_eq!(scan.end, want_end);
    }
}
