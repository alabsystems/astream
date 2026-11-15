//! Evidence that moving the step codec into `astream_wire::steps` changed no
//! verdict of the workflow journal's recovery (`engine.durable.exactly-once-resume`).
//!
//! `scan_steps` now maps `astream_wire::steps::scan_steps_from(bytes, 0)` onto
//! the journal's `StepScan`. This test holds it to the scanner it replaced,
//! copied below verbatim from `durable.rs` and `store.rs` as they stood before
//! the move (astream `77c37f8`) and kept here as a frozen oracle: over journals
//! built from in-order, skipped, repeated and foreign-version step records and
//! then bit-flipped, length-rotted and truncated at random, and over arbitrary
//! bytes, both scanners return the same committed outputs, the same prefix
//! length and the same `Tail`, fault offset and kind included.
//!
//! The oracle keeps its own `STEP_VERSION = 1`, as `durable.rs` declared it, and
//! every journal here is stamped with it: the byte journals on disk hold is a
//! fact the oracle carries, so a build that moved the live constant reads those
//! journals as `BadStep` at byte 0 and disagrees with it here, where a test that
//! imported the live constant would move with it and pass.

use astream_engine::{scan_steps, FaultKind, Tail};
use astream_wire::{Frame, FrameError};
use proptest::prelude::*;

/// The scanner as it stood before the move, kept verbatim but for its name.
mod frozen {
    use super::*;

    pub const STEP_VERSION: u8 = 1;
    const STEP_HEADER: usize = 13;

    fn decode_step(payload: &[u8]) -> Option<(u64, Vec<u8>)> {
        if payload.len() < STEP_HEADER || payload[0] != STEP_VERSION {
            return None;
        }
        let step = u64::from_le_bytes(payload[1..9].try_into().ok()?);
        let len = u32::from_le_bytes(payload[9..13].try_into().ok()?) as usize;
        let end = STEP_HEADER.checked_add(len)?;
        let out = payload.get(STEP_HEADER..end)?.to_vec();
        Some((step, out))
    }

    pub fn scan_steps(bytes: &[u8]) -> (Vec<Vec<u8>>, usize, Tail) {
        let mut committed: Vec<Vec<u8>> = Vec::new();
        let mut pos = 0usize;
        let tail = loop {
            match Frame::decode(&bytes[pos..]) {
                Ok(None) => break end_tail(bytes, pos),
                Err(e) => break corrupt_frame_tail(bytes, pos, e),
                Ok(Some(d)) => match decode_step(&d.frame.payload) {
                    None => {
                        break Tail::Fault {
                            at: pos,
                            kind: FaultKind::BadStep,
                        }
                    }
                    Some((step, _)) if step != committed.len() as u64 => {
                        break Tail::Fault {
                            at: pos,
                            kind: FaultKind::OutOfOrder {
                                expected: committed.len() as u64,
                                found: step,
                            },
                        }
                    }
                    Some((_, output)) => {
                        committed.push(output);
                        pos += d.consumed;
                    }
                },
            }
        };
        (committed, pos, tail)
    }

    fn end_tail(bytes: &[u8], pos: usize) -> Tail {
        if pos >= bytes.len() {
            Tail::Clean
        } else if frame_decodes_after(bytes, pos) {
            Tail::Fault {
                at: pos,
                kind: FaultKind::LengthPastEnd,
            }
        } else {
            Tail::Torn
        }
    }

    fn corrupt_frame_tail(bytes: &[u8], pos: usize, e: FrameError) -> Tail {
        if frame_decodes_after(bytes, pos) {
            Tail::Fault {
                at: pos,
                kind: FaultKind::CorruptFrame(e),
            }
        } else {
            Tail::Torn
        }
    }

    fn frame_decodes_after(bytes: &[u8], pos: usize) -> bool {
        (pos.saturating_add(1)..bytes.len())
            .any(|q| matches!(Frame::decode(&bytes[q..]), Ok(Some(_))))
    }
}

/// One record of a generated journal.
#[derive(Debug, Clone)]
enum Rec {
    /// The next in-order step.
    Next(Vec<u8>),
    /// A step `n` past the next one (a gap).
    Skip(u64, Vec<u8>),
    /// The previous step again.
    Repeat(Vec<u8>),
    /// A record under another step version.
    Foreign(Vec<u8>),
}

/// Damage applied after the journal is built.
#[derive(Debug, Clone)]
enum Damage {
    None,
    /// XOR one byte (position taken modulo the length).
    Flip(usize, u8),
    /// Overwrite one frame-header length field with a value past the end.
    RotLength(usize),
    /// Keep only a prefix.
    Truncate(usize),
}

fn record(version: u8, step: u64, body: &[u8]) -> Vec<u8> {
    let mut p = vec![version];
    p.extend_from_slice(&step.to_le_bytes());
    p.extend_from_slice(&(body.len() as u32).to_le_bytes());
    p.extend_from_slice(body);
    Frame::new(p).encode().unwrap()
}

fn journal(recs: &[Rec], damage: &Damage) -> Vec<u8> {
    let mut bytes = Vec::new();
    let mut starts = Vec::new();
    let mut next = 0u64;
    for r in recs {
        starts.push(bytes.len());
        let frame = match r {
            Rec::Next(b) => {
                next += 1;
                record(frozen::STEP_VERSION, next - 1, b)
            }
            Rec::Skip(n, b) => record(frozen::STEP_VERSION, next + n, b),
            Rec::Repeat(b) => record(frozen::STEP_VERSION, next.saturating_sub(1), b),
            Rec::Foreign(b) => record(frozen::STEP_VERSION.wrapping_add(1), next, b),
        };
        bytes.extend_from_slice(&frame);
    }
    match *damage {
        Damage::None => {}
        Damage::Flip(at, x) if !bytes.is_empty() => {
            let at = at % bytes.len();
            bytes[at] ^= x;
        }
        Damage::RotLength(which) if !starts.is_empty() => {
            let at = starts[which % starts.len()];
            let past = (2 * bytes.len()) as u32;
            bytes[at + 4..at + 8].copy_from_slice(&past.to_le_bytes());
        }
        Damage::Truncate(keep) => bytes.truncate(keep % (bytes.len() + 1)),
        _ => {}
    }
    bytes
}

fn body() -> impl Strategy<Value = Vec<u8>> {
    prop::collection::vec(any::<u8>(), 0..24)
}

fn rec() -> impl Strategy<Value = Rec> {
    prop_oneof![
        6 => body().prop_map(Rec::Next),
        1 => (1u64..4, body()).prop_map(|(n, b)| Rec::Skip(n, b)),
        1 => body().prop_map(Rec::Repeat),
        1 => body().prop_map(Rec::Foreign),
    ]
}

fn damage() -> impl Strategy<Value = Damage> {
    prop_oneof![
        Just(Damage::None),
        (any::<usize>(), 1u8..=255).prop_map(|(at, x)| Damage::Flip(at, x)),
        any::<usize>().prop_map(Damage::RotLength),
        any::<usize>().prop_map(Damage::Truncate),
    ]
}

fn assert_same(bytes: &[u8]) -> Result<(), TestCaseError> {
    let now = scan_steps(bytes);
    let (committed, valid_len, tail) = frozen::scan_steps(bytes);
    prop_assert_eq!(now.committed, committed);
    prop_assert_eq!(now.valid_len, valid_len);
    prop_assert_eq!(now.tail, tail);
    Ok(())
}

#[test]
fn the_fixed_cases_agree_on_every_verdict() {
    // One witness of each verdict a journal can reach, so no verdict the property
    // below compares depends on the generators happening to produce it. (Not
    // BadEnvelope, which only the log's envelope reader finds, nor PastLastStep,
    // which needs 2^64 records from step 0.)
    let good = journal(
        &[Rec::Next(b"a".to_vec()), Rec::Next(b"b".to_vec())],
        &Damage::None,
    );
    let cases = [
        (good.clone(), Tail::Clean),
        (good[..good.len() - 1].to_vec(), Tail::Torn),
        (
            journal(
                &[Rec::Next(b"a".to_vec()), Rec::Skip(2, b"b".to_vec())],
                &Damage::None,
            ),
            Tail::Fault {
                at: good.len() / 2,
                kind: FaultKind::OutOfOrder {
                    expected: 1,
                    found: 3,
                },
            },
        ),
        (
            journal(
                &[Rec::Next(b"a".to_vec()), Rec::Foreign(b"b".to_vec())],
                &Damage::None,
            ),
            Tail::Fault {
                at: good.len() / 2,
                kind: FaultKind::BadStep,
            },
        ),
        (
            journal(
                &[
                    Rec::Next(b"a".to_vec()),
                    Rec::Next(b"b".to_vec()),
                    Rec::Next(b"c".to_vec()),
                ],
                &Damage::RotLength(1),
            ),
            Tail::Fault {
                at: good.len() / 2,
                kind: FaultKind::LengthPastEnd,
            },
        ),
        (
            // The last body byte of the middle record (records are the same
            // size, so it is the byte before `good.len()`): its CRC fails, and
            // the intact record behind it makes that a fault.
            journal(
                &[
                    Rec::Next(b"a".to_vec()),
                    Rec::Next(b"b".to_vec()),
                    Rec::Next(b"c".to_vec()),
                ],
                &Damage::Flip(good.len() - 1, 0x01),
            ),
            Tail::Fault {
                at: good.len() / 2,
                kind: FaultKind::CorruptFrame(FrameError::ChecksumMismatch),
            },
        ),
        (
            // A crash's cut through a record whose body nests a whole frame,
            // past the nested frame: it decodes behind the partial record, so
            // BOTH scanners call the cut a rotted length, not a torn tail. The
            // wire documents this as the rule's one over-strict case; it is the
            // old rule's, not one the move introduced.
            {
                let mut nest = b"p".to_vec();
                nest.extend_from_slice(&record(frozen::STEP_VERSION, 0, b"x"));
                nest.push(b's');
                let j = journal(&[Rec::Next(b"a".to_vec()), Rec::Next(nest)], &Damage::None);
                j[..j.len() - 1].to_vec()
            },
            Tail::Fault {
                at: good.len() / 2,
                kind: FaultKind::LengthPastEnd,
            },
        ),
    ];
    for (bytes, want) in cases {
        assert_eq!(scan_steps(&bytes).tail, want);
        let (_, _, frozen_tail) = frozen::scan_steps(&bytes);
        assert_eq!(frozen_tail, want);
    }
}

proptest! {
    /// Generated journals, damaged at random, get the same verdict from both.
    #[test]
    fn a_damaged_journal_gets_the_verdict_it_got_before_the_move(
        recs in prop::collection::vec(rec(), 0..8),
        damage in damage(),
    ) {
        assert_same(&journal(&recs, &damage))?;
    }

    /// Arbitrary bytes get the same verdict from both.
    #[test]
    fn arbitrary_bytes_get_the_verdict_they_got_before_the_move(
        bytes in prop::collection::vec(any::<u8>(), 0..96),
    ) {
        assert_same(&bytes)?;
    }
}
