// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Full-result controls for moving decoded envelopes directly into Merkle nodes.

use super::*;
use crate::envelope::{EnvelopeError, ENV_VERSION};
use astream_wire::{Frame, FrameError};

// Frozen from main merkle.rs SHA-256
// 99557393714b1fcab8044b5d12058a92638c24cf60a42611c633c07c1432a4d0.
// The public slice constructor deliberately retains its original clone semantics.
fn legacy_from_log_bytes(bytes: &[u8]) -> Result<MerkleChain, MerkleError> {
    let mut reader = Log::read_bytes(bytes, Offset::ZERO);
    let mut envelopes = Vec::new();
    for item in &mut reader {
        match item {
            Ok(env) => envelopes.push(env),
            Err(e) => return Err(MerkleError::Decode(e)),
        }
    }
    if let Some(at) = reader.incomplete_at() {
        return Err(MerkleError::Decode(ReadError::Incomplete { at }));
    }
    MerkleChain::from_envelopes(&envelopes)
}

fn envelope(seq: u64, record: Record, caused_by: Option<CausedBy>) -> Envelope {
    Envelope {
        seq: Offset(seq),
        ts_logical: u64::MAX.saturating_sub(seq),
        caused_by,
        record,
    }
}

fn records() -> Vec<Envelope> {
    vec![
        envelope(
            0,
            Record::Resize {
                cols: 0,
                rows: u16::MAX,
            },
            None,
        ),
        envelope(
            1,
            Record::In {
                bytes: Vec::new(),
                client_id: 0,
                client_seq: 0,
            },
            Some(CausedBy {
                partition: None,
                offset: 0,
            }),
        ),
        envelope(
            2,
            Record::Out(vec![0, 0xff, b'\x1b', b'[', b'3', b'1', b'm']),
            Some(CausedBy {
                partition: Some(u64::MAX),
                offset: u64::MAX,
            }),
        ),
        envelope(3, Record::Exit { code: i32::MIN }, None),
        envelope(4, Record::Out(Vec::new()), None),
        envelope(
            5,
            Record::In {
                bytes: (0..8192).map(|i| (i % 251) as u8).collect(),
                client_id: u64::MAX,
                client_seq: u64::MAX,
            },
            Some(CausedBy {
                partition: Some(0),
                offset: 0,
            }),
        ),
        envelope(
            6,
            Record::Out(vec![b'x'; 16_384]),
            Some(CausedBy {
                partition: None,
                offset: u64::MAX,
            }),
        ),
        envelope(7, Record::Exit { code: i32::MAX }, None),
    ]
}

fn encode(envelopes: &[Envelope]) -> Vec<u8> {
    let mut bytes = Vec::new();
    for env in envelopes {
        bytes.extend_from_slice(&env.encode().unwrap());
    }
    bytes
}

fn payload(env: &Envelope) -> Vec<u8> {
    Frame::decode(&env.encode().unwrap())
        .unwrap()
        .unwrap()
        .frame
        .payload
}

fn compare(bytes: &[u8]) -> Result<MerkleChain, MerkleError> {
    let actual = MerkleChain::from_log_bytes(bytes);
    let reference = legacy_from_log_bytes(bytes);
    assert_eq!(actual, reference);
    if let (Ok(actual), Ok(reference)) = (&actual, &reference) {
        assert_eq!(actual.nodes(), reference.nodes());
        assert_eq!(actual.head_hash(), reference.head_hash());
        assert_eq!(actual.to_envelopes(), reference.to_envelopes());
        assert_eq!(actual.verify(), Ok(()));
        assert_eq!(reference.verify(), Ok(()));
    }
    actual
}

#[test]
fn owned_merkle_nodes_match_the_frozen_constructor_for_every_record_prefix() {
    let envelopes = records();
    for end in 0..=envelopes.len() {
        let chain = compare(&encode(&envelopes[..end])).unwrap();
        assert_eq!(chain.to_envelopes(), envelopes[..end]);
        assert_eq!(chain.len(), end);
        for (index, node) in chain.nodes().iter().enumerate() {
            assert_eq!(node.seq, Offset(index as u64));
            if index == 0 {
                assert!(node.parents.is_empty());
            } else {
                assert_eq!(node.parents, vec![chain.nodes()[index - 1].hash]);
            }
        }
        if end == 0 {
            assert_eq!(chain.head_hash(), CommitHash::empty_tree());
        }
    }
}

#[test]
fn accepted_noncanonical_payloads_hash_the_decoded_envelope_not_wire_padding() {
    let envelopes = vec![
        envelope(0, Record::Out(b"out".to_vec()), None),
        envelope(
            1,
            Record::In {
                bytes: b"in".to_vec(),
                client_id: 17,
                client_seq: 23,
            },
            Some(CausedBy {
                partition: None,
                offset: 0,
            }),
        ),
        envelope(
            2,
            Record::Resize {
                cols: 0,
                rows: u16::MAX,
            },
            Some(CausedBy {
                partition: Some(0),
                offset: u64::MAX,
            }),
        ),
        envelope(3, Record::Exit { code: i32::MIN }, None),
    ];
    let mut bytes = Vec::new();
    for env in &envelopes {
        let mut body = payload(env);
        if let Some(cause) = env.caused_by {
            body[18] = u8::MAX; // Any nonzero cause-present flag is accepted.
            if cause.partition.is_some() {
                body[27] = 3; // Any nonzero partition-present flag is accepted.
            }
        }
        body.extend_from_slice(&[0xfe, 0, 0xaa, 0x55]);
        assert_eq!(Envelope::from_payload(&body), Ok(env.clone()));
        bytes.extend_from_slice(&Frame::new(body).encode().unwrap());
    }
    assert_ne!(bytes, encode(&envelopes));
    let chain = compare(&bytes).unwrap();
    assert_eq!(chain, MerkleChain::from_envelopes(&envelopes).unwrap());
}

#[test]
fn owned_merkle_errors_match_at_every_byte_boundary_and_corruption() {
    // Keep the exhaustive byte controls small; large owned bodies are exercised
    // independently by the full-prefix test above.
    let bytes = encode(&records()[..4]);
    for end in 0..=bytes.len() {
        let _ = compare(&bytes[..end]);
    }
    for at in 0..bytes.len() {
        let mut changed = bytes.clone();
        changed[at] ^= 0x80;
        let _ = compare(&changed);
    }
}

#[test]
fn late_decode_failures_return_the_first_exact_error_instead_of_a_partial_chain() {
    let prefix = encode(&records()[..3]);
    let next = envelope(3, Record::Out(b"last".to_vec()), None);
    let valid = next.encode().unwrap();

    let mut bad_length = payload(&next);
    bad_length[2..10].copy_from_slice(&9u64.to_le_bytes());
    bad_length[19..23].copy_from_slice(&100u32.to_le_bytes());
    let mut bad_version = payload(&next);
    bad_version[0] = ENV_VERSION - 1;
    let mut bad_tag = payload(&next);
    bad_tag[1] = 0;
    let mut bad_crc = valid.clone();
    *bad_crc.last_mut().unwrap() ^= 0x80;
    let bad_sequence = envelope(9, Record::Out(b"last".to_vec()), None)
        .encode()
        .unwrap();
    for (tail, expected) in [
        (
            Frame::new(bad_length).encode().unwrap(),
            ReadError::Envelope(EnvelopeError::BadBodyLen),
        ),
        (
            Frame::new(bad_version).encode().unwrap(),
            ReadError::Envelope(EnvelopeError::BadVersion(ENV_VERSION - 1)),
        ),
        (
            Frame::new(bad_tag).encode().unwrap(),
            ReadError::Envelope(EnvelopeError::BadTag(0)),
        ),
        (bad_crc, ReadError::Frame(FrameError::ChecksumMismatch)),
        (
            bad_sequence,
            ReadError::SeqMismatch {
                expected: Offset(3),
                found: Offset(9),
            },
        ),
    ] {
        let mut bytes = prefix.clone();
        bytes.extend_from_slice(&tail);
        // A later incomplete frame must not replace the earlier error.
        bytes.extend_from_slice(&valid[..5]);
        assert_eq!(compare(&bytes), Err(MerkleError::Decode(expected)));
    }
    for end in [1, 5, valid.len() - 1] {
        let mut bytes = prefix.clone();
        bytes.extend_from_slice(&valid[..end]);
        assert_eq!(
            compare(&bytes),
            Err(MerkleError::Decode(ReadError::Incomplete {
                at: prefix.len()
            }))
        );
    }
}

#[test]
fn owned_chain_lca_and_diffs_match_the_collect_then_clone_reference() {
    let shared = records()[..3].to_vec();
    let mut left = shared.clone();
    left.push(envelope(3, Record::Out(b"left".to_vec()), None));
    let mut right = shared;
    right.push(envelope(
        3,
        Record::In {
            bytes: b"right".to_vec(),
            client_id: 3,
            client_seq: 4,
        },
        None,
    ));
    right.push(envelope(4, Record::Exit { code: 7 }, None));
    let left_bytes = encode(&left);
    let right_bytes = encode(&right);
    let actual_left = compare(&left_bytes).unwrap();
    let actual_right = compare(&right_bytes).unwrap();
    let reference_left = legacy_from_log_bytes(&left_bytes).unwrap();
    let reference_right = legacy_from_log_bytes(&right_bytes).unwrap();
    assert_eq!(
        lca(&actual_left, &actual_right),
        lca(&reference_left, &reference_right)
    );
    assert_eq!(
        diff_chains(&actual_left, &actual_right),
        diff_chains(&reference_left, &reference_right)
    );
    assert_eq!(
        diff_chains(&actual_right, &actual_left),
        diff_chains(&reference_right, &reference_left)
    );
    assert_eq!(lca(&actual_left, &MerkleChain::empty()), None);
}

#[test]
fn the_public_slice_constructor_keeps_independent_ownership_and_first_offset_error() {
    let mut inputs = records();
    let original = inputs.clone();
    let chain = MerkleChain::from_envelopes(&inputs).unwrap();
    for (input, node) in inputs.iter_mut().zip(chain.nodes()) {
        input.ts_logical = 0;
        input.caused_by = None;
        match (&mut input.record, &node.envelope.record) {
            (Record::In { bytes, .. }, Record::In { bytes: stored, .. })
            | (Record::Out(bytes), Record::Out(stored)) => {
                if !bytes.is_empty() {
                    assert_ne!(bytes.as_ptr(), stored.as_ptr());
                }
                bytes.fill(0xa5);
                bytes.push(0x5a);
            }
            _ => {}
        }
    }
    drop(inputs);
    assert_eq!(chain.to_envelopes(), original);
    chain.verify().unwrap();

    let mut non_dense = original;
    non_dense[1].seq = Offset(9);
    non_dense[2].seq = Offset(u64::MAX);
    assert_eq!(
        MerkleChain::from_envelopes(&non_dense),
        Err(MerkleError::NonDenseOffset {
            expected: 1,
            found: 9
        })
    );
}
