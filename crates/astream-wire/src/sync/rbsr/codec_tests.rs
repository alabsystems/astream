// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

use super::*;

fn identities(count: usize) -> Vec<Digest> {
    (0..count)
        .map(|number| {
            let mut id = [0; 32];
            id[24..].copy_from_slice(&(number as u64).to_be_bytes());
            id
        })
        .collect()
}

fn messages() -> Vec<Message> {
    let items = (0..PAGE)
        .map(|number| Frontier {
            actor: [number as u8; 48],
            sequence: number as u64 + 1,
            id: [number as u8; 32],
        })
        .collect::<Vec<_>>();
    let mut counts = [0; 16];
    counts[3] = 128;
    counts[15] = u64::MAX;
    let mut messages = vec![
        Message::Frontiers {
            items: items.clone(),
            done: false,
        },
        Message::Prefixes { items, done: true },
        Message::Split {
            range: Range::ROOT,
            children: Box::new(std::array::from_fn(|position| {
                Probe::new(
                    Fingerprint {
                        count: position as u64 + 1,
                        sum: [position as u8; 32],
                    },
                    position % 2 == 0,
                )
            })),
        },
        Message::SplitReply {
            range: Range::ROOT,
            different: 0x8009,
            counts,
        },
        Message::ListRequest {
            range: Range::ROOT,
            after: None,
        },
        Message::ListRequest {
            range: Range::ROOT,
            after: Some([255; 32]),
        },
        Message::List {
            range: Range::ROOT,
            ids: identities(PAGE),
            done: false,
        },
        Message::List {
            range: Range::ROOT,
            ids: Vec::new(),
            done: true,
        },
        Message::Difference {
            ids: identities(PAGE),
            done: true,
            local_only: true,
        },
        Message::Finish {
            local_only: Fingerprint::default(),
            remote_only: Fingerprint {
                count: 999,
                sum: [17; 32],
            },
        },
        Message::Refine,
        Message::Accepted,
    ];
    for count in [0, 1, 127, 128, 255, 256, u64::MAX] {
        messages.push(Message::Root(Fingerprint {
            count,
            sum: [0; 32],
        }));
    }
    messages
}

#[test]
fn every_message_round_trips_and_every_truncation_refuses() {
    for message in messages() {
        let bytes = message.encode().unwrap();
        assert!(bytes.len() <= MAX_FRAME_BYTES);
        assert_eq!(Message::decode(&bytes).unwrap(), message);
        for end in 0..bytes.len() {
            assert!(
                Message::decode(&bytes[..end]).is_err(),
                "{message:?} at {end}"
            );
        }
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(Message::decode(&trailing).is_err());
        // Valid mutations must still have exactly one canonical representation.
        for position in 0..bytes.len() {
            let mut changed = bytes.clone();
            changed[position] ^= 128;
            if let Ok(decoded) = Message::decode(&changed) {
                assert_eq!(decoded.encode().unwrap(), changed);
            }
        }
    }
}

#[test]
fn hostile_counts_ranges_and_unordered_lists_refuse_before_unbounded_allocation() {
    for message in [
        Message::Frontiers {
            items: Vec::new(),
            done: false,
        },
        Message::Prefixes {
            items: Vec::new(),
            done: false,
        },
    ] {
        assert_eq!(message.encode(), Err(Error::Wire));
    }
    assert_eq!(Message::decode(b"AR1\x01\0\0"), Err(Error::Wire));
    assert_eq!(Message::decode(b"AR1\x02\0\0"), Err(Error::Wire));
    assert_eq!(Message::decode(b"AR1\x05\x01\x11\0"), Err(Error::Range));
    assert_eq!(Message::decode(b"AR1\x05\x41"), Err(Error::Range));
    assert_eq!(
        Message::decode(&vec![0; MAX_FRAME_BYTES + 1]),
        Err(Error::Wire)
    );
    for count in [vec![128, 0], vec![255; 10], vec![128; 11]] {
        let mut bytes = b"AR1\0".to_vec();
        bytes.extend(count);
        bytes.extend([0; 32]);
        assert_eq!(Message::decode(&bytes), Err(Error::Wire));
    }
    assert_eq!(Message::decode(b"AR1\x01\x02\0"), Err(Error::Wire));
    assert_eq!(Message::decode(b"AR1\x01\x01\x41"), Err(Error::Wire));
    assert_eq!(
        Message::Root(Fingerprint {
            count: 0,
            sum: [1; 32]
        })
        .encode(),
        Err(Error::Wire)
    );
    for ids in [
        identities(PAGE + 1),
        vec![[1; 32], [0; 32]],
        vec![[1; 32]; 2],
    ] {
        assert_eq!(
            Message::Difference {
                ids,
                done: true,
                local_only: false
            }
            .encode(),
            Err(Error::Wire)
        );
    }
    assert_eq!(
        Message::Difference {
            ids: Vec::new(),
            done: false,
            local_only: true,
        }
        .encode(),
        Err(Error::Wire)
    );
    let range = Range::ROOT.children().unwrap()[1];
    assert_eq!(
        Message::List {
            range,
            ids: vec![[0; 32]],
            done: true
        }
        .encode(),
        Err(Error::Wire)
    );
    assert_eq!(
        Message::ListRequest {
            range,
            after: Some([0; 32])
        }
        .encode(),
        Err(Error::Wire)
    );
    let leaf = Range::new([255; 32], 64).unwrap();
    assert_eq!(
        Message::Split {
            range: leaf,
            children: Box::new([Probe::Full(Fingerprint::default()); 16])
        }
        .encode(),
        Err(Error::Wire)
    );
    let mut reply = Message::SplitReply {
        range,
        different: 0,
        counts: [0; 16],
    };
    if let Message::SplitReply { counts, .. } = &mut reply {
        counts[9] = 1;
    }
    assert_eq!(reply.encode(), Err(Error::Wire));
}

#[test]
fn frame_bound_is_not_an_inventory_list_cap() {
    let ids = identities(PAGE * 5 + 17);
    let mut decoded = Vec::new();
    for (page, chunk) in ids.chunks(PAGE).enumerate() {
        let done = (page + 1) * PAGE >= ids.len();
        let bytes = Message::Difference {
            ids: chunk.to_vec(),
            done,
            local_only: false,
        }
        .encode()
        .unwrap();
        let Message::Difference {
            ids: received,
            done: received_done,
            local_only: false,
        } = Message::decode(&bytes).unwrap()
        else {
            panic!("wrong message variant");
        };
        assert_eq!(received_done, done);
        decoded.extend(received);
    }
    assert_eq!(decoded, ids);
}
