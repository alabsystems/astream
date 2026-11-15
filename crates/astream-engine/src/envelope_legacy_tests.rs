//! Frozen owned decoder from the baseline source, used only as a test oracle.
//! Validation helpers are copied so the oracle never calls the new body parser.

use super::{
    CausedBy, Envelope, EnvelopeError, EnvelopePrefix, HEADER_LEN, TAG_EXIT, TAG_IN, TAG_OUT,
    TAG_RESIZE,
};
use astream_term::Record;
use astream_wire::Offset;

const fn envelope_version_valid(version: u8) -> bool {
    version == 3
}

pub(crate) struct OwnedEnvelopeOracle;
impl OwnedEnvelopeOracle {
    const fn decode_envelope_header(hdr: &[u8; HEADER_LEN]) -> (u8, u8, Offset, u64) {
        let version = hdr[0];
        let tag = hdr[1];
        let seq = Offset(
            (hdr[2] as u64)
                | ((hdr[3] as u64) << 8)
                | ((hdr[4] as u64) << 16)
                | ((hdr[5] as u64) << 24)
                | ((hdr[6] as u64) << 32)
                | ((hdr[7] as u64) << 40)
                | ((hdr[8] as u64) << 48)
                | ((hdr[9] as u64) << 56),
        );
        let ts_logical = (hdr[10] as u64)
            | ((hdr[11] as u64) << 8)
            | ((hdr[12] as u64) << 16)
            | ((hdr[13] as u64) << 24)
            | ((hdr[14] as u64) << 32)
            | ((hdr[15] as u64) << 40)
            | ((hdr[16] as u64) << 48)
            | ((hdr[17] as u64) << 56);
        (version, tag, seq, ts_logical)
    }

    const fn decode_u64_le(bytes: &[u8; 8]) -> u64 {
        (bytes[0] as u64)
            | ((bytes[1] as u64) << 8)
            | ((bytes[2] as u64) << 16)
            | ((bytes[3] as u64) << 24)
            | ((bytes[4] as u64) << 32)
            | ((bytes[5] as u64) << 40)
            | ((bytes[6] as u64) << 48)
            | ((bytes[7] as u64) << 56)
    }

    const fn decode_in_prefix(hdr: &[u8; 20]) -> (u64, u64, usize) {
        let client_id = (hdr[0] as u64)
            | ((hdr[1] as u64) << 8)
            | ((hdr[2] as u64) << 16)
            | ((hdr[3] as u64) << 24)
            | ((hdr[4] as u64) << 32)
            | ((hdr[5] as u64) << 40)
            | ((hdr[6] as u64) << 48)
            | ((hdr[7] as u64) << 56);
        let client_seq = (hdr[8] as u64)
            | ((hdr[9] as u64) << 8)
            | ((hdr[10] as u64) << 16)
            | ((hdr[11] as u64) << 24)
            | ((hdr[12] as u64) << 32)
            | ((hdr[13] as u64) << 40)
            | ((hdr[14] as u64) << 48)
            | ((hdr[15] as u64) << 56);
        let len = ((hdr[16] as u32)
            | ((hdr[17] as u32) << 8)
            | ((hdr[18] as u32) << 16)
            | ((hdr[19] as u32) << 24)) as usize;
        (client_id, client_seq, len)
    }

    const fn decode_out_len(hdr: &[u8; 4]) -> usize {
        ((hdr[0] as u32)
            | ((hdr[1] as u32) << 8)
            | ((hdr[2] as u32) << 16)
            | ((hdr[3] as u32) << 24)) as usize
    }

    const fn decode_resize_body(hdr: &[u8; 4]) -> (u16, u16) {
        let cols = (hdr[0] as u16) | ((hdr[1] as u16) << 8);
        let rows = (hdr[2] as u16) | ((hdr[3] as u16) << 8);
        (cols, rows)
    }

    const fn decode_exit_body(hdr: &[u8; 4]) -> i32 {
        ((hdr[0] as u32)
            | ((hdr[1] as u32) << 8)
            | ((hdr[2] as u32) << 16)
            | ((hdr[3] as u32) << 24)) as i32
    }

    const fn decode_envelope_prefix(payload: &[u8]) -> Result<EnvelopePrefix<'_>, EnvelopeError> {
        let &[h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, ref after_header @ ..] =
            payload
        else {
            return Err(EnvelopeError::Short);
        };
        let (version, tag, seq, ts_logical) = Self::decode_envelope_header(&[
            h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
        ]);
        if !envelope_version_valid(version) {
            return Err(EnvelopeError::BadVersion(version));
        }
        let &[cause_present, ref after_cause_flag @ ..] = after_header else {
            return Err(EnvelopeError::Short);
        };
        let (caused_by, body) = if cause_present == 0 {
            (None, after_cause_flag)
        } else {
            let &[o0, o1, o2, o3, o4, o5, o6, o7, part_present, ref after_part_flag @ ..] =
                after_cause_flag
            else {
                return Err(EnvelopeError::Short);
            };
            let offset = Self::decode_u64_le(&[o0, o1, o2, o3, o4, o5, o6, o7]);
            if part_present == 0 {
                (
                    Some(CausedBy {
                        partition: None,
                        offset,
                    }),
                    after_part_flag,
                )
            } else {
                let &[p0, p1, p2, p3, p4, p5, p6, p7, ref after_part @ ..] = after_part_flag else {
                    return Err(EnvelopeError::Short);
                };
                let partition = Some(Self::decode_u64_le(&[p0, p1, p2, p3, p4, p5, p6, p7]));
                (Some(CausedBy { partition, offset }), after_part)
            }
        };
        Ok((tag, seq, ts_logical, caused_by, body))
    }

    const fn decode_in_header(body: &[u8]) -> Result<(u64, u64, usize, &[u8]), EnvelopeError> {
        let &[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, ref rest @ ..] =
            body
        else {
            return Err(EnvelopeError::Short);
        };
        let (client_id, client_seq, len) = Self::decode_in_prefix(&[
            b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18,
            b19,
        ]);
        if rest.len() < len {
            return Err(EnvelopeError::BadBodyLen);
        }
        Ok((client_id, client_seq, len, rest))
    }

    const fn decode_out_header(body: &[u8]) -> Result<(usize, &[u8]), EnvelopeError> {
        let &[b0, b1, b2, b3, ref rest @ ..] = body else {
            return Err(EnvelopeError::Short);
        };
        let len = Self::decode_out_len(&[b0, b1, b2, b3]);
        if rest.len() < len {
            return Err(EnvelopeError::BadBodyLen);
        }
        Ok((len, rest))
    }

    const fn decode_resize_slice(body: &[u8]) -> Result<(u16, u16), EnvelopeError> {
        let &[b0, b1, b2, b3, ref _rest @ ..] = body else {
            return Err(EnvelopeError::Short);
        };
        Ok(Self::decode_resize_body(&[b0, b1, b2, b3]))
    }

    const fn decode_exit_slice(body: &[u8]) -> Result<i32, EnvelopeError> {
        let &[b0, b1, b2, b3, ref _rest @ ..] = body else {
            return Err(EnvelopeError::Short);
        };
        Ok(Self::decode_exit_body(&[b0, b1, b2, b3]))
    }

    pub(crate) fn from_payload(payload: &[u8]) -> Result<Envelope, EnvelopeError> {
        let (tag, seq, ts_logical, caused_by, body) = Self::decode_envelope_prefix(payload)?;

        let record = match tag {
            TAG_IN => {
                // client_id(8) + client_seq(8) + len(4) + bytes
                let (client_id, client_seq, len, rest) = Self::decode_in_header(body)?;
                let Some(in_bytes) = rest.get(..len) else {
                    return Err(EnvelopeError::BadBodyLen);
                };
                super::owned_decode_work::record(in_bytes.len());
                Record::In {
                    bytes: in_bytes.to_vec(),
                    client_id,
                    client_seq,
                }
            }
            TAG_OUT => {
                let (len, rest) = Self::decode_out_header(body)?;
                let Some(out_bytes) = rest.get(..len) else {
                    return Err(EnvelopeError::BadBodyLen);
                };
                super::owned_decode_work::record(out_bytes.len());
                Record::Out(out_bytes.to_vec())
            }
            TAG_RESIZE => {
                let (cols, rows) = Self::decode_resize_slice(body)?;
                Record::Resize { cols, rows }
            }
            TAG_EXIT => {
                let code = Self::decode_exit_slice(body)?;
                Record::Exit { code }
            }
            other => return Err(EnvelopeError::BadTag(other)),
        };
        Ok(Envelope {
            seq,
            ts_logical,
            caused_by,
            record,
        })
    }
}

#[test]
fn frozen_owned_decoder_matches_current_parser_for_hostile_payloads() {
    use astream_wire::Frame;
    let compare = |payload: &[u8]| {
        let old = OwnedEnvelopeOracle::from_payload(payload);
        assert_eq!(Envelope::from_payload(payload), old);
        let metadata = old.map(|env| super::EnvelopeMetadata {
            seq: env.seq,
            ts_logical: env.ts_logical,
            caused_by: env.caused_by,
            input_key: match env.record {
                Record::In {
                    client_id,
                    client_seq,
                    ..
                } => Some((client_id, client_seq)),
                _ => None,
            },
        });
        assert_eq!(super::EnvelopeMetadata::from_payload(payload), metadata);
    };
    let causes = [
        None,
        Some(CausedBy {
            partition: None,
            offset: u64::MAX,
        }),
        Some(CausedBy {
            partition: Some(77),
            offset: u64::MAX,
        }),
    ];
    for len in [0, 1, 7, 257] {
        let records = [
            Record::In {
                bytes: (0..len).map(|i| i as u8).collect(),
                client_id: u64::MAX,
                client_seq: 0,
            },
            Record::Out((0..len).map(|i| 255u8.wrapping_sub(i as u8)).collect()),
            Record::Resize {
                cols: 0,
                rows: u16::MAX,
            },
            Record::Exit { code: i32::MIN },
        ];
        for record in records {
            for cause in causes {
                for seq in [Offset::ZERO, Offset(u64::MAX)] {
                    let bytes = Envelope {
                        seq,
                        ts_logical: u64::MAX,
                        caused_by: cause,
                        record: record.clone(),
                    }
                    .encode()
                    .unwrap();
                    let payload = Frame::decode(&bytes).unwrap().unwrap().frame.payload;
                    for end in 0..=payload.len() {
                        compare(&payload[..end]);
                    }
                    for at in 0..payload.len() {
                        let mut changed = payload.clone();
                        changed[at] ^= 0x80;
                        compare(&changed);
                    }
                    let mut trailing = payload.clone();
                    trailing.extend_from_slice(&[0, 255, 17]);
                    compare(&trailing);
                }
            }
        }
    }
    // Presence flags intentionally accept every nonzero byte, including255.
    for cause in 0u8..=255 {
        for part in [0u8, 1, 2, 255] {
            let mut payload = vec![3, TAG_OUT];
            payload.extend_from_slice(&[0; 16]);
            payload.push(cause);
            if cause != 0 {
                payload.extend_from_slice(&u64::MAX.to_le_bytes());
                payload.push(part);
                if part != 0 {
                    payload.extend_from_slice(&77u64.to_le_bytes());
                }
            }
            payload.extend_from_slice(&1u32.to_le_bytes());
            payload.push(9);
            assert!(OwnedEnvelopeOracle::from_payload(&payload).is_ok());
            compare(&payload);
        }
    }
    let mut state = 0x517cc1b727220a95u64;
    for len in 0..512 {
        let mut payload = Vec::new();
        for _ in 0..len {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            payload.push(state as u8);
        }
        compare(&payload);
    }
}

#[test]
fn metadata_decoder_preserves_permissive_format_and_error_precedence() {
    use super::EnvelopeMetadata;
    let mut header = vec![3, 255];
    header.extend_from_slice(&[0; 16]);
    // Header version wins before a missing cause flag; cause availability wins
    // before an otherwise unknown tag is dispatched.
    let mut version = header.clone();
    version[0] = 9;
    assert_eq!(
        EnvelopeMetadata::from_payload(&version),
        Err(EnvelopeError::BadVersion(9))
    );
    assert_eq!(
        EnvelopeMetadata::from_payload(&header),
        Err(EnvelopeError::Short)
    );
    header.push(2);
    assert_eq!(
        EnvelopeMetadata::from_payload(&header),
        Err(EnvelopeError::Short)
    );
    header.extend_from_slice(&[0; 8]);
    header.push(255);
    assert_eq!(
        EnvelopeMetadata::from_payload(&header),
        Err(EnvelopeError::Short)
    );
    header.extend_from_slice(&[0; 8]);
    assert_eq!(
        EnvelopeMetadata::from_payload(&header),
        Err(EnvelopeError::BadTag(255))
    );
    assert_eq!(
        Envelope::from_payload(&header),
        OwnedEnvelopeOracle::from_payload(&header)
    );
}
