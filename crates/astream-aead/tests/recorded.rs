// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Answers recorded from this crate while it sealed through RustCrypto's
//! `chacha20poly1305` 0.10.1 (astream 7066fab), by a scratch crate outside the
//! workspace, so the cipher underneath can change without the wire changing:
//!
//! - `fixtures/seal-oracle.tsv`: 49 [`seal_with_nonce`] answers over four keys and four
//!   nonces (the draft's, all-zero, all-0xff, an arbitrary one), AAD lengths 0 to 300
//!   and plaintext lengths 0, 1, 15, 16, 17, 63, 64, 65, 255, 256, 4096, 4097 and 16389
//!   (257 ChaCha20 blocks). AAD and plaintext are named by length: byte `i` is
//!   `(i % 251) ^ seed`, seed 0x5a for AAD and 0xc3 for plaintext.
//! - `fixtures/sealed-session.txt`: one pre-shared-key [`SealedStream`] session, every
//!   byte each side wrote (hello, confirm, five records), and what each side wrote.
//!
//! Each recorded seal must come back byte for byte, each recorded box and both halves
//! of the session must open, and a flipped bit anywhere must not.

use astream_aead::{open, seal_with_nonce, AeadError, NONCE_LEN};

const SEALS: &str = include_str!("fixtures/seal-oracle.tsv");

fn unhex(s: &str) -> Vec<u8> {
    assert!(s.len().is_multiple_of(2), "odd-length hex");
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("hex"))
        .collect()
}

fn pattern(seed: u8, len: usize) -> Vec<u8> {
    (0..len).map(|i| ((i % 251) as u8) ^ seed).collect()
}

struct Row {
    key: [u8; 32],
    nonce: [u8; NONCE_LEN],
    aad: Vec<u8>,
    plaintext: Vec<u8>,
    sealed: Vec<u8>,
}

fn rows() -> Vec<Row> {
    SEALS
        .lines()
        .filter(|l| !l.starts_with('#') && !l.is_empty())
        .map(|l| {
            let c: Vec<&str> = l.split('\t').collect();
            assert_eq!(c.len(), 5, "{l}");
            Row {
                key: unhex(c[0]).try_into().expect("32-byte key"),
                nonce: unhex(c[1]).try_into().expect("24-byte nonce"),
                aad: pattern(0x5a, c[2].parse().expect("aad_len")),
                plaintext: pattern(0xc3, c[3].parse().expect("pt_len")),
                sealed: unhex(c[4]),
            }
        })
        .collect()
}

#[test]
fn every_recorded_seal_comes_back_byte_for_byte() {
    let rows = rows();
    assert_eq!(rows.len(), 49);
    for (i, r) in rows.iter().enumerate() {
        assert_eq!(
            seal_with_nonce(&r.key, &r.nonce, &r.aad, &r.plaintext),
            r.sealed,
            "row {i}: aad {} bytes, plaintext {} bytes",
            r.aad.len(),
            r.plaintext.len()
        );
    }
}

#[test]
fn every_recorded_box_opens_to_its_plaintext() {
    for (i, r) in rows().iter().enumerate() {
        assert_eq!(
            open(&r.key, &r.aad, &r.sealed).as_deref(),
            Ok(r.plaintext.as_slice()),
            "row {i}"
        );
    }
}

#[test]
fn a_flipped_bit_in_tag_ciphertext_aad_or_nonce_fails_every_recorded_box() {
    for (i, r) in rows().iter().enumerate() {
        let last = r.sealed.len() - 1;
        let ct = NONCE_LEN..NONCE_LEN + r.plaintext.len();
        // Nonce byte 0 feeds HChaCha20, byte 23 the ChaCha20 nonce; then the tag's
        // first and last bytes, then the ciphertext's ends.
        let mut flips = vec![0, NONCE_LEN - 1, last + 1 - 16, last];
        if !ct.is_empty() {
            flips.extend([ct.start, ct.end - 1]);
        }
        for at in flips {
            for bit in [0x01u8, 0x80] {
                let mut bad = r.sealed.clone();
                bad[at] ^= bit;
                assert_eq!(
                    open(&r.key, &r.aad, &bad),
                    Err(AeadError),
                    "row {i}: byte {at} bit {bit:#04x}"
                );
            }
        }
        let mut aad = r.aad.clone();
        match aad.first_mut() {
            Some(b) => *b ^= 0x01,
            None => aad.push(0),
        }
        assert_eq!(
            open(&r.key, &aad, &r.sealed),
            Err(AeadError),
            "row {i}: aad"
        );
        let mut key = r.key;
        key[31] ^= 0x01;
        assert_eq!(
            open(&key, &r.aad, &r.sealed),
            Err(AeadError),
            "row {i}: key"
        );
    }
}

/// The recorded session, read through [`SealedStream`], which compiles under the `stream`
/// feature (on by default).
#[cfg(feature = "stream")]
mod session {
    use super::unhex;
    use astream_aead::{SealedStream, HELLO_LEN};
    use std::io::{Cursor, ErrorKind, Read};

    const SESSION: &str = include_str!("fixtures/sealed-session.txt");

    struct Session {
        key: [u8; 32],
        c2s: Vec<u8>,
        s2c: Vec<u8>,
        c2s_messages: Vec<u8>,
        s2c_messages: Vec<u8>,
    }

    fn session() -> Session {
        let mut s = Session {
            key: [0; 32],
            c2s: Vec::new(),
            s2c: Vec::new(),
            c2s_messages: Vec::new(),
            s2c_messages: Vec::new(),
        };
        for l in SESSION.lines().filter(|l| !l.starts_with('#')) {
            let (tag, hex) = l.split_once('\t').expect("tag\\thex");
            let bytes = unhex(hex);
            match tag {
                "key" => s.key = bytes.try_into().expect("32-byte key"),
                "c2s.wire" => s.c2s = bytes,
                "s2c.wire" => s.s2c = bytes,
                "c2s.message" => s.c2s_messages.extend(bytes),
                "s2c.message" => s.s2c_messages.extend(bytes),
                other => panic!("unknown line {other}"),
            }
        }
        s
    }

    /// Read one direction of the recorded session as the side that received it: the
    /// record layer bound to both recorded hellos, then every record after the hello.
    fn receive(s: &Session, wire: &[u8], as_client: bool) -> std::io::Result<Vec<u8>> {
        let mut binding = s.c2s[..HELLO_LEN].to_vec();
        binding.extend_from_slice(&s.s2c[..HELLO_LEN]);
        let records = Cursor::new(wire[HELLO_LEN..].to_vec());
        let mut stream = SealedStream::with_transcript(records, s.key, &binding, as_client);
        let mut got = Vec::new();
        stream.read_to_end(&mut got)?;
        Ok(got)
    }

    #[test]
    fn the_recorded_session_opens_in_both_directions() {
        let s = session();
        assert_eq!(receive(&s, &s.c2s, false).unwrap(), s.c2s_messages);
        assert_eq!(receive(&s, &s.s2c, true).unwrap(), s.s2c_messages);
    }

    #[test]
    fn the_recorded_session_refuses_a_flipped_bit_and_the_wrong_role() {
        let s = session();
        // The wrong role reads with the other direction's byte: the confirm fails.
        let err = receive(&s, &s.c2s, true).unwrap_err();
        assert_eq!(err.kind(), ErrorKind::InvalidData);
        // A bit flipped in the last record's tag.
        let mut wire = s.s2c.clone();
        let last = wire.len() - 1;
        wire[last] ^= 0x01;
        assert_eq!(
            receive(&s, &wire, true).unwrap_err().kind(),
            ErrorKind::InvalidData
        );
        // A bit flipped in the client's hello, which both directions' AAD binds.
        let mut moved = session();
        moved.c2s[HELLO_LEN - 1] ^= 0x01;
        assert_eq!(
            receive(&moved, &moved.s2c, true).unwrap_err().kind(),
            ErrorKind::InvalidData
        );
    }
}
