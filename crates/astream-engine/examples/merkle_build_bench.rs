//! Merkle construction controls. Use separate `legacy`/`current` processes for RSS.
use astream_engine::{CausedBy, CommitHash, Envelope, MerkleChain, MerkleError, Offset, ReadError};
use astream_term::Record;
use astream_wire::frame::decode_frame_slice;
use std::hint::black_box;
use std::time::Instant;

// LogReader's pre-change discipline, retained here because its incomplete-tail
// position is crate-private. This benchmark does not expand the production API.
struct LegacyReader<'a> {
    buf: &'a [u8],
    pos: usize,
    expected: Offset,
    start: Offset,
}

impl LegacyReader<'_> {
    fn incomplete_at(&self) -> Option<usize> {
        (self.pos < self.buf.len()).then_some(self.pos)
    }
}

impl Iterator for LegacyReader<'_> {
    type Item = Result<Envelope, ReadError>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (_, tail) = self.buf.split_at_checked(self.pos)?;
            match decode_frame_slice(tail) {
                Ok(None) => return None,
                Err(err) => {
                    self.pos = self.buf.len();
                    return Some(Err(ReadError::Frame(err)));
                }
                Ok(Some((payload, consumed))) => {
                    self.pos = self.pos.saturating_add(consumed);
                    let env = match Envelope::from_payload(payload) {
                        Ok(env) => env,
                        Err(err) => {
                            self.pos = self.buf.len();
                            return Some(Err(ReadError::Envelope(err)));
                        }
                    };
                    if env.seq != self.expected {
                        let err = ReadError::SeqMismatch {
                            expected: self.expected,
                            found: env.seq,
                        };
                        self.pos = self.buf.len();
                        return Some(Err(err));
                    }
                    match self.expected.checked_next() {
                        Some(next) => self.expected = next,
                        None => {
                            self.pos = self.buf.len();
                            return Some(Err(ReadError::OffsetOverflow));
                        }
                    }
                    if env.seq.0 < self.start.0 {
                        continue;
                    }
                    return Some(Ok(env));
                }
            }
        }
    }
}

fn legacy(bytes: &[u8]) -> Result<MerkleChain, MerkleError> {
    let mut reader = LegacyReader {
        buf: bytes,
        pos: 0,
        expected: Offset::ZERO,
        start: Offset::ZERO,
    };
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

fn fixture(records: usize, body_len: usize) -> Vec<u8> {
    let mut bytes = Vec::new();
    for index in 0..records {
        let record = if index % 4 == 0 {
            Record::In {
                bytes: vec![index as u8; body_len],
                client_id: (index % 64) as u64,
                client_seq: index as u64,
            }
        } else {
            Record::Out(vec![index as u8; body_len])
        };
        let env = Envelope {
            seq: Offset(index as u64),
            ts_logical: index as u64 * 17,
            caused_by: match index % 3 {
                0 => None,
                1 => Some(CausedBy {
                    partition: None,
                    offset: (index as u64).saturating_sub(1),
                }),
                _ => Some(CausedBy {
                    partition: Some(77),
                    offset: index as u64,
                }),
            },
            record,
        };
        bytes.extend_from_slice(&env.encode().unwrap());
    }
    bytes
}

fn run(mode: &str, bytes: &[u8]) -> Result<MerkleChain, MerkleError> {
    match mode {
        "legacy" => legacy(black_box(bytes)),
        "current" => MerkleChain::from_log_bytes(black_box(bytes)),
        _ => panic!("mode must be legacy or current"),
    }
}

fn summary(result: &Result<MerkleChain, MerkleError>) -> Result<(usize, CommitHash), MerkleError> {
    result
        .as_ref()
        .map(|chain| (chain.len(), chain.head_hash()))
        .map_err(Clone::clone)
}

fn measure(mode: &str, case: &str, bytes: &[u8], rounds: usize) {
    let expected = summary(&run(mode, bytes));
    let mut times = [0; 3];
    for elapsed in &mut times {
        let started = Instant::now();
        for _ in 0..rounds {
            let result = run(mode, bytes);
            assert_eq!(summary(&result), expected);
            drop(black_box(result));
        }
        *elapsed = started.elapsed().as_nanos() / rounds as u128;
    }
    times.sort_unstable();
    println!(
        "MERKLE_BUILD mode={mode} case={case} log_bytes={} rounds={rounds} ns={} result={expected:?}",
        bytes.len(),
        times[1]
    );
}

fn main() {
    let args: Vec<_> = std::env::args().collect();
    if args.get(1).is_some_and(|arg| arg == "generate") {
        let path = args.get(2).expect("generate needs a path");
        let records: usize = args.get(3).expect("record count").parse().unwrap();
        let body_len: usize = args.get(4).expect("body bytes").parse().unwrap();
        std::fs::write(path, fixture(records, body_len)).unwrap();
        return;
    }
    let mode = args.get(1).map_or("current", String::as_str);
    assert!(matches!(mode, "legacy" | "current"));
    if let Some(path) = args.get(2) {
        let bytes = std::fs::read(path).unwrap();
        measure(mode, "file", &bytes, 1);
        return;
    }
    for (records, body_len, rounds) in [
        (2048, 64, 4),
        (4096, 1024, 2),
        (4096, 16384, 1),
        (512, 0, 4),
    ] {
        let bytes = fixture(records, body_len);
        let case = format!("valid-{records}-{body_len}");
        measure(mode, &case, &bytes, rounds);
        let mut bad_crc = bytes.clone();
        if let Some(last) = bad_crc.last_mut() {
            *last ^= 1;
        }
        measure(mode, &format!("crc-{records}-{body_len}"), &bad_crc, rounds);
        if !bytes.is_empty() {
            measure(
                mode,
                &format!("incomplete-{records}-{body_len}"),
                &bytes[..bytes.len() - 1],
                rounds,
            );
        }
    }
    measure(mode, "empty", &[], 64);
}
