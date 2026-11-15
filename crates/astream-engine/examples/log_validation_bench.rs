//! Public-API validation controls; fixtures and snapshots are built outside timing.
//! Fixture byte counts describe workload, not measured allocator calls or peaks.
use astream_engine::{
    cross_edges_from_logs, materialize_fleet_cut, recover, resume_fleet_cut, CausedBy, Clock, Cut,
    Disk, Effects, Envelope, FleetSnapshot, Log, Offset, Partition, ReadError, Rng, Session,
};
use astream_term::{render::frame_hash, Record};
use astream_wire::Frame;
use std::cell::Cell;
use std::hint::black_box;
use std::time::Instant;

struct ReadDisk<'a>(&'a [u8]);
impl Disk for ReadDisk<'_> {
    fn append(&mut self, _: &[u8]) {
        panic!("read-only benchmark disk");
    }
    fn read_all(&self) -> &[u8] {
        self.0
    }
    fn len(&self) -> usize {
        self.0.len()
    }
}
struct ProbeClock<'a>(&'a Cell<u64>);
impl Clock for ProbeClock<'_> {
    fn now_logical(&mut self) -> u64 {
        let n = self.0.get();
        self.0.set(n.saturating_add(1));
        n
    }
    fn advance_past(&mut self, ts: u64) {
        self.0.set(self.0.get().max(ts.saturating_add(1)));
    }
}
struct ProbeRng;
impl Rng for ProbeRng {
    fn next_u64(&mut self) -> u64 {
        0
    }
}
struct ReadEffects<'a> {
    disk: ReadDisk<'a>,
    clock: ProbeClock<'a>,
    rng: ProbeRng,
}
impl<'a> Effects for ReadEffects<'a> {
    type C = ProbeClock<'a>;
    type R = ProbeRng;
    type D = ReadDisk<'a>;
    fn clock(&mut self) -> &mut Self::C {
        &mut self.clock
    }
    fn rng(&mut self) -> &mut Self::R {
        &mut self.rng
    }
    fn disk(&mut self) -> &mut Self::D {
        &mut self.disk
    }
}
fn fixture(n: usize, body_len: usize) -> Vec<u8> {
    let mut bytes = Vec::new();
    for i in 0..n {
        let record = if i % 4 == 0 {
            Record::In {
                bytes: vec![i as u8; body_len],
                client_id: (i % 64) as u64,
                client_seq: (i / 64) as u64,
            }
        } else {
            Record::Out(vec![0; body_len])
        };
        let env = Envelope {
            seq: Offset(i as u64),
            ts_logical: i as u64 * 17,
            caused_by: (i % 16 == 0).then_some(CausedBy {
                partition: Some(77),
                offset: i as u64,
            }),
            record,
        };
        bytes.extend_from_slice(&env.encode().unwrap());
    }
    bytes
}
fn read_digest(bytes: &[u8], start: Offset) -> u64 {
    let mut sum = 0u64;
    for item in Log::read_bytes(black_box(bytes), start) {
        match item {
            Ok(env) => {
                let body = match &env.record {
                    Record::In {
                        bytes,
                        client_id,
                        client_seq,
                    } => bytes.len() as u64 ^ client_id ^ client_seq,
                    Record::Out(bytes) => bytes.len() as u64,
                    Record::Resize { cols, rows } => u64::from(*cols) ^ u64::from(*rows),
                    Record::Exit { code } => *code as u64,
                };
                sum = sum.rotate_left(3) ^ env.seq.0 ^ env.ts_logical ^ body;
                black_box(env);
            }
            Err(err) => {
                sum ^= error_digest(&err);
                break;
            }
        }
    }
    sum
}
fn error_digest(err: &ReadError) -> u64 {
    match err {
        ReadError::Frame(_) => 1,
        ReadError::Envelope(_) => 2,
        ReadError::SeqMismatch { expected, found } => 3 ^ expected.0 ^ found.0,
        ReadError::OffsetOverflow => 4,
        ReadError::Incomplete { at } => 5 ^ *at as u64,
    }
}
fn session_digest(bytes: &[u8]) -> u64 {
    let tick = Cell::new(0);
    let fx = ReadEffects {
        disk: ReadDisk(bytes),
        clock: ProbeClock(&tick),
        rng: ProbeRng,
    };
    match Session::resume_from(fx) {
        Ok(s) => {
            let digest = s.next_offset().0
                ^ s.last_in_offset().map_or(0, |x| x.0)
                ^ tick.get()
                ^ u64::from(s.is_duplicate(0, 0));
            black_box(s);
            digest
        }
        Err(err) => error_digest(&err) ^ tick.get(),
    }
}
fn snapshot(bytes: &[u8], n: usize) -> FleetSnapshot {
    // Include the external cause frontier; an absent cause log materializes an
    // empty partition snapshot rather than fabricating records for that frontier.
    let cut = Cut {
        offsets: vec![
            (Partition(0), Offset(n.saturating_sub(2) as u64)),
            (Partition(77), Offset(n as u64)),
        ],
    };
    materialize_fleet_cut(&cut, &[(Partition(0), bytes)], 2, 2).unwrap()
}
fn measure(
    case: &str,
    n: usize,
    body_len: usize,
    log_bytes: usize,
    rounds: usize,
    mut f: impl FnMut() -> u64,
) {
    let expected = f();
    let mut times = [0; 3];
    for sample in &mut times {
        let begin = Instant::now();
        for _ in 0..rounds {
            assert_eq!(black_box(f()), expected);
        }
        *sample = begin.elapsed().as_nanos() / rounds as u128;
    }
    times.sort_unstable();
    println!("LOG_VALIDATION case={case} records={n} body_bytes={body_len} log_bytes={log_bytes} rounds={rounds} ns_per_scan={} digest={expected} fixture_body_bytes={} accounting=fixture_not_allocator", times[1], n * body_len);
}
fn main() {
    for (n, body_len, rounds) in [
        (8192, 64, 8),
        (4096, 1024, 2),
        (256, 64 * 1024, 1),
        (64, 1024 * 1024, 1),
        (512, 0, 8),
    ] {
        let bytes = fixture(n, body_len);
        let fleet = snapshot(&bytes, n);
        let logs = [(Partition(0), bytes.as_slice())];
        measure("yield_all", n, body_len, bytes.len(), rounds, || {
            read_digest(&bytes, Offset::ZERO)
        });
        measure("skip_all", n, body_len, bytes.len(), rounds, || {
            read_digest(&bytes, Offset(u64::MAX))
        });
        measure("skip_prefix", n, body_len, bytes.len(), rounds, || {
            read_digest(&bytes, Offset(n as u64 - 1))
        });
        measure("recover", n, body_len, bytes.len(), rounds, || {
            let r = recover(&bytes);
            let sum = r.valid_len as u64 ^ r.records ^ u64::from(r.torn);
            black_box(r);
            sum
        });
        measure("cross_edges", n, body_len, bytes.len(), rounds, || {
            let edges = cross_edges_from_logs(&logs);
            let mut sum = edges.len() as u64;
            for e in &edges {
                sum = sum.rotate_left(3) ^ e.cause.1 .0 ^ e.effect.1 .0;
            }
            black_box(edges);
            sum
        });
        measure("session_resume", n, body_len, bytes.len(), rounds, || {
            session_digest(&bytes)
        });
        measure("fleet_resume", n, body_len, bytes.len(), rounds, || {
            let out = resume_fleet_cut(&fleet, &logs).unwrap();
            let sum = frame_hash(&out[0].1);
            black_box(out);
            sum
        });
    }
    let empty = [];
    for (case, start) in [
        ("empty_yield", Offset::ZERO),
        ("empty_skip", Offset(u64::MAX)),
    ] {
        measure(case, 0, 0, 0, 10_000, || read_digest(&empty, start));
    }
    let mut malformed = vec![
        astream_engine::ENV_VERSION,
        astream_engine::envelope::TAG_OUT,
    ];
    malformed.extend_from_slice(&7u64.to_le_bytes());
    malformed.extend_from_slice(&0u64.to_le_bytes());
    malformed.push(0);
    malformed.extend_from_slice(&9u32.to_le_bytes());
    malformed.push(1);
    let malformed = Frame::new(malformed).encode().unwrap();
    for (case, start) in [
        ("malformed_yield", Offset::ZERO),
        ("malformed_skip", Offset(u64::MAX)),
    ] {
        measure(case, 1, 1, malformed.len(), 10_000, || {
            read_digest(&malformed, start)
        });
    }
}
