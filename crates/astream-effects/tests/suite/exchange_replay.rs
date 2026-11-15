// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Evidence for `effects.cooperative.exchange-door`: the doors whose live value
//! the program supplies — a reply ([`EffectSeam::exchange`]), an output
//! ([`EffectSeam::emit`]) and a sticky flag ([`EffectSeam::raised`]) — plus the
//! monotonic clock, record and replay byte-identically against an independent
//! oracle, and replay never calls a live closure (every replay here runs with
//! closures that panic). A wrong door, request or output, a kind swapped for
//! another, and a short tape each refuse with their own typed divergence and
//! consume nothing; a tape longer than the run — a last output, or a flag's
//! rise the replay never polled up to — is refused where the program ends, by
//! `finish`; a flag polled back to back tapes one record whose false-read
//! count pins the read that saw it rise; a `Raised` record the replay has not
//! reached refuses the next door rather than being skipped; the untaped
//! [`LiveSeam`] answers what the recording seam answers; and a sink-streamed
//! recording and a lazily-pulled replay see the same records as the in-memory
//! forms.

use astream_effects::demo::{ask, say};
use astream_effects::{
    converse, converse_oracle, converse_values, EffectRecord, EffectSeam, EffectsLog, LiveSeam,
    OsEffects, RealEffects, RecordingSeam, ReplayDivergence, ReplaySeam,
};
use std::cell::Cell;
use std::convert::Infallible;
use std::rc::Rc;

/// A file every checkout has, so the record pass reads a REAL file with no
/// temp file to create or clean up.
const REAL_FILE: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/Cargo.toml");

/// A deterministic backend: every door steps to a new value on each read (so a
/// transposed or repeated record is visible), and any path reads as bytes
/// derived from the path — including paths that exist nowhere, which is how a
/// replay of its tape shows it touched no filesystem.
#[derive(Clone, Default)]
struct Fixed {
    reads: u64,
}

impl RealEffects for Fixed {
    fn real_now_nanos(&mut self) -> u64 {
        self.reads += 1;
        1_700_000_000_000_000_000 + self.reads
    }
    fn real_now_mono_nanos(&mut self) -> u64 {
        self.reads += 1;
        1_000 * self.reads
    }
    fn real_next_rand(&mut self) -> u64 {
        self.reads += 1;
        self.reads.wrapping_mul(0x9E37_79B9_7F4A_7C15)
    }
    fn real_read_file(&mut self, path: &str) -> std::io::Result<Vec<u8>> {
        self.reads += 1;
        Ok(format!("contents of {path}").into_bytes())
    }
}

/// The live peer: the reply depends on the request, so a different question
/// gets a different answer.
fn peer(request: &[u8]) -> Vec<u8> {
    let mut reply = b"re: ".to_vec();
    reply.extend(request.iter().rev());
    reply
}

/// A live flag that answers `script` in order (its last answer forever after)
/// and counts how many times it was read.
fn scripted(script: &'static [bool], reads: Rc<Cell<usize>>) -> impl FnMut() -> bool {
    move || {
        let n = reads.get();
        reads.set(n + 1);
        script[n.min(script.len() - 1)]
    }
}

/// The live closures a replay must never call.
fn no_peer(_: &[u8]) -> Vec<u8> {
    panic!("replay called the live peer")
}
fn no_flag() -> bool {
    panic!("replay read the live flag")
}

/// Record [`converse`] over `backend` with the flag script `stops`.
fn record<O: RealEffects>(backend: O, path: &str, stops: &'static [bool]) -> (u64, EffectsLog) {
    let mut rec = RecordingSeam::new(backend);
    let reads = Rc::new(Cell::new(0));
    let Ok(digest) = converse(&mut rec, path, &mut peer, &mut scripted(stops, reads));
    (digest, rec.into_log())
}

/// Replay [`converse`] from `log` with closures that panic, as a whole run:
/// the program, then [`ReplaySeam::finish`] where it ends. Returns the result
/// and where the replay stopped.
fn replay(log: EffectsLog, path: &str) -> (Result<u64, ReplayDivergence>, usize) {
    let mut seam = ReplaySeam::new(log);
    let r = converse(&mut seam, path, &mut no_peer, &mut no_flag)
        .and_then(|digest| seam.finish().map(|()| digest));
    (r, seam.position())
}

#[test]
fn record_then_replay_over_every_door_is_byte_identical_against_an_independent_oracle() {
    // RECORD: the real OS clocks, rng and file; the live peer; a stop raised
    // on the third of four back-to-back polls.
    let mut rec = RecordingSeam::new(OsEffects::new());
    let flag_reads = Rc::new(Cell::new(0));
    let peer_calls = Cell::new(0);
    let mut counting_peer = |request: &[u8]| {
        peer_calls.set(peer_calls.get() + 1);
        peer(request)
    };
    let Ok(recorded) = converse(
        &mut rec,
        REAL_FILE,
        &mut counting_peer,
        &mut scripted(&[false, false, true, true], flag_reads.clone()),
    );
    let log = rec.into_log();
    assert_eq!(peer_calls.get(), 1, "recording calls the live peer once");
    assert_eq!(
        flag_reads.get(),
        3,
        "the flag is read until it rises, then latched: the fourth poll never reads it"
    );

    // The tape's shape and values, read straight off the records.
    let v = converse_values(&log).expect("a converse tape");
    assert_eq!(
        v.file,
        std::fs::read(REAL_FILE).unwrap(),
        "the real file's bytes"
    );
    assert_eq!(v.raised_at, Some(2), "the stop rose on the third poll");
    assert_eq!(v.reply, peer(&v.request), "the taped reply is the peer's");
    assert_eq!(v.said, [b"got ".as_slice(), &v.reply].concat());
    assert!(v.mono1 >= v.mono0, "the monotonic clock did not run back");

    // REPLAY: tape only, closures that panic if called.
    let (replayed, at) = replay(log.clone(), REAL_FILE);
    assert_eq!(replayed, Ok(recorded), "replay reproduces the recorded run");
    assert_eq!(at, log.0.len(), "and consumed the whole tape");
    // The independent oracle over the taped values agrees: the replayed
    // program asked exactly the taped request, printed exactly the taped
    // output, and saw the flag rise at exactly the taped poll.
    assert_eq!(
        recorded,
        converse_oracle(&v),
        "replay == independent oracle"
    );
    // Sensitivity, so the agreement is not vacuous: moving the rise by one
    // poll, dropping it, or changing one reply byte moves the oracle.
    for (what, other) in [
        ("rise one poll earlier", {
            let mut o = v.clone();
            o.raised_at = Some(1);
            o
        }),
        ("no rise", {
            let mut o = v.clone();
            o.raised_at = None;
            o
        }),
        ("one reply byte", {
            let mut o = v.clone();
            o.reply[0] ^= 1;
            o
        }),
    ] {
        assert_ne!(converse_oracle(&other), recorded, "{what} moves the digest");
    }

    // A second replay from the same tape is identical (deterministic).
    assert_eq!(replay(log, REAL_FILE).0, Ok(recorded));
}

#[test]
fn replay_with_live_closures_that_panic_completes_where_the_world_is_gone() {
    // Recorded against a path that exists nowhere (the deterministic backend
    // answers it); replayed with panicking peer and flag. Completing proves no
    // closure ran and no file was opened.
    let gone = "/nonexistent/astream-effects/replay-world";
    let (recorded, log) = record(Fixed::default(), gone, &[true]);
    assert_eq!(converse_values(&log).unwrap().raised_at, Some(0));
    assert_eq!(replay(log, gone).0, Ok(recorded));

    // Nor does a tape that has ended send either door to the world: the reply
    // door refuses, and the flag reads false (a rise the recording saw would
    // have left a Raised record).
    let mut ended = ReplaySeam::new(EffectsLog::default());
    assert_eq!(
        ended.exchange("peer", b"q", &mut no_peer),
        Err(ReplayDivergence::Exhausted {
            expected: "Exchange"
        })
    );
    assert_eq!(
        poll(&mut ended, "stop", 3, &mut no_flag),
        Ok(vec![false; 3])
    );
}

/// One recorded converse tape over the deterministic backend, its digest, and
/// the positions of its records.
fn fixed_tape() -> (u64, Vec<EffectRecord>) {
    let (digest, log) = record(Fixed::default(), "/f", &[false, true]);
    (digest, log.0)
}
const EXCHANGE_AT: usize = 4;
const EMIT_AT: usize = 5;

#[test]
fn a_wrong_door_request_output_kind_or_length_refuses_with_its_own_variant() {
    let (_, tape) = fixed_tape();
    let (request, said) = match (&tape[EXCHANGE_AT], &tape[EMIT_AT]) {
        (EffectRecord::Exchange { request, .. }, EffectRecord::Emit { bytes, .. }) => {
            (request.clone(), bytes.clone())
        }
        other => panic!("unexpected tape layout: {other:?}"),
    };
    let edited = |edit: &dyn Fn(&mut Vec<EffectRecord>)| {
        let mut t = tape.clone();
        edit(&mut t);
        replay(EffectsLog(t), "/f")
    };

    // Wrong door: the exchange was recorded through another door.
    let (r, at) = edited(&|t| {
        if let EffectRecord::Exchange { door, .. } = &mut t[EXCHANGE_AT] {
            *door = "teller".into();
        }
    });
    assert_eq!(
        r,
        Err(ReplayDivergence::DoorDiverged {
            recorded: "teller".into(),
            asked: "peer".into(),
        })
    );
    assert_eq!(at, EXCHANGE_AT, "a refusal consumes nothing");

    // Wrong request: a different random word on the tape makes the program
    // ask a different question, which the recorded reply does not answer.
    let (r, at) = edited(&|t| t[2] = EffectRecord::Rand(7));
    assert_eq!(
        r,
        Err(ReplayDivergence::RequestDiverged {
            door: "peer".into(),
            recorded: request.clone(),
            asked: ask(7, b"contents of /f"),
        })
    );
    assert_eq!(at, EXCHANGE_AT);

    // Wrong output: a different reply on the tape makes the program print a
    // different line, caught at the output door itself.
    let (r, at) = edited(&|t| {
        if let EffectRecord::Exchange { reply, .. } = &mut t[EXCHANGE_AT] {
            *reply = b"something else".to_vec();
        }
    });
    assert_eq!(
        r,
        Err(ReplayDivergence::OutputDiverged {
            door: "out".into(),
            recorded: said.clone(),
            emitted: say(b"something else"),
        })
    );
    assert_eq!(at, EMIT_AT);

    // An output through another door is a door divergence too.
    let (r, _) = edited(&|t| {
        if let EffectRecord::Emit { door, .. } = &mut t[EMIT_AT] {
            *door = "journal".into();
        }
    });
    assert_eq!(
        r,
        Err(ReplayDivergence::DoorDiverged {
            recorded: "journal".into(),
            asked: "out".into(),
        })
    );

    // Wrong kind: the opening monotonic read finds the wall clock.
    let (r, at) = edited(&|t| t.swap(0, 1));
    assert!(
        matches!(
            r,
            Err(ReplayDivergence::KindMismatch {
                expected: "Mono",
                found: EffectRecord::Clock(_)
            })
        ),
        "{r:?}"
    );
    assert_eq!(at, 0);

    // Short tapes: cut before the closing monotonic read, before the output,
    // and before the exchange.
    let (r, _) = edited(&|t| {
        t.pop();
    });
    assert_eq!(r, Err(ReplayDivergence::Exhausted { expected: "Mono" }));
    // An output past the end of the tape is a replay saying something the
    // recorded run never said. Nothing is left to compare it with, and that
    // is a refusal at the output itself, not a pass: an `emit` that let it
    // through would only be caught at the next read, and a program whose
    // drift is its last words would replay green.
    let (r, at) = edited(&|t| t.truncate(EMIT_AT));
    assert_eq!(r, Err(ReplayDivergence::Exhausted { expected: "Emit" }));
    assert_eq!(at, EMIT_AT);
    let mut ended = ReplaySeam::new(EffectsLog::default());
    assert_eq!(
        ended.emit("out", b"one line too many"),
        Err(ReplayDivergence::Exhausted { expected: "Emit" })
    );
    assert_eq!(ended.position(), 0);
    let (r, at) = edited(&|t| t.truncate(EXCHANGE_AT));
    assert_eq!(
        r,
        Err(ReplayDivergence::Exhausted {
            expected: "Exchange"
        })
    );
    assert_eq!(at, EXCHANGE_AT);
}

#[test]
fn a_tape_longer_than_the_run_is_refused_where_the_program_ends() {
    // No door sees a LONG tape: the program stops asking, every door it did
    // use answered from the tape, and it returns its digest. The records left
    // are what the recorded run went on to do, and `finish` — called where
    // the program ends — refuses them, consuming nothing.
    let (digest, tape) = fixed_tape();
    let last_words = EffectRecord::Emit {
        door: "out".into(),
        bytes: b"bye".to_vec(),
    };
    let mut longer = tape.clone();
    longer.push(last_words.clone());
    let mut seam = ReplaySeam::new(EffectsLog(longer.clone()));
    assert_eq!(
        converse(&mut seam, "/f", &mut no_peer, &mut no_flag),
        Ok(digest),
        "every door the program used answered: nothing else catches the extra line"
    );
    let unreached = ReplayDivergence::Unreached {
        position: tape.len(),
        found: last_words.clone(),
    };
    assert_eq!(seam.finish(), Err(unreached.clone()));
    assert_eq!(
        seam.finish(),
        Err(unreached.clone()),
        "finishing consumes nothing"
    );
    assert_eq!(
        (seam.position(), seam.peek()),
        (tape.len(), Some(&last_words))
    );
    assert_eq!(
        replay(EffectsLog(longer), "/f"),
        (Err(unreached), tape.len()),
        "a whole-run replay reports it"
    );
    // The exact tape finishes clean, as often as it is asked.
    let mut exact = ReplaySeam::new(EffectsLog(tape.clone()));
    assert_eq!(
        converse(&mut exact, "/f", &mut no_peer, &mut no_flag),
        Ok(digest)
    );
    assert_eq!((exact.finish(), exact.finish()), (Ok(()), Ok(())));

    // A flag the recorded run polled F then T (one false read before the
    // rise): a replay that polls it once and returns has taken the
    // not-stopped path. The flag door answers false and leaves the record —
    // by design, since the count says a later read — so only `finish` sees
    // that the rise was never reached.
    let rose = EffectRecord::Raised {
        door: "stop".into(),
        false_reads: 1,
    };
    let mut once = ReplaySeam::new(EffectsLog(vec![rose.clone()]));
    assert_eq!(once.raised("stop", &mut no_flag), Ok(false));
    assert_eq!(
        once.finish(),
        Err(ReplayDivergence::Unreached {
            position: 0,
            found: rose.clone(),
        })
    );
    // Polled as the recorded run polled it, the same tape finishes clean.
    let mut twice = ReplaySeam::new(EffectsLog(vec![rose]));
    assert_eq!(
        poll(&mut twice, "stop", 2, &mut no_flag),
        Ok(vec![false, true])
    );
    assert_eq!(twice.finish(), Ok(()));

    // An empty tape run by a program that asks nothing is complete.
    assert_eq!(ReplaySeam::new(EffectsLog::default()).finish(), Ok(()));
}

/// Read `door` `n` times through `seam`, collecting the answers.
fn poll<S: EffectSeam>(
    seam: &mut S,
    door: &str,
    n: usize,
    live: &mut dyn FnMut() -> bool,
) -> Result<Vec<bool>, S::Error> {
    (0..n).map(|_| seam.raised(door, live)).collect()
}

#[test]
fn raised_over_f_f_t_t_tapes_one_record_and_replays_the_same_answers() {
    let reads = Rc::new(Cell::new(0));
    let mut rec = RecordingSeam::new(Fixed::default());
    let Ok(answers) = poll(
        &mut rec,
        "stop",
        4,
        &mut scripted(&[false, false, true, true], reads.clone()),
    );
    assert_eq!(answers, [false, false, true, true]);
    assert_eq!(reads.get(), 3, "latched after the first true read");
    let log = rec.into_log();
    assert_eq!(
        log.0,
        [EffectRecord::Raised {
            door: "stop".into(),
            false_reads: 2,
        }],
        "one record, counting the two false reads before it"
    );

    let mut rep = ReplaySeam::new(log);
    assert_eq!(
        poll(&mut rep, "stop", 4, &mut no_flag),
        Ok(vec![false, false, true, true]),
        "the same answers, with nothing else on the tape to separate the reads"
    );
    assert_eq!((rep.position(), rep.peek()), (1, None));

    // The count is what tells back-to-back reads apart: the same rise one read
    // earlier is a different tape, and replays one read earlier.
    let mut rec = RecordingSeam::new(Fixed::default());
    let Ok(early) = poll(
        &mut rec,
        "stop",
        4,
        &mut scripted(&[false, true], Rc::default()),
    );
    let early_log = rec.into_log();
    assert_eq!(early, [false, true, true, true]);
    assert_eq!(
        early_log.0,
        [EffectRecord::Raised {
            door: "stop".into(),
            false_reads: 1,
        }]
    );
    assert_eq!(
        poll(&mut ReplaySeam::new(early_log), "stop", 4, &mut no_flag),
        Ok(early)
    );
}

#[test]
fn false_read_counts_are_per_door_and_restart_at_every_record() {
    // stop F, handover F, (mono), stop F, handover T, stop T. The Mono restarts
    // both counts; the handover's rise counts only its own reads since the
    // Mono (none); the stop's false read sits before the handover's record,
    // which restarts its count, so the stop's rise counts none either.
    let mut stop = scripted(&[false, false, true], Rc::default());
    let mut hand = scripted(&[false, true], Rc::default());
    let mut rec = RecordingSeam::new(Fixed::default());
    let Ok(a) = rec.raised("stop", &mut stop);
    let Ok(b) = rec.raised("handover", &mut hand);
    let Ok(mono) = rec.mono_nanos();
    let Ok(c) = rec.raised("stop", &mut stop);
    let Ok(d) = rec.raised("handover", &mut hand);
    let Ok(e) = rec.raised("stop", &mut stop);
    let answers = [a, b, c, d, e];
    assert_eq!(answers, [false, false, false, true, true]);
    let log = rec.into_log();
    assert_eq!(
        log.0,
        [
            EffectRecord::Mono(mono),
            EffectRecord::Raised {
                door: "handover".into(),
                false_reads: 0,
            },
            EffectRecord::Raised {
                door: "stop".into(),
                false_reads: 0,
            },
        ]
    );

    let mut rep = ReplaySeam::new(log);
    let a = rep.raised("stop", &mut no_flag);
    let b = rep.raised("handover", &mut no_flag);
    assert_eq!(rep.mono_nanos(), Ok(mono));
    let c = rep.raised("stop", &mut no_flag);
    let d = rep.raised("handover", &mut no_flag);
    let e = rep.raised("stop", &mut no_flag);
    assert_eq!(
        [a, b, c, d, e],
        answers.map(Ok),
        "replay gives the same answers"
    );

    // A false read of ANOTHER door between two of this door's reads does not
    // shift this door's count.
    let tape = EffectsLog(vec![EffectRecord::Raised {
        door: "stop".into(),
        false_reads: 1,
    }]);
    let mut rep = ReplaySeam::new(tape);
    let seen = [
        rep.raised("handover", &mut no_flag),
        rep.raised("stop", &mut no_flag),
        rep.raised("handover", &mut no_flag),
        rep.raised("stop", &mut no_flag),
    ];
    assert_eq!(seen, [Ok(false), Ok(false), Ok(false), Ok(true)]);
}

#[test]
fn a_lowered_flag_stays_raised_on_every_seam() {
    // The live flag rises and FALLS. Every seam latches, so the program sees
    // the same answers with recording on, off, or replayed.
    const SCRIPT: &[bool] = &[false, true, false, false];
    let latched = vec![false, true, true, true];

    let reads = Rc::new(Cell::new(0));
    let mut rec = RecordingSeam::new(Fixed::default());
    let Ok(recorded) = poll(&mut rec, "stop", 4, &mut scripted(SCRIPT, reads.clone()));
    assert_eq!((recorded.clone(), reads.get()), (latched.clone(), 2));

    let reads = Rc::new(Cell::new(0));
    let mut live = LiveSeam::new(Fixed::default());
    let Ok(untaped) = poll(&mut live, "stop", 4, &mut scripted(SCRIPT, reads.clone()));
    assert_eq!((untaped, reads.get()), (latched.clone(), 2));

    assert_eq!(
        poll(
            &mut ReplaySeam::new(rec.into_log()),
            "stop",
            4,
            &mut no_flag
        ),
        Ok(latched)
    );
}

#[test]
fn a_raised_record_ahead_of_an_exchange_is_refused_not_skipped() {
    let raised = EffectRecord::Raised {
        door: "stop".into(),
        false_reads: 0,
    };
    let tape = EffectsLog(vec![
        raised.clone(),
        EffectRecord::Exchange {
            door: "peer".into(),
            request: b"q".to_vec(),
            reply: b"a".to_vec(),
        },
    ]);
    let mut rep = ReplaySeam::new(tape);
    // The recorded program read the stop before it asked; this one asks first.
    assert_eq!(
        rep.exchange("peer", b"q", &mut no_peer),
        Err(ReplayDivergence::KindMismatch {
            expected: "Exchange",
            found: raised.clone(),
        })
    );
    assert_eq!(rep.position(), 0, "the refusal consumed nothing");
    assert_eq!(rep.peek(), Some(&raised), "the record is still next");
    // Reading ANOTHER flag does not take it either.
    assert_eq!(rep.raised("handover", &mut no_flag), Ok(false));
    assert_eq!(rep.position(), 0);
    // Reading the recorded flag does, and the exchange then answers.
    assert_eq!(rep.raised("stop", &mut no_flag), Ok(true));
    assert_eq!(rep.position(), 1);
    assert_eq!(rep.exchange("peer", b"q", &mut no_peer), Ok(b"a".to_vec()));
    assert_eq!(rep.raised("stop", &mut no_flag), Ok(true), "latched");

    // The count is held to as well: the recorded program polled three times
    // before the flag rose (two false reads); a replay that polls once and
    // moves on finds the rise still ahead of it, and is refused there.
    let counted = EffectRecord::Raised {
        door: "stop".into(),
        false_reads: 2,
    };
    let mut rep = ReplaySeam::new(EffectsLog(vec![counted.clone(), EffectRecord::Mono(5)]));
    assert_eq!(rep.raised("stop", &mut no_flag), Ok(false));
    assert_eq!(
        rep.mono_nanos(),
        Err(ReplayDivergence::KindMismatch {
            expected: "Mono",
            found: counted,
        })
    );
    assert_eq!(rep.position(), 0);
}

#[test]
fn a_live_seam_answers_like_the_recording_seam_and_keeps_no_tape() {
    // The same deterministic world under LiveSeam and RecordingSeam: the same
    // digest, the same live calls. LiveSeam has no log, no sink and no
    // `into_log` — the one thing it hands back is its backend.
    fn counted<S: EffectSeam<Error = Infallible>>(seam: &mut S) -> (u64, usize, usize) {
        let peer_calls = Cell::new(0);
        let reads = Rc::new(Cell::new(0));
        let Ok(digest) = converse(
            seam,
            "/f",
            &mut |q: &[u8]| {
                peer_calls.set(peer_calls.get() + 1);
                peer(q)
            },
            &mut scripted(&[false, false, false, true], reads.clone()),
        );
        (digest, peer_calls.get(), reads.get())
    }
    let mut live = LiveSeam::new(Fixed::default());
    let untaped = counted(&mut live);
    let mut rec = RecordingSeam::new(Fixed::default());
    let taped = counted(&mut rec);
    assert_eq!(untaped, taped);
    assert_eq!(
        (untaped.1, untaped.2),
        (1, 4),
        "one peer call, four flag reads"
    );
    assert_eq!(
        live.into_inner().reads,
        5,
        "the backend saw mono, clock, rand, file, mono"
    );
    assert_eq!(rec.into_log().0.len(), 8, "the recording kept all eight");

    // The request's length is decimal, including zero and digit carries.
    for (len, decimal) in [(0, "0"), (9, "9"), (10, "10"), (99, "99"), (100, "100")] {
        assert_eq!(
            ask(0, &vec![b'x'; len]),
            format!("ask rand=0000000000000000 len={decimal}").into_bytes()
        );
    }
}

/// An iterator over records that counts how many the consumer pulled.
struct Counting {
    records: std::vec::IntoIter<EffectRecord>,
    pulled: Rc<Cell<usize>>,
}

impl Iterator for Counting {
    type Item = EffectRecord;
    fn next(&mut self) -> Option<EffectRecord> {
        let r = self.records.next();
        if r.is_some() {
            self.pulled.set(self.pulled.get() + 1);
        }
        r
    }
}

#[test]
fn a_sink_streams_the_same_records_and_a_streaming_replay_pulls_them_lazily() {
    let (digest, log) = record(Fixed::default(), "/f", &[false, true]);
    // The same run streamed to a closure instead of kept.
    let mut streamed = Vec::new();
    let mut rec = RecordingSeam::with_sink(Fixed::default(), |r: &EffectRecord| {
        streamed.push(r.clone())
    });
    let Ok(streamed_digest) = converse(
        &mut rec,
        "/f",
        &mut peer,
        &mut scripted(&[false, true], Rc::default()),
    );
    drop(rec);
    assert_eq!((streamed_digest, &streamed), (digest, &log.0));

    // A boxed `Send` sink is a sink, and the seam over it is `Send`, so a
    // recorder can be handed to another thread or kept behind a lock. A lock
    // around the seam is held while a door's `live` closure runs, though, so a
    // recorder whose live round trips may reach another door through the
    // same recorder runs the round trip outside the lock and gives `exchange`
    // the reply it already has — and tapes the same record.
    fn assert_send<T: Send>(_: &T) {}
    let boxed: Box<dyn FnMut(&EffectRecord) + Send> = Box::new(|_| {});
    let shared = std::sync::Mutex::new(RecordingSeam::with_sink(Fixed::default(), boxed));
    assert_send(&shared);
    let reply = peer(b"q");
    let Ok(got) = shared
        .lock()
        .expect("an unpoisoned lock")
        .exchange("peer", b"q", &mut |_| reply.clone());
    assert_eq!(got, peer(b"q"));
    let mut inside = RecordingSeam::new(Fixed::default());
    let mut outside = RecordingSeam::new(Fixed::default());
    let Ok(_) = inside.exchange("peer", b"q", &mut peer);
    let reply = peer(b"q");
    let Ok(_) = outside.exchange("peer", b"q", &mut |_| reply.clone());
    assert_eq!(inside.into_log(), outside.into_log());

    // Replay from an iterator, step by step through the program's first four
    // doors: the seam pulls a record only when the program reaches it, plus at
    // most one of look-ahead.
    let pulled = Rc::new(Cell::new(0));
    let mut rep = ReplaySeam::streaming(Counting {
        records: streamed.into_iter(),
        pulled: pulled.clone(),
    });
    assert_eq!(pulled.get(), 0, "nothing is pulled before the program asks");
    assert!(rep.mono_nanos().is_ok());
    assert!(
        pulled.get() <= rep.position() + 1,
        "pulled {}",
        pulled.get()
    );
    assert!(rep.now_nanos().is_ok());
    assert!(rep.next_rand().is_ok());
    assert!(rep.read_file("/f").is_ok());
    assert_eq!(rep.position(), 4);
    assert!(pulled.get() <= 5, "pulled {}", pulled.get());
    // And the whole program replays from a streamed tape, pulling it once.
    let pulled = Rc::new(Cell::new(0));
    let mut whole = ReplaySeam::streaming(Counting {
        records: log.0.clone().into_iter(),
        pulled: pulled.clone(),
    });
    assert_eq!(
        converse(&mut whole, "/f", &mut no_peer, &mut no_flag),
        Ok(digest)
    );
    assert_eq!(pulled.get(), log.0.len());
    assert_eq!(whole.finish(), Ok(()), "and the stream is at its end");
}

#[test]
fn the_wall_and_monotonic_clocks_never_stand_in_for_each_other() {
    assert_eq!(
        ReplaySeam::new(EffectsLog(vec![EffectRecord::Clock(5)])).mono_nanos(),
        Err(ReplayDivergence::KindMismatch {
            expected: "Mono",
            found: EffectRecord::Clock(5),
        })
    );
    assert_eq!(
        ReplaySeam::new(EffectsLog(vec![EffectRecord::Mono(5)])).now_nanos(),
        Err(ReplayDivergence::KindMismatch {
            expected: "Clock",
            found: EffectRecord::Mono(5),
        })
    );
}

/// The first `n` characters of `s`, for a failure message about a message that
/// is too long to print.
fn head(s: &str, n: usize) -> String {
    s.chars().take(n).collect()
}

#[test]
fn a_divergence_message_stays_short_when_the_bytes_are_long() {
    // A reply door carries whole screens, and so does the record a refusal
    // FOUND: the likeliest first divergence is a build that adds a clock read
    // and finds a screen-carrying Exchange where its Mono should be. Every
    // refusal that holds bytes — in its own fields or in that record — names
    // the divergence in under a KiB, in its Display and in its Debug alike,
    // because Debug is what `?` out of `main`, `unwrap` and `expect` print,
    // and a recorded screen belongs on the tape, not in whatever stderr, log
    // or reply carries the message.
    let screen = vec![b'x'; 64 * 1024];
    let mut moved = screen.clone();
    moved[1000] = b'y';
    let found = EffectRecord::Exchange {
        door: "ctl".into(),
        request: screen.clone(),
        reply: screen.clone(),
    };
    let drifted = ReplaySeam::new(EffectsLog(vec![found.clone()])).mono_nanos();
    assert_eq!(
        drifted,
        Err(ReplayDivergence::KindMismatch {
            expected: "Mono",
            found,
        })
    );
    let refusals = [
        drifted.unwrap_err(),
        ReplayDivergence::KindMismatch {
            expected: "Clock",
            found: EffectRecord::File {
                path: "/f".into(),
                bytes: screen.clone(),
            },
        },
        ReplayDivergence::KindMismatch {
            expected: "Clock",
            found: EffectRecord::Emit {
                door: "out".into(),
                bytes: screen.clone(),
            },
        },
        ReplayDivergence::RequestDiverged {
            door: "ctl".into(),
            recorded: screen.clone(),
            asked: moved.clone(),
        },
        ReplayDivergence::OutputDiverged {
            door: "out".into(),
            recorded: screen.clone(),
            emitted: moved.clone(),
        },
        ReplayDivergence::Unrecorded {
            door: "ctl".into(),
            request: screen.clone(),
        },
        ReplayDivergence::Unreached {
            position: 9,
            found: EffectRecord::Exchange {
                door: "ctl".into(),
                request: screen.clone(),
                reply: screen.clone(),
            },
        },
    ];
    for refusal in &refusals {
        for (form, msg) in [
            ("Display", refusal.to_string()),
            ("Debug", format!("{refusal:?}")),
        ] {
            assert!(
                msg.len() < 1024,
                "{form} is {} bytes: {}…",
                msg.len(),
                head(&msg, 160)
            );
        }
    }
    // The found record is still named: its kind and its door.
    let drift = refusals[0].to_string();
    assert!(
        drift.contains("Exchange") && drift.contains("\"ctl\""),
        "{drift}"
    );

    // Two screens that share their first KiB: a message that showed each
    // side's head would print the same text twice. It names the byte where
    // they part and shows each side from just before it, so the differing
    // byte is in the message.
    for refusal in &refusals[3..5] {
        for msg in [refusal.to_string(), format!("{refusal:?}")] {
            assert!(msg.contains("1000"), "names the offset: {msg}");
            assert!(msg.contains('y'), "shows the differing byte: {msg}");
        }
    }
}
