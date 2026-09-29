//! Claim `term.perceive.semantic-events`: a recorded terminal session is
//! classified into the semantic boundaries a driving agent wakes on —
//! prompt-ready, command-start, command-end (+ exit), and screen-quiescence —
//! deterministically from the `Out` log, program-agnostic via OSC-133/633 marks
//! plus a per-program glyph profile (consulted only for a target that has
//! emitted no OSC-133/633 A/C/D mark), in the streaming order (marks in record
//! order, then the settle events), panic-free + deterministic over arbitrary
//! bytes, and with the streaming classifier equal to the batch one over the
//! fixtures, an ST-terminated session split at every byte boundary, and
//! proptest-generated chunked byte streams.

use astream_term::events::{classify, quiesced_at, EventClassifier, Profile, SessionEvent};
use astream_term::record::Record;
use proptest::prelude::*;

fn out(s: &[u8]) -> Record {
    Record::Out(s.to_vec())
}

// A realistic OSC-133 command cycle: prompt (A), the echoed command line, the
// output-start mark (C), the output, then command-end with exit 0 (D;0). aterm's
// integrated shells emit exactly this shape.
fn osc133_session() -> Vec<Record> {
    vec![
        out(b"\x1b[2J\x1b[H"),
        out(b"\x1b]133;A\x07user@host % "), // prompt drawn, ready
        out(b"echo hi\r\n"),                // the command line echoes
        out(b"\x1b]133;C\x07"),             // output starts
        out(b"hi\r\n"),                     // the output
        out(b"\x1b]133;D;0\x07"),           // command ended, exit 0
        out(b"\x1b]133;A\x07user@host % "), // next prompt, ready again
    ]
}

// The same cycle with ST (`ESC \`) terminators, as one byte string — the shape a
// PTY read boundary can fall anywhere inside.
fn st_terminated_session() -> Vec<u8> {
    [
        b"\x1b[2J\x1b[H".as_slice(),
        b"\x1b]133;A\x1b\\user@host % ",
        b"echo hi\r\n",
        b"\x1b]133;C\x1b\\",
        b"hi\r\n",
        b"\x1b]133;D;0\x1b\\",
        b"\x1b]133;A\x1b\\user@host % ",
    ]
    .concat()
}

// Run the streaming classifier exactly as the pump does: push every record as it
// arrives, then quiesce once when the stream goes idle.
fn stream(cols: u16, rows: u16, recs: &[Record]) -> Vec<SessionEvent> {
    let mut c = EventClassifier::new(cols, rows, Profile::common());
    let mut ev = Vec::new();
    for r in recs {
        ev.extend(c.push(r));
    }
    ev.extend(c.quiesce());
    ev
}

// The OSC mark events of a timeline with their offsets erased: what a split must
// preserve (recognition), independent of where the split moved each mark to.
fn marks(ev: &[SessionEvent]) -> Vec<(char, Option<i32>)> {
    ev.iter()
        .filter_map(|e| match e {
            SessionEvent::PromptReady { .. } => Some(('A', None)),
            SessionEvent::CommandStart { .. } => Some(('C', None)),
            SessionEvent::CommandEnd { exit, .. } => Some(('D', *exit)),
            SessionEvent::Quiesced { .. } => None,
        })
        .collect()
}

#[test]
fn osc133_marks_classify_to_wake_boundaries() {
    let recs = osc133_session();
    let ev = classify(80, 24, &recs, &Profile::common());

    // The exact timeline: the four OSC boundaries at their record offsets, in
    // record order, exit code carried through, then the settle event (record 6
    // paints the last prompt). No glyph PromptReady: the session is integrated.
    assert_eq!(
        ev,
        vec![
            SessionEvent::PromptReady { offset: 1 },
            SessionEvent::CommandStart { offset: 3 },
            SessionEvent::CommandEnd {
                offset: 5,
                exit: Some(0)
            },
            SessionEvent::PromptReady { offset: 6 },
            SessionEvent::Quiesced { offset: 6 },
        ]
    );

    // The public accessor names the record each event is anchored to.
    assert_eq!(
        ev.iter().map(SessionEvent::offset).collect::<Vec<_>>(),
        vec![1, 3, 5, 6, 6]
    );

    // Deterministic: classifying twice is identical.
    assert_eq!(ev, classify(80, 24, &recs, &Profile::common()));
}

#[test]
fn nonzero_exit_is_captured() {
    let recs = vec![
        out(b"\x1b]133;A\x07$ "),
        out(b"\x1b]133;C\x07"),
        out(b"boom\r\n"),
        out(b"\x1b]133;D;127\x07"),
    ];
    let ev = classify(80, 24, &recs, &Profile::common());
    // The D mark repaints nothing (the fold swallows OSC), so the settle is the
    // `boom` line at record 2 — strictly before the mark's own offset, which is
    // why the mark precedes `Quiesced` in the timeline despite the higher offset.
    let q = 2;
    assert_eq!(quiesced_at(80, 24, &recs), Some(q));
    assert_eq!(
        ev,
        vec![
            SessionEvent::PromptReady { offset: 0 },
            SessionEvent::CommandStart { offset: 1 },
            SessionEvent::CommandEnd {
                offset: 3,
                exit: Some(127)
            },
            SessionEvent::Quiesced { offset: q },
        ]
    );
}

#[test]
fn glyph_profile_finds_prompt_without_osc() {
    // A bare REPL: no OSC-133 at all, but the settled screen ends in `>>>`.
    let recs = vec![out(b"\x1b[2J\x1b[HPython 3.9\r\n"), out(b">>> ")];
    let ev = classify(80, 24, &recs, &Profile::common());
    // Quiescence is emitted, and the glyph profile supplies PromptReady at it.
    assert_eq!(quiesced_at(80, 24, &recs), Some(1));
    assert_eq!(
        ev,
        vec![
            SessionEvent::Quiesced { offset: 1 },
            SessionEvent::PromptReady { offset: 1 },
        ]
    );
}

#[test]
fn glyph_markers_cover_claude_a_repl_and_a_shell_but_not_codex() {
    // Every marker of the common profile is read as prompt-ready at the settle.
    for marker in ["❯", ">>>", "$", "%", "#"] {
        let prompt = format!("{marker} ");
        let recs = vec![out(b"\x1b[2J\x1b[Hbanner\r\n"), out(prompt.as_bytes())];
        let ev = classify(80, 24, &recs, &Profile::common());
        assert!(
            ev.contains(&SessionEvent::PromptReady { offset: 1 }),
            "{marker:?} must be read as prompt-ready: {ev:?}"
        );
    }
    // Codex's `»` composer is visible while Codex is still working, so it is NOT
    // a prompt glyph (DESIGN-drive-pipe.md §5): its wake is quiescence alone.
    let recs = vec![out(b"\x1b[2J\x1b[Hworking...\r\n"), out("» ".as_bytes())];
    let ev = classify(80, 24, &recs, &Profile::common());
    assert_eq!(ev, vec![SessionEvent::Quiesced { offset: 1 }]);
}

#[test]
fn no_glyph_no_false_prompt() {
    // Output that does NOT end in a prompt marker yields no glyph PromptReady.
    let recs = vec![out(b"\x1b[2J\x1b[Hjust some output text\r\n")];
    let ev = classify(80, 24, &recs, &Profile::common());
    assert!(
        !ev.iter()
            .any(|e| matches!(e, SessionEvent::PromptReady { .. })),
        "no prompt marker present, so no PromptReady: {ev:?}"
    );
    // But quiescence is still reported.
    assert!(ev
        .iter()
        .any(|e| matches!(e, SessionEvent::Quiesced { .. })));
}

#[test]
fn glyph_prompt_is_suppressed_while_an_osc_command_runs() {
    // An integrated shell has told us a command is in flight (C seen, no D); the
    // download stalls with a progress line ending in `%` on screen. The settle
    // must NOT be read as a prompt — the driver would type into a running curl.
    let recs = vec![
        out(b"\x1b[2J\x1b[H\x1b]133;A\x07$ "),
        out(b"curl big\r\n"),
        out(b"\x1b]133;C\x07"),
        out(b"\r####          45.0%"),
    ];
    let expected = vec![
        SessionEvent::PromptReady { offset: 0 },
        SessionEvent::CommandStart { offset: 2 },
        SessionEvent::Quiesced { offset: 3 },
    ];
    assert_eq!(classify(80, 24, &recs, &Profile::common()), expected);
    assert_eq!(stream(80, 24, &recs), expected);
}

#[test]
fn integrated_session_never_reads_a_glyph_as_prompt() {
    // Once a session has shown any OSC-133/633 mark, prompt-ready is the A mark's
    // job: a `$ ` drawn WITHOUT its A mark after a command ended (a nested
    // non-integrated shell, a redraw) is not a prompt — the settle still wakes.
    let recs = vec![
        out(b"\x1b]133;A\x07$ "),
        out(b"sh\r\n"),
        out(b"\x1b]133;C\x07"),
        out(b"\x1b]133;D;0\x07"),
        out(b"$ "),
    ];
    let expected = vec![
        SessionEvent::PromptReady { offset: 0 },
        SessionEvent::CommandStart { offset: 2 },
        SessionEvent::CommandEnd {
            offset: 3,
            exit: Some(0),
        },
        SessionEvent::Quiesced { offset: 4 },
    ];
    assert_eq!(classify(80, 24, &recs, &Profile::common()), expected);
    assert_eq!(stream(80, 24, &recs), expected);

    // The streaming classifier exposes the state it gates on.
    let mut c = EventClassifier::new(80, 24, Profile::common());
    assert!(!c.integrated());
    c.push(&recs[0]);
    assert!(c.integrated(), "an A mark proves shell integration");
}

#[test]
fn a_non_lifecycle_mark_letter_does_not_disable_the_glyph_profile() {
    // `B` (input boundary), `E` (command line) and `P` (property) are documented
    // as NOT wakes, and an unknown letter is not one either. None of them carries
    // the prompt/command lifecycle, so none may hand prompt-ready to signal 1:
    // the gate is A/C/D. Otherwise ONE such byte sequence anywhere in the output
    // — here a log line a REPL printed — would permanently blind glyph detection
    // for the rest of the session.
    for letter in ["B", "E", "P;Cwd=/tmp", "Z"] {
        let line = format!("log line: \x1b]133;{letter}\x07 oops\r\n");
        let recs = vec![
            out(b"\x1b[2J\x1b[Hcat log.txt\r\n"),
            out(line.as_bytes()),
            out(b">>> "),
        ];
        let expected = vec![
            SessionEvent::Quiesced { offset: 2 },
            SessionEvent::PromptReady { offset: 2 },
        ];
        assert_eq!(
            classify(80, 24, &recs, &Profile::common()),
            expected,
            "a `{letter}` mark must leave the glyph profile on"
        );
        assert_eq!(stream(80, 24, &recs), expected, "and in the stream too");

        // The state the gate reads stays false through the whole session.
        let mut c = EventClassifier::new(80, 24, Profile::common());
        for r in &recs {
            c.push(r);
        }
        assert!(
            !c.integrated(),
            "a `{letter}` mark is not proof that signal 1 owns prompt-ready"
        );
    }

    // 633 marks gate the same way: `633;P` (VS Code's cwd report) is not a
    // lifecycle mark, `633;A` is.
    let mut c = EventClassifier::new(80, 24, Profile::common());
    c.push(&out(b"\x1b]633;P;Cwd=/home\x07"));
    assert!(!c.integrated());
    c.push(&out(b"\x1b]633;A\x07"));
    assert!(c.integrated());
}

#[test]
fn quiescence_is_the_last_painting_change() {
    // Trailing In/Exit records don't paint, so quiescence stays at the last Out
    // that changed the screen.
    let recs = vec![
        out(b"\x1b[2J\x1b[Hone"),
        out(b" two"),
        Record::In {
            bytes: b"x".to_vec(),
            client_id: 1,
            client_seq: 1,
        },
        Record::Exit { code: 0 },
    ];
    assert_eq!(quiesced_at(80, 24, &recs), Some(1));
}

#[test]
fn settle_events_follow_a_mark_that_repaints_nothing() {
    // A mark whose record leaves the screen unchanged lands AFTER the settle
    // point. The timeline is the streaming order — the mark, then Quiesced at the
    // (earlier) settle offset — not a global offset sort, and batch == stream.
    let cases: Vec<(Vec<Record>, Vec<SessionEvent>)> = vec![
        (
            // The ST terminator split so the trailing `\` is a record of its own:
            // the parser swallows it, the carry completes the mark at offset 1.
            vec![out(b"\x1b]133;D;0\x1b"), out(b"\\")],
            vec![
                SessionEvent::CommandEnd {
                    offset: 1,
                    exit: Some(0),
                },
                SessionEvent::Quiesced { offset: 0 },
            ],
        ),
        (
            // A prompt mark on a record that repaints an identical (blank) screen.
            vec![out(b"\x1b[2J\x1b[H"), out(b"\x1b]133;A\x07\x1b[2J\x1b[H")],
            vec![
                SessionEvent::PromptReady { offset: 1 },
                SessionEvent::Quiesced { offset: 0 },
            ],
        ),
    ];
    for (recs, expected) in cases {
        assert_eq!(classify(80, 24, &recs, &Profile::common()), expected);
        assert_eq!(stream(80, 24, &recs), expected);
    }
}

#[test]
fn panic_free_and_deterministic_over_arbitrary_bytes() {
    // A deterministic pseudo-fuzz (no dependency): feed adversarial byte streams,
    // including truncated/oversized OSC introducers, and assert the classifier
    // never panics and is a pure function — as one record, and split into
    // records at pseudo-random boundaries (the carry/split path), where the
    // streaming classifier must equal the batch one.
    let mut state: u64 = 0x9e3779b97f4a7c15;
    let mut next = || {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
        state >> 33
    };
    for _ in 0..400 {
        let mut bytes = Vec::new();
        let n = (next() as usize) % 64;
        for _ in 0..n {
            let b = next() as u8;
            // Bias toward OSC introducers and terminators to hit the parser.
            bytes.push(match b % 8 {
                0 => 0x1b,
                1 => b']',
                2 => b';',
                3 => 0x07,
                4 => b'1',
                5 => b'3',
                6 => b'D',
                _ => b,
            });
        }
        let whole = vec![out(&bytes)];
        let a = classify(40, 8, &whole, &Profile::common());
        let b = classify(40, 8, &whole, &Profile::common());
        assert_eq!(a, b, "classify must be deterministic on {bytes:?}");

        let mut split = Vec::new();
        let mut rest: &[u8] = &bytes;
        while !rest.is_empty() {
            let k = (next() as usize % 8).clamp(1, rest.len());
            split.push(out(&rest[..k]));
            rest = &rest[k..];
        }
        let batch = classify(40, 8, &split, &Profile::common());
        assert_eq!(
            stream(40, 8, &split),
            batch,
            "streaming must equal batch on the split {split:?}"
        );
    }
}

#[test]
fn streaming_classifier_matches_batch() {
    let cases: Vec<Vec<Record>> = vec![
        osc133_session(),
        vec![out(b"\x1b[2J\x1b[HPython 3.9\r\n"), out(b">>> ")],
        vec![out(b"\x1b[2J\x1b[Hjust some output text\r\n")],
        // Ends in a D mark (the settle point may precede it).
        vec![
            out(b"\x1b]133;A\x07$ "),
            out(b"\x1b]133;C\x07"),
            out(b"boom\r\n"),
            out(b"\x1b]133;D;127\x07"),
        ],
        // Ends in a C mark: a command still running at the settle.
        vec![
            out(b"\x1b]133;A\x07$ "),
            out(b"sleep 9\r\n"),
            out(b"\x1b]133;C\x07"),
        ],
        // A D mark split across two records.
        vec![
            out(b"\x1b]133;A\x07$ "),
            out(b"cmd\r\n"),
            out(b"\x1b]133;C\x07output\r\n\x1b]133;"),
            out(b"D;0\x07"),
        ],
        // Marks that repaint nothing (land after the settle point).
        vec![out(b"\x1b]133;D;0\x1b"), out(b"\\")],
        vec![out(b"boom\r\n"), out(b"\x1b]133;D;127\x07")],
        vec![out(b"\x1b[2J\x1b[H"), out(b"\x1b]133;A\x07\x1b[2J\x1b[H")],
        // A stalled progress line while a command runs.
        vec![
            out(b"\x1b[2J\x1b[H\x1b]133;A\x07$ "),
            out(b"curl big\r\n"),
            out(b"\x1b]133;C\x07"),
            out(b"\r####          45.0%"),
        ],
    ];
    for recs in cases {
        let batch = classify(80, 24, &recs, &Profile::common());
        assert_eq!(
            stream(80, 24, &recs),
            batch,
            "streaming must equal batch on {recs:?}"
        );
    }
}

#[test]
fn osc_mark_split_across_records_is_recognized() {
    // A `\x1b]133;D;0\x07` command-end mark split across two Out records (two PTY
    // reads): the introducer ends record 2, the letter+params begin record 3.
    let recs = vec![
        out(b"\x1b]133;A\x07$ "),
        out(b"cmd\r\n"),
        out(b"\x1b]133;C\x07output\r\n\x1b]133;"),
        out(b"D;0\x07"),
    ];
    let batch = classify(80, 24, &recs, &Profile::common());
    assert!(
        batch.contains(&SessionEvent::CommandEnd {
            offset: 3,
            exit: Some(0)
        }),
        "a split CommandEnd must be recognized (batch): {batch:?}"
    );
    // The streaming classifier recognises it too — and produces the same timeline.
    assert_eq!(stream(80, 24, &recs), batch);
}

#[test]
fn an_unterminated_mark_ends_at_the_next_escape_and_never_swallows_later_marks() {
    // `ESC` anywhere begins a new escape (the fold's parser, ECMA-48): a mark cut
    // off by one is abandoned, never extended to the next BEL/ST it finds. The
    // later, well-formed marks must all be recognised -- here in one record, and
    // with the unterminated mark carried across a record boundary.
    let expect = vec![('C', None), ('D', Some(1))];
    let one = vec![out(
        b"\x1b]133;A\x1b[0m$ \x1b]133;C\x07boom\r\n\x1b]133;D;1\x07",
    )];
    let batch = classify(80, 24, &one, &Profile::common());
    assert_eq!(marks(&batch), expect, "{batch:?}");
    assert_eq!(stream(80, 24, &one), batch);

    let split = vec![out(b"\x1b]133;A"), out(b"\x1b]133;C\x07\x1b]133;D;1\x07")];
    let batch = classify(80, 24, &split, &Profile::common());
    assert_eq!(marks(&batch), expect, "{batch:?}");
    assert_eq!(stream(80, 24, &split), batch);

    // An `ESC` as the last byte of a record may be the first half of a split ST,
    // so that mark waits for the next record instead of being abandoned.
    let st = vec![out(b"\x1b]133;D;0\x1b"), out(b"\\")];
    let batch = classify(80, 24, &st, &Profile::common());
    assert_eq!(marks(&batch), vec![('D', Some(0))], "{batch:?}");
}

#[test]
fn st_terminated_session_split_at_every_byte_boundary_streams_equal_batch() {
    let whole = st_terminated_session();
    let reference = classify(80, 24, &[out(&whole)], &Profile::common());
    let shape = marks(&reference);
    assert_eq!(
        shape,
        vec![('A', None), ('C', None), ('D', Some(0)), ('A', None)],
        "the unsplit session recognises all four marks: {reference:?}"
    );

    // Two records, the boundary at every byte — including inside `ESC ]`, the
    // code digits, the letter, and between the ST's ESC and `\`.
    for i in 0..=whole.len() {
        let recs = vec![out(&whole[..i]), out(&whole[i..])];
        let batch = classify(80, 24, &recs, &Profile::common());
        assert_eq!(stream(80, 24, &recs), batch, "split at byte {i}");
        assert_eq!(marks(&batch), shape, "every mark survives a split at {i}");
    }

    // Every boundary at once: one byte per record.
    let recs: Vec<Record> = whole.iter().map(|b| out(&[*b])).collect();
    let batch = classify(80, 24, &recs, &Profile::common());
    assert_eq!(stream(80, 24, &recs), batch, "one byte per record");
    assert_eq!(marks(&batch), shape);
}

// Bytes biased toward the OSC grammar (introducer, codes, letters, both
// terminators, prompt glyphs, line ends), with plain arbitrary bytes mixed in.
fn osc_biased_byte() -> impl Strategy<Value = u8> {
    prop_oneof![
        3 => prop::sample::select(vec![
            0x1bu8, b']', b';', 0x07, b'\\', b'1', b'3', b'6', b'A', b'C', b'D', b'0',
            b'$', b'%', b'>', b'\r', b'\n', b' ',
        ]),
        1 => any::<u8>(),
    ]
}

// What an integrated shell or a bare program actually emits: complete marks with
// either terminator (133 and 633), exit codes, prompts, output, clears, a title
// OSC, and the loose ESC / `\` halves of a split ST.
fn session_token() -> impl Strategy<Value = Vec<u8>> {
    prop_oneof![
        Just(b"\x1b]133;A\x07".to_vec()),
        Just(b"\x1b]133;A\x1b\\".to_vec()),
        Just(b"\x1b]133;C\x07".to_vec()),
        Just(b"\x1b]633;C\x1b\\".to_vec()),
        (0i32..256).prop_map(|e| format!("\x1b]133;D;{e}\x07").into_bytes()),
        Just(b"\x1b]133;D\x1b\\".to_vec()),
        Just(b"\x1b[2J\x1b[H".to_vec()),
        Just(b"$ ".to_vec()),
        Just(b"user@host % ".to_vec()),
        Just(b">>> ".to_vec()),
        Just(b"hi\r\n".to_vec()),
        Just(b"45.0%".to_vec()),
        Just(b"\x1b".to_vec()),
        Just(b"\\".to_vec()),
        Just(b"\x1b]0;title\x07".to_vec()),
        Just(Vec::new()),
    ]
}

// Chunk `whole` into Out records at the cut lengths (cycled).
fn chunk(whole: &[u8], cuts: &[usize]) -> Vec<Record> {
    let mut recs = Vec::new();
    let mut rest = whole;
    let mut i = 0;
    while !rest.is_empty() {
        let k = cuts[i % cuts.len()].min(rest.len());
        recs.push(out(&rest[..k]));
        rest = &rest[k..];
        i += 1;
    }
    if recs.is_empty() {
        recs.push(out(b""));
    }
    recs
}

proptest! {
    /// Over arbitrary chunked byte streams (a mark may straddle any chunk
    /// boundary), the streaming classifier equals the batch one, and both are
    /// deterministic and panic-free.
    #[test]
    fn streaming_equals_batch_over_arbitrary_chunked_bytes(
        chunks in prop::collection::vec(prop::collection::vec(osc_biased_byte(), 0..12), 1..8),
        cols in 1u16..16,
        rows in 1u16..6,
    ) {
        let recs: Vec<Record> = chunks.iter().map(|c| Record::Out(c.clone())).collect();
        let batch = classify(cols, rows, &recs, &Profile::common());
        prop_assert_eq!(&batch, &classify(cols, rows, &recs, &Profile::common()));
        prop_assert_eq!(stream(cols, rows, &recs), batch);
    }

    /// Over generated sessions of real shell-integration tokens, cut into records
    /// at arbitrary lengths — so marks straddle records, land on records that
    /// repaint nothing, and split between the ST's ESC and `\` — the streaming
    /// classifier equals the batch one.
    #[test]
    fn streaming_equals_batch_over_generated_sessions(
        tokens in prop::collection::vec(session_token(), 1..12),
        cuts in prop::collection::vec(1usize..6, 1..24),
        cols in 1u16..40,
        rows in 1u16..8,
    ) {
        let recs = chunk(&tokens.concat(), &cuts);
        let batch = classify(cols, rows, &recs, &Profile::common());
        prop_assert_eq!(stream(cols, rows, &recs), batch);
    }
}
