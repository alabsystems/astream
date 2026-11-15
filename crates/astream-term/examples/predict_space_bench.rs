//! Public positional-verdict controls. Predictor/grid/pending setup and final
//! screen/hash verification are outside timing; retirement result creation is timed.
use astream_term::{render::frame_hash, Folder, Predictor, Record, Verdict};
use std::hint::black_box;
use std::time::Instant;

fn fixture(case: &str, width: u16) -> (Predictor, Record, usize, Verdict) {
    let mut p = Predictor::new(width, 4);
    let w = width as usize;
    let mut input;
    let mut echo;
    let (count, expected) = match case {
        "lost_spaces" => {
            input = vec![b' '; w];
            echo = Vec::new();
            (w, Verdict::Lost)
        }
        "lost_multirow" => {
            input = vec![b' '; w * 3];
            echo = Vec::new();
            (w * 3, Verdict::Lost)
        }
        "redraw_spaces" => {
            input = vec![b' '; w - 1];
            echo = input.clone();
            echo.extend_from_slice(b"X\r");
            (w - 1, Verdict::Confirmed)
        }
        "cursor_spaces" => {
            input = vec![b' '; w - 1];
            echo = input.clone();
            (w - 1, Verdict::Confirmed)
        }
        "ordinary" => {
            input = vec![b'x'; w - 1];
            echo = input.clone();
            echo.push(b'\r');
            (w - 1, Verdict::Confirmed)
        }
        "wide" => {
            input = vec![b' '; w - 4];
            echo = input.clone();
            echo.extend_from_slice("界\r".as_bytes());
            (w - 4, Verdict::Confirmed)
        }
        "combining" => {
            input = vec![b' '; w - 2];
            echo = input.clone();
            echo.extend_from_slice("e\u{301}\r".as_bytes());
            (w - 2, Verdict::Confirmed)
        }
        "trim_spaces" => {
            input = vec![b' '; w - 2];
            echo = input.clone();
            echo.extend_from_slice(b"X \r");
            (w - 2, Verdict::Confirmed)
        }
        "one_glyph" => {
            input = vec![b'x'];
            echo = input.clone();
            (1, Verdict::Confirmed)
        }
        "causal" => {
            input = vec![b' '; 8];
            echo = input.clone();
            (1, Verdict::Confirmed)
        }
        _ => panic!("unknown fixture"),
    };
    if case == "causal" {
        assert!(p.predict_at(7, 9, &input));
    } else {
        assert!(p.predict(7, &input));
    }
    // Keep input ownership out of the measured operation, just as a real caller
    // has already enqueued its prediction before an output/reconcile arrives.
    input.clear();
    (p, Record::Out(echo), count, expected)
}
fn operation(p: &mut Predictor, case: &str, record: &Record) -> Vec<(u64, Verdict)> {
    if case.starts_with("lost_") {
        p.reconcile()
    } else if case == "causal" {
        p.apply_output_caused(1, Some(9), record)
    } else {
        p.apply_output_at(1, record)
    }
}
fn measure(case: &str, width: u16) {
    let rounds = if width >= 1000 { 16 } else { 64 };
    let mut times = [0u128; 3];
    let mut expected_digest = None;
    for ns in &mut times {
        let mut predictors: Vec<_> = (0..rounds).map(|_| fixture(case, width).0).collect();
        let (_, record, count, expected) = fixture(case, width);
        let mut results = Vec::with_capacity(rounds);
        let start = Instant::now();
        for p in &mut predictors {
            results.push(black_box(operation(p, case, black_box(&record))));
        }
        *ns = start.elapsed().as_nanos() / rounds as u128;
        let mut folded = Folder::new(width, 4);
        if !case.starts_with("lost_") {
            folded.apply(&record);
        }
        let screen = folded.into_screen();
        let hash = frame_hash(&screen);
        for (p, result) in predictors.iter().zip(&results) {
            assert_eq!(p.authoritative(), &screen);
            assert_eq!(result.len(), count);
            assert!(result
                .iter()
                .all(|&(seq, verdict)| seq == 7 && verdict == expected));
        }
        let digest = (hash, count, expected);
        if let Some(old) = &expected_digest {
            assert_eq!(old, &digest);
        } else {
            expected_digest = Some(digest);
        }
    }
    times.sort_unstable();
    let (hash, count, expected) = expected_digest.unwrap();
    println!("PREDICT_SPACE case={case} width={width} rows=4 rounds={rounds} ns={} verdicts={count} verdict={expected:?} hash={hash}", times[1]);
}
fn main() {
    for width in [80u16, 120, 240, 1000] {
        for case in [
            "lost_spaces",
            "lost_multirow",
            "redraw_spaces",
            "cursor_spaces",
            "ordinary",
            "wide",
            "combining",
            "trim_spaces",
            "one_glyph",
            "causal",
        ] {
            measure(case, width);
        }
    }
}
