//! The bench re-measurement rule (`BENCH_ATTEMPTS` in `runner.rs`).
//!
//! A throughput floor is one-sided: contention can only make a measurement SLOWER, so a
//! single sample taken on a busy machine says the machine was busy, not that the code
//! regressed. The runner therefore re-measures a BENCH claim that missed its bound and
//! keeps the best sample. The whole question this file exists to answer is whether that
//! is a genuine estimator or a way to buy a green gate, so it pins BOTH halves:
//!
//! * a bench whose measurement varies (a busy machine) is allowed to reach its floor; and
//! * a bench that is genuinely below its floor on EVERY sample still FAILS.
//!
//! Every arm of the "best sample" rule is pinned by a fixture whose measurement VARIES,
//! because a fixture that reports one constant value cannot tell "kept the best" from
//! "kept the first" — a test that cannot fail is worse than no test, since it reads as
//! cover. So the ceiling arm gets a high-then-low fixture and the two-sided band arm gets
//! a three-sample one, and each asserts the `metric_value` the rule is supposed to select.
//!
//! The commands here are `sh` one-liners rather than real benchmarks, so the test costs
//! milliseconds and has no timing sensitivity of its own — a test about flakiness must
//! not itself be flaky.

use astream_evidence::manifest::Claim;
use astream_evidence::runner::run_claim;
use std::path::Path;

fn claim(id: &str, command: &str, min_value: Option<f64>, max_value: Option<f64>) -> Claim {
    Claim {
        id: id.to_string(),
        kind: "bench".to_string(),
        text: "fixture".to_string(),
        command: command.to_string(),
        expected_output_sha: None,
        metric: Some("m".to_string()),
        min_value,
        max_value,
        platform: None,
    }
}

/// A private directory for one test's marker files, emptied first so a crashed earlier run
/// cannot make a fixture non-deterministic. The marker files are what let an `sh` one-liner
/// report a DIFFERENT measurement on each attempt, which is the whole point: a constant
/// fixture cannot distinguish "kept the best sample" from "kept the first".
fn fixture_dir(name: &str) -> (Cleanup, std::path::PathBuf) {
    let dir = std::env::temp_dir().join(format!("asbench_{name}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let guard = Cleanup(dir.clone());
    std::fs::create_dir_all(&dir).unwrap();
    (guard, dir)
}

/// Removes a test's scratch directory when dropped, so the test leaves nothing behind
/// whether it passes or panics.
struct Cleanup(std::path::PathBuf);

impl Drop for Cleanup {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// A counter file makes "the machine was busy for the first sample" deterministic: the
/// command reports a low value on its first run and a high one afterwards, exactly the
/// shape of a bench that was contended once. Without the retry this claim fails.
#[test]
fn a_bench_that_misses_once_and_then_meets_its_floor_passes() {
    let dir = std::env::temp_dir().join(format!("asbench_slow_{}", std::process::id()));
    let _tmp = Cleanup(dir.clone());
    std::fs::create_dir_all(&dir).unwrap();
    let counter = dir.join("n");
    let _ = std::fs::remove_file(&counter);
    let cmd = format!(
        "if [ -f {c} ]; then echo 'METRIC m 500'; else touch {c}; echo 'METRIC m 10'; fi",
        c = counter.display()
    );

    let r = run_claim(
        Path::new("."),
        &claim("slow-first", &cmd, Some(100.0), None),
    );
    assert!(
        r.passed,
        "a bench that reached its floor on a later sample must pass: {}",
        r.note
    );
    assert_eq!(
        r.metric_value,
        Some(500.0),
        "the reported value must be the BEST sample, not the first"
    );
}

/// THE HALF THAT MATTERS. A genuine regression is below the floor on every sample, so
/// re-measuring must not rescue it. If this test ever passes, the retry has stopped being
/// an estimator and become a way to buy a green gate.
#[test]
fn a_bench_below_its_floor_on_every_sample_still_fails() {
    let r = run_claim(
        Path::new("."),
        &claim("always-slow", "echo 'METRIC m 10'", Some(100.0), None),
    );
    assert!(
        !r.passed,
        "a bench below its floor on every sample must FAIL — retrying is an estimator, \
         not an exemption: {}",
        r.note
    );
    assert!(
        r.note.contains("below floor"),
        "the failure must still name the floor it missed, got {:?}",
        r.note
    );
}

/// A ceiling runs the same way with the comparison inverted: "better" is LOWER, so the best
/// sample is the smallest one. The fixture reports a HIGH value first and a low one after —
/// the ceiling-side mirror of the floor fixture above — so this test fails if the ceiling
/// direction is ever lost: keeping the highest sample leaves the claim red at 900.
#[test]
fn a_ceiling_keeps_the_lowest_sample() {
    let (_tmp, dir) = fixture_dir("ceil_slow");
    let seen = dir.join("seen");
    let cmd = format!(
        "if [ -f {c} ]; then echo 'METRIC m 50'; else touch {c}; echo 'METRIC m 900'; fi",
        c = seen.display()
    );

    let r = run_claim(
        Path::new("."),
        &claim("high-first", &cmd, None, Some(100.0)),
    );
    assert!(
        r.passed,
        "a bench that came in under its ceiling on a later sample must pass: {}",
        r.note
    );
    assert_eq!(
        r.metric_value,
        Some(50.0),
        "under a ceiling the reported value must be the LOWEST sample, not the first"
    );
}

/// The ceiling's counterpart to the floor's half-that-matters: re-measuring must not rescue
/// a bench that is over its ceiling on every sample.
#[test]
fn a_ceiling_still_fails_when_every_sample_is_over() {
    let r = run_claim(
        Path::new("."),
        &claim("always-high", "echo 'METRIC m 900'", None, Some(100.0)),
    );
    assert!(
        !r.passed,
        "a bench above its ceiling on every sample must FAIL: {}",
        r.note
    );
    assert!(
        r.note.contains("above ceiling"),
        "the failure must still name the ceiling it exceeded, got {:?}",
        r.note
    );
}

/// A claim carrying BOTH bounds is satisfied only inside the band, and "better" means
/// nearer to the band from whichever side the sample missed on. That is not the same rule
/// as "higher": a sample that overshoots the CEILING is worse than one below the floor, and
/// an in-band sample beats both. The three samples here — below, far over, in band — are
/// the exact order that a floor-shaped comparison gets wrong, discarding a measurement the
/// machine demonstrably produced and reporting the claim red.
#[test]
fn a_band_keeps_the_in_band_sample_over_one_that_overshot_the_ceiling() {
    let (_tmp, dir) = fixture_dir("band_pass");
    let (a, b) = (dir.join("a"), dir.join("b"));
    let cmd = format!(
        "if [ ! -f {a} ]; then touch {a}; echo 'METRIC m 50'; \
         elif [ ! -f {b} ]; then touch {b}; echo 'METRIC m 500'; \
         else echo 'METRIC m 150'; fi",
        a = a.display(),
        b = b.display()
    );

    let r = run_claim(
        Path::new("."),
        &claim("band", &cmd, Some(100.0), Some(200.0)),
    );
    assert!(
        r.passed,
        "a band claim that measured an in-band sample must pass rather than report an \
         earlier sample that overshot the ceiling: {}",
        r.note
    );
    assert_eq!(
        r.metric_value,
        Some(150.0),
        "the reported value must be the in-band sample"
    );
}

/// And when a band claim misses on every sample it must still FAIL — reporting the sample
/// NEAREST the band, not the largest one. Samples 1000, 250, 5000 against 100..=200: the
/// honest answer is 250 over the ceiling, and a floor-shaped comparison answers 5000.
#[test]
fn a_band_that_misses_everywhere_fails_and_reports_the_nearest_sample() {
    let (_tmp, dir) = fixture_dir("band_fail");
    let (a, b) = (dir.join("a"), dir.join("b"));
    let cmd = format!(
        "if [ ! -f {a} ]; then touch {a}; echo 'METRIC m 1000'; \
         elif [ ! -f {b} ]; then touch {b}; echo 'METRIC m 250'; \
         else echo 'METRIC m 5000'; fi",
        a = a.display(),
        b = b.display()
    );

    let r = run_claim(
        Path::new("."),
        &claim("band-miss", &cmd, Some(100.0), Some(200.0)),
    );
    assert!(
        !r.passed,
        "no sample was in band, so this must FAIL: {}",
        r.note
    );
    assert_eq!(
        r.metric_value,
        Some(250.0),
        "a failing band claim must report the sample nearest the band, not the largest"
    );
    assert!(
        r.note.contains("above ceiling"),
        "the failure must name the bound the reported sample missed, got {:?}",
        r.note
    );
}

/// A bench that misses on every attempt reports the FINAL attempt's output (both streams),
/// so the failure can be diagnosed from the run log. All three samples are equal, so the
/// kept "best" sample stays the first one — the output must not come from it.
#[test]
fn a_bench_failing_every_attempt_reports_the_last_attempts_output() {
    let (_tmp, dir) = fixture_dir("tail_last");
    let (a, b) = (dir.join("a"), dir.join("b"));
    let cmd = format!(
        "if [ ! -f {a} ]; then touch {a}; n=1; elif [ ! -f {b} ]; then touch {b}; n=2; \
         else n=3; fi; echo \"attempt $n\"; echo \"attempt $n stderr\" >&2; echo 'METRIC m 10'",
        a = a.display(),
        b = b.display()
    );

    let r = run_claim(Path::new("."), &claim("tail-last", &cmd, Some(100.0), None));
    assert!(!r.passed, "below the floor on every attempt: {}", r.note);
    assert!(
        r.stdout_tail.contains("attempt 3") && !r.stdout_tail.contains("attempt 1"),
        "the last attempt's stdout, got {:?}",
        r.stdout_tail
    );
    assert_eq!(r.stderr_tail, "attempt 3 stderr");
}

/// A missing metric is a loud failure, and no amount of re-measuring may turn it into a
/// quiet one — a bench that prints nothing is a bench that guards nothing.
#[test]
fn a_bench_printing_no_metric_still_fails_after_every_attempt() {
    let r = run_claim(
        Path::new("."),
        &claim("no-metric", "echo 'nothing here'", Some(100.0), None),
    );
    assert!(!r.passed, "a bench with no metric must FAIL: {}", r.note);
    assert!(
        r.note.contains("not found"),
        "the failure must say the metric was missing, got {:?}",
        r.note
    );
}

/// A `test` claim is not a measurement, so it must run EXACTLY ONCE: retrying one would
/// hide a flaky test, and this project would rather see the flake. The counter file makes
/// a second invocation observable — if the runner retried, the claim would go green.
#[test]
fn a_failing_test_claim_is_never_re_run() {
    let dir = std::env::temp_dir().join(format!("asbench_test_{}", std::process::id()));
    let _tmp = Cleanup(dir.clone());
    std::fs::create_dir_all(&dir).unwrap();
    let counter = dir.join("n");
    let _ = std::fs::remove_file(&counter);
    // Fails the first time, would succeed on any retry.
    let cmd = format!(
        "if [ -f {c} ]; then exit 0; else touch {c}; exit 1; fi",
        c = counter.display()
    );
    let mut c = claim("test-once", &cmd, None, None);
    c.kind = "test".to_string();
    c.metric = None;

    let r = run_claim(Path::new("."), &c);
    assert!(
        !r.passed,
        "a failing test claim must stay failed — retrying a test hides a flake: {}",
        r.note
    );
}
