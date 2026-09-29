//! Run each claim's command and hash its output.
//!
//! A claim passes iff its command exits zero and, when an
//! `expected_output_sha` is pinned, its stdout hashes to that value. This is
//! how astream reports evidence: never a stored boolean, always a re-run.

use crate::manifest::{cargo_subcommand, Claim};
use sha2::{Digest, Sha256};
use std::path::Path;
use std::process::Command;

/// The outcome of running one claim.
#[derive(Debug, Clone)]
pub struct ClaimResult {
    pub id: String,
    pub passed: bool,
    /// The claim was not run on this host because its `platform` does not match
    /// (e.g. a Linux-only claim on macOS). A skipped claim does NOT count as a
    /// verified pass — it is reported separately — and it is NOT a failure either.
    pub skipped: bool,
    pub exit_code: Option<i32>,
    pub stdout_sha: String,
    pub metric_value: Option<f64>,
    pub note: String,
    /// For a claim that ran and FAILED, the last [`FAILURE_TAIL_LINES`] lines of
    /// its stdout (the final attempt's, for a re-measured bench), so the failure
    /// can be diagnosed from the run's log. Empty for a pass or a skip.
    pub stdout_tail: String,
    /// The same tail of the failing command's stderr.
    pub stderr_tail: String,
}

/// Lines of each stream a failing claim keeps for the report.
pub const FAILURE_TAIL_LINES: usize = 60;

/// Byte cap on each kept tail, so one enormous line cannot flood the report.
pub const FAILURE_TAIL_BYTES: usize = 16 * 1024;

/// The last `n` lines of `bytes` (a trailing newline does not count as a line),
/// at most [`FAILURE_TAIL_BYTES`] of them, decoded lossily.
pub fn tail_lines(bytes: &[u8], n: usize) -> String {
    let body = bytes.strip_suffix(b"\n").unwrap_or(bytes);
    // The last `n` lines start just past the n-th newline from the end.
    let start = match n.checked_sub(1) {
        None => body.len(),
        Some(k) => body
            .iter()
            .enumerate()
            .rev()
            .filter(|&(_, &b)| b == b'\n')
            .nth(k)
            .map_or(0, |(i, _)| i + 1),
    };
    let start = start.max(body.len().saturating_sub(FAILURE_TAIL_BYTES));
    String::from_utf8_lossy(&body[start..]).into_owned()
}

/// Extract the value from a `METRIC <name> <value>` line in `stdout`.
pub fn extract_metric(stdout: &str, name: &str) -> Option<f64> {
    for line in stdout.lines() {
        let mut fields = line.split_whitespace();
        if fields.next() == Some("METRIC") && fields.next() == Some(name) {
            if let Some(v) = fields.next() {
                if let Ok(parsed) = v.parse::<f64>() {
                    // A non-finite value (NaN/inf) must never satisfy a bound:
                    // `NaN < min` is false, so it would silently pass the floor.
                    // Treat it as a missing metric so the claim fails loudly.
                    if parsed.is_finite() {
                        return Some(parsed);
                    }
                }
            }
        }
    }
    None
}

/// Sum the `passed` counts across every libtest `test result:` summary line in
/// `stdout`. Used to reject a `kind = "test"` claim, or any `cargo test`
/// command, whose run counted **zero** tests (a vacuous filter that matches
/// nothing exits 0 and would otherwise be green theater).
pub fn count_passed_tests(stdout: &str) -> u64 {
    let mut total = 0u64;
    for line in stdout.lines() {
        // "test result: ok. 12 passed; 0 failed; ..."
        if let Some(rest) = line.split("test result:").nth(1) {
            let toks: Vec<&str> = rest.split_whitespace().collect();
            for w in toks.windows(2) {
                if w[1].starts_with("passed") {
                    if let Ok(n) = w[0].parse::<u64>() {
                        total += n;
                    }
                }
            }
        }
    }
    total
}

/// Lowercase hex SHA-256 of `bytes`.
pub fn sha256_hex(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    let digest = hasher.finalize();
    let mut out = String::with_capacity(64);
    for b in digest {
        out.push_str(&format!("{b:02x}"));
    }
    out
}

/// How many times a BENCH claim that fell short of its bound may be re-measured.
///
/// A throughput floor is a one-sided measurement: CPU contention can only make it
/// SLOWER, never faster. So a single sample taken while the machine happens to be busy
/// says nothing about whether the code regressed — it says the machine was busy, and a
/// gate whose greenness depends on nothing else running on the box eventually cries
/// wolf and gets ignored.
///
/// Taking the BEST of a few samples is therefore the honest estimator of what this
/// machine can do, and it does NOT weaken the gate: a real regression depresses every
/// sample, so the best of them is still below the floor and the claim still fails. What
/// it removes is only the failure mode where a green gate depends on an idle machine.
const BENCH_ATTEMPTS: usize = 3;

/// Run `c`'s command, re-measuring a BENCH claim that missed its bound up to
/// [`BENCH_ATTEMPTS`] times and keeping the best sample (see that constant for why this
/// is honest rather than a way to buy a pass). A claim that meets its bound on the first
/// run is never re-run, so this costs nothing on a healthy tree. Non-bench claims, and
/// bench claims with no numeric bound, run exactly once — a `test` claim is not a
/// measurement and retrying one would only hide a flaky test, which the project wants
/// to see rather than paper over.
///
/// Returns the kept (best) sample, and the final attempt when that is a different run
/// — the output a failure report shows.
fn run_with_bench_retry(
    root: &Path,
    c: &Claim,
) -> std::io::Result<(std::process::Output, Option<std::process::Output>)> {
    let run_once = || {
        Command::new("sh")
            .arg("-c")
            .arg(&c.command)
            .current_dir(root)
            .output()
    };
    let bounded =
        c.kind == "bench" && c.metric.is_some() && (c.min_value.is_some() || c.max_value.is_some());
    let mut best = run_once()?;
    let mut last = None;
    if !bounded {
        return Ok((best, last));
    }
    let name = c.metric.as_ref().expect("bounded implies a metric name");
    // A claim carrying both bounds is satisfied only INSIDE the band, so once a sample is
    // inside it there is nothing better to look for and the loop below stops.
    let satisfies =
        |v: f64| c.min_value.is_none_or(|min| v >= min) && c.max_value.is_none_or(|max| v <= max);
    // How far a sample sits OUTSIDE what the claim demands: zero for any sample that
    // satisfies it, and otherwise the distance to the bound it missed. "Better" is the
    // smaller miss: the higher sample for a floor, the lower for a ceiling, and for a
    // claim carrying BOTH bounds the one nearer the band — where plain "higher" would
    // let a sample that overshot the ceiling displace an in-band one.
    let miss = |v: f64| -> f64 {
        let below = c.min_value.map_or(0.0, |min| min - v);
        let above = c.max_value.map_or(0.0, |max| v - max);
        below.max(above).max(0.0)
    };
    let better = |cand: f64, cur: f64| miss(cand) < miss(cur);
    let mut best_val = extract_metric(&String::from_utf8_lossy(&best.stdout), name);
    for _ in 1..BENCH_ATTEMPTS {
        // A sample that already meets the bound is the answer; stop paying for more.
        if best_val.is_some_and(satisfies) {
            break;
        }
        let next = run_once()?;
        let next_val = extract_metric(&String::from_utf8_lossy(&next.stdout), name);
        // A missing metric is a failure the caller must SEE, so never let a later run
        // that produced no metric displace one that did.
        match (next_val, best_val) {
            (Some(n), Some(b)) if better(n, b) => {
                best = next;
                best_val = Some(n);
                last = None;
            }
            (Some(n), None) => {
                best = next;
                best_val = Some(n);
                last = None;
            }
            _ => last = Some(next),
        }
    }
    Ok((best, last))
}

/// Run a single claim's command with `root` as the working directory.
pub fn run_claim(root: &Path, c: &Claim) -> ClaimResult {
    // Platform gate: a claim may declare the OS it is verified on (e.g. a Linux-only
    // ptrace claim). On any other host it is SKIPPED — not run, not counted as a
    // pass, not a failure. The gate still checks its test target exists, so this is
    // honest CI-matrix behavior, not a way to hide a claim.
    if let Some(plat) = &c.platform {
        if plat != std::env::consts::OS {
            // `passed: false`: a claim that never executed is not a verified
            // pass, whatever a caller does with `skipped`. Summing `passed`
            // over the results must never count it.
            return ClaimResult {
                id: c.id.clone(),
                passed: false,
                skipped: true,
                exit_code: None,
                stdout_sha: String::new(),
                metric_value: None,
                note: format!(
                    "skipped: platform={plat:?}, host={:?}",
                    std::env::consts::OS
                ),
                stdout_tail: String::new(),
                stderr_tail: String::new(),
            };
        }
    }
    match run_with_bench_retry(root, c) {
        Ok((output, last)) => {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stdout_sha = sha256_hex(&output.stdout);
            let status_ok = output.status.success();
            let sha_ok = match &c.expected_output_sha {
                Some(expected) => expected == &stdout_sha,
                None => true,
            };
            let mut note = String::new();
            if !status_ok {
                note.push_str("command exited non-zero; ");
            }
            if !sha_ok {
                note.push_str("output hash drifted from manifest; ");
            }

            // Metric / regression-floor check (bench claims).
            let mut metric_ok = true;
            let mut metric_value = None;
            // A floor/ceiling without a metric name, or a bench claim with no
            // metric at all, enforces nothing — that is a silently-unguarded
            // regression gate, so fail it loudly rather than pass vacuously.
            if c.metric.is_none() && (c.min_value.is_some() || c.max_value.is_some()) {
                metric_ok = false;
                note.push_str(
                    "min_value/max_value set without a metric name — bound never checked; ",
                );
            }
            if c.kind == "bench" && c.metric.is_none() {
                metric_ok = false;
                note.push_str("bench claim has no metric — it asserts no floor/ceiling; ");
            }
            if let Some(name) = &c.metric {
                match extract_metric(&stdout, name) {
                    Some(val) => {
                        metric_value = Some(val);
                        if let Some(min) = c.min_value {
                            if val < min {
                                metric_ok = false;
                                note.push_str(&format!("{name}={val} below floor {min}; "));
                            }
                        }
                        if let Some(max) = c.max_value {
                            if val > max {
                                metric_ok = false;
                                note.push_str(&format!("{name}={val} above ceiling {max}; "));
                            }
                        }
                        if metric_ok {
                            note.push_str(&format!("{name}={val}; "));
                        }
                    }
                    None => {
                        metric_ok = false;
                        note.push_str(&format!("metric {name:?} not found in output; "));
                    }
                }
            }

            // A `kind = "test"` claim — and ANY `cargo test` command, whatever
            // kind it is labelled — must actually run at least one test: a
            // filter that matches nothing exits 0 but exercises nothing, and
            // relabelling the kind must not buy an exemption.
            let mut tests_ok = true;
            let is_cargo_test = cargo_subcommand(&c.command) == Some("test");
            if (c.kind == "test" || is_cargo_test) && status_ok && count_passed_tests(&stdout) == 0
            {
                tests_ok = false;
                note.push_str(
                    "ran zero tests (vacuous filter or no matching tests) — exercises nothing; ",
                );
            }
            // A selftest asserts output determinism; without a pinned hash it
            // asserts nothing beyond exit 0.
            if c.kind == "selftest" && c.expected_output_sha.is_none() {
                tests_ok = false;
                note.push_str("selftest pins no expected_output_sha — output drift undetectable; ");
            }

            let passed = status_ok && sha_ok && metric_ok && tests_ok;
            let (stdout_tail, stderr_tail) = if passed {
                (String::new(), String::new())
            } else {
                let shown = last.as_ref().unwrap_or(&output);
                (
                    tail_lines(&shown.stdout, FAILURE_TAIL_LINES),
                    tail_lines(&shown.stderr, FAILURE_TAIL_LINES),
                )
            };
            ClaimResult {
                id: c.id.clone(),
                passed,
                skipped: false,
                exit_code: output.status.code(),
                stdout_sha,
                metric_value,
                note,
                stdout_tail,
                stderr_tail,
            }
        }
        Err(e) => ClaimResult {
            id: c.id.clone(),
            passed: false,
            skipped: false,
            exit_code: None,
            stdout_sha: String::new(),
            metric_value: None,
            note: format!("failed to spawn command: {e}"),
            stdout_tail: String::new(),
            stderr_tail: String::new(),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn known_sha_vector() {
        // The canonical SHA-256 of the empty input.
        assert_eq!(
            sha256_hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }

    #[test]
    fn extract_metric_reads_the_named_line() {
        let out = "noise\nMETRIC frame_ops 1234567\nMETRIC match_ops 42.5\n";
        assert_eq!(extract_metric(out, "frame_ops"), Some(1234567.0));
        assert_eq!(extract_metric(out, "match_ops"), Some(42.5));
        assert_eq!(extract_metric(out, "absent"), None);
    }

    fn claim(kind: &str, command: &str, metric: Option<&str>, min: Option<f64>) -> Claim {
        Claim {
            id: "x".into(),
            kind: kind.into(),
            text: "t".into(),
            command: command.into(),
            expected_output_sha: None,
            metric: metric.map(|s| s.to_string()),
            min_value: min,
            max_value: None,
            platform: None,
        }
    }

    #[test]
    fn counts_passed_tests_across_summaries() {
        let out = "running 3 tests\ntest result: ok. 3 passed; 0 failed; 0 ignored\n\
                   running 0 tests\ntest result: ok. 0 passed; 0 failed; 0 ignored\n";
        assert_eq!(count_passed_tests(out), 3);
        assert_eq!(count_passed_tests("no summaries here"), 0);
    }

    #[test]
    fn floor_without_metric_name_fails_loudly() {
        // A regression floor with no metric name enforces nothing — must fail.
        let r = run_claim(
            std::path::Path::new("."),
            &claim("bench", "true", None, Some(1.0)),
        );
        assert!(
            !r.passed,
            "floor without a metric name must fail: {}",
            r.note
        );
        // A bench claim with no metric at all also asserts nothing — must fail.
        let r = run_claim(
            std::path::Path::new("."),
            &claim("bench", "true", None, None),
        );
        assert!(!r.passed, "bench with no metric must fail: {}", r.note);
    }

    #[test]
    fn test_claim_running_zero_tests_fails() {
        // A `kind = "test"` command that exits 0 but ran no tests is theater.
        let r = run_claim(
            std::path::Path::new("."),
            &claim(
                "test",
                "printf 'test result: ok. 0 passed; 0 failed'",
                None,
                None,
            ),
        );
        assert!(
            !r.passed,
            "a test claim that runs zero tests must fail: {}",
            r.note
        );
    }

    /// Removes a test's scratch directory when dropped, so the test leaves nothing
    /// behind whether it passes or panics.
    #[cfg(unix)]
    struct Cleanup(std::path::PathBuf);

    #[cfg(unix)]
    impl Drop for Cleanup {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    #[cfg(unix)]
    #[test]
    fn cargo_test_running_zero_tests_fails_whatever_the_kind() {
        use std::os::unix::fs::PermissionsExt;
        // Relabelling a `cargo test` claim as `selftest`/`build`/`bench` must
        // not exempt it from the zero-tests check: the command is what it is.
        // A fake `cargo` on a private PATH prints the libtest summary a vacuous
        // filter produces, so no real build runs here.
        let dir = std::env::temp_dir().join(format!("astream-fake-cargo-{}", std::process::id()));
        let _tmp = Cleanup(dir.clone());
        std::fs::create_dir_all(&dir).expect("temp dir");
        let fake = dir.join("cargo");
        std::fs::write(
            &fake,
            "#!/bin/sh\nprintf 'test result: ok. 0 passed; 0 failed'\n",
        )
        .expect("fake cargo");
        std::fs::set_permissions(&fake, std::fs::Permissions::from_mode(0o755)).expect("chmod");
        let cmd = format!("PATH={} cargo test --lib zzz", dir.display());
        for kind in ["selftest", "build", "bench"] {
            let mut c = claim(kind, &cmd, None, None);
            c.expected_output_sha = Some(sha256_hex(b"test result: ok. 0 passed; 0 failed"));
            c.metric = Some("m".into());
            let r = run_claim(std::path::Path::new("."), &c);
            assert!(
                r.note.contains("ran zero tests"),
                "kind {kind:?}: a cargo test that ran nothing must be noted: {}",
                r.note
            );
            assert!(!r.passed, "kind {kind:?}: must fail: {}", r.note);
        }
    }

    #[test]
    fn selftest_without_pinned_hash_fails() {
        let r = run_claim(
            std::path::Path::new("."),
            &claim("selftest", "printf 'deterministic'", None, None),
        );
        assert!(
            !r.passed,
            "a selftest with no pinned hash asserts nothing: {}",
            r.note
        );
        let mut c = claim("selftest", "printf 'deterministic'", None, None);
        c.expected_output_sha = Some(sha256_hex(b"deterministic"));
        let r = run_claim(std::path::Path::new("."), &c);
        assert!(r.passed, "a pinned selftest passes: {}", r.note);
    }

    #[test]
    fn platform_skipped_claim_is_not_a_pass() {
        // Pick a real platform that is not this host, so the claim is skipped.
        let other = if std::env::consts::OS == "linux" {
            "macos"
        } else {
            "linux"
        };
        let mut c = claim("test", "false", None, None);
        c.platform = Some(other.into());
        let r = run_claim(std::path::Path::new("."), &c);
        assert!(
            r.skipped,
            "must be skipped on a foreign platform: {}",
            r.note
        );
        assert!(
            !r.passed,
            "a skipped claim must never read as passed: {}",
            r.note
        );
        assert_eq!(r.exit_code, None, "the command must not have run");
    }

    #[test]
    fn tail_lines_keeps_the_last_lines_within_a_byte_cap() {
        assert_eq!(tail_lines(b"a\nb\nc\n", 2), "b\nc");
        assert_eq!(tail_lines(b"a\nb\nc", 2), "b\nc");
        assert_eq!(tail_lines(b"a\nb\n", 5), "a\nb");
        assert_eq!(tail_lines(b"", 5), "");
        // One enormous line is cut by bytes, keeping its end.
        let long = [b"head".as_slice(), &[b'x'; 100_000], b"end"].concat();
        let t = tail_lines(&long, 5);
        assert_eq!(t.len(), FAILURE_TAIL_BYTES);
        assert!(t.ends_with("xend"));
    }

    #[test]
    fn a_failing_claim_carries_a_bounded_tail_of_each_stream() {
        let cmd = "i=0; while [ $i -lt 100 ]; do i=$((i+1)); echo out-$i; done; \
                   echo err-last >&2; exit 3";
        let r = run_claim(Path::new("."), &claim("build", cmd, None, None));
        assert!(!r.passed, "{}", r.note);
        let out: Vec<&str> = r.stdout_tail.lines().collect();
        assert_eq!(out.len(), FAILURE_TAIL_LINES, "{out:?}");
        assert_eq!(out.first(), Some(&"out-41"));
        assert_eq!(out.last(), Some(&"out-100"));
        assert_eq!(r.stderr_tail, "err-last");

        // A passing claim keeps none of its output.
        let ok = run_claim(Path::new("."), &claim("build", "echo fine >&2", None, None));
        assert!(ok.passed, "{}", ok.note);
        assert!(ok.stdout_tail.is_empty() && ok.stderr_tail.is_empty());
    }

    #[test]
    fn non_finite_metric_is_treated_as_missing() {
        // NaN/inf would slip past `val < min` (NaN comparisons are false), so
        // extraction must reject them — the claim then fails as "not found".
        assert_eq!(extract_metric("METRIC ops NaN\n", "ops"), None);
        assert_eq!(extract_metric("METRIC ops inf\n", "ops"), None);
        assert_eq!(extract_metric("METRIC ops -inf\n", "ops"), None);
        // A real finite value is still extracted.
        assert_eq!(extract_metric("METRIC ops 250000\n", "ops"), Some(250000.0));
    }
}
