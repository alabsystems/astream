//! Run each claim's command and hash its output.
//!
//! A claim passes iff its command exits zero and, when an
//! `expected_output_sha` is pinned, its stdout hashes to that value. This is
//! how astream reports evidence: never a stored boolean, always a re-run.

use crate::manifest::{targo_subcommand, Claim};
use crate::timeout::{effective_claim_timeout_ms, run_command_with_timeout, BoundedCommandOutput};
use astream_digest::Sha256;
use std::path::Path;

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
    /// its stdout, so the failure can be diagnosed from the run's log.
    /// Empty for a pass or a skip.
    pub stdout_tail: String,
    /// The same tail of the failing command's stderr.
    pub stderr_tail: String,
}

/// Lines of each stream a failing claim keeps for the report.
pub const FAILURE_TAIL_LINES: usize = 60;

/// Byte cap on each kept tail, so one enormous line cannot flood the report.
pub const FAILURE_TAIL_BYTES: usize = 16 * 1024;

fn utf8_lossy_clean(bytes: &[u8]) -> String {
    if let Ok(s) = core::str::from_utf8(bytes) {
        return s.to_owned();
    }
    let mut out = String::new();
    for chunk in bytes.utf8_chunks() {
        out.push_str(chunk.valid());
        if !chunk.invalid().is_empty() {
            out.push('\u{FFFD}');
        }
    }
    out
}

/// The last `n` lines of `bytes` (a trailing newline does not count as a line),
/// at most [`FAILURE_TAIL_BYTES`] of them, decoded lossily.
pub fn tail_lines(bytes: &[u8], n: usize) -> String {
    let body = bytes.strip_suffix(b"\n").unwrap_or(bytes);
    // The last `n` lines start just past the n-th newline from the end.
    let start = match n.checked_sub(1) {
        None => body.len(),
        Some(k) => {
            let mut newlines = 0usize;
            let mut found = 0usize;
            let mut idx = body.len();
            while idx > 0 {
                idx -= 1;
                if matches!(body.get(idx), Some(b'\n')) {
                    if newlines == k {
                        found = idx.saturating_add(1);
                        break;
                    }
                    newlines = newlines.saturating_add(1);
                }
            }
            found
        }
    };
    let start = start.max(body.len().saturating_sub(FAILURE_TAIL_BYTES));
    utf8_lossy_clean(body.get(start..).unwrap_or(&[]))
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
/// `stdout`. Used to reject a `kind = "test"` claim, or any `targo <lane>
/// test` command, whose run counted **zero** tests (a vacuous filter that matches
/// nothing exits 0 and would otherwise be green theater).
pub fn count_passed_tests(stdout: &str) -> u64 {
    let mut total = 0u64;
    for line in stdout.lines() {
        // "test result: ok. 12 passed; 0 failed; ..."
        if let Some(rest) = line.split("test result:").nth(1) {
            let mut prev: Option<&str> = None;
            for tok in rest.split_whitespace() {
                if tok.starts_with("passed") {
                    if let Some(first) = prev {
                        if let Ok(n) = first.parse::<u64>() {
                            total = total.saturating_add(n);
                        }
                    }
                }
                prev = Some(tok);
            }
        }
    }
    total
}

/// Lowercase hex SHA-256 of `bytes`.
pub fn sha256_hex(bytes: &[u8]) -> String {
    const HEX: [char; 16] = [
        '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f',
    ];
    let digest = Sha256::digest_slice(bytes);
    let mut out = String::with_capacity(64);
    let mut rest = digest.as_slice();
    while let &[b, ref tail @ ..] = rest {
        out.push(HEX[((b >> 4) & 0xF) as usize]);
        out.push(HEX[(b & 0xF) as usize]);
        rest = tail;
    }
    out
}

/// Four-byte magic prefix (`"AECR"`) for a 20-byte runner claim report wire header.
pub const CLAIM_REPORT_WIRE_MAGIC: [u8; 4] = *b"AECR";

/// Wire format version for runner claim report wire headers.
pub const CLAIM_REPORT_WIRE_VERSION: u8 = 1;

/// Encode a 20-byte runner claim report wire header:
/// `[0..4] = b"AECR"`, `[4] = version (1)`, `[5] = passed (0/1)`, `[6] = skipped (0/1)`,
/// `[7] = kind_tag` (`0 = test`, `1 = bench`, `2 = cmd`),
/// `[8..12] = exit_code (BE)`, `[12..20] = passed_tests (BE)`.
#[must_use]
pub const fn encode_claim_report_wire(
    passed: bool,
    skipped: bool,
    kind_tag: u8,
    exit_code: u32,
    passed_tests: u64,
) -> Option<[u8; 20]> {
    let pass_tag = passed as u8;
    let skip_tag = skipped as u8;
    let out = [
        CLAIM_REPORT_WIRE_MAGIC[0],
        CLAIM_REPORT_WIRE_MAGIC[1],
        CLAIM_REPORT_WIRE_MAGIC[2],
        CLAIM_REPORT_WIRE_MAGIC[3],
        CLAIM_REPORT_WIRE_VERSION,
        pass_tag,
        skip_tag,
        kind_tag,
        ((exit_code >> 24) & 0xFF) as u8,
        ((exit_code >> 16) & 0xFF) as u8,
        ((exit_code >> 8) & 0xFF) as u8,
        (exit_code & 0xFF) as u8,
        ((passed_tests >> 56) & 0xFF) as u8,
        ((passed_tests >> 48) & 0xFF) as u8,
        ((passed_tests >> 40) & 0xFF) as u8,
        ((passed_tests >> 32) & 0xFF) as u8,
        ((passed_tests >> 24) & 0xFF) as u8,
        ((passed_tests >> 16) & 0xFF) as u8,
        ((passed_tests >> 8) & 0xFF) as u8,
        (passed_tests & 0xFF) as u8,
    ];
    if kind_tag > 2 || (passed && skipped) || (passed && exit_code != 0) {
        return None;
    }
    Some(out)
}

/// Decode a 20-byte runner claim report wire header into
/// `(passed, skipped, kind_tag, exit_code, passed_tests)`.
#[must_use]
pub const fn decode_claim_report_wire(buf: &[u8]) -> Option<(bool, bool, u8, u32, u64)> {
    let [b'A', b'E', b'C', b'R', CLAIM_REPORT_WIRE_VERSION, pass_tag, skip_tag, kind_tag, e0, e1, e2, e3, p0, p1, p2, p3, p4, p5, p6, p7, ..] =
        *buf
    else {
        return None;
    };
    let exit_code = ((e0 as u32) << 24) | ((e1 as u32) << 16) | ((e2 as u32) << 8) | (e3 as u32);
    let passed_tests = ((p0 as u64) << 56)
        | ((p1 as u64) << 48)
        | ((p2 as u64) << 40)
        | ((p3 as u64) << 32)
        | ((p4 as u64) << 24)
        | ((p5 as u64) << 16)
        | ((p6 as u64) << 8)
        | (p7 as u64);
    let passed = match pass_tag {
        0 => false,
        1 => true,
        _ => return None,
    };
    let skipped = match skip_tag {
        0 => false,
        1 => true,
        _ => return None,
    };
    if kind_tag > 2 || (passed && skipped) || (passed && exit_code != 0) {
        return None;
    };
    Some((passed, skipped, kind_tag, exit_code, passed_tests))
}

fn spawn_claim_once(
    root: &Path,
    command: &str,
    timeout_secs: Option<u64>,
) -> std::io::Result<BoundedCommandOutput> {
    let limit_ms = effective_claim_timeout_ms(timeout_secs, None);
    run_command_with_timeout(root, command, limit_ms)
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
    match spawn_claim_once(root, &c.command, c.timeout_secs) {
        Ok(output) => {
            let stdout = utf8_lossy_clean(&output.stdout);
            let stdout_sha = sha256_hex(&output.stdout);
            let status_ok = !output.timed_out && output.status.success();
            let sha_ok = match &c.expected_output_sha {
                Some(expected) => expected == &stdout_sha,
                None => true,
            };
            let mut note = String::new();
            if output.timed_out {
                note.push_str(&format!("command timed out after {} ms; ", output.limit_ms));
            } else if !status_ok {
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

            // A `kind = "test"` claim — and ANY `targo <lane> test` command, whatever
            // kind it is labelled — must actually run at least one test: a
            // filter that matches nothing exits 0 but exercises nothing, and
            // relabelling the kind must not buy an exemption.
            let mut tests_ok = true;
            let is_targo_test = targo_subcommand(&c.command) == Some("test");
            if (c.kind == "test" || is_targo_test) && status_ok && count_passed_tests(&stdout) == 0
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
                (
                    tail_lines(&output.stdout, FAILURE_TAIL_LINES),
                    tail_lines(&output.stderr, FAILURE_TAIL_LINES),
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
            timeout_secs: None,
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
    fn targo_test_running_zero_tests_fails_whatever_the_kind() {
        use std::os::unix::fs::PermissionsExt;
        // Relabelling a `targo <lane> test` claim as `selftest`/`build`/`bench`
        // must not exempt it from the zero-tests check: the command is what it
        // is. A fake `targo` on a private PATH prints the libtest summary a
        // vacuous filter produces, so no real build runs here.
        let dir = std::env::temp_dir().join(format!("astream-fake-targo-{}", std::process::id()));
        let _tmp = Cleanup(dir.clone());
        std::fs::create_dir_all(&dir).expect("temp dir");
        let fake = dir.join("targo");
        std::fs::write(
            &fake,
            "#!/bin/sh\nprintf 'test result: ok. 0 passed; 0 failed'\n",
        )
        .expect("fake targo");
        std::fs::set_permissions(&fake, std::fs::Permissions::from_mode(0o755)).expect("chmod");
        let cmd = format!("PATH={} targo --unverified test --lib zzz", dir.display());
        for kind in ["selftest", "build", "bench"] {
            let mut c = claim(kind, &cmd, None, None);
            c.expected_output_sha = Some(sha256_hex(b"test result: ok. 0 passed; 0 failed"));
            c.metric = Some("m".into());
            let r = run_claim(std::path::Path::new("."), &c);
            assert!(
                r.note.contains("ran zero tests"),
                "kind {kind:?}: a targo test that ran nothing must be noted: {}",
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

    #[cfg(unix)]
    #[test]
    fn benchmark_claim_keeps_its_first_attempt_and_failure_evidence() {
        let root = std::env::temp_dir().join(".ubd").join(format!(
            "astream-evidence-single-attempt-{}-{}.noindex",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&root).unwrap();
        let _cleanup = Cleanup(root.clone());
        for (metric, exit, min, max) in [
            (0, 0, Some(10.0), None),
            (0, 7, Some(10.0), None),
            (15, 7, Some(10.0), None),
            (25, 0, None, Some(20.0)),
        ] {
            let dir = root.join(format!("metric-{metric}-exit-{exit}"));
            std::fs::create_dir(&dir).unwrap();
            let command = format!(
                "if test -e attempt; then printf 2 > attempt; \
                 printf 'METRIC ops 15\\n'; printf later >&2; else \
                 printf 1 > attempt; printf 'METRIC ops {metric}\\n'; \
                 printf first >&2; exit {exit}; fi"
            );
            let mut c = claim("bench", &command, Some("ops"), min);
            c.max_value = max;
            let result = run_claim(&dir, &c);
            assert_eq!(
                std::fs::read_to_string(dir.join("attempt")).unwrap(),
                "1",
                "{result:?}"
            );
            assert!(!result.passed, "{result:?}");
            assert_eq!(result.exit_code, Some(exit));
            assert_eq!(result.metric_value, Some(f64::from(metric)));
            let stdout = format!("METRIC ops {metric}\n");
            assert_eq!(result.stdout_sha, sha256_hex(stdout.as_bytes()));
            assert_eq!(result.stdout_tail, stdout.trim_end());
            assert_eq!(result.stderr_tail, "first");
        }
        let mut control = claim(
            "bench",
            "printf 'METRIC ops 15\\n'",
            Some("ops"),
            Some(10.0),
        );
        control.max_value = Some(20.0);
        let result = run_claim(&root, &control);
        assert!(result.passed, "{result:?}");
        assert_eq!(result.metric_value, Some(15.0));
    }

    #[test]
    fn clean_origin_claim_timeout_kills_hung_claim_fail_closed() {
        let mut c = claim(
            "build",
            "printf 'before-hang\\n'; exec sleep 10",
            None,
            None,
        );
        c.timeout_secs = Some(1);
        let res = run_claim(&std::env::temp_dir(), &c);
        assert!(!res.passed);
        assert!(
            res.note.contains("command timed out after 1000 ms;"),
            "unexpected note: {}",
            res.note
        );
    }
}
