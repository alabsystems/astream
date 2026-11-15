// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Keep the READY gate observable inside the publisher's isolated public clone.

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

struct Cleanup(PathBuf);

impl Drop for Cleanup {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

struct Run {
    output: Output,
    compiler_target: String,
    expected_target: String,
    report_exists: bool,
    used_default_target: bool,
    admissions: Vec<String>,
    preserved_foreign_payload: bool,
}

fn executable(path: &Path, body: &str) {
    fs::write(path, body).expect("write test executable");
    fs::set_permissions(path, fs::Permissions::from_mode(0o755))
        .expect("make test executable runnable");
}

fn wire_floor(script_src: &str) -> u64 {
    script_src
        .lines()
        .find_map(|line| {
            let trimmed = line.trim().trim_matches('"');
            let rest = trimmed.strip_prefix("astream-wire|")?;
            let (floor, _) = rest.split_once('|')?;
            floor.parse::<u64>().ok()
        })
        .expect("astream-wire floor in scripts/verify-ready.sh")
}

fn run(mode: &str, explicit_output: bool) -> (Run, u64, u64) {
    let root = std::env::temp_dir().join(format!(
        "astream-verify-ready-{mode}-{explicit_output}-{}",
        std::process::id()
    ));
    fs::create_dir(&root).expect("exclusive scratch directory");
    let _cleanup = Cleanup(root.clone());
    let bin = root.join("bin");
    fs::create_dir(&bin).expect("test PATH directory");
    fs::create_dir(root.join("scripts")).expect("test scripts directory");
    let script_src = include_str!("../../../../scripts/verify-ready.sh");
    let floor = wire_floor(script_src);
    let proved = floor + 52;
    let total = proved + 100;
    let script = root.join("scripts/verify-ready.sh");
    fs::write(&script, script_src).expect("copy real READY script");
    executable(
        &bin.join("targo"),
        &format!(
            r#"#!/bin/sh
set -eu
if [ "$1" = --unverified ]; then
    printf '%s\n' 'targo fixture (targo 0.1.0)'
    exit 0
fi
printf '%s\n' "$CARGO_TARGET_DIR" >"$ASTREAM_TEST_TARGET"
# Simulate the installed driver's admission boundary, not its ownership schema.
# The script may create report directories but must leave compiler custody alone.
if [ -n "${{CARGO_BUILD_BUILD_DIR+x}}${{TARGO_BUILD_BUILD_DIR+x}}" ]; then
    printf '%s\n' 'inherited native intermediates must not reach READY'
    exit 76
fi
if [ -e "$CARGO_TARGET_DIR" ] || [ -L "$CARGO_TARGET_DIR" ]; then
    if [ ! -f "$CARGO_TARGET_DIR/.fixture-admitted-target" ]; then
        printf '%s\n' refused >>"$ASTREAM_TEST_ADMISSIONS"
        printf '%s\n' 'explicit build target is unmanaged or unsupported'
        exit 75
    fi
    printf '%s\n' reused >>"$ASTREAM_TEST_ADMISSIONS"
else
    mkdir -m 700 "$CARGO_TARGET_DIR"
    printf '%s\n' 'fixture only, not atpkg metadata' >"$CARGO_TARGET_DIR/.fixture-admitted-target"
    printf '%s\n' created >>"$ASTREAM_TEST_ADMISSIONS"
fi
while [ "$1" != --report-dir ]; do shift; done
mkdir -p "$2"
printf '%s\n' '{{"verification_gate":{{"counts":{{"total":{total},"proved":{proved},"failed":0,"unknown":100,"runtime_checked":0,"assumed":0,"mandated":0,"contract_panics":0}},"decision":"conditional-pass","exit_code":0,"coverage":{{"eligible":1,"processed":1,"coverage_complete":true}}}}}}' >"$2/report.json"
printf '%s\n' 'fixture compiler diagnostic'
case "$ASTREAM_TEST_MODE" in
    missing) printf '%s\n' 'compiler finished without its census' ;;
    malformed) printf '%s\n' 'Gate: unreadable result' ;;
    *) printf '%s\n' 'Gate: CONDITIONAL-PASS [advisory lane, exit 0] ({proved} proved, 0 failed, 0 runtime-checked, 0 assumed, 0 mandated, 0 contract-panic, 100 unknown / {total} total)' ;;
esac
"#
        ),
    );
    // The parser is unchanged; these tests exercise artifact placement and log
    // transport without depending on a system jq or invoking a real compiler.
    executable(
        &bin.join("jq"),
        &format!(
            r#"#!/bin/sh
set -eu
case "$1" in
    -e) exit 0 ;;
    -r) printf '{total}\t{proved}\t0\t100\t0\t0\t0\t0\tconditional-pass\t0\ttrue\n' ;;
    *) exit 98 ;;
esac
"#
        ),
    );
    let target = root.join("publisher artifacts");
    let out = if explicit_output {
        root.join("explicit reports")
    } else {
        target.join("trust-ready")
    };
    let build = PathBuf::from(format!("{}.target.noindex", out.display()));
    if mode == "unmanaged" {
        fs::create_dir_all(&build).expect("caller-precreated unmanaged target");
        fs::write(build.join("foreign"), b"must survive refusal").unwrap();
    }
    let trace = root.join("compiler-target");
    let admissions = root.join("admissions");
    let mut command = Command::new("/bin/bash");
    command
        .arg(&script)
        .arg("astream-wire")
        .env("PATH", format!("{}:/usr/bin:/bin", bin.display()))
        .env("CARGO_TARGET_DIR", &target)
        .env("ASTREAM_TEST_TARGET", &trace)
        .env("ASTREAM_TEST_ADMISSIONS", &admissions)
        .env("ASTREAM_TEST_MODE", mode)
        .env("CARGO_BUILD_BUILD_DIR", root.join("native intermediates"))
        .env(
            "TARGO_BUILD_BUILD_DIR",
            root.join("other native intermediates"),
        )
        .env_remove("TRUST_OUT_DIR");
    if explicit_output {
        command.env("TRUST_OUT_DIR", &out);
    }
    let mut output = command.output().expect("run real READY script");
    if mode == "repeat" {
        assert!(
            output.status.success(),
            "first run must admit its fresh target"
        );
        output = command.output().expect("repeat READY with admitted target");
    }
    let compiler_target = fs::read_to_string(trace).expect("compiler artifact trace");
    (
        Run {
            output,
            compiler_target: compiler_target.trim_end().to_owned(),
            expected_target: build.to_str().expect("UTF-8 scratch").to_owned(),
            report_exists: out.join("astream-wire/report.json").is_file(),
            used_default_target: root.join("target").exists(),
            admissions: fs::read_to_string(&admissions)
                .unwrap_or_default()
                .lines()
                .map(str::to_owned)
                .collect(),
            preserved_foreign_payload: fs::read(build.join("foreign")).ok().as_deref()
                == Some(b"must survive refusal"),
        },
        floor,
        proved,
    )
}

#[test]
fn uses_the_publishers_artifact_root_and_forwards_its_census() {
    let (run, floor, proved) = run("valid", false);
    assert!(
        run.output.status.success(),
        "stdout={} stderr={}",
        String::from_utf8_lossy(&run.output.stdout),
        String::from_utf8_lossy(&run.output.stderr)
    );
    assert_eq!(run.compiler_target, run.expected_target);
    assert_eq!(run.admissions, vec!["created"]);
    assert!(run.report_exists);
    assert!(!run.used_default_target);
    let output = String::from_utf8_lossy(&run.output.stdout);
    assert!(output.contains("Gate: CONDITIONAL-PASS [advisory lane, exit 0]"));
    assert!(output.contains("fixture compiler diagnostic"));
    assert!(output.contains(&format!("proved {proved} (floor {floor})")));
}

#[test]
fn preserves_an_explicit_report_directory() {
    let (run, _, _) = run("valid", true);
    assert!(run.output.status.success());
    assert_eq!(run.compiler_target, run.expected_target);
    assert_eq!(run.admissions, vec!["created"]);
    assert!(run.report_exists);
    assert!(!run.used_default_target);
}

#[test]
fn refuses_a_report_without_a_readable_compiler_census() {
    for mode in ["missing", "malformed"] {
        let (run, _, _) = run(mode, false);
        assert_eq!(run.output.status.code(), Some(2), "mode={mode}");
        assert!(run.report_exists, "mode={mode}");
        let output = String::from_utf8_lossy(&run.output.stdout);
        assert!(output.contains("no readable Gate banner"), "mode={mode}");
        assert!(!output.contains("OK (exit 0)"), "mode={mode}");
    }
}

#[test]
fn reuses_only_the_drivers_admitted_compiler_directory() {
    for explicit in [false, true] {
        let (run, _, _) = run("repeat", explicit);
        assert!(run.output.status.success());
        assert_eq!(run.compiler_target, run.expected_target);
        assert_eq!(run.admissions, vec!["created", "reused"]);
        assert!(run.report_exists);
        assert!(!run.used_default_target);
    }
}

#[test]
fn unmanaged_existing_target_is_refused_without_deleting_foreign_files() {
    for explicit in [false, true] {
        let (run, _, _) = run("unmanaged", explicit);
        assert_eq!(run.output.status.code(), Some(2));
        assert_eq!(run.compiler_target, run.expected_target);
        assert_eq!(run.admissions, vec!["refused"]);
        assert!(run.preserved_foreign_payload);
        assert!(!run.report_exists);
        let output = String::from_utf8_lossy(&run.output.stdout);
        assert!(output.contains("explicit build target is unmanaged or unsupported"));
        assert!(output.contains("TOOLCHAIN/CLI ERROR"));
        assert!(!output.contains("OK (exit 0)"));
    }
}
