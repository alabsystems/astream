// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exercise the stock-check script without compiling: its compiler selection
//! must survive a PATH that has no rustup compiler proxy.

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
    checks: Vec<String>,
    selected_compiler: String,
    used_path_compiler: bool,
}

fn executable(path: &Path, body: &str) {
    fs::write(path, body).expect("write test executable");
    fs::set_permissions(path, fs::Permissions::from_mode(0o755))
        .expect("make test executable runnable");
}

fn run(mode: &str) -> Run {
    let root =
        std::env::temp_dir().join(format!("astream-stock-check-{mode}-{}", std::process::id()));
    fs::create_dir(&root).expect("exclusive scratch directory");
    let _cleanup = Cleanup(root.clone());
    let bin = root.join("bin");
    fs::create_dir(&bin).expect("test PATH directory");
    fs::create_dir(root.join("scripts")).expect("test scripts directory");
    let script = root.join("scripts/stock-check.sh");
    fs::write(&script, include_str!("../../../../scripts/stock-check.sh"))
        .expect("copy real stock-check script");
    let selected = root.join("selected compiler");
    executable(
        &selected,
        r#"#!/bin/sh
set -eu
printf '%s\n' 'rustc 1.99.1' 'release: 1.99.1' 'host: aarch64-apple-darwin'
if [ "$ASTREAM_TEST_MODE" = trust ]; then printf '%s\n' 'trust: test-compiler'; fi
"#,
    );
    executable(
        &bin.join("rustc"),
        "#!/bin/sh\nprintf used >\"$ASTREAM_TEST_WRONG_COMPILER\"\nexit 97\n",
    );
    executable(
        &bin.join("rustup"),
        r#"#!/bin/sh
set -eu
case "$1:$2:$3" in
    which:--toolchain:fixture-stock)
        if [ "$ASTREAM_TEST_MODE" = missing ]; then
            printf '%s\n' 'test compiler unavailable' >&2
            exit 1
        fi
        printf '%s\n' "$ASTREAM_TEST_COMPILER"
        ;;
    run:fixture-stock:rustc)
        shift 3
        exec "$ASTREAM_TEST_COMPILER" "$@"
        ;;
    target:list:--installed)
        printf '%s\n' aarch64-apple-darwin x86_64-unknown-linux-gnu \
            aarch64-unknown-linux-gnu x86_64-apple-darwin x86_64-pc-windows-msvc
        ;;
    run:fixture-stock:cargo)
        "${RUSTC:-rustc}" -vV >/dev/null
        printf '%s\n' "$RUSTC" >>"$ASTREAM_TEST_CHECKS"
        ;;
    *) printf '%s\n' "unexpected rustup arguments: $*" >&2; exit 98 ;;
esac
"#,
    );
    let checks = root.join("checks");
    let wrong = root.join("wrong-compiler");
    let output = Command::new("/bin/bash")
        .arg(&script)
        .env("PATH", format!("{}:/usr/bin:/bin", bin.display()))
        .env("STOCK_TOOLCHAIN", "fixture-stock")
        .env("STOCK_OUT_DIR", root.join("out"))
        .env("ASTREAM_TEST_MODE", mode)
        .env("ASTREAM_TEST_COMPILER", &selected)
        .env("ASTREAM_TEST_CHECKS", &checks)
        .env("ASTREAM_TEST_WRONG_COMPILER", &wrong)
        .env("RUSTC", bin.join("rustc"))
        .output()
        .expect("run real stock-check script");
    let checked = match fs::read_to_string(&checks) {
        Ok(text) => text.lines().map(str::to_owned).collect(),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Vec::new(),
        Err(error) => panic!("read compiler trace: {error}"),
    };
    Run {
        output,
        checks: checked,
        selected_compiler: selected.to_str().expect("UTF-8 scratch path").to_owned(),
        used_path_compiler: wrong.exists(),
    }
}

#[test]
fn uses_the_selected_stock_compiler_without_a_path_proxy() {
    let run = run("stock");
    assert!(
        run.output.status.success(),
        "stdout={} stderr={}",
        String::from_utf8_lossy(&run.output.stdout),
        String::from_utf8_lossy(&run.output.stderr)
    );
    assert_eq!(run.checks.len(), 12, "every target/feature row must run");
    assert!(run.checks.iter().all(|path| path == &run.selected_compiler));
    assert!(!run.used_path_compiler, "PATH rustc must never run");
}

#[test]
fn refuses_an_unresolved_compiler_before_any_checks() {
    let run = run("missing");
    assert_eq!(run.output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&run.output.stdout).contains("COULD NOT RUN"));
    assert!(run.checks.is_empty());
    assert!(
        !run.used_path_compiler,
        "resolution failure must not fall back"
    );
}

#[test]
fn refuses_a_selected_trust_compiler_before_any_checks() {
    let run = run("trust");
    assert_eq!(run.output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&run.output.stdout).contains("not a stock one"));
    assert!(run.checks.is_empty());
    assert!(!run.used_path_compiler);
}
