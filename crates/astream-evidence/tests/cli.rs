//! The CLI's exit codes are its contract: a mis-pointed `gate --root` must be
//! a loud refusal (exit 2), never a vacuous "PASS (0 findings)" over nothing.

use std::path::{Path, PathBuf};
use std::process::Command;

fn bin() -> Command {
    Command::new(env!("CARGO_BIN_EXE_astream-evidence"))
}

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join(name)
}

/// Removes a test's scratch directory when dropped, so the test leaves nothing behind
/// whether it passes or panics.
struct Cleanup(std::path::PathBuf);

impl Drop for Cleanup {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[test]
fn gate_refuses_a_nonexistent_root() {
    // Process-unique: a fixed shared temp path that something else has created
    // turns this into a silent false pass (exit 2 for the wrong reason).
    let missing = std::env::temp_dir().join(format!(
        "astream-evidence-cli-no-such-root-{}",
        std::process::id()
    ));
    let out = bin()
        .args(["gate", "--root"])
        .arg(&missing)
        .output()
        .expect("run the binary");
    let stderr = String::from_utf8_lossy(&out.stderr);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert_eq!(
        out.status.code(),
        Some(2),
        "stdout={stdout} stderr={stderr}"
    );
    assert!(stderr.contains("refusing to run"), "stderr={stderr}");
    assert!(!stdout.contains("PASS"), "must never print PASS: {stdout}");
}

#[test]
fn gate_refuses_a_directory_that_is_not_a_workspace_root() {
    // A crate directory: real, but not the tree the gate is meant to judge.
    let out = bin()
        .args(["gate", "--root"])
        .arg(fixture("clean"))
        .output()
        .expect("run the binary");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(2), "stderr={stderr}");
    assert!(
        stderr.contains("not an astream workspace root"),
        "stderr={stderr}"
    );
}

#[test]
fn run_prints_a_failing_claims_output_under_its_fail_line() {
    // A FAIL line alone ("command exited non-zero") cannot be diagnosed from a CI
    // log; the tail of the command's own output must follow it. A passing claim
    // stays one line.
    let root =
        std::env::temp_dir().join(format!("astream-evidence-cli-run-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    let _tmp = Cleanup(root.clone());
    std::fs::create_dir_all(root.join("evidence")).expect("temp dirs");
    std::fs::write(
        root.join("evidence/manifest.toml"),
        "[meta]\nproject = \"t\"\n\n\
         [[claim]]\nid = \"fails.loudly\"\nkind = \"build\"\ntext = \"t\"\n\
         command = \"echo diag-out; echo diag-err >&2; exit 1\"\n\n\
         [[claim]]\nid = \"passes.quietly\"\nkind = \"build\"\ntext = \"t\"\n\
         command = \"echo quiet-out\"\n",
    )
    .expect("manifest");
    let out = bin()
        .args(["run", "--root"])
        .arg(&root)
        .output()
        .expect("run the binary");
    let _ = std::fs::remove_dir_all(&root);
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert_eq!(out.status.code(), Some(1), "stdout={stdout}");
    let fail = stdout.find("[FAIL] fails.loudly").expect("the FAIL line");
    let pass = stdout.find("[PASS] passes.quietly").expect("the PASS line");
    for diag in ["diag-out", "diag-err"] {
        let at = stdout
            .find(diag)
            .unwrap_or_else(|| panic!("{diag} missing: {stdout}"));
        assert!(
            fail < at && at < pass,
            "{diag} not under its FAIL line: {stdout}"
        );
    }
    assert!(
        !stdout.contains("quiet-out"),
        "a pass stays quiet: {stdout}"
    );
}

#[test]
fn run_reports_each_claim_as_it_finishes() {
    // A claim that hangs must not hide every result before it: each line is
    // printed when its claim finishes, so the last line names progress so far
    // (and a CI job killed at its timeout still shows what passed and failed).
    use std::io::{BufRead, BufReader};
    use std::time::Duration;
    let root = std::env::temp_dir().join(format!(
        "astream-evidence-cli-stream-{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&root);
    let _tmp = Cleanup(root.clone());
    std::fs::create_dir_all(root.join("evidence")).expect("temp dirs");
    let stop = root.join("stop");
    std::fs::write(
        root.join("evidence/manifest.toml"),
        format!(
            "[meta]\nproject = \"t\"\n\n\
             [[claim]]\nid = \"quick\"\nkind = \"build\"\ntext = \"t\"\ncommand = \"true\"\n\n\
             [[claim]]\nid = \"waits\"\nkind = \"build\"\ntext = \"t\"\n\
             command = \"while [ ! -f '{}' ]; do sleep 0.05; done\"\n",
            stop.display()
        ),
    )
    .expect("manifest");
    let mut child = bin()
        .args(["run", "--root"])
        .arg(&root)
        .stdout(std::process::Stdio::piped())
        .spawn()
        .expect("run the binary");
    let (tx, rx) = std::sync::mpsc::channel();
    let out = child.stdout.take().unwrap();
    std::thread::spawn(move || {
        for line in BufReader::new(out).lines().map_while(Result::ok) {
            let _ = tx.send(line);
        }
    });
    let mut seen = false;
    while let Ok(line) = rx.recv_timeout(Duration::from_secs(10)) {
        if line.contains("[PASS] quick") {
            seen = true;
            break;
        }
    }
    // Release the waiting claim either way, so the run ends.
    std::fs::write(&stop, "").expect("stop file");
    let status = child.wait().expect("wait");
    let _ = std::fs::remove_dir_all(&root);
    assert!(
        seen,
        "the first claim's result must be printed while the second still runs"
    );
    assert!(status.success());
}

#[test]
fn a_malformed_invocation_is_a_usage_error_not_a_default() {
    // Run from the repository root, where falling back to `--root .` would
    // quietly judge (or print) the real tree: a dropped `--root` value or a
    // misspelled flag must be refused, not read as "use the default".
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join("..");
    for args in [
        vec!["gate", "--root"],
        vec!["gate", "--rot", "."],
        vec!["render", "--wirte"],
        vec!["run", "--write"],
        vec!["selftest", "extra"],
    ] {
        let out = bin()
            .args(&args)
            .current_dir(&root)
            .output()
            .expect("run the binary");
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert_eq!(out.status.code(), Some(2), "{args:?}: stderr={stderr}");
        assert!(stderr.contains("usage:"), "{args:?}: stderr={stderr}");
    }
}

#[test]
fn render_write_reports_an_unreadable_readme_as_such() {
    let root = std::env::temp_dir().join(format!(
        "astream-evidence-cli-render-{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&root);
    let _tmp = Cleanup(root.clone());
    std::fs::create_dir_all(root.join("evidence")).expect("temp dirs");
    std::fs::write(
        root.join("evidence/manifest.toml"),
        "[meta]\nproject = \"t\"\n",
    )
    .expect("manifest");
    let out = bin()
        .args(["render", "--write", "--root"])
        .arg(&root)
        .output()
        .expect("run the binary");
    let _ = std::fs::remove_dir_all(&root);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(1), "stderr={stderr}");
    assert!(
        stderr.contains("README.md") && !stderr.contains("marker"),
        "a missing README is not a missing marker: {stderr}"
    );
}

#[test]
fn gate_accepts_the_repository_root() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join("..");
    let out = bin()
        .args(["gate", "--root"])
        .arg(&root)
        .output()
        .expect("run the binary");
    let stderr = String::from_utf8_lossy(&out.stderr);
    let stdout = String::from_utf8_lossy(&out.stdout);
    // 0 (clean) or 1 (findings) are verdicts; 2 would mean the root itself was refused.
    assert_ne!(
        out.status.code(),
        Some(2),
        "stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("astream-evidence gate:") || stderr.contains("astream-evidence gate:"),
        "stdout={stdout} stderr={stderr}"
    );
}
