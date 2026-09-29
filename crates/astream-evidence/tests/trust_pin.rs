//! The Trust verification report is an attached artifact: `make ci` cannot run
//! the Trust toolchain, so the one thing the harness CAN hold the artifact to
//! is internal consistency with the script that re-captures it — the toolchain
//! commit both name must be the same, and the script must never hide the
//! compiler's own output (a swallowed unknown-flag error would read as a
//! "REFUTED" verdict).

use std::path::{Path, PathBuf};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join("..")
}

fn read(rel: &str) -> String {
    let p = repo_root().join(rel);
    std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()))
}

fn pinned_commit(script: &str) -> String {
    script
        .lines()
        .find_map(|l| l.strip_prefix("TRUST_PINNED_COMMIT="))
        .map(|v| {
            v.split('#')
                .next()
                .unwrap_or("")
                .trim()
                .trim_matches('"')
                .to_string()
        })
        .expect("scripts/verify-trust.sh must pin the Trust commit as TRUST_PINNED_COMMIT=")
}

#[test]
fn verify_trust_script_and_artifact_pin_the_same_toolchain() {
    let script = read("scripts/verify-trust.sh");
    let artifact = read("evidence/verify/trust-wire.md");
    let pin = pinned_commit(&script);
    assert!(
        pin.len() >= 7 && pin.chars().all(|c| c.is_ascii_hexdigit()),
        "the pin must be a git commit prefix; got {pin:?}"
    );
    assert!(
        artifact.contains(&pin),
        "evidence/verify/trust-wire.md must be captured with the pinned Trust commit {pin}"
    );
}

#[test]
fn verify_trust_script_never_hides_compiler_output() {
    let script = read("scripts/verify-trust.sh");
    for hidden in ["2>/dev/null", "2> /dev/null", "&>/dev/null", "&> /dev/null"] {
        assert!(
            !script.contains(hidden),
            "the script must show the compiler's stderr, never redirect it away ({hidden:?})"
        );
    }
}
