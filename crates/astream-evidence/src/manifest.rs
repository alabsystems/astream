//! The evidence manifest: the single source of truth for astream's claims.

use serde::Deserialize;
use std::path::Path;

/// The closed set of claim kinds. `kind` decides how a claim is judged, so an
/// unknown spelling (`"tests"`, `"unit"`) must be a load error — otherwise a
/// claim could opt out of the checks its real kind carries (the zero-tests
/// check for `test`, the pinned hash for `selftest`) and stay green.
pub const KINDS: &[&str] = &["build", "test", "selftest", "bench"];

/// The closed set of `platform` values: `std::env::consts::OS` spellings. A
/// value outside this set (`"Linux"`, `"linux "`, `"ubuntu"`) would match no
/// host anywhere and silently skip the claim forever, so it is a load error.
pub const PLATFORMS: &[&str] = &[
    "linux",
    "macos",
    "ios",
    "freebsd",
    "dragonfly",
    "netbsd",
    "openbsd",
    "solaris",
    "illumos",
    "android",
    "windows",
];

/// A parsed `evidence/manifest.toml`.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Manifest {
    pub meta: Meta,
    #[serde(default)]
    pub claim: Vec<Claim>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Meta {
    pub project: String,
}

/// One claim: a statement that is true iff `command` succeeds (and, if set,
/// its stdout hashes to `expected_output_sha`, and the named `metric` stays
/// within `[min_value, max_value]`).
///
/// For `kind = "bench"`, the command prints one or more lines of the form
/// `METRIC <name> <value>`; the claim asserts a floor/ceiling on `metric`.
/// This is the regression gate behind the "never worse on a measured axis"
/// rule — a change that drops a metric below its floor fails the gate.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Claim {
    pub id: String,
    /// One of [`KINDS`]; validated at load time.
    pub kind: String,
    pub text: String,
    pub command: String,
    #[serde(default)]
    pub expected_output_sha: Option<String>,
    /// Name of the `METRIC <name> <value>` line to check (bench claims).
    #[serde(default)]
    pub metric: Option<String>,
    /// Lower bound the metric must meet (the regression floor).
    #[serde(default)]
    pub min_value: Option<f64>,
    /// Upper bound the metric must not exceed (e.g. a latency ceiling).
    #[serde(default)]
    pub max_value: Option<f64>,
    /// OS this claim is verified on (`std::env::consts::OS`, e.g. `"linux"`,
    /// one of [`PLATFORMS`]; validated at load time). When set and not
    /// matching the host, `run` SKIPS the claim (it is verified on its
    /// platform, not here) — used for the Linux-only ptrace Effects claim.
    /// `None` (the default) means the claim runs on every platform.
    #[serde(default)]
    pub platform: Option<String>,
}

/// The cargo subcommand a claim command runs, if the command is a cargo
/// invocation: `cargo test ...` -> `Some("test")`. Leading `VAR=value`
/// environment assignments (`BENCH_N=500 cargo run ...`), a `+toolchain`
/// selector, and cargo's own leading flags (`-q`, `--locked`) are skipped.
/// A command whose program is not cargo yields `None`.
pub fn cargo_subcommand(command: &str) -> Option<&str> {
    let mut toks = command
        .split_whitespace()
        .skip_while(|t| is_env_assignment(t));
    let prog = toks.next()?;
    if basename(prog) != "cargo" {
        return None;
    }
    toks.find(|t| !t.starts_with('-') && !t.starts_with('+'))
}

/// The program a claim command runs, as a basename: its first token after any
/// leading `VAR=value` environment assignments (`BENCH_N=5 /bin/echo x` ->
/// `Some("echo")`). `None` for a command with no program.
pub fn command_program(command: &str) -> Option<&str> {
    command
        .split_whitespace()
        .find(|t| !is_env_assignment(t))
        .map(basename)
}

fn basename(prog: &str) -> &str {
    prog.rsplit('/').next().unwrap_or(prog)
}

pub(crate) fn is_env_assignment(tok: &str) -> bool {
    match tok.split_once('=') {
        Some((name, _)) => {
            !name.is_empty() && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        }
        None => false,
    }
}

impl Manifest {
    /// Load and parse a manifest from disk.
    pub fn load(path: &Path) -> Result<Manifest, String> {
        let text =
            std::fs::read_to_string(path).map_err(|e| format!("read {}: {e}", path.display()))?;
        Manifest::parse(&text, &path.display().to_string())
    }

    /// Parse manifest text and validate its structure. `origin` names the
    /// source in error messages (a path, or a label for in-memory text).
    ///
    /// Rejected here, so that neither `run`, `render`, nor `gate` can ever
    /// consume the claim: a duplicate id, a `kind` outside [`KINDS`], a
    /// `platform` outside [`PLATFORMS`], and a malformed `expected_output_sha`.
    pub fn parse(text: &str, origin: &str) -> Result<Manifest, String> {
        let m: Manifest = toml::from_str(text).map_err(|e| format!("parse {origin}: {e}"))?;
        // A claim id is the stable handle the evidence story is keyed on; a
        // duplicate (copy-paste, or a lax claim shadowing a strict one) must
        // not pass silently.
        let mut seen = std::collections::HashSet::new();
        for c in &m.claim {
            if !seen.insert(c.id.as_str()) {
                return Err(format!("parse {origin}: duplicate claim id {:?}", c.id));
            }
            if !KINDS.contains(&c.kind.as_str()) {
                return Err(format!(
                    "parse {origin}: claim {:?} has unknown kind {:?} (expected one of {})",
                    c.id,
                    c.kind,
                    KINDS.join(", ")
                ));
            }
            if let Some(p) = &c.platform {
                if !PLATFORMS.contains(&p.as_str()) {
                    return Err(format!(
                        "parse {origin}: claim {:?} has unknown platform {:?} — it would match no \
                         host and be skipped everywhere (expected one of {})",
                        c.id,
                        p,
                        PLATFORMS.join(", ")
                    ));
                }
            }
            if let Some(sha) = &c.expected_output_sha {
                let well_formed =
                    sha.len() == 64 && sha.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'));
                if !well_formed {
                    return Err(format!(
                        "parse {origin}: claim {:?} has a malformed expected_output_sha {:?} \
                         (expected 64 lowercase hex digits)",
                        c.id, sha
                    ));
                }
            }
        }
        Ok(m)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn manifest(claim_body: &str) -> String {
        format!("[meta]\nproject = \"t\"\n\n[[claim]]\nid = \"c\"\n{claim_body}\n")
    }

    #[test]
    fn rejects_unknown_kind() {
        let text = manifest("kind = \"tests\"\ntext = \"t\"\ncommand = \"cargo test --locked\"");
        let err = Manifest::parse(&text, "mem").expect_err("an unknown kind must not load");
        assert!(err.contains("unknown kind"), "{err}");
        for k in KINDS {
            let text = manifest(&format!(
                "kind = \"{k}\"\ntext = \"t\"\ncommand = \"cargo test --locked\""
            ));
            assert!(Manifest::parse(&text, "mem").is_ok(), "kind {k:?} is valid");
        }
    }

    #[test]
    fn rejects_unknown_platform() {
        for bad in ["Linux", "linux ", "ubuntu"] {
            let text = manifest(&format!(
                "kind = \"test\"\ntext = \"t\"\ncommand = \"cargo test --locked\"\nplatform = \"{bad}\""
            ));
            let err = Manifest::parse(&text, "mem").expect_err("an unknown platform must not load");
            assert!(err.contains("unknown platform"), "{err}");
        }
        let text = manifest(
            "kind = \"test\"\ntext = \"t\"\ncommand = \"cargo test --locked\"\nplatform = \"linux\"",
        );
        assert!(Manifest::parse(&text, "mem").is_ok());
    }

    #[test]
    fn rejects_malformed_output_sha() {
        let text = manifest(
            "kind = \"selftest\"\ntext = \"t\"\ncommand = \"cargo run --locked\"\nexpected_output_sha = \"abc\"",
        );
        let err = Manifest::parse(&text, "mem").expect_err("a short sha must not load");
        assert!(err.contains("malformed expected_output_sha"), "{err}");
    }

    #[test]
    fn rejects_duplicate_ids() {
        let text = "[meta]\nproject = \"t\"\n\n[[claim]]\nid = \"c\"\nkind = \"test\"\ntext = \"t\"\ncommand = \"cargo test\"\n\n[[claim]]\nid = \"c\"\nkind = \"test\"\ntext = \"t\"\ncommand = \"cargo test\"\n";
        let err = Manifest::parse(text, "mem").expect_err("duplicate ids must not load");
        assert!(err.contains("duplicate claim id"), "{err}");
    }

    #[test]
    fn cargo_subcommand_skips_env_toolchain_and_flags() {
        assert_eq!(cargo_subcommand("cargo test --locked -p x"), Some("test"));
        assert_eq!(
            cargo_subcommand("BENCH_N=500 cargo run --quiet --release --locked -p x"),
            Some("run")
        );
        assert_eq!(
            cargo_subcommand("cargo +nightly -q --locked build"),
            Some("build")
        );
        assert_eq!(cargo_subcommand("/usr/bin/cargo check"), Some("check"));
        assert_eq!(cargo_subcommand("sh -c true"), None);
        assert_eq!(cargo_subcommand("bash scripts/x.sh cargo test"), None);
        assert_eq!(cargo_subcommand(""), None);
    }

    #[test]
    fn command_program_skips_env_assignments() {
        assert_eq!(command_program("cargo test"), Some("cargo"));
        assert_eq!(
            command_program("BENCH_N=5 A_B=x /bin/echo hi"),
            Some("echo")
        );
        assert_eq!(command_program("sh -c 'X=1 true'"), Some("sh"));
        assert_eq!(command_program("X=1"), None);
        assert_eq!(command_program("  "), None);
    }
}
