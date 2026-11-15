//! The evidence manifest: the single source of truth for astream's claims.

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

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "manifest_island.rs"]
mod manifest_island;
#[cfg(not(clean_islands))]
pub use crate::twins::manifest_claim_count_advance;
#[cfg(clean_islands)]
pub use manifest_island::manifest_claim_count_advance;

contract_fn! {
    /// Verified check that a parsed manifest declares at least one claim (`0 < count`),
    /// linked via `clean-kernel-defeq` to `manifest_has_claims_isl`.
    #[must_use]
    pub const fn manifest_has_claims(count: usize) -> bool
    clauses [ensures result == (0 < count)]
    {
        0 < count
    }
}

/// A parsed `evidence/manifest.toml`.
#[derive(Debug)]
pub struct Manifest {
    pub meta: Meta,
    pub claim: Vec<Claim>,
}

#[derive(Debug)]
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
#[derive(Debug, Clone)]
pub struct Claim {
    pub id: String,
    /// One of [`KINDS`]; validated at load time.
    pub kind: String,
    pub text: String,
    pub command: String,
    pub expected_output_sha: Option<String>,
    /// Name of the `METRIC <name> <value>` line to check (bench claims).
    pub metric: Option<String>,
    /// Lower bound the metric must meet (the regression floor).
    pub min_value: Option<f64>,
    /// Upper bound the metric must not exceed (e.g. a latency ceiling).
    pub max_value: Option<f64>,
    /// OS this claim is verified on (`std::env::consts::OS`, e.g. `"linux"`,
    /// one of [`PLATFORMS`]; validated at load time). When set and not
    /// matching the host, `run` SKIPS the claim (it is verified on its
    /// platform, not here) — used for the Linux-only ptrace Effects claim.
    /// `None` (the default) means the claim runs on every platform.
    pub platform: Option<String>,
    /// Optional per-claim wall-clock timeout in seconds (`> 0`; defaults to
    /// [`crate::timeout::DEFAULT_CLAIM_TIMEOUT_SECS`] when omitted).
    pub timeout_secs: Option<u64>,
}

/// The two lanes a Targo compilation names before its verb: `targo --unverified
/// <verb>` (proof pipeline off, no proof claim) and `targo trust <verb>`
/// (verified, fail-closed). astream builds, tests and runs on the Trust
/// toolchain, and a nested `targo` does not inherit its parent's lane, so
/// every claim command names one.
pub const TARGO_LANES: &[&str] = &["--unverified", "trust"];

/// How a claim command invokes `targo`, read from its program (past any
/// leading `VAR=value` environment assignments).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TargoCall<'a> {
    /// The lane named before the verb (one of [`TARGO_LANES`]), if any.
    pub lane: Option<&'a str>,
    /// The subcommand: `test`, `build`, `run`, ...; `None` for a bare flag call.
    pub verb: Option<&'a str>,
    /// A rustup `+toolchain` selector among the leading tokens, if any: it
    /// picks a rustup toolchain, which is not how a Trust lane is chosen.
    pub toolchain: Option<&'a str>,
}

/// Parse a claim command as a `targo` invocation: `targo --unverified test
/// ...` -> lane `--unverified`, verb `test`; `targo trust check ...` -> lane
/// `trust`, verb `check`. Leading `VAR=value` assignments (`BENCH_N=500 targo
/// --unverified run ...`) and targo's own leading flags (`-q`, `--locked`) are
/// skipped. A command whose program is not `targo` — including the stock
/// `cargo` — yields `None`.
#[allow(clippy::question_mark)]
pub fn targo_call(command: &str) -> Option<TargoCall<'_>> {
    let mut toks = command.split_whitespace();
    let mut prog_opt = None;
    for tok in toks.by_ref() {
        if !is_env_assignment(tok) {
            prog_opt = Some(tok);
            break;
        }
    }
    let Some(prog) = prog_opt else {
        return None;
    };
    if basename(prog) != "targo" {
        return None;
    }
    let mut call = TargoCall {
        lane: None,
        verb: None,
        toolchain: None,
    };
    for t in toks {
        if t.starts_with('+') {
            call.toolchain = Some(t);
        } else if call.lane.is_none() && TARGO_LANES.contains(&t) {
            call.lane = Some(t);
        } else if !t.starts_with('-') {
            call.verb = Some(t);
            break;
        }
    }
    Some(call)
}

/// The targo subcommand a claim command runs, past its lane: `targo
/// --unverified test ...` -> `Some("test")`. `None` when the program is not
/// `targo` or names no verb.
pub fn targo_subcommand(command: &str) -> Option<&str> {
    match targo_call(command) {
        Some(c) => c.verb,
        None => None,
    }
}

/// The program a claim command runs, as a basename: its first token after any
/// leading `VAR=value` environment assignments (`BENCH_N=5 /bin/echo x` ->
/// `Some("echo")`). `None` for a command with no program.
pub fn command_program(command: &str) -> Option<&str> {
    for tok in command.split_whitespace() {
        if !is_env_assignment(tok) {
            return Some(basename(tok));
        }
    }
    None
}

fn basename(prog: &str) -> &str {
    prog.rsplit('/').next().unwrap_or(prog)
}

/// Check whether `bytes` is a leading `VAR=value` environment assignment token.
#[must_use]
pub const fn is_env_assignment_bytes(bytes: &[u8]) -> bool {
    let mut i = 0usize;
    while i < bytes.len() {
        let b = bytes[i];
        if b == b'=' {
            return i > 0;
        }
        let is_alnum_or_under = (b >= b'0' && b <= b'9')
            || (b >= b'a' && b <= b'z')
            || (b >= b'A' && b <= b'Z')
            || b == b'_';
        if !is_alnum_or_under {
            return false;
        }
        i = i.saturating_add(1);
    }
    false
}

/// Check whether `bytes` is a 64-byte lowercase hexadecimal SHA-256 digest string.
#[must_use]
pub const fn is_valid_sha256_hex(bytes: &[u8]) -> bool {
    if bytes.len() != 64 {
        return false;
    }
    let mut i = 0usize;
    while i < bytes.len() {
        let b = bytes[i];
        let ok = (b >= b'0' && b <= b'9') || (b >= b'a' && b <= b'f');
        if !ok {
            return false;
        }
        i = i.saturating_add(1);
    }
    true
}

pub(crate) fn is_env_assignment(tok: &str) -> bool {
    is_env_assignment_bytes(tok.as_bytes())
}

fn parse_opt_timeout_secs(
    tbl: &toml::map::Map<String, toml::Value>,
) -> Result<Option<u64>, String> {
    match tbl.get("timeout_secs") {
        Some(toml::Value::Integer(i)) => {
            if *i <= 0 {
                Err("field `timeout_secs` in [[claim]] must be a positive integer (> 0)".to_owned())
            } else {
                Ok(Some(*i as u64))
            }
        }
        Some(_) => {
            Err("field `timeout_secs` in [[claim]] must be a positive integer (> 0)".to_owned())
        }
        None => Ok(None),
    }
}

impl Manifest {
    /// Load and parse a manifest from disk.
    pub fn load(path: &Path) -> Result<Manifest, String> {
        let bytes = match std::fs::read(path) {
            Ok(b) => b,
            Err(e) => return Err(format!("read {}: {e}", path.display())),
        };
        let text = match core::str::from_utf8(&bytes) {
            Ok(t) => t,
            Err(e) => return Err(format!("read {}: {e}", path.display())),
        };
        Manifest::parse(text, &path.display().to_string())
    }

    /// Parse manifest text and validate its structure. `origin` names the
    /// source in error messages (a path, or a label for in-memory text).
    ///
    /// Rejected here, so that neither `run`, `render`, nor `gate` can ever
    /// consume the claim: a duplicate id, a `kind` outside [`KINDS`], a
    /// `platform` outside [`PLATFORMS`], and a malformed `expected_output_sha`.
    fn parse_raw(text: &str) -> Result<Manifest, String> {
        let root_val: toml::Value = text.parse().map_err(|e: toml::de::Error| e.to_string())?;
        let Some(root) = root_val.as_table() else {
            return Err("manifest root must be a table".to_owned());
        };
        for k in root.keys() {
            if k != "meta" && k != "claim" {
                return Err(format!("unknown field `{k}`, expected `meta` or `claim`"));
            }
        }
        let Some(meta_val) = root.get("meta") else {
            return Err("missing field `meta`".to_owned());
        };
        let Some(meta_tbl) = meta_val.as_table() else {
            return Err("`meta` must be a table".to_owned());
        };
        for k in meta_tbl.keys() {
            if k != "project" {
                return Err(format!("unknown field `{k}` in [meta], expected `project`"));
            }
        }
        let Some(project) = meta_tbl.get("project").and_then(toml::Value::as_str) else {
            return Err("missing string field `meta.project`".to_owned());
        };
        let meta = Meta {
            project: project.to_owned(),
        };
        let mut claims = Vec::new();
        if let Some(claim_val) = root.get("claim") {
            let Some(arr) = claim_val.as_array() else {
                return Err("`claim` must be an array of tables".to_owned());
            };
            for item in arr {
                let Some(tbl) = item.as_table() else {
                    return Err("each `[[claim]]` entry must be a table".to_owned());
                };
                for k in tbl.keys() {
                    if !matches!(
                        k.as_str(),
                        "id" | "kind"
                            | "text"
                            | "command"
                            | "expected_output_sha"
                            | "metric"
                            | "min_value"
                            | "max_value"
                            | "platform"
                            | "timeout_secs"
                    ) {
                        return Err(format!("unknown field `{k}` in [[claim]]"));
                    }
                }
                let req_str = |field: &str| -> Result<String, String> {
                    match tbl.get(field) {
                        Some(v) => match v.as_str() {
                            Some(s) => Ok(s.to_owned()),
                            None => Err(format!("field `{field}` in [[claim]] must be a string")),
                        },
                        None => Err(format!("missing field `{field}` in [[claim]]")),
                    }
                };
                let opt_str = |field: &str| -> Result<Option<String>, String> {
                    match tbl.get(field) {
                        Some(v) => match v.as_str() {
                            Some(s) => Ok(Some(s.to_owned())),
                            None => Err(format!("field `{field}` in [[claim]] must be a string")),
                        },
                        None => Ok(None),
                    }
                };
                let opt_f64 = |field: &str| -> Result<Option<f64>, String> {
                    match tbl.get(field) {
                        Some(toml::Value::Float(f)) => Ok(Some(*f)),
                        Some(toml::Value::Integer(i)) => Ok(Some(*i as f64)),
                        Some(_) => Err(format!("field `{field}` in [[claim]] must be a number")),
                        None => Ok(None),
                    }
                };
                claims.push(Claim {
                    id: req_str("id")?,
                    kind: req_str("kind")?,
                    text: req_str("text")?,
                    command: req_str("command")?,
                    expected_output_sha: opt_str("expected_output_sha")?,
                    metric: opt_str("metric")?,
                    min_value: opt_f64("min_value")?,
                    max_value: opt_f64("max_value")?,
                    platform: opt_str("platform")?,
                    timeout_secs: parse_opt_timeout_secs(tbl)?,
                });
            }
        }
        Ok(Manifest {
            meta,
            claim: claims,
        })
    }

    pub fn parse(text: &str, origin: &str) -> Result<Manifest, String> {
        let m: Manifest = match Self::parse_raw(text) {
            Ok(m) => m,
            Err(e) => return Err(format!("parse {origin}: {e}")),
        };
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
                if !is_valid_sha256_hex(sha.as_bytes()) {
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
        let text = manifest(
            "kind = \"tests\"\ntext = \"t\"\ncommand = \"targo --unverified test --locked\"",
        );
        let err = Manifest::parse(&text, "mem").expect_err("an unknown kind must not load");
        assert!(err.contains("unknown kind"), "{err}");
        for k in KINDS {
            let text = manifest(&format!(
                "kind = \"{k}\"\ntext = \"t\"\ncommand = \"targo --unverified test --locked\""
            ));
            assert!(Manifest::parse(&text, "mem").is_ok(), "kind {k:?} is valid");
        }
    }

    #[test]
    fn rejects_unknown_platform() {
        for bad in ["Linux", "linux ", "ubuntu"] {
            let text = manifest(&format!(
                "kind = \"test\"\ntext = \"t\"\ncommand = \"targo --unverified test --locked\"\nplatform = \"{bad}\""
            ));
            let err = Manifest::parse(&text, "mem").expect_err("an unknown platform must not load");
            assert!(err.contains("unknown platform"), "{err}");
        }
        let text = manifest(
            "kind = \"test\"\ntext = \"t\"\ncommand = \"targo --unverified test --locked\"\nplatform = \"linux\"",
        );
        assert!(Manifest::parse(&text, "mem").is_ok());
    }

    #[test]
    fn rejects_malformed_output_sha() {
        let text = manifest(
            "kind = \"selftest\"\ntext = \"t\"\ncommand = \"targo --unverified run --locked\"\nexpected_output_sha = \"abc\"",
        );
        let err = Manifest::parse(&text, "mem").expect_err("a short sha must not load");
        assert!(err.contains("malformed expected_output_sha"), "{err}");
    }

    #[test]
    fn rejects_duplicate_ids() {
        let text = "[meta]\nproject = \"t\"\n\n[[claim]]\nid = \"c\"\nkind = \"test\"\ntext = \"t\"\ncommand = \"targo --unverified test\"\n\n[[claim]]\nid = \"c\"\nkind = \"test\"\ntext = \"t\"\ncommand = \"targo --unverified test\"\n";
        let err = Manifest::parse(text, "mem").expect_err("duplicate ids must not load");
        assert!(err.contains("duplicate claim id"), "{err}");
    }

    #[test]
    fn targo_call_reads_lane_verb_and_selector_past_env_and_flags() {
        let call = |cmd| targo_call(cmd).map(|c| (c.lane, c.verb, c.toolchain));
        assert_eq!(
            call("targo --unverified test --locked -p x"),
            Some((Some("--unverified"), Some("test"), None))
        );
        assert_eq!(
            call("BENCH_N=500 targo --unverified run --quiet --release --locked -p x"),
            Some((Some("--unverified"), Some("run"), None))
        );
        assert_eq!(
            call("targo trust check -p x"),
            Some((Some("trust"), Some("check"), None))
        );
        assert_eq!(
            call("targo -q --locked --unverified build"),
            Some((Some("--unverified"), Some("build"), None))
        );
        assert_eq!(
            call("targo +nightly --unverified build"),
            Some((Some("--unverified"), Some("build"), Some("+nightly")))
        );
        assert_eq!(
            call("targo test --locked"),
            Some((None, Some("test"), None))
        );
        assert_eq!(call("targo --version"), Some((None, None, None)));
        assert_eq!(
            call("/opt/bin/targo --unverified check"),
            Some((Some("--unverified"), Some("check"), None))
        );
        // The stock driver is not targo, whatever its verb.
        assert_eq!(call("cargo test --locked"), None);
        assert_eq!(call("sh -c true"), None);
        assert_eq!(call("bash scripts/x.sh targo --unverified test"), None);
        assert_eq!(call(""), None);
    }

    #[test]
    fn targo_subcommand_is_the_verb_past_the_lane() {
        assert_eq!(
            targo_subcommand("targo --unverified test --locked -p x"),
            Some("test")
        );
        assert_eq!(targo_subcommand("targo trust build -p x"), Some("build"));
        assert_eq!(targo_subcommand("cargo test"), None);
        assert_eq!(targo_subcommand("targo --locked"), None);
    }

    #[test]
    fn command_program_skips_env_assignments() {
        assert_eq!(command_program("targo --unverified test"), Some("targo"));
        assert_eq!(
            command_program("BENCH_N=5 A_B=x /bin/echo hi"),
            Some("echo")
        );
        assert_eq!(command_program("sh -c 'X=1 true'"), Some("sh"));
        assert_eq!(command_program("X=1"), None);
        assert_eq!(command_program("  "), None);
    }

    #[test]
    fn parses_positive_timeout_secs_and_rejects_non_positive_or_non_integer() {
        let ok = manifest(
            "kind = \"test\"\ntext = \"t\"\ncommand = \"targo --unverified test --locked\"\ntimeout_secs = 30",
        );
        let parsed = Manifest::parse(&ok, "mem").unwrap();
        assert_eq!(parsed.claim[0].timeout_secs, Some(30));

        for bad in ["0", "-5", "\"30\"", "1.5"] {
            let text = manifest(&format!(
                "kind = \"test\"\ntext = \"t\"\ncommand = \"targo --unverified test --locked\"\ntimeout_secs = {bad}"
            ));
            let err = Manifest::parse(&text, "mem").unwrap_err();
            assert!(err.contains("timeout_secs"), "{err}");
        }
    }
}
