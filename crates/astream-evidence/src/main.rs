//! `astream-evidence` — the honesty-harness CLI.
//!
//! Subcommands:
//! * `gate [--root DIR]`     — run the merge-gate lints; exit 1 on any finding,
//!   exit 2 if DIR is not an astream workspace root (nothing is ever "gated" vacuously).
//! * `render [--write] [--root DIR]` — render the evidence table from the manifest.
//! * `run [--root DIR]`      — run every claim's command and report pass/fail.
//! * `selftest`              — print a deterministic line (pinned by hash in the manifest).

#![forbid(unsafe_code)]

// A contracted fn is written once, through `contract_fn!`: under a Trust compiler
// (`cfg(clean_islands)`, build.rs) it carries its `ensures` clause, which no stock rustc can
// parse, and every other compiler gets the plain fn.
#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

// Plain-Rust twins of the functions this binary's Clean island compiles, for a compiler
// that cannot lex the island.
#[cfg(any(test, not(clean_islands)))]
#[path = "main_twins.rs"]
mod twins;

use astream_evidence::{gate, manifest::Manifest, render, runner};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

const USAGE: &str = "usage: astream-evidence <gate|render [--write]|run|selftest> [--root DIR]";

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "main_island.rs"]
mod main_island;
#[cfg(clean_islands)]
use main_island::cli_passed_advance;
#[cfg(not(clean_islands))]
use twins::cli_passed_advance;

contract_fn! {
    /// Verified check that a claim-run summary has zero failed claims (`failed == 0`),
    /// linked via `clean-kernel-defeq` to `cli_all_claims_passed_isl`.
    #[must_use]
    pub const fn cli_all_claims_passed(failed: usize) -> bool
    clauses [ensures result == (failed == 0)]
    {
        failed == 0
    }
}

/// Four-byte magic prefix (`"AEVC"`) for a 20-byte `astream-evidence` CLI summary wire header.
pub const CLI_SUMMARY_WIRE_MAGIC: [u8; 4] = *b"AEVC";

/// Wire format version for `astream-evidence` CLI summary wire headers.
pub const CLI_SUMMARY_WIRE_VERSION: u8 = 1;

/// Encode a 20-byte `astream-evidence` CLI summary wire header:
/// `[0..4] = b"AEVC"`, `[4] = version (1)`, `[5] = subcommand_tag` (`0..=3`),
/// `[6] = write_flag` (`0` or `1`, only `1` when `subcommand_tag == 1`),
/// `[7] = status_code` (`0..=2`), `[8..12] = passed (BE)`,
/// `[12..16] = failed (BE)`, `[16..20] = skipped (BE)`.
#[must_use]
pub const fn cli_encode_summary_wire(
    subcommand_tag: u8,
    write: bool,
    status_code: u8,
    passed: u32,
    failed: u32,
    skipped: u32,
) -> Option<[u8; 20]> {
    let write_tag = write as u8;
    let out = [
        CLI_SUMMARY_WIRE_MAGIC[0],
        CLI_SUMMARY_WIRE_MAGIC[1],
        CLI_SUMMARY_WIRE_MAGIC[2],
        CLI_SUMMARY_WIRE_MAGIC[3],
        CLI_SUMMARY_WIRE_VERSION,
        subcommand_tag,
        write_tag,
        status_code,
        ((passed >> 24) & 0xFF) as u8,
        ((passed >> 16) & 0xFF) as u8,
        ((passed >> 8) & 0xFF) as u8,
        (passed & 0xFF) as u8,
        ((failed >> 24) & 0xFF) as u8,
        ((failed >> 16) & 0xFF) as u8,
        ((failed >> 8) & 0xFF) as u8,
        (failed & 0xFF) as u8,
        ((skipped >> 24) & 0xFF) as u8,
        ((skipped >> 16) & 0xFF) as u8,
        ((skipped >> 8) & 0xFF) as u8,
        (skipped & 0xFF) as u8,
    ];
    if subcommand_tag > 3 || status_code > 2 || (write && subcommand_tag != 1) {
        return None;
    }
    Some(out)
}

/// Decode a 20-byte `astream-evidence` CLI summary wire header into
/// `(subcommand_tag, write, status_code, passed, failed, skipped)`.
#[must_use]
pub const fn cli_decode_summary_wire(buf: &[u8]) -> Option<(u8, bool, u8, u32, u32, u32)> {
    let [b'A', b'E', b'V', b'C', CLI_SUMMARY_WIRE_VERSION, subcommand_tag, write_tag, status_code, p0, p1, p2, p3, f0, f1, f2, f3, s0, s1, s2, s3, ..] =
        *buf
    else {
        return None;
    };
    let passed = ((p0 as u32) << 24) | ((p1 as u32) << 16) | ((p2 as u32) << 8) | (p3 as u32);
    let failed = ((f0 as u32) << 24) | ((f1 as u32) << 16) | ((f2 as u32) << 8) | (f3 as u32);
    let skipped = ((s0 as u32) << 24) | ((s1 as u32) << 16) | ((s2 as u32) << 8) | (s3 as u32);
    let write = match write_tag {
        0 => false,
        1 => true,
        _ => return None,
    };
    if subcommand_tag > 3 || status_code > 2 || (write && subcommand_tag != 1) {
        return None;
    }
    Some((subcommand_tag, write, status_code, passed, failed, skipped))
}

/// Four-byte magic prefix (`"AEVG"`) for a 16-byte `astream-evidence` gate report wire header.
pub const CLI_GATE_WIRE_MAGIC: [u8; 4] = *b"AEVG";

/// Wire format version for `astream-evidence` gate report wire headers.
pub const CLI_GATE_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `astream-evidence` gate report wire header:
/// `[0..4] = b"AEVG"`, `[4] = version (1)`, `[5] = status_code` (`0..=2`), `[6..8] = 0`,
/// `[8..12] = violations (BE)`, `[12..16] = caches_skipped (BE)`.
#[must_use]
pub const fn cli_encode_gate_wire(
    status_code: u8,
    violations: u32,
    caches_skipped: u32,
) -> Option<[u8; 16]> {
    let out = [
        CLI_GATE_WIRE_MAGIC[0],
        CLI_GATE_WIRE_MAGIC[1],
        CLI_GATE_WIRE_MAGIC[2],
        CLI_GATE_WIRE_MAGIC[3],
        CLI_GATE_WIRE_VERSION,
        status_code,
        0,
        0,
        ((violations >> 24) & 0xFF) as u8,
        ((violations >> 16) & 0xFF) as u8,
        ((violations >> 8) & 0xFF) as u8,
        (violations & 0xFF) as u8,
        ((caches_skipped >> 24) & 0xFF) as u8,
        ((caches_skipped >> 16) & 0xFF) as u8,
        ((caches_skipped >> 8) & 0xFF) as u8,
        (caches_skipped & 0xFF) as u8,
    ];
    if status_code > 2 || (status_code == 0 && violations != 0) {
        return None;
    }
    Some(out)
}

/// Decode a 16-byte `astream-evidence` gate report wire header into
/// `(status_code, violations, caches_skipped)`.
#[must_use]
pub const fn cli_decode_gate_wire(buf: &[u8]) -> Option<(u8, u32, u32)> {
    let [b'A', b'E', b'V', b'G', CLI_GATE_WIRE_VERSION, status_code, 0, 0, v0, v1, v2, v3, c0, c1, c2, c3, ..] =
        *buf
    else {
        return None;
    };
    let violations = ((v0 as u32) << 24) | ((v1 as u32) << 16) | ((v2 as u32) << 8) | (v3 as u32);
    let caches_skipped =
        ((c0 as u32) << 24) | ((c1 as u32) << 16) | ((c2 as u32) << 8) | (c3 as u32);
    if status_code > 2 || (status_code == 0 && violations != 0) {
        return None;
    }
    Some((status_code, violations, caches_skipped))
}

/// Four-byte magic prefix (`"AEVR"`) for a 20-byte `astream-evidence` claim result wire header.
pub const CLI_CLAIM_WIRE_MAGIC: [u8; 4] = *b"AEVR";

/// Wire format version for `astream-evidence` claim result wire headers.
pub const CLI_CLAIM_WIRE_VERSION: u8 = 1;

/// Encode a 20-byte `astream-evidence` claim result wire header:
/// `[0..4] = b"AEVR"`, `[4] = version (1)`, `[5] = outcome_tag` (`0 = pass`, `1 = fail`, `2 = skip`),
/// `[6..8] = exit_code (BE)`, `[8..12] = claim_idx (BE)`,
/// `[12..16] = stdout_lines (BE)`, `[16..20] = stderr_lines (BE)`.
#[must_use]
pub const fn cli_encode_claim_wire(
    outcome_tag: u8,
    exit_code: u16,
    claim_idx: u32,
    stdout_lines: u32,
    stderr_lines: u32,
) -> Option<[u8; 20]> {
    let out = [
        CLI_CLAIM_WIRE_MAGIC[0],
        CLI_CLAIM_WIRE_MAGIC[1],
        CLI_CLAIM_WIRE_MAGIC[2],
        CLI_CLAIM_WIRE_MAGIC[3],
        CLI_CLAIM_WIRE_VERSION,
        outcome_tag,
        ((exit_code >> 8) & 0xFF) as u8,
        (exit_code & 0xFF) as u8,
        ((claim_idx >> 24) & 0xFF) as u8,
        ((claim_idx >> 16) & 0xFF) as u8,
        ((claim_idx >> 8) & 0xFF) as u8,
        (claim_idx & 0xFF) as u8,
        ((stdout_lines >> 24) & 0xFF) as u8,
        ((stdout_lines >> 16) & 0xFF) as u8,
        ((stdout_lines >> 8) & 0xFF) as u8,
        (stdout_lines & 0xFF) as u8,
        ((stderr_lines >> 24) & 0xFF) as u8,
        ((stderr_lines >> 16) & 0xFF) as u8,
        ((stderr_lines >> 8) & 0xFF) as u8,
        (stderr_lines & 0xFF) as u8,
    ];
    if outcome_tag > 2 || (outcome_tag == 0 && exit_code != 0) {
        return None;
    }
    Some(out)
}

/// Decode a 20-byte `astream-evidence` claim result wire header into
/// `(outcome_tag, exit_code, claim_idx, stdout_lines, stderr_lines)`.
#[must_use]
pub const fn cli_decode_claim_wire(buf: &[u8]) -> Option<(u8, u16, u32, u32, u32)> {
    let [b'A', b'E', b'V', b'R', CLI_CLAIM_WIRE_VERSION, outcome_tag, e0, e1, c0, c1, c2, c3, o0, o1, o2, o3, r0, r1, r2, r3, ..] =
        *buf
    else {
        return None;
    };
    let exit_code = ((e0 as u16) << 8) | (e1 as u16);
    let claim_idx = ((c0 as u32) << 24) | ((c1 as u32) << 16) | ((c2 as u32) << 8) | (c3 as u32);
    let stdout_lines = ((o0 as u32) << 24) | ((o1 as u32) << 16) | ((o2 as u32) << 8) | (o3 as u32);
    let stderr_lines = ((r0 as u32) << 24) | ((r1 as u32) << 16) | ((r2 as u32) << 8) | (r3 as u32);
    if outcome_tag > 2 || (outcome_tag == 0 && exit_code != 0) {
        return None;
    }
    Some((
        outcome_tag,
        exit_code,
        claim_idx,
        stdout_lines,
        stderr_lines,
    ))
}

/// Four-byte magic prefix (`"AEVS"`) for a 20-byte `astream-evidence` selftest wire header.
pub const CLI_SELFTEST_WIRE_MAGIC: [u8; 4] = *b"AEVS";

/// Wire format version for `astream-evidence` selftest wire headers.
pub const CLI_SELFTEST_WIRE_VERSION: u8 = 1;

/// Encode a 20-byte `astream-evidence` selftest wire header:
/// `[0..4] = b"AEVS"`, `[4] = version (1)`, `[5] = subsystem_mask` (`1..=7`), `[6..8] = 0`,
/// `[8..12] = output_bytes (BE)`, `[12..20] = digest_prefix (BE)`.
#[must_use]
pub const fn cli_encode_selftest_wire(
    subsystem_mask: u8,
    output_bytes: u32,
    digest_prefix: u64,
) -> Option<[u8; 20]> {
    let out = [
        CLI_SELFTEST_WIRE_MAGIC[0],
        CLI_SELFTEST_WIRE_MAGIC[1],
        CLI_SELFTEST_WIRE_MAGIC[2],
        CLI_SELFTEST_WIRE_MAGIC[3],
        CLI_SELFTEST_WIRE_VERSION,
        subsystem_mask,
        0,
        0,
        ((output_bytes >> 24) & 0xFF) as u8,
        ((output_bytes >> 16) & 0xFF) as u8,
        ((output_bytes >> 8) & 0xFF) as u8,
        (output_bytes & 0xFF) as u8,
        ((digest_prefix >> 56) & 0xFF) as u8,
        ((digest_prefix >> 48) & 0xFF) as u8,
        ((digest_prefix >> 40) & 0xFF) as u8,
        ((digest_prefix >> 32) & 0xFF) as u8,
        ((digest_prefix >> 24) & 0xFF) as u8,
        ((digest_prefix >> 16) & 0xFF) as u8,
        ((digest_prefix >> 8) & 0xFF) as u8,
        (digest_prefix & 0xFF) as u8,
    ];
    if subsystem_mask == 0 || subsystem_mask > 7 || output_bytes == 0 {
        return None;
    }
    Some(out)
}

/// Decode a 20-byte `astream-evidence` selftest wire header into
/// `(subsystem_mask, output_bytes, digest_prefix)`.
#[must_use]
pub const fn cli_decode_selftest_wire(buf: &[u8]) -> Option<(u8, u32, u64)> {
    let [b'A', b'E', b'V', b'S', CLI_SELFTEST_WIRE_VERSION, subsystem_mask, 0, 0, o0, o1, o2, o3, d0, d1, d2, d3, d4, d5, d6, d7, ..] =
        *buf
    else {
        return None;
    };
    let output_bytes = ((o0 as u32) << 24) | ((o1 as u32) << 16) | ((o2 as u32) << 8) | (o3 as u32);
    let digest_prefix = ((d0 as u64) << 56)
        | ((d1 as u64) << 48)
        | ((d2 as u64) << 40)
        | ((d3 as u64) << 32)
        | ((d4 as u64) << 24)
        | ((d5 as u64) << 16)
        | ((d6 as u64) << 8)
        | (d7 as u64);
    if subsystem_mask == 0 || subsystem_mask > 7 || output_bytes == 0 {
        return None;
    }
    Some((subsystem_mask, output_bytes, digest_prefix))
}

/// Four-byte magic prefix (`"AEVV"`) for a 20-byte `astream-evidence` verdict wire header.
pub const CLI_VERDICT_WIRE_MAGIC: [u8; 4] = *b"AEVV";

/// Wire format version for `astream-evidence` verdict wire headers.
pub const CLI_VERDICT_WIRE_VERSION: u8 = 1;

/// Encode a 20-byte `astream-evidence` verdict wire header:
/// `[0..4] = b"AEVV"`, `[4] = version (1)`, `[5] = exit_code` (`0..=2`), `[6..8] = 0`,
/// `[8..12] = verified_claims (BE)`, `[12..20] = manifest_digest_prefix (BE)`.
#[must_use]
pub const fn cli_encode_verdict_wire(
    exit_code: u8,
    verified_claims: u32,
    manifest_digest_prefix: u64,
) -> Option<[u8; 20]> {
    let out = [
        CLI_VERDICT_WIRE_MAGIC[0],
        CLI_VERDICT_WIRE_MAGIC[1],
        CLI_VERDICT_WIRE_MAGIC[2],
        CLI_VERDICT_WIRE_MAGIC[3],
        CLI_VERDICT_WIRE_VERSION,
        exit_code,
        0,
        0,
        ((verified_claims >> 24) & 0xFF) as u8,
        ((verified_claims >> 16) & 0xFF) as u8,
        ((verified_claims >> 8) & 0xFF) as u8,
        (verified_claims & 0xFF) as u8,
        ((manifest_digest_prefix >> 56) & 0xFF) as u8,
        ((manifest_digest_prefix >> 48) & 0xFF) as u8,
        ((manifest_digest_prefix >> 40) & 0xFF) as u8,
        ((manifest_digest_prefix >> 32) & 0xFF) as u8,
        ((manifest_digest_prefix >> 24) & 0xFF) as u8,
        ((manifest_digest_prefix >> 16) & 0xFF) as u8,
        ((manifest_digest_prefix >> 8) & 0xFF) as u8,
        (manifest_digest_prefix & 0xFF) as u8,
    ];
    if exit_code > 2 || (exit_code == 0 && verified_claims == 0) {
        return None;
    }
    Some(out)
}

/// Decode a 20-byte `astream-evidence` verdict wire header into
/// `(exit_code, verified_claims, manifest_digest_prefix)`.
#[must_use]
pub const fn cli_decode_verdict_wire(buf: &[u8]) -> Option<(u8, u32, u64)> {
    let [b'A', b'E', b'V', b'V', CLI_VERDICT_WIRE_VERSION, exit_code, 0, 0, v0, v1, v2, v3, d0, d1, d2, d3, d4, d5, d6, d7, ..] =
        *buf
    else {
        return None;
    };
    let verified_claims =
        ((v0 as u32) << 24) | ((v1 as u32) << 16) | ((v2 as u32) << 8) | (v3 as u32);
    let manifest_digest_prefix = ((d0 as u64) << 56)
        | ((d1 as u64) << 48)
        | ((d2 as u64) << 40)
        | ((d3 as u64) << 32)
        | ((d4 as u64) << 24)
        | ((d5 as u64) << 16)
        | ((d6 as u64) << 8)
        | (d7 as u64);
    if exit_code > 2 || (exit_code == 0 && verified_claims == 0) {
        return None;
    }
    Some((exit_code, verified_claims, manifest_digest_prefix))
}

fn main() -> ExitCode {
    // `args_os`: an argument that is not UTF-8 is a usage error, not a panic.
    let mut args = Vec::new();
    for raw in std::env::args_os().skip(1) {
        match raw.into_string() {
            Ok(s) => args.push(s),
            Err(_) => return usage("an argument is not valid UTF-8"),
        }
    }
    let Some((cmd, rest)) = args.split_first() else {
        return usage("missing subcommand");
    };
    // The flags each subcommand takes. Anything else is refused, never ignored:
    // a dropped `--root` value or a misspelled `--write` would otherwise run
    // against `.` or print instead of writing, and still exit 0.
    let flags: &[&str] = match cmd.as_str() {
        "gate" | "run" => &["--root"],
        "render" => &["--root", "--write"],
        "selftest" => &[],
        other => return usage(&format!("unknown subcommand {other:?}")),
    };
    let opts = match Opts::parse(rest, flags) {
        Ok(o) => o,
        Err(e) => return usage(&e),
    };
    match cmd.as_str() {
        "gate" => cmd_gate(&opts.root),
        "render" => cmd_render(&opts.root, opts.write),
        "run" => cmd_run(&opts.root),
        _ => cmd_selftest(),
    }
}

fn say(msg: &str) {
    println!("{msg}");
}

fn usage(msg: &str) -> ExitCode {
    eprintln!("astream-evidence: {msg}\n{USAGE}");
    ExitCode::from(2)
}

struct Opts {
    root: PathBuf,
    write: bool,
}

impl Opts {
    fn parse(args: &[String], flags: &[&str]) -> Result<Opts, String> {
        let mut opts = Opts {
            root: PathBuf::from("."),
            write: false,
        };
        let mut rest = args;
        while let [a, tail @ ..] = rest {
            let mut allowed = false;
            let mut fl_rest = flags;
            while let [fl, fl_tail @ ..] = fl_rest {
                if fl.as_bytes() == a.as_bytes() {
                    allowed = true;
                    break;
                }
                fl_rest = fl_tail;
            }
            if !allowed {
                return Err(format!("unexpected argument {a:?}"));
            }
            if a.as_bytes() == b"--root" {
                let [dir, after_dir @ ..] = tail else {
                    return Err("--root expects a directory".to_string());
                };
                opts.root = PathBuf::from(dir.as_str());
                rest = after_dir;
            } else {
                opts.write = true;
                rest = tail;
            }
        }
        Ok(opts)
    }
}

fn cmd_gate(root: &Path) -> ExitCode {
    // A mis-pointed `--root` (typo, off-by-one `..`) must fail loudly, never
    // report PASS over an empty or foreign tree: the lints find nothing where
    // there is nothing, which is a vacuous green, not a verdict.
    if let Err(e) = gate::check_root(root) {
        eprintln!("astream-evidence gate: refusing to run: {e}");
        return ExitCode::from(2);
    }
    let (violations, caches) = gate::run_gate_reporting(root);
    // NAME every cache directory the walk skipped. A `CACHEDIR.TAG` is how a
    // build tree is recognized whatever it is called — and it is also one file
    // anybody could create, so the exclusion is reported rather than silent: a
    // directory hidden from every lint should be readable in the gate's own
    // output, not discoverable only by reading the walker.
    for dir in &caches {
        say(&format!(
            "astream-evidence gate: skipped {} (CACHEDIR.TAG: a tool cache, not source)",
            dir.display()
        ));
    }
    if violations.is_empty() {
        say(&format!(
            "astream-evidence gate: PASS (0 findings) under {}",
            root.display()
        ));
        ExitCode::SUCCESS
    } else {
        eprintln!(
            "astream-evidence gate: FAIL ({} findings)",
            violations.len()
        );
        for v in &violations {
            eprintln!("  {v}");
        }
        ExitCode::from(1)
    }
}

fn cmd_render(root: &Path, write: bool) -> ExitCode {
    let manifest_path = root.join("evidence").join("manifest.toml");
    let m = match Manifest::load(&manifest_path) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("{e}");
            return ExitCode::from(1);
        }
    };
    let block = render::render_block(&m);
    if !write {
        say(&block);
        return ExitCode::SUCCESS;
    }
    let readme_path = root.join("README.md");
    let readme_bytes = match std::fs::read(&readme_path) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("read {}: {e}", readme_path.display());
            return ExitCode::from(1);
        }
    };
    let readme = match core::str::from_utf8(&readme_bytes) {
        Ok(text) => text,
        Err(e) => {
            eprintln!("read {}: {e}", readme_path.display());
            return ExitCode::from(1);
        }
    };
    match render::splice(readme, &block) {
        Ok(updated) => match std::fs::write(&readme_path, updated) {
            Ok(()) => {
                say(&format!(
                    "rendered evidence block into {}",
                    readme_path.display()
                ));
                ExitCode::SUCCESS
            }
            Err(e) => {
                eprintln!("write {}: {e}", readme_path.display());
                ExitCode::from(1)
            }
        },
        Err(e) => {
            eprintln!("{e}");
            ExitCode::from(1)
        }
    }
}

fn cmd_run(root: &Path) -> ExitCode {
    let manifest_path = root.join("evidence").join("manifest.toml");
    let m = match Manifest::load(&manifest_path) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("{e}");
            return ExitCode::from(1);
        }
    };
    // Counted per claim, so each is at most `m.claim.len()`: the saturating adds
    // below never engage; they only make the counting total.
    let mut failed: usize = 0;
    let mut skipped: usize = 0;
    let mut passed: usize = 0;
    say(&format!("astream-evidence run: {} claim(s)", m.claim.len()));
    // Each result is printed as its claim finishes, not after the whole run: a
    // claim that hangs then leaves every earlier result on screen (and in a CI log
    // cut off at its timeout), and the last line printed says how far it got.
    for c in &m.claim {
        let r = runner::run_claim(root, c);
        let mark = if r.skipped {
            skipped = skipped.saturating_add(1);
            "SKIP"
        } else if r.passed {
            passed = cli_passed_advance(passed as u64, passed.saturating_add(1) as u64) as usize;
            "PASS"
        } else {
            failed = failed.saturating_add(1);
            "FAIL"
        };
        let sha_prefix = sha_prefix(&r.stdout_sha);
        say(&format!(
            "  [{mark}] {} (exit={:?} sha={}) {}",
            r.id, r.exit_code, sha_prefix, r.note
        ));
        print_tail("stdout", &r.stdout_tail);
        print_tail("stderr", &r.stderr_tail);
    }
    if cli_all_claims_passed(failed) {
        // Every claim was skipped or passed, so the passed count IS the verified
        // count (it was `len - skipped`, a subtraction with nothing to bound it).
        let verified = passed;
        if skipped == 0 {
            say(&format!("all {verified} claim(s) verified"));
        } else {
            say(&format!(
                "all {verified} claim(s) verified ({skipped} skipped on this platform)"
            ));
        }
        ExitCode::SUCCESS
    } else {
        eprintln!("{failed} claim(s) failed");
        ExitCode::from(1)
    }
}

/// The first 12 characters of a claim's stdout digest for its result line (all of
/// it when shorter). The digest is hex; a non-ASCII value that 12 bytes would cut
/// inside a character is shown whole rather than panicking.
fn sha_prefix(sha: &str) -> &str {
    match sha.get(..12) {
        Some(prefix) => prefix,
        None => sha,
    }
}

/// A failing claim's output tail, delimited and indented under its FAIL line.
fn print_tail(stream: &str, tail: &str) {
    if tail.is_empty() {
        return;
    }
    say(&format!(
        "      --- {stream} (last {} lines at most) ---",
        runner::FAILURE_TAIL_LINES
    ));
    for line in tail.lines() {
        say(&format!("      | {line}"));
    }
}

fn cmd_selftest() -> ExitCode {
    // Deterministic output; its hash is pinned in evidence/manifest.toml to
    // demonstrate output-drift detection on a deterministic command.
    say("astream-evidence selftest: wire+gate+render operational");
    ExitCode::SUCCESS
}

#[cfg(test)]
mod tests {
    use super::{
        cli_decode_claim_wire, cli_decode_gate_wire, cli_decode_selftest_wire,
        cli_decode_summary_wire, cli_decode_verdict_wire, cli_encode_claim_wire,
        cli_encode_gate_wire, cli_encode_selftest_wire, cli_encode_summary_wire,
        cli_encode_verdict_wire, sha_prefix,
    };

    #[test]
    fn sha_prefix_is_12_chars_or_the_whole_digest_and_never_panics() {
        let full = "0123456789abcdef0123456789abcdef";
        assert_eq!(sha_prefix(full), "0123456789ab");
        assert_eq!(sha_prefix("abc"), "abc");
        assert_eq!(sha_prefix(""), "");
        assert_eq!(sha_prefix("0123456789ab"), "0123456789ab");
        // 11 ASCII bytes then a 2-byte char: byte 12 is inside it. The old
        // `&sha[..12]` panicked here; the prefix is now the whole value.
        let odd = "0123456789a\u{e9}xyz";
        assert_eq!(sha_prefix(odd), odd);
    }

    #[test]
    fn cli_wire_codecs_round_trip() {
        let s = cli_encode_summary_wire(1, true, 0, 12, 0, 2).expect("valid summary");
        assert_eq!(cli_decode_summary_wire(&s), Some((1, true, 0, 12, 0, 2)));
        assert!(cli_encode_summary_wire(2, true, 0, 1, 0, 0).is_none());

        let g = cli_encode_gate_wire(0, 0, 3).expect("valid gate");
        assert_eq!(cli_decode_gate_wire(&g), Some((0, 0, 3)));
        assert!(cli_encode_gate_wire(0, 1, 0).is_none());

        let c = cli_encode_claim_wire(0, 0, 5, 10, 0).expect("valid claim");
        assert_eq!(cli_decode_claim_wire(&c), Some((0, 0, 5, 10, 0)));
        assert!(cli_encode_claim_wire(0, 1, 5, 10, 0).is_none());

        let st = cli_encode_selftest_wire(7, 56, 0x0123_4567_89ab_cdef).expect("valid selftest");
        assert_eq!(
            cli_decode_selftest_wire(&st),
            Some((7, 56, 0x0123_4567_89ab_cdef))
        );
        assert!(cli_encode_selftest_wire(0, 56, 1).is_none());

        let vw = cli_encode_verdict_wire(0, 12, 0xfedc_ba98_7654_3210).expect("valid verdict");
        assert_eq!(
            cli_decode_verdict_wire(&vw),
            Some((0, 12, 0xfedc_ba98_7654_3210))
        );
        assert!(cli_encode_verdict_wire(0, 0, 1).is_none());
        assert!(cli_encode_verdict_wire(3, 1, 1).is_none());
    }
}
