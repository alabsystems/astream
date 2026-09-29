//! `astream-evidence` — the honesty-harness CLI.
//!
//! Subcommands:
//! * `gate [--root DIR]`     — run the merge-gate lints; exit 1 on any finding,
//!   exit 2 if DIR is not an astream workspace root (nothing is ever "gated" vacuously).
//! * `render [--write] [--root DIR]` — render the evidence table from the manifest.
//! * `run [--root DIR]`      — run every claim's command and report pass/fail.
//! * `selftest`              — print a deterministic line (pinned by hash in the manifest).

use astream_evidence::{gate, manifest::Manifest, render, runner};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

const USAGE: &str = "usage: astream-evidence <gate|render [--write]|run|selftest> [--root DIR]";

fn main() -> ExitCode {
    // `args_os`: an argument that is not UTF-8 is a usage error, not a panic.
    let Some(args) = std::env::args_os()
        .skip(1)
        .map(|a| a.into_string().ok())
        .collect::<Option<Vec<String>>>()
    else {
        return usage("an argument is not valid UTF-8");
    };
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
        let mut it = args.iter();
        while let Some(a) = it.next() {
            match a.as_str() {
                f if !flags.contains(&f) => return Err(format!("unexpected argument {a:?}")),
                "--root" => {
                    let dir = it.next().ok_or("--root expects a directory")?;
                    opts.root = PathBuf::from(dir);
                }
                _ => opts.write = true,
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
        println!(
            "astream-evidence gate: skipped {} (CACHEDIR.TAG: a tool cache, not source)",
            dir.display()
        );
    }
    if violations.is_empty() {
        println!(
            "astream-evidence gate: PASS (0 findings) under {}",
            root.display()
        );
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
        println!("{block}");
        return ExitCode::SUCCESS;
    }
    let readme_path = root.join("README.md");
    let readme = match std::fs::read_to_string(&readme_path) {
        Ok(text) => text,
        Err(e) => {
            eprintln!("read {}: {e}", readme_path.display());
            return ExitCode::from(1);
        }
    };
    match render::splice(&readme, &block) {
        Ok(updated) => match std::fs::write(&readme_path, updated) {
            Ok(()) => {
                println!("rendered evidence block into {}", readme_path.display());
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
    let mut failed = 0;
    let mut skipped = 0;
    println!("astream-evidence run: {} claim(s)", m.claim.len());
    // Each result is printed as its claim finishes, not after the whole run: a
    // claim that hangs then leaves every earlier result on screen (and in a CI log
    // cut off at its timeout), and the last line printed says how far it got.
    for c in &m.claim {
        let r = runner::run_claim(root, c);
        let mark = if r.skipped {
            skipped += 1;
            "SKIP"
        } else if r.passed {
            "PASS"
        } else {
            failed += 1;
            "FAIL"
        };
        let sha_prefix = &r.stdout_sha[..r.stdout_sha.len().min(12)];
        println!(
            "  [{mark}] {} (exit={:?} sha={}) {}",
            r.id, r.exit_code, sha_prefix, r.note
        );
        print_tail("stdout", &r.stdout_tail);
        print_tail("stderr", &r.stderr_tail);
    }
    if failed == 0 {
        let verified = m.claim.len() - skipped;
        if skipped == 0 {
            println!("all {verified} claim(s) verified");
        } else {
            println!("all {verified} claim(s) verified ({skipped} skipped on this platform)");
        }
        ExitCode::SUCCESS
    } else {
        eprintln!("{failed} claim(s) failed");
        ExitCode::from(1)
    }
}

/// A failing claim's output tail, delimited and indented under its FAIL line.
fn print_tail(stream: &str, tail: &str) {
    if tail.is_empty() {
        return;
    }
    println!(
        "      --- {stream} (last {} lines at most) ---",
        runner::FAILURE_TAIL_LINES
    );
    for line in tail.lines() {
        println!("      | {line}");
    }
}

fn cmd_selftest() -> ExitCode {
    // Deterministic output; its hash is pinned in evidence/manifest.toml to
    // demonstrate output-drift detection on a deterministic command.
    println!("astream-evidence selftest: wire+gate+render operational");
    ExitCode::SUCCESS
}
