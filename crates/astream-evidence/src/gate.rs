//! The merge gate. Each lint maps to a confirmed failure mode of the predecessor and
//! turns it into a hard, machine-checkable rejection:
//!
//! * `no-git-deps`        — the predecessor pinned 404 git revisions; the public repo
//!   would not build. astream forbids git dependencies — in every dependency
//!   table, in `[patch]` / `[replace]` redirects, and as a `git+` source in
//!   `Cargo.lock` (the ground truth for what cargo fetches).
//! * `undeclared-cfg`     — a templating typo (`cloud-dropbox` ->
//!   `cloud-Andrew Yates`) silently dead-coded a module.
//!   A cfg-feature reference to an undeclared feature
//!   is rejected.
//! * `drift-marker`       — incomplete / session-drift checkpoints landed on
//!   main. Those markers, and unlinked task notes, are
//!   rejected.
//! * `tautology`          — the predecessor had "proofs" of `8 + 4 + 4 == 16`. A test
//!   whose every assertion is a constant expression is
//!   rejected.
//! * `verify-isolation`   — verification tooling broke the substrate build.
//!   A `verify*` workspace member is rejected.
//! * `doc-tamper`         — the README cited a status file that did not exist.
//!   The generated evidence block must match the
//!   manifest render exactly.
//! * `manifest-integrity` — the predecessor counted decorative "proofs" as rigor and
//!   cited an evidence file that did not exist. A claim
//!   backed by a known no-op program (a denylist:
//!   `true`, `:`, `echo`, `printf`, `cat`, `head`,
//!   `tail`), whose command does not fit its kind
//!   (`test` must run `cargo test`, `build` must run
//!   `cargo build`/`check`, `selftest` must pin a hash),
//!   or citing a path / cargo target that is absent is
//!   rejected. This binds the manifest to reality at
//!   *gate* time, not only when `run` executes it. It
//!   NARROWS the decorative-proof class — an exit-0
//!   program outside the denylist still passes the gate
//!   (and is caught by `run` only if its kind's pass
//!   condition bites).
//!
//! The lints are deliberately text-based and heuristic (the honest residual
//! gap: a determined author can still write a tautology that technically
//! touches a symbol). They are the enforcement spine, not a correctness proof.

use crate::manifest::{cargo_subcommand, command_program, is_env_assignment, Manifest};
use crate::needles;
use crate::render;
use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};

/// A single gate finding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Violation {
    pub lint: String,
    pub path: String,
    pub detail: String,
}

impl std::fmt::Display for Violation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}] {}: {}", self.lint, self.path, self.detail)
    }
}

/// Directories never scanned, at any depth: build output and VCS metadata.
///
/// A NAME is not enough on its own, which is why [`is_cache_dir`] exists beside
/// this list: a build directory can carry another name (`target` as a symlink to
/// `target.noindex`, a custom `CARGO_TARGET_DIR`), and symlinks are never
/// followed here. Walked as source, its compiled binaries would report their
/// marker words as this tree's violations.
const SKIP_DIRS: &[&str] = &["target", ".git"];

/// The Cache Directory Tagging Specification signature. A directory holding a
/// `CACHEDIR.TAG` that begins with this exact line is a tool's cache, not source
/// — cargo writes one into every target directory, whatever it is named and
/// wherever `CARGO_TARGET_DIR` puts it.
const CACHEDIR_SIGNATURE: &str = "Signature: 8a477f597d28d172789f06886806bc55";

/// Whether `dir` is a tool cache, by the standard tag rather than by its name.
///
/// This is deliberately NOT a bare-name rule (see [`SKIP_DIRS`]). It is also
/// not silent — every directory skipped this way is counted and NAMED in the
/// gate's summary, because a lint that can be switched off by creating one file
/// must at minimum say out loud that it was. Planting a tag to hide source from
/// the gate is then a visible act in the gate's own output, not a quiet bypass.
fn is_cache_dir(dir: &Path) -> bool {
    fs::read_to_string(dir.join("CACHEDIR.TAG"))
        .map(|text| text.starts_with(CACHEDIR_SIGNATURE))
        .unwrap_or(false)
}

/// Named hidden directories that hold TOOL STATE, never source, skipped at any
/// depth: VCS internals, an editor's workspace, a direnv/Nix cache, and an
/// agent harness's `.claude/worktrees/…`, which can hold whole checkouts of
/// this repo whose fixtures would otherwise be reported as this tree's
/// violations. The list is deliberately NAMED, not "every name beginning with
/// a dot": a dot-directory is an ordinary place to vendor a path dependency
/// (`helper = { path = "../.vendor/helper" }`), cargo compiles it, and
/// excluding every dot-directory would let a real, built module escape every
/// lint — the dead-code-by-typo class this gate exists to stop.
const SKIP_HIDDEN: &[&str] = &[
    ".git", ".jj", ".hg", ".svn", ".claude", ".idea", ".vscode", ".direnv",
];

/// The gate's own intentional-violation test data, skipped ONLY at this exact
/// path under the scanned root. A directory merely *named* `fixtures`
/// anywhere else (`crates/x/src/fixtures/`, `docs/fixtures/`) is scanned like
/// any other — a bare-name exclusion would be a one-`mkdir` bypass of every lint.
const OWN_FIXTURES: &str = "crates/astream-evidence/tests/fixtures";

fn rel(root: &Path, p: &Path) -> String {
    p.strip_prefix(root).unwrap_or(p).display().to_string()
}

fn has_ext(p: &Path, ext: &str) -> bool {
    p.extension().and_then(|e| e.to_str()) == Some(ext)
}

fn is_cargo_manifest(p: &Path) -> bool {
    p.file_name().and_then(|n| n.to_str()) == Some("Cargo.toml")
}

fn is_cargo_lockfile(p: &Path) -> bool {
    p.file_name().and_then(|n| n.to_str()) == Some("Cargo.lock")
}

/// Read a text file for scanning. Non-UTF-8 bytes are replaced, never used as
/// an excuse to skip the file: `read_to_string` fails on a single stray
/// Latin-1 byte, and an empty scan would let one byte hide every marker.
fn read_text_lossy(p: &Path) -> String {
    fs::read(p)
        .map(|bytes| String::from_utf8_lossy(&bytes).into_owned())
        .unwrap_or_default()
}

/// Recursively list files under `root`, plus the cache directories the walk
/// skipped by their `CACHEDIR.TAG` — returned so the caller can NAME them rather
/// than let a tag-shaped exclusion be invisible.
///
/// Skipped: [`SKIP_DIRS`], the NAMED tool-state directories of [`SKIP_HIDDEN`],
/// and the gate's [`OWN_FIXTURES`]. Any OTHER dot-directory is scanned exactly
/// like source, because a path dependency can live in one and cargo compiles
/// it. Symlinks are never followed: a link to `..`, `/`, or `$HOME` would
/// re-walk the tree until `PATH_MAX` or pull out-of-tree files into the scan
/// and report them as this tree's violations.
fn collect_files_reporting(root: &Path) -> (Vec<PathBuf>, Vec<PathBuf>) {
    let own_fixtures = root.join(OWN_FIXTURES);
    let mut out = Vec::new();
    let mut caches = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let entries = match fs::read_dir(&dir) {
            Ok(e) => e,
            Err(_) => continue,
        };
        for entry in entries.flatten() {
            let path = entry.path();
            // `DirEntry::file_type` does not follow symlinks (`Path::is_dir` does).
            let ft = match entry.file_type() {
                Ok(ft) => ft,
                Err(_) => continue,
            };
            if ft.is_symlink() {
                continue;
            }
            if ft.is_dir() {
                let name = entry.file_name().to_string_lossy().to_string();
                if SKIP_DIRS.contains(&name.as_str())
                    || SKIP_HIDDEN.contains(&name.as_str())
                    || path == own_fixtures
                {
                    continue;
                }
                if is_cache_dir(&path) {
                    caches.push(path);
                    continue;
                }
                stack.push(path);
            } else {
                out.push(path);
            }
        }
    }
    (out, caches)
}

/// Is `root` something the gate can meaningfully judge? The lints report
/// nothing over an empty or foreign directory, so a mistyped `--root` would
/// otherwise be a vacuous PASS. The CLI refuses to run unless `root` is a
/// directory holding a workspace `Cargo.toml`, the evidence manifest, and the
/// README the doc-tamper lint compares against. (Library callers may still run
/// [`run_gate`] over a bare fixture subtree; that is a deliberate test mode.)
pub fn check_root(root: &Path) -> Result<(), String> {
    if !root.is_dir() {
        return Err(format!("{} is not a directory", root.display()));
    }
    for required in ["Cargo.toml", "evidence/manifest.toml", "README.md"] {
        if !root.join(required).is_file() {
            return Err(format!(
                "{} is not an astream workspace root: {required} is missing",
                root.display()
            ));
        }
    }
    Ok(())
}

/// Run all lints over a tree rooted at `root`.
pub fn run_gate(root: &Path) -> Vec<Violation> {
    run_gate_reporting(root).0
}

/// [`run_gate`], plus the cache directories the walk skipped by their
/// `CACHEDIR.TAG`, for a caller that means to NAME them. A skip nobody can see
/// is a lint nobody can trust.
pub fn run_gate_reporting(root: &Path) -> (Vec<Violation>, Vec<PathBuf>) {
    let (files, caches) = collect_files_reporting(root);
    let mut v = Vec::new();
    v.extend(lint_no_git_deps(root, &files));
    v.extend(lint_undeclared_cfg(root, &files));
    v.extend(lint_drift_markers(root, &files));
    v.extend(lint_tautological_tests(root, &files));
    v.extend(lint_verify_isolation(root, &files));
    v.extend(lint_doc_tamper(root));
    v.extend(lint_manifest_integrity(root, &files));
    (v, caches)
}

// --- no-git-deps ----------------------------------------------------------

/// Every dependency in `text` (any kind/section) that is specified as a git
/// dependency, by name. Parses TOML, so quote style and spacing (`git = '...'`,
/// `git  =  "..."`, all resolved by cargo as git deps) cannot hide one.
///
/// Scanned: `[dependencies]`, `[dev-dependencies]`, `[build-dependencies]`,
/// `[workspace.dependencies]`, `[target.*.<those>]`, every `[patch.<source>]`
/// table (the canonical way to redirect a crates.io crate to a git checkout),
/// and the deprecated `[replace]` table.
fn manifest_git_deps(text: &str) -> Vec<String> {
    use toml::value::Table;
    let mut hits = Vec::new();
    let val = match text.parse::<toml::Value>() {
        Ok(v) => v,
        Err(_) => return hits, // unparseable: cargo cannot resolve it either
    };
    fn scan(tbl: &Table, hits: &mut Vec<String>) {
        for (name, spec) in tbl {
            if spec
                .as_table()
                .map(|t| t.contains_key("git"))
                .unwrap_or(false)
            {
                hits.push(name.clone());
            }
        }
    }
    let dep_sects = ["dependencies", "dev-dependencies", "build-dependencies"];
    for sect in dep_sects {
        if let Some(t) = val.get(sect).and_then(|v| v.as_table()) {
            scan(t, &mut hits);
        }
    }
    if let Some(ws) = val
        .get("workspace")
        .and_then(|v| v.get("dependencies"))
        .and_then(|v| v.as_table())
    {
        scan(ws, &mut hits);
    }
    if let Some(targets) = val.get("target").and_then(|v| v.as_table()) {
        for (_, t) in targets {
            for sect in dep_sects {
                if let Some(d) = t.get(sect).and_then(|v| v.as_table()) {
                    scan(d, &mut hits);
                }
            }
        }
    }
    // `[patch.crates-io] foo = { git = ... }` (any source name) and `[replace]`.
    if let Some(patch) = val.get("patch").and_then(|v| v.as_table()) {
        for (_, redirects) in patch {
            if let Some(t) = redirects.as_table() {
                scan(t, &mut hits);
            }
        }
    }
    if let Some(t) = val.get("replace").and_then(|v| v.as_table()) {
        scan(t, &mut hits);
    }
    hits
}

/// Every `[[package]]` in a `Cargo.lock` whose `source` is a git URL. The
/// lockfile is what cargo actually fetches, so it catches a git dependency
/// however it entered the graph (a transitive dependency's manifest included).
fn lockfile_git_sources(text: &str) -> Vec<String> {
    let mut hits = Vec::new();
    let val = match text.parse::<toml::Value>() {
        Ok(v) => v,
        Err(_) => return hits,
    };
    if let Some(packages) = val.get("package").and_then(|v| v.as_array()) {
        for p in packages {
            let is_git = p
                .get("source")
                .and_then(|s| s.as_str())
                .map(|s| s.starts_with("git+"))
                .unwrap_or(false);
            if is_git {
                let name = p.get("name").and_then(|n| n.as_str()).unwrap_or("?");
                hits.push(name.to_string());
            }
        }
    }
    hits
}

fn lint_no_git_deps(root: &Path, files: &[PathBuf]) -> Vec<Violation> {
    let mut out = Vec::new();
    for f in files.iter().filter(|f| is_cargo_manifest(f)) {
        let text = read_text_lossy(f);
        for name in manifest_git_deps(&text) {
            out.push(Violation {
                lint: "no-git-deps".to_string(),
                path: rel(root, f),
                detail: format!(
                    "dependency {name:?} is a git dependency (forbidden — breaks reproducible build)"
                ),
            });
        }
    }
    for f in files.iter().filter(|f| is_cargo_lockfile(f)) {
        let text = read_text_lossy(f);
        for name in lockfile_git_sources(&text) {
            out.push(Violation {
                lint: "no-git-deps".to_string(),
                path: rel(root, f),
                detail: format!(
                    "locked package {name:?} resolves to a git source (forbidden — breaks reproducible build)"
                ),
            });
        }
    }
    out
}

// --- undeclared-cfg -------------------------------------------------------

fn declared_features(cargo_toml: &Path) -> HashSet<String> {
    let mut set = HashSet::new();
    let text = fs::read_to_string(cargo_toml).unwrap_or_default();
    let Ok(val) = text.parse::<toml::Value>() else {
        return set;
    };
    // `dep:NAME` anywhere in [features] suppresses NAME's implicit feature.
    let mut dep_prefixed = HashSet::new();
    if let Some(tbl) = val.get("features").and_then(|v| v.as_table()) {
        for (k, members) in tbl {
            set.insert(k.clone());
            for m in members.as_array().into_iter().flatten() {
                if let Some(dep) = m.as_str().and_then(|s| s.strip_prefix("dep:")) {
                    dep_prefixed.insert(dep.to_string());
                }
            }
        }
    }
    // Otherwise an optional dependency implicitly declares a like-named
    // feature, whether it is a normal or build dependency, target-specific or not.
    let sects = ["dependencies", "build-dependencies"];
    let targets = val.get("target").and_then(|v| v.as_table());
    let tables = sects
        .iter()
        .filter_map(|s| val.get(*s))
        .chain(
            targets
                .into_iter()
                .flat_map(|t| t.values())
                .flat_map(|t| sects.iter().filter_map(|s| t.get(*s))),
        )
        .filter_map(|v| v.as_table());
    for deps in tables {
        for (name, spec) in deps {
            let optional = spec
                .get("optional")
                .and_then(|o| o.as_bool())
                .unwrap_or(false);
            if optional && !dep_prefixed.contains(name) {
                set.insert(name.clone());
            }
        }
    }
    set
}

fn nearest_features<'a>(
    file: &Path,
    crates: &'a [(PathBuf, HashSet<String>)],
) -> Option<&'a HashSet<String>> {
    let mut best: Option<(&PathBuf, &HashSet<String>)> = None;
    for (dir, feats) in crates {
        if file.starts_with(dir) {
            let better = match best {
                None => true,
                Some((bd, _)) => dir.components().count() > bd.components().count(),
            };
            if better {
                best = Some((dir, feats));
            }
        }
    }
    best.map(|(_, f)| f)
}

/// Every feature name referenced by a `cfg(...)` feature predicate in `text`.
/// Matches the word, optional whitespace, `=`, optional whitespace, then the
/// quoted name. Whitespace means ANY ASCII whitespace — spaces, tabs, and
/// newlines — because the attribute grammar accepts a line break around the
/// `=` just as readily, and a reference that hid behind one was invisible
/// (the dead-code-by-typo class). (This doc deliberately avoids writing the
/// literal trigger, which would make the gate flag its own source — the same
/// reason the markers use `needles`.)
///
/// The occurrence must sit in a PREDICATE position: the nearest preceding
/// non-whitespace byte has to be `(` or `,`, which is what the predicate
/// always follows inside `cfg(…)` / `all(…, …)` / `any(…, …)`. Ordinary code
/// that happens to bind a variable of that name across a line break is not a
/// cfg reference, and the lint is a hard blocker with no allow mechanism, so a
/// false positive is an unexplainable merge stop.
fn feature_names(text: &str) -> Vec<String> {
    let b = text.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while let Some(p) = text[i..].find("feature") {
        let start = i + p;
        let mut k = start;
        while k > 0 && b[k - 1].is_ascii_whitespace() {
            k -= 1;
        }
        if k == 0 || (b[k - 1] != b'(' && b[k - 1] != b',') {
            i = start + "feature".len();
            continue;
        }
        let mut j = start + "feature".len();
        while j < b.len() && b[j].is_ascii_whitespace() {
            j += 1;
        }
        if j < b.len() && b[j] == b'=' {
            j += 1;
            while j < b.len() && b[j].is_ascii_whitespace() {
                j += 1;
            }
            if j < b.len() && b[j] == b'"' {
                j += 1;
                if let Some(end) = text[j..].find('"') {
                    out.push(text[j..j + end].to_string());
                    i = j + end + 1;
                    continue;
                }
            }
        }
        i = start + "feature".len();
    }
    out
}

fn lint_undeclared_cfg(root: &Path, files: &[PathBuf]) -> Vec<Violation> {
    let crates: Vec<(PathBuf, HashSet<String>)> = files
        .iter()
        .filter(|f| is_cargo_manifest(f))
        .filter_map(|f| f.parent().map(|d| (d.to_path_buf(), declared_features(f))))
        .collect();

    let mut out = Vec::new();
    for f in files.iter().filter(|f| has_ext(f, "rs")) {
        let text = read_text_lossy(f);
        let feats = nearest_features(f, &crates);
        for name in feature_names(&text) {
            let declared = feats.map(|s| s.contains(&name)).unwrap_or(false);
            if !declared {
                out.push(Violation {
                    lint: "undeclared-cfg".to_string(),
                    path: rel(root, f),
                    detail: format!(
                        "cfg references undeclared feature {name:?} (not in the crate's Cargo.toml) \
                         — the class of bug that dead-coded a whole module of the predecessor"
                    ),
                });
            }
        }
    }
    out
}

// --- drift-marker ---------------------------------------------------------

fn lint_drift_markers(root: &Path, files: &[PathBuf]) -> Vec<Violation> {
    let task = needles::task_marker();
    let fixme = needles::fixme_marker();
    let incomplete = needles::incomplete_marker();
    let drift = needles::drift_marker();
    let extras = needles::extra_drift_markers();

    // Notes hide in more than .rs/.md/.toml: plain-text, YAML, shell, JSON, and
    // extension-less NOTES files all ship a checkpoint marker just as well.
    // Files are read lossily (see `read_text_lossy`): a stray non-UTF-8 byte
    // must never turn a note into an unscanned one.
    let scan = |f: &&PathBuf| {
        has_ext(f, "rs")
            || has_ext(f, "md")
            || has_ext(f, "toml")
            || has_ext(f, "txt")
            || has_ext(f, "yml")
            || has_ext(f, "yaml")
            || has_ext(f, "sh")
            || has_ext(f, "json")
            || f.extension().is_none()
    };

    let mut out = Vec::new();
    for f in files.iter().filter(scan) {
        let text = read_text_lossy(f);
        for (i, line) in text.lines().enumerate() {
            if line.contains(&incomplete) {
                out.push(Violation {
                    lint: "drift-marker".to_string(),
                    path: rel(root, f),
                    detail: format!("line {}: incomplete-checkpoint marker", i + 1),
                });
            }
            if line.contains(&drift) {
                out.push(Violation {
                    lint: "drift-marker".to_string(),
                    path: rel(root, f),
                    detail: format!("line {}: session-drift marker", i + 1),
                });
            }
            for tag in &extras {
                if line.contains(tag.as_str()) {
                    out.push(Violation {
                        lint: "drift-marker".to_string(),
                        path: rel(root, f),
                        detail: format!("line {}: work-in-progress checkpoint marker", i + 1),
                    });
                }
            }
            for kw in [&task, &fixme] {
                // Every occurrence needs its own link, e.g. `(#123)` with a
                // NUMERIC issue; `(#)` or `(#notanissue)` does not count.
                let unlinked = line.match_indices(kw.as_str()).any(|(p, _)| {
                    let after = &line[p + kw.len()..];
                    let linked = after
                        .trim_start()
                        .strip_prefix("(#")
                        .map(|r| {
                            let num: String = r.chars().take_while(|c| *c != ')').collect();
                            !num.is_empty() && num.chars().all(|c| c.is_ascii_digit())
                        })
                        .unwrap_or(false);
                    !linked
                });
                if unlinked {
                    out.push(Violation {
                        lint: "drift-marker".to_string(),
                        path: rel(root, f),
                        detail: format!(
                            "line {}: task note without an issue link (use the form NAME(#123))",
                            i + 1
                        ),
                    });
                }
            }
        }
    }
    out
}

// --- tautology ------------------------------------------------------------

fn matching_delim(bytes: &[u8], open: usize, open_b: u8, close_b: u8) -> Option<usize> {
    let mut depth = 0i32;
    let mut i = open;
    while i < bytes.len() {
        let c = bytes[i];
        if c == open_b {
            depth += 1;
        } else if c == close_b {
            depth -= 1;
            if depth == 0 {
                return Some(i);
            }
        }
        i += 1;
    }
    None
}

/// Primitive type names: in `(8 + 4 + 4) as u32` the cast target is not a
/// symbol under test, any more than the `as` keyword is.
const PRIMITIVE_TYPES: &[&str] = &[
    "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize", "f32",
    "f64", "bool", "char",
];

/// Length of the string literal starting at `b[i]` (which must be `"`), or
/// `None` if unterminated. Handles `\"` escapes.
fn string_literal_len(b: &[u8], i: usize) -> Option<usize> {
    let mut j = i + 1;
    while j < b.len() {
        match b[j] {
            b'\\' => j += 2,
            b'"' => return Some(j + 1 - i),
            _ => j += 1,
        }
    }
    None
}

/// Length of the raw string literal whose `#`s or `"` start at `b[i]`
/// (`r"..."`, `r#"..."#`), or `None` if unterminated.
fn raw_string_len(b: &[u8], i: usize) -> Option<usize> {
    let mut hashes = 0;
    while i + hashes < b.len() && b[i + hashes] == b'#' {
        hashes += 1;
    }
    if i + hashes >= b.len() || b[i + hashes] != b'"' {
        return None;
    }
    let mut j = i + hashes + 1;
    while j < b.len() {
        if b[j] == b'"'
            && b[j + 1..]
                .iter()
                .take(hashes)
                .filter(|c| **c == b'#')
                .count()
                == hashes
        {
            return Some(j + 1 + hashes - i);
        }
        j += 1;
    }
    None
}

/// Length of the char literal starting at `b[i]` (which must be `'`) —
/// `'x'`, `'\n'`, `'\u{1F}'`, a multi-byte char — or `None` if this quote
/// opens a lifetime (`'a`) rather than a literal.
fn char_literal_len(b: &[u8], i: usize) -> Option<usize> {
    let mut j = i + 1;
    if j >= b.len() {
        return None;
    }
    if b[j] == b'\\' {
        j += 1;
        // Escape: `\n`, `\'`, `\\`, `\x41`, `\u{...}` — scan to the closing quote.
        while j < b.len() && b[j] != b'\'' {
            j += 1;
        }
        return (j < b.len()).then_some(j + 1 - i);
    }
    // One UTF-8 scalar (1..=4 bytes) then the closing quote; otherwise a lifetime.
    let width = match b[j] {
        c if c < 0x80 => 1,
        c if c >= 0xF0 => 4,
        c if c >= 0xE0 => 3,
        _ => 2,
    };
    (j + width < b.len() && b[j + width] == b'\'').then_some(j + width + 1 - i)
}

/// True if `inner` (an assertion's argument list) is a constant expression: it
/// has at least one literal (numeric, boolean, string, or char) and, after
/// recognizing numeric type suffixes/radixes, the boolean keywords, string and
/// char literal *contents*, the `as` keyword, and primitive type names as
/// non-identifiers, no identifier remains. Catches the laundered forms
/// `8u8 + 4u8 + 4u8, 16u8` (a type suffix is not a real symbol),
/// `assert!(true)`, `assert_eq!(8 + 4 + 4, 16, "header size")` (a message's
/// words are text, not symbols) and `(8 + 4 + 4) as u32, 16` (a cast target
/// is a type, not a symbol), while letting `value()` through.
fn inner_is_constant(inner: &str) -> bool {
    let b = inner.as_bytes();
    let mut i = 0;
    let mut has_lit = false;
    let mut has_ident = false;
    while i < b.len() {
        let c = b[i];
        if c == b'"' {
            has_lit = true;
            match string_literal_len(b, i) {
                Some(n) => i += n,
                None => break,
            }
            continue;
        }
        if c == b'\'' {
            match char_literal_len(b, i) {
                Some(n) => {
                    has_lit = true;
                    i += n;
                }
                None => i += 1, // a lifetime tick; the name after it is scanned as a word
            }
            continue;
        }
        if c.is_ascii_digit() {
            // One numeric literal incl. radix prefix, '.', '_', and type suffix.
            has_lit = true;
            i += 1;
            while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'.' || b[i] == b'_') {
                i += 1;
            }
            continue;
        }
        if c.is_ascii_alphabetic() || c == b'_' {
            let start = i;
            while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                i += 1;
            }
            // start..i sit on ASCII boundaries, so this slice is always valid.
            let word = &inner[start..i];
            // A string prefix (`b"..."`, `r"..."`, `br#"..."#`, `c"..."`) or a
            // byte-char prefix (`b'x'`) is part of the literal, not a symbol.
            if i < b.len() && matches!(word, "b" | "r" | "br" | "c" | "cr") {
                let len = match b[i] {
                    b'"' if !word.contains('r') => string_literal_len(b, i),
                    b'"' | b'#' => raw_string_len(b, i),
                    b'\'' if word == "b" => char_literal_len(b, i),
                    _ => None,
                };
                if let Some(n) = len {
                    has_lit = true;
                    i += n;
                    continue;
                }
            }
            match word {
                "true" | "false" => has_lit = true,
                "as" => {}
                w if PRIMITIVE_TYPES.contains(&w) => {}
                _ => has_ident = true,
            }
            continue;
        }
        i += 1;
    }
    !has_ident && has_lit
}

/// True if `body` contains at least one assertion whose argument list is a
/// constant expression (no identifier), e.g. `assert_eq!(8 + 4 + 4, 16)`.
///
/// The argument list is the delimiter group directly after the `!` (optionally
/// after whitespace), in any of the three delimiters a macro accepts. A mention
/// of the name with no group after it (a comment, prose) is not an invocation.
fn body_is_tautological(body: &str) -> bool {
    let bytes = body.as_bytes();
    for macro_name in ["assert_eq!", "assert_ne!", "assert!"] {
        let mut idx = 0;
        while let Some(pos) = body[idx..].find(macro_name) {
            let after = idx + pos + macro_name.len();
            idx = after;
            let open = body.len() - body[after..].trim_start().len();
            let close = match bytes.get(open) {
                Some(b'(') => b')',
                Some(b'[') => b']',
                Some(b'{') => b'}',
                _ => continue,
            };
            if let Some(end) = matching_delim(bytes, open, bytes[open], close) {
                if inner_is_constant(&body[open + 1..end]) {
                    return true;
                }
                idx = end;
            }
        }
    }
    false
}

fn lint_tautological_tests(root: &Path, files: &[PathBuf]) -> Vec<Violation> {
    let test_attr = "#[test]";
    let mut out = Vec::new();
    for f in files.iter().filter(|f| has_ext(f, "rs")) {
        let text = read_text_lossy(f);
        let bytes = text.as_bytes();
        let mut idx = 0;
        while let Some(pos) = text[idx..].find(test_attr) {
            let at = idx + pos;
            if let Some(brace_rel) = text[at..].find('{') {
                let bstart = at + brace_rel;
                if let Some(bend) = matching_delim(bytes, bstart, b'{', b'}') {
                    let body = &text[bstart + 1..bend];
                    if body_is_tautological(body) {
                        out.push(Violation {
                            lint: "tautology".to_string(),
                            path: rel(root, f),
                            detail:
                                "a test asserts only constant expressions (no symbol exercised)"
                                    .to_string(),
                        });
                    }
                    idx = bend;
                    continue;
                }
            }
            idx = at + test_attr.len();
        }
    }
    out
}

// --- verify-isolation -----------------------------------------------------

fn lint_verify_isolation(root: &Path, files: &[PathBuf]) -> Vec<Violation> {
    let mut out = Vec::new();

    // (1) A verify* workspace MEMBER (the explicit members list).
    let ws = root.join("Cargo.toml");
    if let Ok(text) = fs::read_to_string(&ws) {
        if let Ok(val) = text.parse::<toml::Value>() {
            if let Some(members) = val
                .get("workspace")
                .and_then(|w| w.get("members"))
                .and_then(|m| m.as_array())
            {
                for m in members {
                    if let Some(s) = m.as_str() {
                        if s.starts_with("verify") || s.contains("/verify") {
                            out.push(Violation {
                                lint: "verify-isolation".to_string(),
                                path: "Cargo.toml".to_string(),
                                detail: format!(
                                    "verification member {s:?} must live in a SEPARATE workspace so it cannot break the substrate build"
                                ),
                            });
                        }
                    }
                }
            }
        }
    }

    // (2) cargo also compiles PATH dependencies of substrate crates, so a
    // `verify-* = { path = "../verify-*" }` edge enters the build graph without
    // being a workspace member — the most natural way to reintroduce the exact
    // predecessor failure. Scan every manifest's dependency tables.
    for f in files.iter().filter(|f| is_cargo_manifest(f)) {
        let text = read_text_lossy(f);
        let val = match text.parse::<toml::Value>() {
            Ok(v) => v,
            Err(_) => continue,
        };
        // The plain tables and their `[target.<cfg>.*]` twins: cargo compiles both.
        let sects = ["dependencies", "dev-dependencies", "build-dependencies"];
        let mut tables = Vec::new();
        for sect in sects {
            if let Some(t) = val.get(sect).and_then(|v| v.as_table()) {
                tables.push((sect.to_string(), t));
            }
        }
        if let Some(targets) = val.get("target").and_then(|v| v.as_table()) {
            for (cfg, t) in targets {
                for sect in sects {
                    if let Some(d) = t.get(sect).and_then(|v| v.as_table()) {
                        tables.push((format!("target.{cfg}.{sect}"), d));
                    }
                }
            }
        }
        for (sect, tbl) in tables {
            for (name, spec) in tbl {
                let path_basename_is_verify = spec
                    .as_table()
                    .and_then(|s| s.get("path"))
                    .and_then(|p| p.as_str())
                    .map(|p| {
                        p.rsplit(['/', '\\'])
                            .next()
                            .unwrap_or(p)
                            .starts_with("verify")
                    })
                    .unwrap_or(false);
                if name.starts_with("verify") || path_basename_is_verify {
                    out.push(Violation {
                        lint: "verify-isolation".to_string(),
                        path: rel(root, f),
                        detail: format!(
                            "{sect} edge {name:?} pulls a verify* crate into the substrate build graph; verification tooling must live in a SEPARATE workspace"
                        ),
                    });
                }
            }
        }
    }

    out
}

// --- doc-tamper -----------------------------------------------------------

fn lint_doc_tamper(root: &Path) -> Vec<Violation> {
    let mut out = Vec::new();
    let manifest_path = root.join("evidence").join("manifest.toml");
    let readme_path = root.join("README.md");
    if !manifest_path.exists() || !readme_path.exists() {
        return out; // nothing to check (e.g. a fixture subtree)
    }
    // A manifest that does not load is reported by `manifest-integrity`
    // (which owns the manifest's own validity); there is no block to compare.
    let m = match Manifest::load(&manifest_path) {
        Ok(m) => m,
        Err(_) => return out,
    };
    let expected = render::render_block(&m);
    let readme = fs::read_to_string(&readme_path).unwrap_or_default();
    match render::extract(&readme) {
        None => out.push(Violation {
            lint: "doc-tamper".to_string(),
            path: "README.md".to_string(),
            detail: "evidence block markers are missing, out of order, or duplicated".to_string(),
        }),
        Some(actual) => {
            // Compare CONTENT, not checkout line-ending policy: a Windows clone
            // with git's default `core.autocrlf=true` smudges README.md to CRLF
            // while the renderer always emits `\n` — the same block, different
            // bytes. Normalizing both sides keeps the lint about tamper (claim
            // drift), which is what it exists to catch; a real edit still fails.
            let normalize = |s: &str| s.replace("\r\n", "\n");
            if normalize(&actual).trim() != normalize(&expected).trim() {
                out.push(Violation {
                    lint: "doc-tamper".to_string(),
                    path: "README.md".to_string(),
                    detail:
                        "generated evidence block is stale; run `astream-evidence render --write`"
                            .to_string(),
                });
            }
        }
    }
    out
}

// --- manifest-integrity ---------------------------------------------------

/// Programs that exit zero without exercising any project artifact. A claim
/// backed by one of these is decorative "evidence" — the predecessor's failure where
/// a confident claim sits atop a command that proves nothing. The file-dump
/// tools (`cat`/`head`/`tail`) are here too: echoing a committed golden file
/// hashes green while running none of the product code the claim describes.
/// This is a DENYLIST: it narrows the class (any other exit-0 program passes
/// the gate); the kind-shape rules below close it for `test`/`build` claims.
const NOOP_PROGRAMS: &[&str] = &["true", ":", "echo", "printf", "cat", "head", "tail"];

/// `[package].name` of a Cargo manifest, if it is a package (not a bare
/// workspace root).
fn package_name(cargo_toml: &Path) -> Option<String> {
    let text = fs::read_to_string(cargo_toml).ok()?;
    let val = text.parse::<toml::Value>().ok()?;
    val.get("package")?
        .get("name")?
        .as_str()
        .map(|s| s.to_string())
}

/// Map every crate name in the tree to its directory.
fn crate_dirs(files: &[PathBuf]) -> std::collections::HashMap<String, PathBuf> {
    let mut map = std::collections::HashMap::new();
    for f in files.iter().filter(|f| is_cargo_manifest(f)) {
        if let (Some(name), Some(dir)) = (package_name(f), f.parent()) {
            map.insert(name, dir.to_path_buf());
        }
    }
    map
}

/// A token that names a filesystem path (relative or absolute), as opposed to
/// a flag, a URL, or a bare word.
fn is_path_token(t: &str) -> bool {
    t.contains('/') && !t.contains("://") && !t.starts_with('-')
}

/// Does cargo target `name` of `kind` (`"tests"` / `"examples"`) exist for
/// `pkg` (or any crate, if `pkg` is unspecified)? An unknown `pkg` is reported
/// separately, so here it resolves as "present" to avoid a double finding.
fn cargo_target_exists(
    crates: &std::collections::HashMap<String, PathBuf>,
    pkg: Option<&str>,
    kind: &str,
    name: &str,
) -> bool {
    let file = format!("{name}.rs");
    match pkg {
        Some(p) => match crates.get(p) {
            Some(dir) => dir.join(kind).join(&file).exists(),
            None => true,
        },
        None => crates
            .values()
            .any(|dir| dir.join(kind).join(&file).exists()),
    }
}

/// Why a claim's command does not fit its declared kind, if it does not. The
/// runner judges a claim by its kind, so the command must be the shape that
/// judgement assumes: a `test` claim passes on libtest's counted results (so
/// it must be `cargo test`), a `build` claim on a compile (`cargo build` /
/// `cargo check`), a `selftest` on a pinned output hash. A claim of another
/// shape under one of these kinds would be judged by a check that cannot bite.
fn kind_shape_violation(kind: &str, command: &str, has_sha: bool) -> Option<String> {
    let sub = cargo_subcommand(command);
    match kind {
        "test" if sub != Some("test") => Some(format!(
            "kind = \"test\" claims pass on libtest's counted results, so the command must be \
             `cargo test ...`; got {command:?}"
        )),
        "build" if !matches!(sub, Some("build") | Some("check")) => Some(format!(
            "kind = \"build\" claims must run `cargo build ...` or `cargo check ...`; got {command:?}"
        )),
        "selftest" if !has_sha => Some(
            "selftest claim pins no expected_output_sha — output drift would never be detected"
                .to_string(),
        ),
        _ => None,
    }
}

/// The first shell construct in `command` (run as `sh -c`) that can turn a
/// failing step into exit 0 — `||`, `;`, a newline, a pipe, a background `&`,
/// or a leading `!` — outside quotes. `&&` propagates a failure and is allowed;
/// so is a redirection such as `2>&1`.
fn status_masking_operator(command: &str) -> Option<&'static str> {
    if command.split_whitespace().next() == Some("!") {
        return Some("`!`");
    }
    let b = command.as_bytes();
    let (mut single, mut double) = (false, false);
    let mut i = 0;
    while i < b.len() {
        let c = b[i];
        if single {
            single = c != b'\'';
        } else if c == b'\\' {
            i += 1; // outside single quotes the next byte is literal
        } else if double {
            double = c != b'"';
        } else {
            match c {
                b'\'' => single = true,
                b'"' => double = true,
                b';' => return Some("`;`"),
                b'\n' => return Some("a newline"),
                b'|' if b.get(i + 1) == Some(&b'|') => return Some("`||`"),
                b'|' => return Some("a pipe `|`"),
                b'&' if b.get(i + 1) == Some(&b'&') => i += 1,
                b'&' if i > 0 && matches!(b[i - 1], b'>' | b'<') => {}
                b'&' => return Some("a background `&`"),
                _ => {}
            }
        }
        i += 1;
    }
    None
}

/// Bind each manifest claim to reality: reject a manifest that does not load,
/// no-op commands, commands that can mask a failing exit status, commands that
/// do not fit their kind, and commands that cite
/// an artifact (path, script, or cargo target/package) the tree does not
/// contain. This narrows the decorative-proof class and closes the
/// cited-but-missing-evidence class at *gate* time, before `run` is invoked.
fn lint_manifest_integrity(root: &Path, files: &[PathBuf]) -> Vec<Violation> {
    let mut out = Vec::new();
    let manifest_path = root.join("evidence").join("manifest.toml");
    if !manifest_path.exists() {
        return out; // no manifest to check (e.g. a fixture subtree)
    }
    let m = match Manifest::load(&manifest_path) {
        Ok(m) => m,
        Err(e) => {
            out.push(Violation {
                lint: "manifest-integrity".to_string(),
                path: "evidence/manifest.toml".to_string(),
                detail: e,
            });
            return out;
        }
    };
    let crates = crate_dirs(files);

    for claim in &m.claim {
        let cmd = claim.command.trim();
        let toks: Vec<&str> = cmd.split_whitespace().collect();
        let here = format!("evidence/manifest.toml [{}]", claim.id);

        if toks.is_empty() {
            out.push(Violation {
                lint: "manifest-integrity".to_string(),
                path: here,
                detail: "claim has an empty command — it exercises nothing".to_string(),
            });
            continue;
        }

        // A regression bound that can never fire is silent theater: a metric
        // floor/ceiling with no metric name, or a `bench` claim asserting no
        // metric at all, would pass `run` vacuously. Reject at gate time.
        if claim.metric.is_none() && (claim.min_value.is_some() || claim.max_value.is_some()) {
            out.push(Violation {
                lint: "manifest-integrity".to_string(),
                path: here.clone(),
                detail:
                    "sets min_value/max_value without a metric name — the bound is never enforced"
                        .to_string(),
            });
        }
        if claim.kind == "bench" && claim.metric.is_none() {
            out.push(Violation {
                lint: "manifest-integrity".to_string(),
                path: here.clone(),
                detail: "bench claim has no metric — it asserts no floor/ceiling".to_string(),
            });
        }
        if let Some(detail) =
            kind_shape_violation(&claim.kind, cmd, claim.expected_output_sha.is_some())
        {
            out.push(Violation {
                lint: "manifest-integrity".to_string(),
                path: here.clone(),
                detail,
            });
        }
        if let Some(op) = status_masking_operator(cmd) {
            out.push(Violation {
                lint: "manifest-integrity".to_string(),
                path: here.clone(),
                detail: format!(
                    "command uses {op}, which can discard a failing exit status (`cargo test ... \
                     || true` exits 0 whatever the tests did); chain steps with `&&`"
                ),
            });
        }

        // The program is what `sh -c` runs: past any leading `VAR=value`.
        let prog_base = command_program(cmd).unwrap_or("");
        if NOOP_PROGRAMS.contains(&prog_base) {
            out.push(Violation {
                lint: "manifest-integrity".to_string(),
                path: here,
                detail: format!(
                    "no-op command {cmd:?} backs claim text {:?} — decorative evidence; \
                     the command must exercise product code",
                    claim.text
                ),
            });
            continue;
        }

        // Validate cited artifacts: explicit paths, plus cargo --test/--example
        // targets and -p packages. Leading `VAR=value` assignments are the
        // program's environment, not paths the claim cites.
        let mut pkg: Option<&str> = None;
        let mut i = toks.iter().take_while(|t| is_env_assignment(t)).count();
        while i < toks.len() {
            let t = toks[i];
            let next = toks.get(i + 1).copied();
            match t {
                "-p" | "--package" => {
                    if let Some(name) = next {
                        pkg = Some(name);
                        if !crates.is_empty() && !crates.contains_key(name) {
                            out.push(Violation {
                                lint: "manifest-integrity".to_string(),
                                path: here.clone(),
                                detail: format!("cites unknown crate {name:?} (-p)"),
                            });
                        }
                        i += 2;
                        continue;
                    }
                }
                "--test" | "--example" | "--bench" => {
                    if let Some(name) = next {
                        let (dir, singular) = match t {
                            "--test" => ("tests", "test"),
                            "--bench" => ("benches", "bench"),
                            _ => ("examples", "example"),
                        };
                        if !cargo_target_exists(&crates, pkg, dir, name) {
                            out.push(Violation {
                                lint: "manifest-integrity".to_string(),
                                path: here.clone(),
                                detail: format!(
                                    "cites cargo {singular} target {name:?} that does not exist"
                                ),
                            });
                        }
                        i += 2;
                        continue;
                    }
                }
                _ => {
                    if is_path_token(t) && !root.join(t).exists() {
                        out.push(Violation {
                            lint: "manifest-integrity".to_string(),
                            path: here.clone(),
                            detail: format!("cites path {t:?} that does not exist in the tree"),
                        });
                    }
                }
            }
            i += 1;
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    // The cfg-feature trigger is assembled at runtime so this file never
    // contains it (the gate scans its own source).
    fn cfg_ref(sep: &str, name: &str) -> String {
        format!("#[cfg({}{sep}\"{name}\")]", "feature")
    }

    #[test]
    fn feature_names_accepts_any_ascii_whitespace_around_eq() {
        let text = format!(
            "{}\nfn a() {{}}\n{}\nfn b() {{}}\n{}\nfn c() {{}}\n",
            cfg_ref(" = ", "one"),
            cfg_ref(" =\n    ", "two"),
            cfg_ref("\t=\r\n", "three")
        );
        assert_eq!(feature_names(&text), vec!["one", "two", "three"]);
    }

    #[test]
    fn feature_names_ignores_ordinary_code_outside_a_cfg_predicate() {
        // The whitespace-tolerant scan must not fire on a binding that merely
        // shares the word. The lint is a hard blocker with no allow mechanism,
        // so a false positive here is an unexplainable merge stop.
        assert!(feature_names("let feature\n    = \"aead\";").is_empty());
        assert!(feature_names("let my_feature = \"aead\";").is_empty());
        // Still found in every predicate position, including inside `all(…)`.
        let word = "feature";
        assert_eq!(
            feature_names(&format!("#[cfg(all(unix, {word} = \"cap\"))]")),
            vec!["cap"]
        );
    }

    #[test]
    fn constant_only_assertions_are_recognised() {
        // The predecessor's form, the laundered suffix form, and a bool-only assert.
        assert!(inner_is_constant("8 + 4 + 4, 16"));
        assert!(inner_is_constant("8u8 + 4u8 + 4u8, 16u8"));
        assert!(inner_is_constant("true"));
        // A message argument's words are text, not symbols under test.
        assert!(inner_is_constant("8 + 4 + 4, 16, \"header size\""));
        assert!(inner_is_constant(
            "true, \"the {} invariant\", \"escaped \\\" quote\""
        ));
        assert!(inner_is_constant("8 + 4 + 4, 16, r#\"raw \"message\"\"#"));
        // Two string literals compared to each other exercise nothing either.
        assert!(inner_is_constant("\"abc\", \"abc\""));
        assert!(
            !inner_is_constant("b\"abc\".len(), 3"),
            "a method call is a symbol"
        );
        // A cast keyword and a primitive type are not symbols under test.
        assert!(inner_is_constant("(8 + 4 + 4) as u32, 16"));
        assert!(inner_is_constant("1u8 as usize + 2, 3"));
        // Char literals are literals; their contents are not identifiers.
        assert!(inner_is_constant("'a', 'a'"));
        assert!(inner_is_constant("'\\n', '\\n'"));
        assert!(inner_is_constant("b'x', 120"));
    }

    #[test]
    fn assertions_touching_a_symbol_are_not_constant() {
        assert!(!inner_is_constant("value(), 42"));
        assert!(!inner_is_constant("value(), 42, \"value is 42\""));
        assert!(!inner_is_constant("value() as i64, 42"));
        assert!(!inner_is_constant("x as u32, 16"));
        assert!(!inner_is_constant("HEADER_SIZE, 12"));
        assert!(!inner_is_constant("i32::MAX, 2147483647"));
        // Nothing at all is not a constant proof either.
        assert!(!inner_is_constant(""));
    }

    #[test]
    fn body_scan_finds_a_constant_assertion_among_real_ones() {
        // The macro names are assembled at runtime: a literal constant-only
        // assertion in this source would be flagged by the gate's own scan.
        let eq = format!("{}!", "assert_eq");
        let body = format!("let v = value();\n{eq}(v, 42);\n{eq}(8 + 4 + 4, 16, \"hdr\");");
        assert!(body_is_tautological(&body));
        let body = format!(
            "let v = value();\n{eq}(v, 42, \"value\");\n{}!(v > 0);",
            "assert"
        );
        assert!(!body_is_tautological(&body));
    }

    #[test]
    fn an_assertions_argument_list_is_the_group_right_after_its_bang() {
        let a = format!("{}!", "assert");
        // A macro may be invoked with any delimiter; a constant assertion in
        // brackets or braces is still a constant assertion.
        assert!(body_is_tautological(&format!("{a}[1 + 1 == 2];")));
        assert!(body_is_tautological(&format!("{a} {{ true }}")));
        // The name without an argument list (a comment, prose) is not an
        // invocation, so the next unrelated parenthesis is not its argument list.
        let body = format!("// {a} is not used here\nlet t = (1, 2);\ncheck(t);");
        assert!(!body_is_tautological(&body));
    }

    #[test]
    fn git_deps_in_patch_and_replace_tables_are_found() {
        let text = "[package]\nname = \"x\"\nversion = \"0.0.0\"\n\n[dependencies]\nsha2 = \"0.10\"\n\n[patch.crates-io]\nsha2 = { git = \"https://example.invalid/sha2\", rev = \"deadbeef\" }\n\n[patch.'https://example.invalid/reg']\nother = { git = \"https://example.invalid/other\" }\n\n[replace]\n\"toml:0.8.0\" = { git = \"https://example.invalid/toml\" }\n";
        let mut hits = manifest_git_deps(text);
        hits.sort();
        assert_eq!(hits, vec!["other", "sha2", "toml:0.8.0"]);
        // A path/registry redirect is not a git dependency.
        let text = "[patch.crates-io]\nsha2 = { path = \"vendor/sha2\" }\n";
        assert!(manifest_git_deps(text).is_empty());
    }

    #[test]
    fn git_sources_in_lockfile_are_found() {
        let text = "version = 4\n\n[[package]]\nname = \"local\"\nversion = \"0.0.0\"\n\n[[package]]\nname = \"sha2\"\nversion = \"0.10.8\"\nsource = \"registry+https://github.com/rust-lang/crates.io-index\"\n\n[[package]]\nname = \"sketchy\"\nversion = \"0.1.0\"\nsource = \"git+https://example.invalid/sketchy?rev=deadbeef#deadbeef\"\n";
        assert_eq!(lockfile_git_sources(text), vec!["sketchy"]);
    }

    #[test]
    fn kind_shape_rules() {
        assert!(kind_shape_violation("test", "cargo test --locked -p x", false).is_none());
        assert!(kind_shape_violation("test", "sh -c true", false).is_some());
        assert!(kind_shape_violation("test", "cargo run --example x", false).is_some());
        assert!(kind_shape_violation("build", "cargo build --locked --workspace", false).is_none());
        assert!(kind_shape_violation("build", "cargo check --locked", false).is_none());
        assert!(kind_shape_violation("build", "cargo --version", false).is_some());
        assert!(kind_shape_violation("selftest", "cargo run --example r", true).is_none());
        assert!(kind_shape_violation("selftest", "cargo run --example r", false).is_some());
        assert!(kind_shape_violation("bench", "BENCH_N=5 cargo run --example b", false).is_none());
    }
}
