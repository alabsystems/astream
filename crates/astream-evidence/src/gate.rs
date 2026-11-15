//! The merge gate. Each lint maps to a confirmed failure mode of the predecessor and
//! turns it into a hard, machine-checkable rejection:
//!
//! * `no-git-deps`        — the predecessor pinned 404 git revisions; the public repo
//!   would not build. astream forbids git dependencies — in every dependency
//!   table, in `[patch]` / `[replace]` redirects, and as a `git+` source in
//!   `Cargo.lock` (the ground truth for what cargo fetches).
//! * `undeclared-cfg`     — a templating typo in a feature name silently
//!   dead-coded a module.
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
//! * `stock-lexable`      — inline Clean islands broke every stock-compiled build
//!   of astream (aterm's cross cells and its Linux lane,
//!   2026-10-17): no stock rustc can lex `clean { … }`
//!   or parse a bare `ensures` clause. An island outside
//!   a `*_island.rs` file, an island file mounted without
//!   `cfg(clean_islands)`, and a contract clause outside
//!   `contract_fn!` are rejected.
//! * `doc-tamper`         — the README cited a status file that did not exist.
//!   The generated evidence block must match the
//!   manifest render exactly.
//! * `manifest-integrity` — the predecessor counted decorative "proofs" as rigor and
//!   cited an evidence file that did not exist. A claim
//!   backed by a known no-op program (a denylist:
//!   `true`, `:`, `echo`, `printf`, `cat`, `head`,
//!   `tail`), whose command does not fit its kind
//!   (`test` must run `targo <lane> test`, `build`
//!   must run `targo <lane> build`/`check`, `selftest`
//!   must pin a hash), that runs the stock toolchain
//!   (`cargo`, `rustc`, a `+toolchain` selector) or a
//!   targo compilation that names no lane, or citing a
//!   path / cargo target that is absent is rejected.
//!   This binds the manifest to reality at
//!   *gate* time, not only when `run` executes it. It
//!   NARROWS the decorative-proof class — an exit-0
//!   program outside the denylist still passes the gate
//!   (and is caught by `run` only if its kind's pass
//!   condition bites).
//!
//! The lints are deliberately text-based and heuristic (the honest residual
//! gap: a determined author can still write a tautology that technically
//! touches a symbol). They are the enforcement spine, not a correctness proof.

use crate::manifest::{
    command_program, is_env_assignment, targo_call, targo_subcommand, Manifest, TARGO_LANES,
};
use crate::needles;
use crate::render;
use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "gate_island.rs"]
mod gate_island;
#[cfg(not(clean_islands))]
pub use crate::twins::gate_violation_advance;
#[cfg(clean_islands)]
pub use gate_island::gate_violation_advance;

contract_fn! {
    /// Verified check that a merge-gate scan produced zero findings (`violations == 0`),
    /// linked via `clean-kernel-defeq` to `gate_is_clean_isl`.
    #[must_use]
    pub const fn gate_is_clean(violations: usize) -> bool
    clauses [ensures result == (violations == 0)]
    {
        violations == 0
    }
}

/// A single gate finding.
#[derive(Debug, Clone, Eq)]
pub struct Violation {
    pub lint: String,
    pub path: String,
    pub detail: String,
}

impl PartialEq for Violation {
    fn eq(&self, other: &Self) -> bool {
        self.lint.as_bytes() == other.lint.as_bytes()
            && self.path.as_bytes() == other.path.as_bytes()
            && self.detail.as_bytes() == other.detail.as_bytes()
    }
}

impl std::fmt::Display for Violation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("[")?;
        f.write_str(self.lint.as_str())?;
        f.write_str("] ")?;
        f.write_str(self.path.as_str())?;
        f.write_str(": ")?;
        f.write_str(self.detail.as_str())
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
    match fs::read(dir.join("CACHEDIR.TAG")) {
        Ok(bytes) => bytes.starts_with(CACHEDIR_SIGNATURE.as_bytes()),
        Err(_) => false,
    }
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

#[inline]
const fn is_ascii_ws(b: u8) -> bool {
    matches!(b, b' ' | b'\t' | b'\n' | b'\r' | 0x0C)
}

#[inline]
const fn is_ascii_digit_byte(b: u8) -> bool {
    b >= b'0' && b <= b'9'
}

#[inline]
const fn is_ascii_alpha_byte(b: u8) -> bool {
    (b >= b'a' && b <= b'z') || (b >= b'A' && b <= b'Z')
}

#[inline]
const fn is_ascii_alnum_byte(b: u8) -> bool {
    is_ascii_digit_byte(b) || is_ascii_alpha_byte(b)
}

fn rel(root: &Path, p: &Path) -> String {
    p.strip_prefix(root).unwrap_or(p).display().to_string()
}

fn has_ext(p: &Path, ext: &str) -> bool {
    match p.extension() {
        Some(e) => e.to_str() == Some(ext),
        None => false,
    }
}

fn is_cargo_manifest(p: &Path) -> bool {
    match p.file_name() {
        Some(n) => n.to_str() == Some("Cargo.toml"),
        None => false,
    }
}

fn is_cargo_lockfile(p: &Path) -> bool {
    match p.file_name() {
        Some(n) => n.to_str() == Some("Cargo.lock"),
        None => false,
    }
}

/// Read a text file for scanning. Non-UTF-8 bytes are replaced, never used as
/// an excuse to skip the file: `read_to_string` fails on a single stray
/// Latin-1 byte, and an empty scan would let one byte hide every marker.
fn read_text_lossy(p: &Path) -> String {
    let Ok(bytes) = fs::read(p) else {
        return String::new();
    };
    if let Ok(s) = core::str::from_utf8(&bytes) {
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
                if path == own_fixtures {
                    continue;
                }
                if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
                    if SKIP_DIRS.contains(&name) || SKIP_HIDDEN.contains(&name) {
                        continue;
                    }
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
    v.extend(lint_stock_lexable(root, &files));
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
            if let Some(t) = spec.as_table() {
                if t.contains_key("git") {
                    hits.push(name.clone());
                }
            }
        }
    }
    let dep_sects = ["dependencies", "dev-dependencies", "build-dependencies"];
    for sect in dep_sects {
        if let Some(v) = val.get(sect) {
            if let Some(t) = v.as_table() {
                scan(t, &mut hits);
            }
        }
    }
    if let Some(w) = val.get("workspace") {
        if let Some(d) = w.get("dependencies") {
            if let Some(ws) = d.as_table() {
                scan(ws, &mut hits);
            }
        }
    }
    if let Some(tv) = val.get("target") {
        if let Some(targets) = tv.as_table() {
            for (_, t) in targets {
                for sect in dep_sects {
                    if let Some(dv) = t.get(sect) {
                        if let Some(d) = dv.as_table() {
                            scan(d, &mut hits);
                        }
                    }
                }
            }
        }
    }
    // `[patch.crates-io] foo = { git = ... }` (any source name) and `[replace]`.
    if let Some(pv) = val.get("patch") {
        if let Some(patch) = pv.as_table() {
            for (_, redirects) in patch {
                if let Some(t) = redirects.as_table() {
                    scan(t, &mut hits);
                }
            }
        }
    }
    if let Some(rv) = val.get("replace") {
        if let Some(t) = rv.as_table() {
            scan(t, &mut hits);
        }
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
    if let Some(pv) = val.get("package") {
        if let Some(packages) = pv.as_array() {
            for p in packages {
                let is_git = match p.get("source") {
                    Some(sv) => match sv.as_str() {
                        Some(s) => s.starts_with("git+"),
                        None => false,
                    },
                    None => false,
                };
                if is_git {
                    let name = match p.get("name") {
                        Some(nv) => nv.as_str().unwrap_or("?"),
                        None => "?",
                    };
                    hits.push(name.to_string());
                }
            }
        }
    }
    hits
}

fn lint_no_git_deps(root: &Path, files: &[PathBuf]) -> Vec<Violation> {
    let mut out = Vec::new();
    for f in files {
        if is_cargo_manifest(f) {
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
        if is_cargo_lockfile(f) {
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
    }
    out
}

// --- undeclared-cfg -------------------------------------------------------

fn declared_features(cargo_toml: &Path) -> HashSet<String> {
    let mut set = HashSet::new();
    let text = read_text_lossy(cargo_toml);
    let Ok(val) = text.parse::<toml::Value>() else {
        return set;
    };
    // `dep:NAME` anywhere in [features] suppresses NAME's implicit feature.
    let mut dep_prefixed = HashSet::new();
    if let Some(fv) = val.get("features") {
        if let Some(tbl) = fv.as_table() {
            for (k, members) in tbl {
                set.insert(k.clone());
                if let Some(arr) = members.as_array() {
                    for m in arr {
                        if let Some(s) = m.as_str() {
                            if let Some(dep) = s.strip_prefix("dep:") {
                                dep_prefixed.insert(dep.to_string());
                            }
                        }
                    }
                }
            }
        }
    }
    // Otherwise an optional dependency implicitly declares a like-named
    // feature, whether it is a normal or build dependency, target-specific or not.
    let sects = ["dependencies", "build-dependencies"];
    let mut tables = Vec::new();
    for s in sects {
        if let Some(v) = val.get(s) {
            if let Some(t) = v.as_table() {
                tables.push(t);
            }
        }
    }
    if let Some(tv) = val.get("target") {
        if let Some(targets) = tv.as_table() {
            for t in targets.values() {
                for s in sects {
                    if let Some(v) = t.get(s) {
                        if let Some(dt) = v.as_table() {
                            tables.push(dt);
                        }
                    }
                }
            }
        }
    }
    for deps in tables {
        for (name, spec) in deps {
            let optional = match spec.get("optional") {
                Some(o) => o.as_bool().unwrap_or(false),
                None => false,
            };
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
    match best {
        Some((_, f)) => Some(f),
        None => None,
    }
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
    while i < text.len() {
        let Some(tail) = text.get(i..) else {
            break;
        };
        let Some(p) = tail.find("feature") else {
            break;
        };
        let start = i.saturating_add(p);
        let mut k = start;
        while k > 0 {
            let Some(&prev) = b.get(k - 1) else {
                break;
            };
            if !is_ascii_ws(prev) {
                break;
            }
            k -= 1;
        }
        if k == 0 || !matches!(b.get(k - 1), Some(b'(' | b',')) {
            i = start.saturating_add("feature".len());
            continue;
        }
        let mut j = start.saturating_add("feature".len());
        while let Some(&ch) = b.get(j) {
            if !is_ascii_ws(ch) {
                break;
            }
            j = j.saturating_add(1);
        }
        if b.get(j) == Some(&b'=') {
            j = j.saturating_add(1);
            while let Some(&ch) = b.get(j) {
                if !is_ascii_ws(ch) {
                    break;
                }
                j = j.saturating_add(1);
            }
            if b.get(j) == Some(&b'"') {
                j = j.saturating_add(1);
                if let Some(rem) = text.get(j..) {
                    if let Some(end) = rem.find('"') {
                        if let Some(feat) = text.get(j..j.saturating_add(end)) {
                            out.push(feat.to_string());
                        }
                        i = j.saturating_add(end).saturating_add(1);
                        continue;
                    }
                }
            }
        }
        i = start.saturating_add("feature".len());
    }
    out
}

fn lint_undeclared_cfg(root: &Path, files: &[PathBuf]) -> Vec<Violation> {
    let mut crates: Vec<(PathBuf, HashSet<String>)> = Vec::new();
    for f in files {
        if is_cargo_manifest(f) {
            if let Some(d) = f.parent() {
                crates.push((d.to_path_buf(), declared_features(f)));
            }
        }
    }

    let mut out = Vec::new();
    for f in files {
        if !has_ext(f, "rs") {
            continue;
        }
        let text = read_text_lossy(f);
        let feats = nearest_features(f, &crates);
        for name in feature_names(&text) {
            let declared = match feats {
                Some(s) => s.contains(&name),
                None => false,
            };
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

fn should_scan_drift_file(f: &Path) -> bool {
    has_ext(f, "rs")
        || has_ext(f, "md")
        || has_ext(f, "toml")
        || has_ext(f, "txt")
        || has_ext(f, "yml")
        || has_ext(f, "yaml")
        || has_ext(f, "sh")
        || has_ext(f, "json")
        || f.extension().is_none()
}

/// Check whether the slice immediately following a task/fixme keyword starts with `(#<digits>)`.
#[must_use]
pub const fn has_numeric_issue_link(after_bytes: &[u8]) -> bool {
    let mut scan = after_bytes;
    let mut state = 0u8;
    while let &[b, ref tail @ ..] = scan {
        match state {
            0 => {
                if is_ascii_ws(b) {
                    scan = tail;
                    continue;
                }
                if b == b'(' {
                    state = 1;
                    scan = tail;
                    continue;
                }
                return false;
            }
            1 => {
                if b == b'#' {
                    state = 2;
                    scan = tail;
                    continue;
                }
                return false;
            }
            2 => {
                if is_ascii_digit_byte(b) {
                    state = 3;
                    scan = tail;
                    continue;
                }
                return false;
            }
            _ => {
                if is_ascii_digit_byte(b) {
                    scan = tail;
                    continue;
                }
                return b == b')';
            }
        }
    }
    false
}

fn lint_drift_markers(root: &Path, files: &[PathBuf]) -> Vec<Violation> {
    let task = needles::task_marker();
    let fixme = needles::fixme_marker();
    let incomplete = needles::incomplete_marker();
    let drift = needles::drift_marker();
    let extras = needles::extra_drift_markers();

    let mut out = Vec::new();
    for f in files {
        if !should_scan_drift_file(f) {
            continue;
        }
        let text = read_text_lossy(f);
        for (i, line) in text.lines().enumerate() {
            let line_no = i.saturating_add(1);
            if line.contains(&incomplete) {
                out.push(Violation {
                    lint: "drift-marker".to_string(),
                    path: rel(root, f),
                    detail: format!("line {line_no}: incomplete-checkpoint marker"),
                });
            }
            if line.contains(&drift) {
                out.push(Violation {
                    lint: "drift-marker".to_string(),
                    path: rel(root, f),
                    detail: format!("line {line_no}: session-drift marker"),
                });
            }
            for tag in &extras {
                if line.contains(tag.as_str()) {
                    out.push(Violation {
                        lint: "drift-marker".to_string(),
                        path: rel(root, f),
                        detail: format!("line {line_no}: work-in-progress checkpoint marker"),
                    });
                }
            }
            for kw in [&task, &fixme] {
                let mut unlinked = false;
                for (p, _) in line.match_indices(kw.as_str()) {
                    let after = line.get(p.saturating_add(kw.len())..).unwrap_or("");
                    if !has_numeric_issue_link(after.trim_start().as_bytes()) {
                        unlinked = true;
                        break;
                    }
                }
                if unlinked {
                    out.push(Violation {
                        lint: "drift-marker".to_string(),
                        path: rel(root, f),
                        detail: format!(
                            "line {line_no}: task note without an issue link (use the form NAME(#123))"
                        ),
                    });
                }
            }
        }
    }
    out
}

// --- tautology ------------------------------------------------------------

#[must_use]
pub const fn matching_delim(bytes: &[u8], open: usize, open_b: u8, close_b: u8) -> Option<usize> {
    let mut depth = 0usize;
    let mut i = open;
    while i < bytes.len() {
        let c = bytes[i];
        if c == open_b {
            depth = depth.saturating_add(1);
        } else if c == close_b {
            depth = depth.saturating_sub(1);
            if depth == 0 {
                return Some(i);
            }
        }
        i = i.saturating_add(1);
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
#[must_use]
pub const fn string_literal_len(b: &[u8], i: usize) -> Option<usize> {
    let mut j = i.saturating_add(1);
    while j < b.len() {
        match b[j] {
            b'\\' => j = j.saturating_add(2),
            b'"' => return j.saturating_add(1).checked_sub(i),
            _ => j = j.saturating_add(1),
        }
    }
    None
}

/// Length of the raw string literal whose `#`s or `"` start at `b[i]`
/// (`r"..."`, `r#"..."#`), or `None` if unterminated.
#[must_use]
pub const fn raw_string_len(b: &[u8], i: usize) -> Option<usize> {
    let mut hashes = 0usize;
    let mut quote_pos = i;
    while quote_pos < b.len() && b[quote_pos] == b'#' {
        hashes = hashes.saturating_add(1);
        quote_pos = quote_pos.saturating_add(1);
    }
    if quote_pos >= b.len() || b[quote_pos] != b'"' {
        return None;
    }
    let mut j = quote_pos.saturating_add(1);
    while j < b.len() {
        if b[j] == b'"' {
            let mut matched = 0usize;
            let mut h_pos = j.saturating_add(1);
            while matched < hashes {
                if h_pos >= b.len() || b[h_pos] != b'#' {
                    break;
                }
                matched = matched.saturating_add(1);
                h_pos = h_pos.saturating_add(1);
            }
            if matched == hashes {
                return j.saturating_add(1).saturating_add(hashes).checked_sub(i);
            }
        }
        j = j.saturating_add(1);
    }
    None
}

/// Length of the char literal starting at `b[i]` (which must be `'`) —
/// `'x'`, `'\n'`, `'\u{1F}'`, a multi-byte char — or `None` if this quote
/// opens a lifetime (`'a`) rather than a literal.
#[must_use]
pub const fn char_literal_len(b: &[u8], i: usize) -> Option<usize> {
    let mut j = i.saturating_add(1);
    if j >= b.len() {
        return None;
    }
    let first = b[j];
    if first == b'\\' {
        j = j.saturating_add(1);
        // Escape: `\n`, `\'`, `\\`, `\x41`, `\u{...}` — scan to the closing quote.
        while j < b.len() {
            if b[j] == b'\'' {
                return j.saturating_add(1).checked_sub(i);
            }
            j = j.saturating_add(1);
        }
        return None;
    }
    // One UTF-8 scalar (1..=4 bytes) then the closing quote; otherwise a lifetime.
    let width = if first < 0x80 {
        1usize
    } else if first >= 0xF0 {
        4
    } else if first >= 0xE0 {
        3
    } else {
        2
    };
    let close_idx = j.saturating_add(width);
    if close_idx < b.len() && b[close_idx] == b'\'' {
        close_idx.saturating_add(1).checked_sub(i)
    } else {
        None
    }
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
    while let Some(&c) = b.get(i) {
        if c == b'"' {
            has_lit = true;
            match string_literal_len(b, i) {
                Some(n) => i = i.saturating_add(n),
                None => break,
            }
            continue;
        }
        if c == b'\'' {
            match char_literal_len(b, i) {
                Some(n) => {
                    has_lit = true;
                    i = i.saturating_add(n);
                }
                None => i = i.saturating_add(1), // a lifetime tick; the name after it is scanned as a word
            }
            continue;
        }
        if is_ascii_digit_byte(c) {
            // One numeric literal incl. radix prefix, '.', '_', and type suffix.
            has_lit = true;
            i = i.saturating_add(1);
            while let Some(&ch) = b.get(i) {
                if is_ascii_alnum_byte(ch) || ch == b'.' || ch == b'_' {
                    i = i.saturating_add(1);
                } else {
                    break;
                }
            }
            continue;
        }
        if is_ascii_alpha_byte(c) || c == b'_' {
            let start = i;
            while let Some(&ch) = b.get(i) {
                if is_ascii_alnum_byte(ch) || ch == b'_' {
                    i = i.saturating_add(1);
                } else {
                    break;
                }
            }
            let word = inner.get(start..i).unwrap_or("");
            // A string prefix (`b"..."`, `r"..."`, `br#"..."#`, `c"..."`) or a
            // byte-char prefix (`b'x'`) is part of the literal, not a symbol.
            if let Some(&next_b) = b.get(i) {
                if matches!(word, "b" | "r" | "br" | "c" | "cr") {
                    let len = match next_b {
                        b'"' if !word.contains('r') => string_literal_len(b, i),
                        b'"' | b'#' => raw_string_len(b, i),
                        b'\'' if word == "b" => char_literal_len(b, i),
                        _ => None,
                    };
                    if let Some(n) = len {
                        has_lit = true;
                        i = i.saturating_add(n);
                        continue;
                    }
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
        i = i.saturating_add(1);
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
        while idx < body.len() {
            let Some(rem) = body.get(idx..) else {
                break;
            };
            let Some(pos) = rem.find(macro_name) else {
                break;
            };
            let after = idx.saturating_add(pos).saturating_add(macro_name.len());
            idx = after;
            let tail = body.get(after..).unwrap_or("");
            let open = body.len().saturating_sub(tail.trim_start().len());
            let (open_b, close) = match bytes.get(open) {
                Some(&b'(') => (b'(', b')'),
                Some(&b'[') => (b'[', b']'),
                Some(&b'{') => (b'{', b'}'),
                _ => continue,
            };
            if let Some(end) = matching_delim(bytes, open, open_b, close) {
                if let Some(inner) = body.get(open.saturating_add(1)..end) {
                    if inner_is_constant(inner) {
                        return true;
                    }
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
    for f in files {
        if !has_ext(f, "rs") {
            continue;
        }
        let text = read_text_lossy(f);
        let bytes = text.as_bytes();
        let mut idx = 0;
        while idx < text.len() {
            let Some(rem) = text.get(idx..) else {
                break;
            };
            let Some(pos) = rem.find(test_attr) else {
                break;
            };
            let at = idx.saturating_add(pos);
            if let Some(at_rem) = text.get(at..) {
                if let Some(brace_rel) = at_rem.find('{') {
                    let bstart = at.saturating_add(brace_rel);
                    if let Some(bend) = matching_delim(bytes, bstart, b'{', b'}') {
                        if let Some(body) = text.get(bstart.saturating_add(1)..bend) {
                            if body_is_tautological(body) {
                                out.push(Violation {
                                    lint: "tautology".to_string(),
                                    path: rel(root, f),
                                    detail:
                                        "a test asserts only constant expressions (no symbol exercised)"
                                            .to_string(),
                                });
                            }
                        }
                        idx = bend;
                        continue;
                    }
                }
            }
            idx = at.saturating_add(test_attr.len());
        }
    }
    out
}

// --- stock-lexable ---------------------------------------------------------

/// Is `line` (trimmed) the head of a Clean island, `clean {`?
fn opens_island(line: &str) -> bool {
    match line.strip_prefix("clean") {
        Some(rest) => rest.trim_start().starts_with('{'),
        None => false,
    }
}

/// Is `line` (trimmed) a bare Trust contract clause, written outside `contract_fn!`?
fn bare_contract_clause(line: &str) -> bool {
    line.starts_with("ensures ") || line.starts_with("requires ")
}

/// The module `line` (trimmed) declares out of line, if it names an island file:
/// `mod <name>_island;`, any visibility.
#[allow(clippy::question_mark)]
fn island_mount(line: &str) -> Option<&str> {
    let decl = match line.strip_prefix("pub") {
        Some(rest) => {
            let r = rest.trim_start();
            r.strip_prefix("(crate)").unwrap_or(r).trim_start()
        }
        None => line,
    };
    let Some(after_mod) = decl.strip_prefix("mod ") else {
        return None;
    };
    let Some(before_semi) = after_mod.trim().strip_suffix(';') else {
        return None;
    };
    let name = before_semi.trim();
    if name.ends_with("_island") {
        Some(name)
    } else {
        None
    }
}

/// Do the attribute lines directly above line `at` gate it on `cfg(clean_islands)`?
fn gated_on_clean_islands(lines: &[&str], at: usize) -> bool {
    let prefix = lines.get(..at).unwrap_or(&[]);
    let mut idx = prefix.len();
    while idx > 0 {
        idx -= 1;
        let Some(raw_attr) = prefix.get(idx) else {
            break;
        };
        let attr = raw_attr.trim();
        if !attr.starts_with("#[") {
            break;
        }
        if attr.starts_with("#[cfg(")
            && attr.contains("clean_islands")
            && !attr.contains("not(clean_islands)")
        {
            return true;
        }
    }
    false
}

/// A stock rustc opens every module a crate declares, cfg'd out or not, so the
/// Trust-only surface lives where it never looks: an island in a `*_island.rs` file
/// mounted under `#[cfg(clean_islands)]` (build.rs sets it only when the compiler
/// answers that it is Trust), a contracted fn inside `contract_fn!` (whose stock arm
/// drops the clause). Lexical, like the other lints: it reads lines, not syntax.
fn lint_stock_lexable(root: &Path, files: &[PathBuf]) -> Vec<Violation> {
    let mut out = Vec::new();
    for f in files {
        if !has_ext(f, "rs") {
            continue;
        }
        let island_file = match f.file_stem() {
            Some(s) => match s.to_str() {
                Some(stem) => stem.ends_with("_island"),
                None => false,
            },
            None => false,
        };
        let text = read_text_lossy(f);
        let mut lines: Vec<&str> = Vec::new();
        for l in text.lines() {
            lines.push(l);
        }
        for (i, raw) in lines.iter().enumerate() {
            let line = raw.trim_start();
            let line_no = i.saturating_add(1);
            if !island_file && opens_island(line) {
                out.push(Violation {
                    lint: "stock-lexable".to_string(),
                    path: rel(root, f),
                    detail: format!(
                        "line {line_no}: an inline `clean {{ … }}` island, which no stock rustc can lex: move it to a \
                         `<module>_island.rs` file mounted under `#[cfg(clean_islands)]`"
                    ),
                });
            }
            if !island_file && bare_contract_clause(line) {
                out.push(Violation {
                    lint: "stock-lexable".to_string(),
                    path: rel(root, f),
                    detail: format!(
                        "line {line_no}: a bare contract clause, which no stock rustc can parse: write the fn \
                         through `contract_fn!` (`clauses [ensures …]`)"
                    ),
                });
            }
            if let Some(name) = island_mount(line) {
                if !gated_on_clean_islands(&lines, i) {
                    out.push(Violation {
                        lint: "stock-lexable".to_string(),
                        path: rel(root, f),
                        detail: format!(
                            "line {line_no}: `mod {name};` is not gated on `#[cfg(clean_islands)]`, so a stock \
                             rustc opens the island"
                        ),
                    });
                }
            }
        }
    }
    out
}

// --- verify-isolation -----------------------------------------------------

fn lint_verify_isolation(root: &Path, files: &[PathBuf]) -> Vec<Violation> {
    let mut out = Vec::new();

    // (1) A verify* workspace MEMBER (the explicit members list).
    let ws = root.join("Cargo.toml");
    if let Ok(bytes) = fs::read(&ws) {
        if let Ok(text) = core::str::from_utf8(&bytes) {
            if let Ok(val) = text.parse::<toml::Value>() {
                if let Some(wv) = val.get("workspace") {
                    if let Some(mv) = wv.get("members") {
                        if let Some(members) = mv.as_array() {
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
            }
        }
    }

    // (2) cargo also compiles PATH dependencies of substrate crates, so a
    // `verify-* = { path = "../verify-*" }` edge enters the build graph without
    // being a workspace member — the most natural way to reintroduce the exact
    // predecessor failure. Scan every manifest's dependency tables.
    for f in files {
        if !is_cargo_manifest(f) {
            continue;
        }
        let text = read_text_lossy(f);
        let val = match text.parse::<toml::Value>() {
            Ok(v) => v,
            Err(_) => continue,
        };
        // The plain tables and their `[target.<cfg>.*]` twins: cargo compiles both.
        let sects = ["dependencies", "dev-dependencies", "build-dependencies"];
        let mut tables = Vec::new();
        for sect in sects {
            if let Some(v) = val.get(sect) {
                if let Some(t) = v.as_table() {
                    tables.push((sect.to_string(), t));
                }
            }
        }
        if let Some(tv) = val.get("target") {
            if let Some(targets) = tv.as_table() {
                for (cfg, t) in targets {
                    for sect in sects {
                        if let Some(dv) = t.get(sect) {
                            if let Some(d) = dv.as_table() {
                                tables.push((format!("target.{cfg}.{sect}"), d));
                            }
                        }
                    }
                }
            }
        }
        for (sect, tbl) in tables {
            for (name, spec) in tbl {
                let path_basename_is_verify = match spec.as_table() {
                    Some(s) => match s.get("path") {
                        Some(pv) => match pv.as_str() {
                            Some(p) => p
                                .rsplit(['/', '\\'])
                                .next()
                                .unwrap_or(p)
                                .starts_with("verify"),
                            None => false,
                        },
                        None => false,
                    },
                    None => false,
                };
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
    let readme = read_text_lossy(&readme_path);
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
            let actual_norm = actual.replace("\r\n", "\n");
            let expected_norm = expected.replace("\r\n", "\n");
            if actual_norm.trim() != expected_norm.trim() {
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
#[allow(clippy::question_mark, clippy::manual_map)]
fn package_name(cargo_toml: &Path) -> Option<String> {
    let Ok(bytes) = fs::read(cargo_toml) else {
        return None;
    };
    let Ok(text) = core::str::from_utf8(&bytes) else {
        return None;
    };
    let Ok(val) = text.parse::<toml::Value>() else {
        return None;
    };
    let Some(pkg) = val.get("package") else {
        return None;
    };
    let Some(name) = pkg.get("name") else {
        return None;
    };
    match name.as_str() {
        Some(s) => Some(s.to_string()),
        None => None,
    }
}

/// Map every crate name in the tree to its directory.
fn crate_dirs(files: &[PathBuf]) -> std::collections::HashMap<String, PathBuf> {
    let mut map = std::collections::HashMap::new();
    for f in files {
        if is_cargo_manifest(f) {
            if let (Some(name), Some(dir)) = (package_name(f), f.parent()) {
                map.insert(name, dir.to_path_buf());
            }
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
        None => {
            for dir in crates.values() {
                if dir.join(kind).join(&file).exists() {
                    return true;
                }
            }
            false
        }
    }
}

/// Why a claim's command does not fit its declared kind, if it does not. The
/// runner judges a claim by its kind, so the command must be the shape that
/// judgement assumes: a `test` claim passes on libtest's counted results (so
/// it must be `targo <lane> test`), a `build` claim on a compile (`targo
/// <lane> build` / `check`), a `selftest` on a pinned output hash. A claim of
/// another shape under one of these kinds would be judged by a check that
/// cannot bite.
fn kind_shape_violation(kind: &str, command: &str, has_sha: bool) -> Option<String> {
    let sub = targo_subcommand(command);
    match kind {
        "test" if sub != Some("test") => Some(format!(
            "kind = \"test\" claims pass on libtest's counted results, so the command must be \
             `targo --unverified test ...` (or `targo trust test ...`); got {command:?}"
        )),
        "build" if !matches!(sub, Some("build") | Some("check")) => Some(format!(
            "kind = \"build\" claims must run `targo --unverified build|check ...` (or `targo \
             trust build|check ...`); got {command:?}"
        )),
        "selftest" if !has_sha => Some(
            "selftest claim pins no expected_output_sha — output drift would never be detected"
                .to_string(),
        ),
        _ => None,
    }
}

/// Stock Rust toolchain programs. astream builds, tests and runs on the Trust
/// toolchain (`targo`, `trustc`), so a claim that reaches for one of these
/// asserts something about a compiler the project does not ship with.
const STOCK_PROGRAMS: &[&str] = &[
    "cargo",
    "rustc",
    "rustdoc",
    "rustup",
    "rustfmt",
    "cargo-clippy",
    "clippy-driver",
];

/// Targo verbs that compile, and so must name a lane: a bare `targo build`
/// is refused and a bare `targo run` proceeds unverified without anyone
/// having chosen that, and a nested `targo` does not inherit its parent's
/// lane either way.
const LANE_VERBS: &[&str] = &[
    "build", "check", "test", "run", "bench", "doc", "install", "rustc",
];

/// Why a claim command's toolchain use is wrong, if it is: a step (the
/// command is split on `&&`, the only chaining the masking rule allows) that
/// runs a stock toolchain program, selects a rustup toolchain with
/// `+toolchain`, or runs a compiling targo verb without naming its lane.
fn toolchain_violation(command: &str) -> Option<String> {
    for step in command.split("&&") {
        let step = step.trim();
        let prog = command_program(step).unwrap_or("");
        if STOCK_PROGRAMS.contains(&prog) {
            return Some(format!(
                "runs the stock Rust toolchain (`{prog}`): claims build and run on the Trust \
                 toolchain — `targo --unverified <verb>` or `targo trust <verb>`; got {command:?}"
            ));
        }
        let Some(call) = targo_call(step) else {
            continue;
        };
        if let Some(sel) = call.toolchain {
            return Some(format!(
                "`{sel}` selects a rustup toolchain; a Trust claim selects a lane ({}), not a \
                 toolchain; got {command:?}",
                TARGO_LANES.join(" / ")
            ));
        }
        if let (None, Some(verb)) = (call.lane, call.verb) {
            if LANE_VERBS.contains(&verb) {
                return Some(format!(
                    "`targo {verb}` names no lane: a nested targo does not inherit one, so the \
                     command must say `targo --unverified {verb}` or `targo trust {verb}`; got \
                     {command:?}"
                ));
            }
        }
    }
    None
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
    while let Some(&c) = b.get(i) {
        if single {
            single = c != b'\'';
        } else if c == b'\\' {
            i = i.saturating_add(1); // outside single quotes the next byte is literal
        } else if double {
            double = c != b'"';
        } else {
            match c {
                b'\'' => single = true,
                b'"' => double = true,
                b';' => return Some("`;`"),
                b'\n' => return Some("a newline"),
                b'|' if b.get(i.saturating_add(1)) == Some(&b'|') => return Some("`||`"),
                b'|' => return Some("a pipe `|`"),
                b'&' if b.get(i.saturating_add(1)) == Some(&b'&') => i = i.saturating_add(1),
                b'&' if i > 0 && matches!(b.get(i - 1), Some(b'>' | b'<')) => {}
                b'&' => return Some("a background `&`"),
                _ => {}
            }
        }
        i = i.saturating_add(1);
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
        let mut toks: Vec<&str> = Vec::new();
        for tok in cmd.split_whitespace() {
            toks.push(tok);
        }
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
        if let Some(detail) = toolchain_violation(cmd) {
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
                    "command uses {op}, which can discard a failing exit status (`targo \
                     --unverified test ... || true` exits 0 whatever the tests did); chain steps \
                     with `&&`"
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
        let mut i = 0usize;
        while i < toks.len() && is_env_assignment(toks[i]) {
            i = i.saturating_add(1);
        }
        while let Some(&t) = toks.get(i) {
            let next = toks.get(i.saturating_add(1)).copied();
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
                        i = i.saturating_add(2);
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
                        i = i.saturating_add(2);
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
            i = i.saturating_add(1);
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
        let shape = |kind, cmd, sha| kind_shape_violation(kind, cmd, sha);
        assert!(shape("test", "targo --unverified test --locked -p x", false).is_none());
        assert!(shape("test", "targo trust test --locked -p x", false).is_none());
        assert!(shape("test", "sh -c true", false).is_some());
        assert!(shape("test", "targo --unverified run --example x", false).is_some());
        // The stock driver is not a test run, whatever its verb.
        assert!(shape("test", "cargo test --locked -p x", false).is_some());
        assert!(shape(
            "build",
            "targo --unverified build --locked --workspace",
            false
        )
        .is_none());
        assert!(shape("build", "targo trust check --locked", false).is_none());
        assert!(shape("build", "targo --version", false).is_some());
        assert!(shape("build", "cargo build --locked", false).is_some());
        assert!(shape("selftest", "targo --unverified run --example r", true).is_none());
        assert!(shape("selftest", "targo --unverified run --example r", false).is_some());
        assert!(shape(
            "bench",
            "BENCH_N=5 targo --unverified run --example b",
            false
        )
        .is_none());
    }

    #[test]
    fn toolchain_rules() {
        let flagged =
            |cmd, needle: &str| toolchain_violation(cmd).is_some_and(|d| d.contains(needle));
        // Stock programs, also behind env assignments and in a later `&&` step.
        assert!(flagged(
            "cargo test --locked",
            "stock Rust toolchain (`cargo`)"
        ));
        assert!(flagged("BENCH_N=5 /usr/bin/cargo run", "(`cargo`)"));
        assert!(flagged("rustc --version", "(`rustc`)"));
        assert!(flagged("rustup run stable cargo test", "(`rustup`)"));
        assert!(flagged(
            "targo --unverified build --locked && cargo test --locked",
            "(`cargo`)"
        ));
        // A rustup toolchain selector is not a lane.
        assert!(flagged(
            "targo +nightly --unverified test",
            "`+nightly` selects"
        ));
        // A compiling verb must name its lane; fmt/tippy/metadata take none.
        assert!(flagged("targo test --locked", "`targo test` names no lane"));
        assert!(flagged("X=1 targo run -p x", "`targo run` names no lane"));
        assert!(flagged(
            "targo --unverified test -p a && targo test -p b",
            "names no lane"
        ));
        for fine in [
            "targo --unverified test --locked -p x",
            "targo trust check -p x",
            "BENCH_N=5 targo --unverified run --quiet --release -p x --example b",
            "targo --unverified test -p a && targo trust test -p b",
            "targo fmt --all -- --check",
            "sh scripts/x.sh",
        ] {
            assert!(toolchain_violation(fine).is_none(), "{fine:?} is fine");
        }
    }
}
